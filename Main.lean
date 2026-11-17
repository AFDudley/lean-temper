/-
  `def_to_structure`: the driver (see README.md).

    def_to_structure --checkout <armada-lean worktree> --slot <1-4> \
      --names RegistryConsistent,Adjudicator.IsDAG --report report.json [--resume]

  Steps:
  1. `lake build`, the linter modules, `scripts/type_lint.lean` (the "before" list).
  2. Import the target's modules into this process (discovery, and the parser
     for the repair loop).
  3. Discovery and the guards (`ArmadaLean/Spec/`, `git grep Spec\.<name>`).
  4. Conversion: `def` → `structure … where holds : body`, plus `P.iff`.
  5. The files that import a converted module, in dependency order, each
     through `lake serve`: open, read the diagnostics, decide one repair per
     error from the elaboration data (`DefToStructure.Patterns`), apply, send
     `didChange`, repeat until the file has no error and no silent projection.
     An edited module is rebuilt (`lake build <Module>`) before the next file
     opens. A round with an error and no repair stops the tool.
  6. One full check: `lake build`, the linter modules, `scripts/type_lint.lean`
     (the "after" list), `scripts/update_gate_baseline.py --hashes-only`,
     `bash scripts/check.sh --json`, and the JSON report.

  `--resume` continues a stopped run after a hand edit: it skips steps 1, 3
  and 4 and reads `<checkout>/.scratch/codemod/state.json`.
-/
import Lean
import DefToStructure.Lsp
import DefToStructure.Parse
import DefToStructure.Patterns
import DefToStructure.Discovery
import DefToStructure.Alias
import DefToStructure.ReplCheck

open Lean DefToStructure DefToStructure.Discovery

namespace DefToStructure

structure Args where
  checkout : System.FilePath
  slot : Nat
  names : Array String
  report : System.FilePath
  resume : Bool
  /-- `--alias WORKLIST.json`: the alias transform (`DefToStructure.Alias`). -/
  alias : Option System.FilePath := none
  /-- `--repl PATH`: the Lean REPL binary for the alias mode's checks. -/
  repl : Option System.FilePath := none

def parseArgs (args : List String) : Except String Args := do
  let mut checkout := ""
  let mut slot := 0
  let mut names := ""
  let mut report := ""
  let mut resume := false
  let mut alias := ""
  let mut repl := ""
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--checkout" :: v :: r => checkout := v; rest := r
    | "--slot" :: v :: r => slot := v.toNat!; rest := r
    | "--names" :: v :: r => names := v; rest := r
    | "--report" :: v :: r => report := v; rest := r
    | "--resume" :: r => resume := true; rest := r
    | "--alias" :: v :: r => alias := v; rest := r
    | "--repl" :: v :: r => repl := v; rest := r
    | a :: _ => throw s!"unknown argument {a}"
    | [] => pure ()
  if checkout.isEmpty || slot == 0 || (names.isEmpty && alias.isEmpty) || report.isEmpty || (resume && !alias.isEmpty)
      || (!alias.isEmpty && repl.isEmpty) then
    throw "usage: def_to_structure --checkout DIR --slot N (--names A,B [--resume] | --alias WORKLIST.json --repl REPL) --report FILE"
  return { checkout, slot, names := (names.splitOn ",").map (·.trimAscii.copy) |>.filter (· ≠ "") |>.toArray,
           report, resume, alias := if alias.isEmpty then none else some alias,
           repl := if repl.isEmpty then none else some repl }

/-- A stop: the tool changes nothing more and reports `msg`. -/
structure StopError where
  msg : String

structure RepairRecord where
  file : String
  line : Nat
  col : Nat
  pattern : String
  pred : Option String
  detail : String
  deriving ToJson, FromJson, Inhabited

structure Timing where
  command : String
  seconds : Float
  exit : Nat
  deriving ToJson, FromJson

/-- The last `n` bytes of `s` (whole characters). -/
def tail (s : String) (n : Nat) : String :=
  if s.length ≤ n then s else (s.toSubstring.drop (s.length - n)).toString

structure PredReport where
  name : String
  path : String
  line : Nat
  alreadyConverted : Bool
  iff : String
  deriving ToJson, FromJson

/-- The persisted state of a run (`.scratch/codemod/state.json`). -/
structure State where
  head : String
  names : Array String
  preds : Array Pred
  predReports : Array PredReport
  files : Array String
  nextIndex : Nat
  repairs : Array RepairRecord
  /-- `constructor` tactics this run inserted: file, byte offset in the current text. -/
  inserted : Array (String × Nat) := #[]
  rounds : Array Json
  stops : Array String
  lintBefore : Json
  timings : Array Timing
  deriving ToJson, FromJson

structure Env where
  args : Args
  root : System.FilePath
  logDir : System.FilePath
  state : IO.Ref State
  lintBeforeFindings : IO.Ref (Array String)
  seen : IO.Ref (Std.HashSet String)
  /-- The alias mode's per-finding results (`stepAlias`). -/
  aliasReport : IO.Ref Json

abbrev M := ReaderT Env (ExceptT StopError IO)

def stop (msg : String) : M α := throw ⟨msg⟩

def modifyState (f : State → State) : M Unit := do (← read).state.modify f

def saveState : M Unit := do
  let e ← read
  IO.FS.writeFile (e.logDir / "state.json") ((toJson (← e.state.get)).pretty ++ "\n")

def log (s : String) : M Unit := IO.eprintln s

-- --- processes ---------------------------------------------------------------

/-- Run a command in the checkout under the run's `flock` slot, logging its output. -/
def runCmd (args : Array String) (logName : String) (cwd : Option System.FilePath := none) : M IO.Process.Output := do
  let e ← read
  let home := (← IO.getEnv "HOME").getD ""
  let lock := s!"{home}/.cache/lean-run/locks/slot-{e.args.slot}.lock"
  let t0 ← IO.monoMsNow
  let spawnArgs : IO.Process.SpawnArgs :=
    { cmd := "flock", args := #[lock, "nice"] ++ args, cwd := cwd.getD e.root, env := ← leanEnv }
  let out ← IO.Process.output spawnArgs
  let dt := (Float.ofNat ((← IO.monoMsNow) - t0)) / 1000.0
  IO.FS.writeFile (e.logDir / logName) (out.stdout ++ "\n--- stderr ---\n" ++ out.stderr)
  modifyState fun s => { s with timings := s.timings.push ⟨" ".intercalate args.toList, dt, out.exitCode.toNat⟩ }
  log s!"[lean] {(" ".intercalate args.toList).take 80} … exit {out.exitCode} in {dt}s"
  return out

def git (args : Array String) : M IO.Process.Output := do
  let sa : IO.Process.SpawnArgs := { cmd := "git", args, cwd := (← read).root }
  IO.Process.output sa

/-- `lake build`, then the linter modules the gate builds too. -/
def fullBuild (tag : String) : M (Bool × String) := do
  let p1 ← runCmd #["lake", "build"] s!"build-{tag}.log"
  if p1.exitCode != 0 then return (false, p1.stdout ++ p1.stderr)
  let p2 ← runCmd #["lake", "build", "ArmadaLean.Lint.TypeDoctrine", "ArmadaLean.Lint.TypeDoctrineTest"]
    s!"build-lint-{tag}.log"
  return (p2.exitCode == 0, p1.stdout ++ p1.stderr ++ p2.stdout ++ p2.stderr)

/-- `scripts/type_lint.lean`: the finding lines and the summary. -/
def typeLint (tag : String) : M (Array String × Json) := do
  let p ← runCmd #["lake", "env", "lean", "scripts/type_lint.lean"] s!"lint-{tag}.log"
  let lines := p.stdout.splitOn "\n"
  let findings := lines.filter (fun l => l.startsWith "{" && !l.startsWith "{\"summary\"") |>.toArray
  let summaries := lines.filter (·.startsWith "{\"summary\"")
  if p.exitCode != 0 || summaries.isEmpty then
    stop s!"scripts/type_lint.lean failed (exit {p.exitCode}):\n{(tail p.stdout 2000)}\n{(tail p.stderr 2000)}"
  IO.FS.writeFile ((← read).logDir / s!"lint-{tag}.jsonl") ("\n".intercalate findings.toList ++ "\n")
  match Json.parse summaries.getLast! with
  | .ok j => return (findings, j)
  | .error err => stop s!"type_lint summary is not JSON: {err}"

/-- A finding line without its `example` field: `repeatedPremise` picks the
    example from the group's uses, and that pick differs between runs. -/
def findingKey (line : String) : String :=
  match Json.parse line with
  | .ok (.obj kvs) => (Json.obj (kvs.erase "example")).compress
  | _ => line

-- --- the repair loop --------------------------------------------------------

def forbidden : List String := ["sorry", "admit", "axiom", "native_decide"]

def countOcc (hay needle : String) : Nat := (hay.splitOn needle).length - 1

def checkForbidden (before after : String) (where_ : String) : M Unit := do
  for w in forbidden do
    if countOcc after w > countOcc before w then
      stop s!"{where_}: the edit would insert `{w}`"

def writeFile (rel : String) (text : String) : M Unit := do
  if rel.startsWith "ArmadaLean/Spec/" then stop s!"{rel}: the tool never edits ArmadaLean/Spec/"
  IO.FS.writeFile ((← read).root / rel) text

/-- Shift the predicate offsets of `rel` by the edits just applied to it. -/
def shiftPreds (rel : String) (edits : Array Edit) : M Unit := do
  let shift (off : Nat) : Nat := Id.run do
    let mut o := off
    for e in edits do
      if e.stop ≤ off then o := o + e.replacement.utf8ByteSize - (e.stop - e.start)
    return o
  modifyState fun s => { s with
    preds := s.preds.map fun p =>
      if p.file == rel then { p with declIdOffset := shift p.declIdOffset, holdsOffset := shift p.holdsOffset } else p
    inserted := s.inserted.map fun (f, o) => if f == rel then (f, shift o) else (f, o) }

def predTexts : M PredTexts := do
  let e ← read
  let s ← e.state.get
  let mut m : Std.HashMap String FileMap := {}
  for p in s.preds do
    unless m.contains p.file do
      m := m.insert p.file (FileMap.ofString (← IO.FS.readFile (e.root / p.file)))
  return { fileMaps := m }

def locOfLink (l : Lsp.LocationLink) : Loc :=
  { uri := l.targetUri, line := l.targetSelectionRange.start.line, character := l.targetSelectionRange.start.character }

def headsOf (h : Lsp.Heads) : Heads := { head := h.head.map locOfLink, arg := h.arg.map locOfLink }

def mkOracle (c : Lsp.Client) (uri : String) (fm : FileMap) : Oracle :=
  let pos (off : Nat) : Lsp.Position := fm.utf8PosToLspPos ⟨off⟩
  { definition := fun off => do return (← c.definition uri (pos off)).map locOfLink
    expectedHead := fun off => do return (← c.expectedTypeHead uri (pos off)).map headsOf
    goalHead := fun off => do return headsOf (← c.goalHead uri (pos off))
    diagExprHeads := fun s e => do
      return (← c.diagExprHeads uri ⟨pos s, pos e⟩).map headsOf }

/-- Repair one file through the server until it has no error and no silent
    projection. Returns whether the file changed. -/
partial def repairFile (c : Lsp.Client) (env : Environment) (rel : String) : M Bool := do
  let e ← read
  let uri := Lsp.uriOf e.root rel
  let text0 ← IO.FS.readFile (e.root / rel)
  c.open uri text0
  let rec loop (round : Nat) (text : String) (changed : Bool) : M Bool := do
    let diags ← c.waitIdle uri
    let errors := diags.filter (·.severity? == some .error)
    let parsed ← Parse.parseFile env rel text
    unless parsed.parseErrors.isEmpty do
      stop s!"{rel}: the file does not parse: {parsed.parseErrors[0]!}"
    let fm := parsed.fileMap
    let trace ← IO.mkRef #[]
    let st ← e.state.get
    let ctx : Ctx := { env, parsed, preds := st.preds, predTexts := ← predTexts,
                       oracle := mkOracle c uri fm, trace,
                       inserted := st.inserted.filterMap fun (f, o) => if f == rel then some o else none }
    let mut chosen : Array (Repair × Nat × Nat) := #[]
    let mut taken : Array Edit := #[]
    let mut unmatched : Array Json := #[]
    -- the silent cases first, alone: they change the elaboration upstream of
    -- the diagnostics, so the diagnostics are decided on the next round
    for r in (← silentProjections ctx) ++ (← silentUnfolds ctx) ++ (← silentConstructors ctx) do
      if r.edits.any fun x => taken.any (conflicts x ·) then continue
      chosen := chosen.push (r, r.edits[0]!.start, 0)
      taken := taken ++ r.edits
    let errorsToDecide := if chosen.isEmpty then errors else #[]
    let ranges := errorsToDecide.map fun d =>
      let r := d.fullRange?.getD d.range
      ((fm.lspPosToUtf8Pos r.start).byteIdx, (fm.lspPosToUtf8Pos r.end).byteIdx, d)
    let sorted := ranges.qsort fun a b => a.1 > b.1 || (a.1 == b.1 && a.2.1 > b.2.1)
    for (s, en, d) in sorted do
      let lp := fm.utf8PosToLspPos ⟨s⟩
      match ← decide ctx s en with
      | none =>
        unmatched := unmatched.push (Json.mkObj [("line", toJson (lp.line + 1)), ("col", toJson lp.character), ("message", toJson d.message)])
      | some r =>
        if r.edits.any fun x => taken.any (conflicts x ·) then continue
        let key := s!"{rel}|{r.pattern}|{r.detail}|{(parsed.text.splitOn "\n")[lp.line]!}"
        if (← e.seen.get).contains key then
          stop s!"{rel}:{lp.line + 1}:{lp.character}: repair `{r.pattern}` would repeat on `{((parsed.text.splitOn "\n")[lp.line]!).trimAscii}`; the tool stops"
        chosen := chosen.push (r, s, 0)
        taken := taken ++ r.edits
    for line in ← trace.get do c.logLine s!"[decide] {rel} round {round}: {line}"
    modifyState fun st => { st with rounds := st.rounds.push (Json.mkObj [
      ("file", toJson rel), ("round", toJson round), ("errors", toJson errors.size),
      ("repairs", toJson chosen.size), ("unmatched", Json.arr unmatched)]) }
    if chosen.isEmpty then
      if errors.isEmpty then
        c.close uri
        return changed
      let u := unmatched[0]!
      stop s!"{rel}:{u.getObjValD "line"}:{u.getObjValD "col"}: no pattern matches:\n{(u.getObjValD "message").getStr?.toOption.getD ""}"
    let edits := chosen.flatMap fun (r, _, _) => r.edits
    let newText := applyEdits text edits
    checkForbidden text newText rel
    writeFile rel newText
    shiftPreds rel edits
    -- the `constructor`s this round inserts, at their offsets in the new text:
    -- moved by the edits that end before the insertion point (the insertion
    -- itself keeps its keyword at that point)
    let newInserted := chosen.filterMap fun (r, _, _) =>
      if r.pattern == "constructor" || r.pattern == "constructor-split" then
        let o := r.edits[0]!.start
        some (rel, edits.foldl (fun acc e => if e.stop < o then acc + e.replacement.utf8ByteSize - (e.stop - e.start) else acc) o)
      else none
    modifyState fun st => { st with inserted := st.inserted ++ newInserted }
    for (r, s, _) in chosen do
      let lp := fm.utf8PosToLspPos ⟨s⟩
      let key := s!"{rel}|{r.pattern}|{r.detail}|{(parsed.text.splitOn "\n")[lp.line]!}"
      e.seen.modify (·.insert key)
      let rec_ : RepairRecord :=
        { file := rel, line := lp.line + 1, col := lp.character, pattern := r.pattern, pred := r.pred, detail := r.detail }
      modifyState fun st => { st with repairs := st.repairs.push rec_ }
      log s!"[repair] {rel}:{lp.line + 1}:{lp.character} {r.pattern}: {r.detail}"
    saveState
    c.change uri newText
    loop (round + 1) newText true
  loop 1 text0 false

-- --- files and dependency order ---------------------------------------------

partial def leanFilesUnder (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for entry in ← dir.readDir do
    if ← entry.path.isDir then out := out ++ (← leanFilesUnder entry.path)
    else if entry.path.extension == some "lean" then out := out.push entry.path
  return out

/-- Every candidate file of the checkout, with its module name and imports. -/
def candidates (root : System.FilePath) : IO (Array (String × Name × Array Name)) := do
  let mut files : Array System.FilePath := #[root / "ArmadaLean.lean"]
  files := files ++ (← leanFilesUnder (root / "ArmadaLean"))
  files := files ++ (← leanFilesUnder (root / "docs" / "counterexamples"))
  let mut out := #[]
  for f in files do
    let rel := (f.toString.drop (root.toString.length + 1)).copy
    out := out.push (rel, moduleName rel, ← fileImports f)
  return out.qsort fun a b => a.1 < b.1

/-- The files that import a module of `roots` (transitively), roots first,
    in an order where every file comes after its imports. -/
def dependents (cands : Array (String × Name × Array Name)) (roots : Array Name) : Array String := Id.run do
  let byMod : Std.HashMap Name (String × Array Name) := cands.foldl (fun m (rel, n, imps) => m.insert n (rel, imps)) {}
  -- modules that (transitively) import a root, plus the roots
  let mut affected : Std.HashSet Name := Std.HashSet.ofArray roots
  let mut changed := true
  while changed do
    changed := false
    for (_, n, imps) in cands do
      if !affected.contains n && imps.any affected.contains then
        affected := affected.insert n
        changed := true
  -- topological order among the affected, ties by path
  let mut remaining := cands.filter fun (_, n, _) => affected.contains n
  let mut done : Std.HashSet Name := {}
  let mut order := #[]
  while !remaining.isEmpty do
    let ready := remaining.filter fun (_, _, imps) => imps.all fun i => !affected.contains i || done.contains i
    if ready.isEmpty then break
    for (rel, n, _) in ready do
      order := order.push rel
      done := done.insert n
    remaining := remaining.filter fun (_, n, _) => !done.contains n
  return order

-- --- the run -----------------------------------------------------------------

def stepBefore : M Unit := do
  let (ok, out) ← fullBuild "before"
  unless ok do stop ("the unchanged tree does not build:\n" ++ (tail out 3000))
  let (findings, summary) ← typeLint "before"
  (← read).lintBeforeFindings.set findings
  modifyState fun s => { s with lintBefore := summary }

def importModulesFor (root : System.FilePath) (files : Array String) : IO Environment := do
  let mut mods : Array Name := #[`ArmadaLean]
  for rel in files do
    for m in ← fileImports (root / rel) do
      unless mods.contains m do mods := mods.push m
  unsafe importTarget root mods

def stepDiscover (env : Environment) : M Unit := do
  let e ← read
  let names := e.args.names
  let resolved := resolveAll env (names.map String.toName)
  let mut founds : Array Found := #[]
  for i in [0:names.size] do
    let cands := resolved[i]!
    unless cands.size == 1 do
      stop s!"discovery: {names[i]!} does not resolve to exactly one ArmadaLean constant: {cands}"
    let n := cands[0]!
    let coreCtx : Core.Context := { fileName := "<discovery>", fileMap := default }
    let found ← match ← (EIO.toIO' ((describe env e.root n).toIO coreCtx { env })) with
      | .ok (f, _, _) => pure f
      | .error err => stop s!"discovery: {err}"
    if found.file.startsWith "ArmadaLean/Spec/" then stop s!"{n} is declared under ArmadaLean/Spec/; refused"
    let short := (n.toString.splitOn ".").getLast!
    let g ← git #["grep", "-n", s!"Spec\\.{short}\\b", "--", "ArmadaLean/Spec"]
    if g.exitCode == 0 && !g.stdout.trimAscii.isEmpty then
      stop s!"{n}: an approved statement names Spec.{short}; refused:\n{g.stdout}"
    founds := founds.push found
  -- conversion, per file
  let files := founds.foldl (fun acc f => if acc.contains f.file then acc else acc.push f.file) #[]
  let mut preds : Array Pred := #[]
  let mut reports : Array PredReport := #[]
  for rel in files do
    let text ← IO.FS.readFile (e.root / rel)
    let fm := FileMap.ofString text
    let inFile := founds.filter (·.file == rel)
    let mut edits : Array (Edit × Found × Nat × Nat) := #[]
    for f in inFile do
      if f.alreadyConverted then
        stop s!"{f.name} is already a converted structure with `.iff`; nothing to do"
      match conversionEdit f text with
      | .ok (ed, nameOff, holdsOff) => edits := edits.push (ed, f, nameOff, holdsOff)
      | .error msg => stop msg
    let newText := applyEdits text (edits.map (·.1))
    checkForbidden text newText rel
    writeFile rel newText
    -- offsets in the new text: shift by the edits that sit before
    for (ed, f, nameOff, holdsOff) in edits do
      let delta := edits.foldl (fun d (o, _, _, _) =>
        if o.stop ≤ ed.start && o != ed then d + o.replacement.utf8ByteSize - (o.stop - o.start) else d) 0
      let base := ed.start + delta
      let explicit := f.binders.filter (·.explicit) |>.toList.flatMap (·.names.toList)
      let pred : Pred :=
        { fullName := f.name.toString, declId := f.declId, file := rel,
          uri := Lsp.uriOf e.root rel, declIdOffset := base + nameOff, holdsOffset := base + holdsOff,
          bodyHead := f.bodyHead, bodyIsStructure := f.bodyIsStructure }
      preds := preds.push pred
      let rep : PredReport :=
        { name := f.name.toString, path := rel, line := (fm.toPosition ⟨f.defStart⟩).line,
          alreadyConverted := false, iff := " ".intercalate (f.declId :: explicit) ++ " ↔ …" }
      reports := reports.push rep
  modifyState fun s => { s with preds, predReports := reports }

def stepFiles (env : Environment) : M Unit := do
  let e ← read
  let s ← e.state.get
  let c ← Lsp.start e.root (e.logDir / "lsp.log")
  let mut i := s.nextIndex
  let files := s.files
  let result ← tryCatch (do
    let mut i := i
    while i < files.size do
      let rel := files[i]!
      log s!"[file] {rel} ({i + 1}/{files.size})"
      let changed ← repairFile c env rel
      if changed && rel.startsWith "ArmadaLean" then
        let m := moduleName rel
        let p ← runCmd #["lake", "build", m.toString] s!"build-{m}.log"
        if p.exitCode != 0 then
          stop s!"lake build {m} failed after the repairs:\n{(tail (p.stdout ++ p.stderr) 3000)}"
        let ilean := e.root / ".lake" / "build" / "lib" / "lean" / ((rel.dropEnd 5).copy ++ ".ilean")
        c.ileanChanged ilean
      i := i + 1
      modifyState fun st => { st with nextIndex := i }
      saveState
    pure (Except.ok ()))
    (fun err => pure (Except.error err))
  i := i
  c.stop
  match result with
  | .ok () => pure ()
  | .error err => throw err

-- --- the alias mode -------------------------------------------------------------

/-- One declaration of the alias work list and its result. -/
structure AliasUnit where
  decl : Name
  file : String
  line : Nat
  findings : Array Alias.Finding
  /-- The accepted form: the proof form and the call-site form. -/
  form : Option String := none
  files : Array String := #[]
  /-- Each tried form and the first error that it gave. -/
  attempts : Array (String × String) := #[]
  deriving Inhabited

def AliasUnit.short (u : AliasUnit) : String := (u.decl.toString.splitOn ".").getLast!

def aliasResults (units : Array AliasUnit) : Json :=
  Json.arr <| units.flatMap fun u => u.findings.map fun f =>
    Json.mkObj [("declaration", toJson f.declaration), ("binder", toJson f.binder), ("rhs", toJson f.rhs),
      ("at", toJson f.at_), ("fixed", toJson u.form.isSome), ("form", toJson u.form),
      ("reason", toJson (if u.form.isSome then "" else (u.attempts.back?.map (·.2)).getD "not tried")),
      ("attempts", Json.arr (u.attempts.map fun (f, m) => Json.mkObj [("form", toJson f), ("error", toJson m)])),
      ("files_changed", toJson u.files)]

/-- Build every module among `files[0:upto]` whose text on disk is not the
    text of its last build. -/
def buildUpTo (files : Array String) (upto : Nat) (disk built : Std.HashMap String String) :
    M (Std.HashMap String String) := do
  let mut built := built
  for k in [0:upto] do
    let rel := files[k]!
    unless rel.startsWith "ArmadaLean" do continue
    let t := disk.getD rel ""
    if built.get? rel != some t then
      let m := moduleName rel
      let p ← runCmd #["lake", "build", m.toString] s!"build-{m}.log"
      if p.exitCode != 0 then stop s!"lake build {m} failed:\n{(tail (p.stdout ++ p.stderr) 3000)}"
      built := built.insert rel t
  return built

/-- The alias mode (`--alias`), one declaration at a time, the last
    declaration of the last file first (a caller before its callee: the
    caller's arguments are then the right-hand side, not its own variable).
    For each declaration: an in-process elaboration of its file and of every
    file that names it, on their current texts (`Alias.declEdits`,
    `Alias.callSites`); then each form in turn, checked through the Lean
    REPL (`ReplCheck`): the new declaration under a fresh name in the
    environment before it, then each changed command that names it. The
    first form without an error is written to the files; with none, the
    files keep their texts. At the end, one `lake build` of the changed
    modules. -/
def stepAlias : M Unit := do
  let e ← read
  let some wl := e.args.alias | stop "--alias: no work list"
  let some replPath := e.args.repl | stop "--alias needs --repl PATH (the Lean REPL)"
  let findings ← match Json.parse (← IO.FS.readFile wl) >>= fun j => do (← j.getArr?).mapM Alias.Finding.ofJson with
    | .ok fs => pure fs
    | .error err => stop s!"the work list is not valid: {err}"
  let mut units : Array AliasUnit := #[]
  for f in findings do
    match units.findIdx? (·.decl.toString == f.declaration) with
    | some i => units := units.modify i fun u => { u with findings := u.findings.push f }
    | none =>
      let line := ((f.at_.splitOn ":")[1]?.bind String.toNat?).getD 0
      units := units.push { decl := f.declaration.toName, file := f.file, line, findings := #[f] }
  -- the files: each declaration's file and every file that names it, in import order
  let cands ← candidates e.root
  let mut mentioned : Std.HashSet String := {}
  for u in units do
    mentioned := mentioned.insert u.file
    let g ← git #["grep", "-lw", u.short, "--", "ArmadaLean.lean", "ArmadaLean", "docs/counterexamples"]
    for l in g.stdout.splitOn "\n" do
      if l ≠ "" then mentioned := mentioned.insert l
  let files := (dependents cands (units.map fun u => moduleName u.file)).filter mentioned.contains
  let fileIdx (rel : String) : Nat := (files.idxOf? rel).getD files.size
  let order := (Array.range units.size).qsort fun a b =>
    let (ua, ub) := (units[a]!, units[b]!)
    fileIdx ua.file > fileIdx ub.file || (ua.file == ub.file && ua.line > ub.line)
  log s!"[alias] {units.size} declarations, {files.size} files"
  let home := (← IO.getEnv "HOME").getD ""
  let sp ← targetSearchPath e.root
  initSearchPath (← findSysroot s!"{home}/.elan/bin/lean") sp
  let mut disk : Std.HashMap String String := {}
  for rel in files do disk := disk.insert rel (← IO.FS.readFile (e.root / rel))
  let c ← Repl.start replPath sp (e.logDir / "repl.log")
  let secs (t0 : Nat) : IO Float := do return (Float.ofNat ((← IO.monoMsNow) - t0)) / 1000.0
  let result ← tryCatch (do
    let mut units := units
    let mut disk := disk
    let mut built := disk
    let mut sessions : Std.HashMap String ReplCheck.Session := {}
    let mut changedFiles : Array String := #[]
    -- the number of accepted declarations when each declaration was tried
    let mut accepts := 0
    let mut triedAt : Std.HashMap Nat Nat := {}
    -- a second pass retries each declaration that failed on a form: the
    -- declarations accepted after it can change its callers and callees
    for (ui, k) in (order ++ order).zipIdx do
      let u := units[ui]!
      if k ≥ order.size && (u.form.isSome || u.attempts.any (·.1 == "analysis")) then continue
      -- no declaration accepted since its first try: the same texts, the same result
      if k ≥ order.size && triedAt[ui]? == some accepts then continue
      triedAt := triedAt.insert ui accepts
      log s!"[alias] {u.decl}{if k ≥ order.size then " (second pass)" else ""}"
      let uFiles := files.filter fun rel => rel == u.file || ((disk.getD rel "").splitOn u.short).length > 1
      -- analysis on the current texts
      built ← buildUpTo files (fileIdx u.file) disk built
      let elabFile (rel : String) : M Alias.FileElab := do
        let t0 ← IO.monoMsNow
        let fe ← Alias.elabText (e.root / rel).toString (moduleName rel) (disk.getD rel "")
        log s!"[alias]   elaborated {rel} in {← secs t0}s"
        unless fe.errors.isEmpty do stop s!"{rel} has errors before the edit: {fe.errors[0]!}"
        return fe
      let fe ← elabFile u.file
      let de ← match Alias.declEdits fe u.decl u.findings with
        | .ok de => pure de
        | .error msg =>
          units := units.set! ui { u with attempts := #[("analysis", msg)] }
          e.aliasReport.set (aliasResults units)
          continue
      let skip := ((Alias.declCommand? fe u.decl).bind Alias.rng?).getD (0, 0)
      let pairs := de.pairs.map (·.site)
      -- each file's call sites: the edits for the disk and the edits for the check
      let mut sites : Array (String × Alias.Sites × Alias.Sites) := #[]
      let mut elabs : Array (String × Alias.FileElab) := #[(u.file, fe)]
      let mut problem : Option String := none
      for rel in uFiles do
        let fe' ← if rel == u.file then pure fe else do
          built ← buildUpTo files (fileIdx rel) disk built
          elabFile rel
        unless fe'.env.contains u.decl do continue
        let sk := if rel == u.file then skip else (0, 0)
        let s ← Alias.callSites fe' u.decl pairs sk "" de.moved
        let sc ← Alias.callSites fe' u.decl pairs sk ReplCheck.suffix de.moved
        if let some pr := s.problem then problem := some s!"{rel}:{pr}"
        if !s.argCasts.isEmpty && (rel.startsWith "ArmadaLean/Spec/" || rel.startsWith "ArmadaLean/Lint/") then
          problem := some s!"{rel}: a call site is under ArmadaLean/Spec/ or ArmadaLean/Lint/"
        sites := sites.push (rel, s, sc)
        if rel != u.file then elabs := elabs.push (rel, fe')
      if let some pr := problem then
        units := units.set! ui { u with attempts := #[("analysis", pr)] }
        e.aliasReport.set (aliasResults units)
        continue
      -- the REPL sessions of the declaration's file and of the files with a changed command
      for (rel, fe') in elabs do
        unless rel == u.file || sites.any (fun (r, _, sc) => r == rel && !sc.argCasts.isEmpty) do continue
        let t0 ← IO.monoMsNow
        let (sess, errs) ← ReplCheck.sync c rel fe' sessions[rel]?
        log s!"[alias]   REPL session {rel} ({sess.ranges.size} chunks) in {← secs t0}s"
        unless errs.isEmpty do stop s!"{rel} has errors in the REPL before the edit: {errs[0]!}"
        sessions := sessions.insert rel sess
      let some dSess := sessions[u.file]? | stop s!"{u.file}: no REPL session"
      let some dIdx := dSess.chunkAt skip.1 | stop s!"{u.decl}: no REPL chunk"
      -- the proof forms, in order
      let mut attempts : Array (String × String) := u.attempts
      let mut proofForms : Array (String × Array Edit) := #[]
      if !de.proofNames then proofForms := proofForms.push ("proof unchanged", #[])
      else match de.proof with
        | .ok eds => proofForms := proofForms.push ("proof substituted", eds)
        | .error msg => attempts := attempts.push ("proof substituted", msg)
      if let some r := de.restated then proofForms := proofForms.push ("proof behind suffices", #[r])
      if let some p := de.preamble then proofForms := proofForms.push ("proof behind generalize", #[p])
      let castsDiffer := sites.any fun (_, s, _) => s.argCasts != s.callCast
      let mut callForms : Array String := if castsDiffer then #["argument casts", "call cast"] else #["plain calls"]
      match sites.findSome? fun (rel, s, _) => match s.rewriteCasts with | .error m => some s!"{rel}:{m}" | .ok _ => none with
      | some m => attempts := attempts.push ("rewrite casts", m)
      | none =>
        if sites.any fun (_, s, _) => s.rewriteCasts.toOption != some s.argCasts then
          callForms := callForms.push "rewrite casts"
      let rename : Edit := { start := de.declIdEnd, stop := de.declIdEnd, replacement := ReplCheck.suffix }
      let stubValue : Edit := { start := de.valueRange.1, stop := de.valueRange.2, replacement := ":= sorry" }
      let mut accepted : Option String := none
      -- an error in the declaration moves to the next proof form; an error
      -- in a caller moves to the next call-site form
      let mut pi := 0
      let mut ci := 0
      while accepted.isNone && pi < proofForms.size && ci < callForms.size do
        let (pf, peds) := proofForms[pi]!
        let cf := callForms[ci]!
        let form := s!"{pf}, {cf}"
        let pick (s : Alias.Sites) : Array Edit :=
          if cf == "call cast" then s.callCast
          else if cf == "rewrite casts" then s.rewriteCasts.toOption.getD #[]
          else s.argCasts
        -- the texts of this form, and the commands of its check
        let mut texts : Array (String × String) := #[]
        let mut bad : Option String := none
        for rel in uFiles do
          let call := match sites.find? (·.1 == rel) with
            | some (_, s, _) => pick s
            | none => #[]
          let own := if rel == u.file then de.sig ++ peds else #[]
          match Alias.nest (call ++ own) with
          | .ok eds => texts := texts.push (rel, applyEdits (disk.getD rel "") eds)
          | .error msg => bad := some s!"{rel}: {msg}"
        let dEdits := Alias.nest (de.sig ++ peds ++ #[rename])
        let dStubEdits := Alias.nest (de.sig ++ #[rename, stubValue])
        let (dEdits, dStubEdits) ← match dEdits, dStubEdits with
          | .ok a, .ok b => pure (a, b)
          | .error msg, _ | _, .error msg => bad := some s!"{u.file}: {msg}"; pure (#[], #[])
        if let some msg := bad then
          attempts := attempts.push (form, msg)
          pi := pi + 1
          continue
        let dText := dSess.editedChunk dIdx dEdits
        let dStub := if de.isTheorem then dSess.editedChunk dIdx dStubEdits else dText
        let mut callers : Array (ReplCheck.Session × Nat × String) := #[]
        for (rel, _, sc) in sites do
          let some sess := sessions[rel]? | continue
          let ceds := pick sc
          for i in sess.touched ceds do
            unless rel == u.file && i == dIdx do callers := callers.push (sess, i, sess.editedChunk i ceds)
        let t0 ← IO.monoMsNow
        let (declErrs, callErrs) ← ReplCheck.check c dSess dIdx dText dStub callers
        log s!"[alias]   checked {form}: the declaration and {callers.size} commands in {← secs t0}s"
        if declErrs.isEmpty && callErrs.isEmpty then
          let changed := (texts.filter fun (rel, t) => t != disk.getD rel "").map (·.1)
          for (rel, t) in texts do
            if t != disk.getD rel "" then
              checkForbidden (disk.getD rel "") t rel
              writeFile rel t
              disk := disk.insert rel t
          accepted := some form
          accepts := accepts + 1
          units := units.set! ui { u with form := some form, files := changed, attempts }
          for rel in changed do
            unless changedFiles.contains rel do changedFiles := changedFiles.push rel
          -- a session after the first changed file imports a changed module: it starts again
          let m := changed.foldl (fun acc rel => min acc (fileIdx rel)) files.size
          sessions := sessions.filter fun rel _ => fileIdx rel ≤ m
        else
          log s!"[alias]   {form}: {(declErrs ++ callErrs)[0]!.take 300}"
          -- the checked texts, for the reader of the report
          let file := e.logDir / s!"alias-check-{u.short}-{attempts.size}.lean"
          IO.FS.writeFile file ("\n\n".intercalate (dText :: callers.toList.map (·.2.2)))
          match callErrs[0]? with
          | some m => attempts := attempts.push (form, s!"at a call site: {m}")
          | none => attempts := attempts.push (form, declErrs[0]!)
          if !declErrs.isEmpty then pi := pi + 1
          if !callErrs.isEmpty then ci := ci + 1
      match accepted with
      | some form => log s!"[alias]   fixed: {form}"
      | none => units := units.set! ui { u with attempts }
      e.aliasReport.set (aliasResults units)
    -- the real check of the REPL's verdicts: one build of the changed modules
    let mods := changedFiles.filter (·.startsWith "ArmadaLean") |>.map fun rel => (moduleName rel).toString
    unless mods.isEmpty do
      let p ← runCmd (#["lake", "build"] ++ mods) "build-alias-changed.log"
      if p.exitCode != 0 then
        stop s!"lake build of the changed modules failed after the REPL accepted them:\n{(tail (p.stdout ++ p.stderr) 3000)}"
    pure (Except.ok ()))
    (fun err => pure (Except.error err))
  c.stop
  match result with
  | .ok () => pure ()
  | .error err => throw err

def stepAfter : M Unit := do
  let e ← read
  let (ok, out) ← fullBuild "after"
  unless ok do stop ("the repaired tree does not build:\n" ++ (tail out 3000))
  let (findings, summary) ← typeLint "after"
  -- the alias mode changes nothing under `scripts/` outside `scripts/codemod/`
  let hashes ← if e.args.alias.isSome then pure Json.null else
    let pyArgs : IO.Process.SpawnArgs :=
      { cmd := "python3", args := #["scripts/update_gate_baseline.py", "--hashes-only"], cwd := e.root }
    let p ← IO.Process.output pyArgs
    pure (Json.mkObj [("exit", toJson p.exitCode.toNat), ("stderr", toJson (tail p.stderr 1000))])
  let head := (← e.state.get).head
  let base := if e.args.alias.isSome then #["--base", head] else #[]
  let chk ← runCmd (#["bash", "scripts/check.sh", "--json"] ++ base) "check.log"
  let checkJson := match (chk.stdout.trimAscii.copy.splitOn "\n").getLast? >>= fun l => (Json.parse l).toOption with
    | some j => j
    | none => Json.mkObj [("error", toJson ((tail chk.stdout 2000) ++ (tail chk.stderr 2000)))]
  let okFields := match checkJson with
    | .obj kvs => Json.obj (kvs.foldl (init := {}) fun acc k v => if k.endsWith "_ok" then acc.insert k v else acc)
    | j => j
  let before := (← e.lintBeforeFindings.get).map findingKey
  let after := findings.map findingKey
  let bset := Std.HashSet.ofArray before
  let aset := Std.HashSet.ofArray after
  let removed := (before.filter (!aset.contains ·)).qsort (· < ·)
  let added := (after.filter (!bset.contains ·)).qsort (· < ·)
  let s ← e.state.get
  let report := Json.mkObj [
    ("checkout", toJson e.root.toString), ("head", toJson s.head), ("names", toJson s.names),
    ("stopped", Json.null), ("stops", toJson s.stops),
    ("predicates", toJson s.predReports), ("repairs", toJson s.repairs), ("rounds", Json.arr s.rounds),
    ("lint_before", s.lintBefore), ("lint_after", summary),
    ("findings_removed", toJson removed), ("findings_added", toJson added),
    ("gate_baseline_hashes", hashes),
    ("check", okFields), ("check_full", checkJson),
    ("files_changed", toJson ((← git #["status", "--porcelain"]).stdout.splitOn "\n" |>.filter (· ≠ "") |>.map (·.drop 3 |>.copy))),
    ("alias", ← e.aliasReport.get),
    ("timings", toJson s.timings)]
  IO.FS.writeFile e.args.report (report.pretty ++ "\n")

def writeStopReport (msg : String) : M Unit := do
  let e ← read
  let s ← e.state.get
  modifyState fun st => { st with stops := st.stops.push msg }
  saveState
  let report := Json.mkObj [
    ("checkout", toJson e.root.toString), ("head", toJson s.head), ("names", toJson s.names),
    ("stopped", toJson msg), ("stops", toJson s.stops), ("predicates", toJson s.predReports),
    ("repairs", toJson s.repairs), ("rounds", Json.arr s.rounds), ("lint_before", s.lintBefore),
    ("files_changed", toJson ((← git #["status", "--porcelain"]).stdout.splitOn "\n" |>.filter (· ≠ "") |>.map (·.drop 3 |>.copy))),
    ("alias", ← e.aliasReport.get),
    ("timings", toJson s.timings)]
  IO.FS.writeFile e.args.report (report.pretty ++ "\n")

def run : M Unit := do
  let e ← read
  if e.args.alias.isSome then
    stepBefore
    stepAlias
    stepAfter
    return
  if !e.args.resume then
    stepBefore
  let cands ← candidates e.root
  if !e.args.resume then
    let env ← importModulesFor e.root (cands.map (·.1))
    stepDiscover env
    let roots := (← e.state.get).preds.map fun p => moduleName p.file
    let files := dependents cands roots
    modifyState fun s => { s with files, nextIndex := 0 }
    saveState
    stepFiles env
  else
    let env ← importModulesFor e.root (cands.map (·.1))
    stepFiles env
  stepAfter

end DefToStructure

open DefToStructure in
unsafe def main (argv : List String) : IO UInt32 := do
  let args ← match parseArgs argv with
    | .ok a => pure a
    | .error msg => IO.eprintln msg; return 2
  let root := (← IO.FS.realPath args.checkout)
  let logDir := root / ".scratch" / "codemod"
  IO.FS.createDirAll logDir
  let gitArgs : IO.Process.SpawnArgs := { cmd := "git", args := #["rev-parse", "HEAD"], cwd := root }
  let head := (← IO.Process.output gitArgs).stdout.trimAscii.copy
  let initial : State :=
    { head, names := args.names, preds := #[], predReports := #[], files := #[], nextIndex := 0,
      repairs := #[], rounds := #[], stops := #[], lintBefore := Json.null, timings := #[] }
  let state ← if args.resume then
      match Json.parse (← IO.FS.readFile (logDir / "state.json")) >>= fromJson? (α := State) with
      | .ok s => pure s
      | .error err => IO.eprintln s!"--resume: cannot read state.json: {err}"; return 2
    else pure initial
  let lintBefore ← if args.resume then
      let text ← IO.FS.readFile (logDir / "lint-before.jsonl")
      pure ((text.splitOn "\n").filter (·.startsWith "{")).toArray
    else pure #[]
  let stateRef ← IO.mkRef state
  let lintRef ← IO.mkRef lintBefore
  let seenRef ← IO.mkRef ({} : Std.HashSet String)
  let aliasRef ← IO.mkRef Json.null
  let env : Env := { args, root, logDir, state := stateRef, lintBeforeFindings := lintRef, seen := seenRef,
                     aliasReport := aliasRef }
  match ← (run.run env).run with
  | .ok () => return 0
  | .error ⟨msg⟩ =>
    IO.eprintln s!"STOPPED: {msg}"
    match ← ((writeStopReport msg).run env).run with
    | .ok () => pure ()
    | .error ⟨m2⟩ => IO.eprintln s!"report failed: {m2}"
    return 2
