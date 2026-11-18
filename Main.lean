/-
  `lean-temper`: the driver (see README.md).

    lean-temper --checkout <target worktree> --slot <1-4> --config CONFIG.json \
      --alias WORKLIST.json --repl REPL --report report.json

  Steps:
  1. `lake build`, then the lint command (`Config.lintCommand`), the "before" list.
  2. The alias pass (`stepAlias`, `LeanTemper.Alias`): each declaration of the
     work list, the last declaration of the last file first, through the
     Lean REPL (`LeanTemper.ReplCheck`).
  3. One full check: `lake build`, the lint command (the "after" list), and
     the check command (`Config.checkCommand`), and the JSON report.
-/
import Lean
import LeanTemper.Target
import LeanTemper.Alias
import LeanTemper.ReplCheck

open Lean LeanTemper

namespace LeanTemper

structure Args where
  checkout : System.FilePath
  slot : Nat
  config : System.FilePath
  /-- `--alias WORKLIST.json`: the declarations the alias pass (`LeanTemper.Alias`) treats. -/
  alias : System.FilePath
  /-- `--repl PATH`: the Lean REPL binary the pass checks a candidate edit through. -/
  repl : System.FilePath
  report : System.FilePath

def parseArgs (args : List String) : Except String Args := do
  let mut checkout := ""
  let mut slot := 0
  let mut config := ""
  let mut alias := ""
  let mut repl := ""
  let mut report := ""
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--checkout" :: v :: r => checkout := v; rest := r
    | "--slot" :: v :: r => slot := v.toNat!; rest := r
    | "--config" :: v :: r => config := v; rest := r
    | "--alias" :: v :: r => alias := v; rest := r
    | "--repl" :: v :: r => repl := v; rest := r
    | "--report" :: v :: r => report := v; rest := r
    | a :: _ => throw s!"unknown argument {a}"
    | [] => pure ()
  if checkout.isEmpty || slot == 0 || config.isEmpty || alias.isEmpty || repl.isEmpty || report.isEmpty then
    throw "usage: lean-temper --checkout DIR --slot N --config CONFIG.json --alias WORKLIST.json --repl REPL --report FILE"
  return { checkout, slot, config, alias, repl, report }

/-- Project-specific rules (`--config PATH`, see README.md, "Configuration").
    Every field is required; a missing file or a missing key stops the run. -/
structure Config where
  /-- Paths (a directory prefix ending `/`) the tool never writes. -/
  protectedPaths : Array String
  /-- The prefix of the target's own source tree (`ArmadaLean`): the file
      `<prefix>.lean`, the directory `<prefix>/`. -/
  sourcePrefix : String
  /-- The commands that run the target's lint, in order; the last command's
      standard output is the lint's JSON-lines findings and summary. -/
  lintCommand : Array (Array String)
  /-- The target's final check command; the tool appends `--base <head>`. -/
  checkCommand : Array String
  deriving FromJson

def loadConfig (path : System.FilePath) : IO (Except String Config) := do
  let text ← try pure (some (← IO.FS.readFile path)) catch e => do IO.eprintln s!"--config: {e}"; pure none
  let some text := text | return .error s!"--config: cannot read {path}"
  match Json.parse text with
  | .error err => return .error s!"--config: {path} is not valid JSON: {err}"
  | .ok j => match fromJson? (α := Config) j with
    | .ok c => return .ok c
    | .error err => return .error s!"--config: {path}: {err}"

/-- A stop: the tool changes nothing more and reports `msg`. -/
structure StopError where
  msg : String

structure Timing where
  command : String
  seconds : Float
  exit : Nat
  deriving ToJson, FromJson

/-- The last `n` bytes of `s` (whole characters). -/
def tail (s : String) (n : Nat) : String :=
  if s.length ≤ n then s else (s.toSubstring.drop (s.length - n)).toString

/-- The persisted state of a run. -/
structure State where
  head : String
  stops : Array String
  lintBefore : Json
  timings : Array Timing
  deriving ToJson, FromJson

structure Env where
  args : Args
  config : Config
  root : System.FilePath
  logDir : System.FilePath
  state : IO.Ref State
  lintBeforeFindings : IO.Ref (Array String)
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

/-- `lake build` of the default target. -/
def fullBuild (tag : String) : M (Bool × String) := do
  let p ← runCmd #["lake", "build"] s!"build-{tag}.log"
  return (p.exitCode == 0, p.stdout ++ p.stderr)

/-- `Config.lintCommand`, in order: the finding lines and the summary of the
    last command's standard output. -/
def typeLint (tag : String) : M (Array String × Json) := do
  let e ← read
  let cmds := e.config.lintCommand
  if cmds.isEmpty then stop "the config's lintCommand is empty"
  let mut out := ""
  for (args, i) in cmds.zipIdx do
    let p ← runCmd args s!"lint-{tag}-{i}.log"
    if p.exitCode != 0 then
      stop s!"the lint command {" ".intercalate args.toList} failed (exit {p.exitCode}):\n{(tail p.stdout 2000)}\n{(tail p.stderr 2000)}"
    out := p.stdout
  let lines := out.splitOn "\n"
  let findings := lines.filter (fun l => l.startsWith "{" && !l.startsWith "{\"summary\"") |>.toArray
  let summaries := lines.filter (·.startsWith "{\"summary\"")
  if summaries.isEmpty then stop s!"the lint command printed no summary line:\n{(tail out 2000)}"
  IO.FS.writeFile ((← read).logDir / s!"lint-{tag}.jsonl") ("\n".intercalate findings.toList ++ "\n")
  match Json.parse summaries.getLast! with
  | .ok j => return (findings, j)
  | .error err => stop s!"the lint summary is not JSON: {err}"

/-- A finding line without its `example` field: `repeatedPremise` picks the
    example from the group's uses, and that pick differs between runs. -/
def findingKey (line : String) : String :=
  match Json.parse line with
  | .ok (.obj kvs) => (Json.obj (kvs.erase "example")).compress
  | _ => line

-- --- edits -------------------------------------------------------------------

def forbidden : List String := ["sorry", "admit", "axiom", "native_decide"]

def countOcc (hay needle : String) : Nat := (hay.splitOn needle).length - 1

def checkForbidden (before after : String) (where_ : String) : M Unit := do
  for w in forbidden do
    if countOcc after w > countOcc before w then
      stop s!"{where_}: the edit would insert `{w}`"

def writeFile (rel : String) (text : String) : M Unit := do
  let e ← read
  if e.config.protectedPaths.any (fun p => rel.startsWith p) then
    stop s!"{rel}: the config protects this path; the tool never edits it"
  IO.FS.writeFile (e.root / rel) text

-- --- files and dependency order ---------------------------------------------

partial def leanFilesUnder (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for entry in ← dir.readDir do
    if ← entry.path.isDir then out := out ++ (← leanFilesUnder entry.path)
    else if entry.path.extension == some "lean" then out := out.push entry.path
  return out

/-- Every candidate file under `Config.sourcePrefix`, with its module name
    and its imports. -/
def candidates (root : System.FilePath) (sourcePrefix : String) : IO (Array (String × Name × Array Name)) := do
  let mut files : Array System.FilePath := #[root / (sourcePrefix ++ ".lean")]
  files := files ++ (← leanFilesUnder (root / sourcePrefix))
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

/-- One work-list entry and its result. -/
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
def buildUpTo (files : Array String) (upto : Nat) (sourcePrefix : String) (disk built : Std.HashMap String String) :
    M (Std.HashMap String String) := do
  let mut built := built
  for k in [0:upto] do
    let rel := files[k]!
    unless rel.startsWith sourcePrefix do continue
    let t := disk.getD rel ""
    if built.get? rel != some t then
      let m := moduleName rel
      let p ← runCmd #["lake", "build", m.toString] s!"build-{m}.log"
      if p.exitCode != 0 then stop s!"lake build {m} failed:\n{(tail (p.stdout ++ p.stderr) 3000)}"
      built := built.insert rel t
  return built

/-- The alias pass (`--alias`), one declaration at a time, the last
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
  let sourcePrefix := e.config.sourcePrefix
  let findings ← match Json.parse (← IO.FS.readFile e.args.alias) >>= fun j => do (← j.getArr?).mapM Alias.Finding.ofJson with
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
  let cands ← candidates e.root sourcePrefix
  let mut mentioned : Std.HashSet String := {}
  for u in units do
    mentioned := mentioned.insert u.file
    let g ← git #["grep", "-lw", u.short, "--", sourcePrefix ++ ".lean", sourcePrefix]
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
  let c ← Repl.start e.args.repl sp (e.logDir / "repl.log")
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
      built ← buildUpTo files (fileIdx u.file) sourcePrefix disk built
      let elabFile (rel : String) : M Alias.FileElab := do
        let t0 ← IO.monoMsNow
        let fe ← Alias.elabText (e.root / rel).toString (moduleName rel) (disk.getD rel "")
        log s!"[alias]   elaborated {rel} in {← secs t0}s"
        unless fe.errors.isEmpty do stop s!"{rel} has errors before the edit: {fe.errors[0]!}"
        return fe
      let fe0 ← elabFile u.file
      -- `fe` is the hoisted text when `rhs` names a variable of the statement's `∀`
      let (fe, deE) ← Alias.declEditsHoisting fe0 u.decl u.findings (e.root / u.file).toString (moduleName u.file)
      let de ← match deE with
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
          built ← buildUpTo files (fileIdx rel) sourcePrefix disk built
          elabFile rel
        unless fe'.env.contains u.decl do continue
        let sk := if rel == u.file then skip else (0, 0)
        let s ← Alias.callSites fe' u.decl pairs sk "" de.moved
        let sc ← Alias.callSites fe' u.decl pairs sk ReplCheck.suffix de.moved
        if let some pr := s.problem then problem := some s!"{rel}:{pr}"
        if !s.argCasts.isEmpty && e.config.protectedPaths.any (fun p => rel.startsWith p) then
          problem := some s!"{rel}: a call site is under a protected path"
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
          | .ok eds =>
            let base := if rel == u.file then fe.text else disk.getD rel ""
            texts := texts.push (rel, applyEdits base eds)
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
    let mods := changedFiles.filter (·.startsWith sourcePrefix) |>.map fun rel => (moduleName rel).toString
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
  let head := (← e.state.get).head
  let chk ← runCmd (e.config.checkCommand ++ #["--base", head]) "check.log"
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
    ("checkout", toJson e.root.toString), ("head", toJson s.head),
    ("stopped", Json.null), ("stops", toJson s.stops),
    ("lint_before", s.lintBefore), ("lint_after", summary),
    ("findings_removed", toJson removed), ("findings_added", toJson added),
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
    ("checkout", toJson e.root.toString), ("head", toJson s.head),
    ("stopped", toJson msg), ("stops", toJson s.stops), ("lint_before", s.lintBefore),
    ("files_changed", toJson ((← git #["status", "--porcelain"]).stdout.splitOn "\n" |>.filter (· ≠ "") |>.map (·.drop 3 |>.copy))),
    ("alias", ← e.aliasReport.get),
    ("timings", toJson s.timings)]
  IO.FS.writeFile e.args.report (report.pretty ++ "\n")

def run : M Unit := do
  stepBefore
  stepAlias
  stepAfter

end LeanTemper

open LeanTemper in
unsafe def main (argv : List String) : IO UInt32 := do
  let args ← match parseArgs argv with
    | .ok a => pure a
    | .error msg => IO.eprintln msg; return 2
  let config ← match ← loadConfig args.config with
    | .ok c => pure c
    | .error msg => IO.eprintln msg; return 2
  let root := (← IO.FS.realPath args.checkout)
  let logDir := root / ".scratch" / "codemod"
  IO.FS.createDirAll logDir
  let gitArgs : IO.Process.SpawnArgs := { cmd := "git", args := #["rev-parse", "HEAD"], cwd := root }
  let head := (← IO.Process.output gitArgs).stdout.trimAscii.copy
  let state : State := { head, stops := #[], lintBefore := Json.null, timings := #[] }
  let stateRef ← IO.mkRef state
  let lintRef ← IO.mkRef (#[] : Array String)
  let aliasRef ← IO.mkRef Json.null
  let env : Env := { args, config, root, logDir, state := stateRef, lintBeforeFindings := lintRef, aliasReport := aliasRef }
  match ← (run.run env).run with
  | .ok () => return 0
  | .error ⟨msg⟩ =>
    IO.eprintln s!"STOPPED: {msg}"
    match ← ((writeStopReport msg).run env).run with
    | .ok () => pure ()
    | .error ⟨m2⟩ => IO.eprintln s!"report failed: {m2}"
    return 2
