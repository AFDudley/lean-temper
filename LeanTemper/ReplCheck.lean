/-
  The check of an alias candidate through the Lean REPL (see ../README.md,
  "Alias mode", and `LeanTemper.Repl`).

  A file runs once in the REPL, one command per request, so that the
  environment after each command stays available (`Session`). An
  environment cannot lose a constant, so a candidate is checked under a
  fresh name: the new declaration `D_aliasCheck` in the environment before
  `D`, and each changed command that names `D` (now `D_aliasCheck`) in the
  environment before that command, after `D_aliasCheck` is added there
  (`bridge`). The command boundaries and the scope commands come from the
  in-process elaboration of the same text (`Alias.FileElab`).
-/
import Lean
import LeanTemper.Alias
import LeanTemper.Repl

open Lean

namespace LeanTemper.ReplCheck

open LeanTemper.Alias

/-- The suffix of the fresh name of a candidate. -/
def suffix : String := "_aliasCheck"

/-- A scope of the file at a command: its opening command, its closing
    command, and the scope commands (`open`, `variable`, …) in it. The
    first frame is the file's top level (no opener, no closer). -/
structure Frame where
  opener : String
  closer : String
  items : Array String := #[]
  deriving Inhabited, BEq

def scopeItemKinds : List Name :=
  [``Parser.Command.open, ``Parser.Command.variable, ``Parser.Command.universe, ``Parser.Command.set_option,
   ``Parser.Command.omit, ``Parser.Command.include]

/-- The byte ranges of the chunks of a file: chunk 0 is the header (and the
    text before the first command), chunk `i + 1` is command `i` with the
    text up to the next command. Also the commands, in order. -/
def chunkRanges (fe : FileElab) : Array (Nat × Nat) × Array Syntax := Id.run do
  let size := fe.text.utf8ByteSize
  let mut cmds : Array (Nat × Syntax) := #[]
  for c in fe.commands do
    if let some (s, _) := rng? c then
      if s < size && !cmds.any (·.1 == s) then cmds := cmds.push (s, c)
  let sorted := cmds.qsort (·.1 < ·.1)
  let starts := #[0] ++ sorted.map (·.1)
  let ranges := starts.zipIdx.map fun (s, i) => (s, (starts[i + 1]?).getD size)
  return (ranges, sorted.map (·.2))

/-- The frames before each command (index = chunk index; chunk 0 has the top level only). -/
def framesOf (text : String) (cmds : Array Syntax) : Array (Array Frame) := Id.run do
  let mut st : Array Frame := #[{ opener := "", closer := "" }]
  let mut out : Array (Array Frame) := #[st]
  for c in cmds do
    out := out.push st
    let some (s, e) := rng? c | continue
    let t := (slice text s e).trimAscii.copy
    let nameOf : Option Name := (descendants c).findSome? fun d => if d.isIdent then some d.getId else none
    if c.isOfKind ``Parser.Command.namespace then
      st := st.push { opener := t, closer := s!"end {(nameOf.getD .anonymous)}" }
    else if c.isOfKind ``Parser.Command.section then
      st := st.push { opener := t, closer := match nameOf with | some n => s!"end {n}" | none => "end" }
    else if c.isOfKind ``Parser.Command.end then
      if st.size > 1 then st := st.pop
    else if scopeItemKinds.any c.isOfKind then
      st := st.modify (st.size - 1) fun f => { f with items := f.items.push t }
  return out

/-- A file as it ran in the REPL. -/
structure Session where
  rel : String
  text : String
  ranges : Array (Nat × Nat)
  /-- `envs[i]`: the environment after chunk `i`. -/
  envs : Array Nat
  frames : Array (Array Frame)
  deriving Inhabited

def Session.chunk (s : Session) (i : Nat) : String := slice s.text s.ranges[i]!.1 s.ranges[i]!.2

/-- The chunk that holds byte `o`. -/
def Session.chunkAt (s : Session) (o : Nat) : Option Nat :=
  s.ranges.findIdx? fun (a, b) => a ≤ o && o < b

/-- The line (1-based) of byte `o` in the session's text. -/
def Session.lineOf (s : Session) (o : Nat) : Nat := (FileMap.ofString s.text |>.toPosition ⟨o⟩).line

/-- Run `fe`'s text in the REPL, chunk by chunk. The chunks equal to those
    of `old` (from the first one on) keep their environments. Returns the
    session and the errors of the chunks that ran. -/
def sync (c : Repl.Client) (rel : String) (fe : FileElab) (old? : Option Session) : IO (Session × Array String) := do
  let (ranges, cmds) := chunkRanges fe
  let chunk (i : Nat) := slice fe.text ranges[i]!.1 ranges[i]!.2
  let mut keep := 0
  if let some old := old? then
    while keep < ranges.size && keep < old.ranges.size && chunk keep == old.chunk keep do keep := keep + 1
  let mut envs : Array Nat := (old?.map (·.envs.extract 0 keep)).getD #[]
  let mut errs : Array String := #[]
  let fm := FileMap.ofString fe.text
  for i in [keep:ranges.size] do
    let (n, ms) ← c.cmd (chunk i) envs.back?
    envs := envs.push n
    let line0 := (fm.toPosition ⟨ranges[i]!.1⟩).line
    for m in ms do errs := errs.push s!"{rel}:{line0 + m.line - 1}:{m.col}: {m.text}"
  return ({ rel, text := fe.text, ranges, envs, frames := framesOf fe.text cmds }, errs)

/-- The text that adds the declaration text `d` (written for the scopes
    `dFrames`) in an environment whose scopes are `here`: close `here`,
    open `dFrames` in a section, `d`, close them, open `here` again. -/
def bridge (here dFrames : Array Frame) (d : String) : String := Id.run do
  if here == dFrames then return d
  let mut out : Array String := #[]
  for f in (here.extract 1 here.size).reverse do out := out.push f.closer
  out := out.push "section"
  out := out ++ dFrames[0]!.items
  for f in dFrames.extract 1 dFrames.size do out := (out.push f.opener) ++ f.items
  out := out.push d
  for f in (dFrames.extract 1 dFrames.size).reverse do out := out.push f.closer
  out := out.push "end"
  for f in here.extract 1 here.size do out := (out.push f.opener) ++ f.items
  return "\n".intercalate out.toList ++ "\n"

/-- The text of chunk `i` of `s` with `edits` (offsets in `s.text`) applied. -/
def Session.editedChunk (s : Session) (i : Nat) (edits : Array Edit) : String :=
  let (a, b) := s.ranges[i]!
  let local_ := edits.filterMap fun ed =>
    if a ≤ ed.start && ed.stop ≤ b && !(ed.start == b && ed.stop == b) then
      some { ed with start := ed.start - a, stop := ed.stop - a }
    else none
  applyEdits (s.chunk i) local_

/-- The chunks of `s` that `edits` touch. -/
def Session.touched (s : Session) (edits : Array Edit) : Array Nat :=
  (List.range s.ranges.size).toArray.filter fun i =>
    let (a, b) := s.ranges[i]!
    i > 0 && edits.any fun ed => a ≤ ed.start && ed.stop ≤ b && !(ed.start == b && ed.stop == b)

/-- The errors of one candidate: of the declaration (`dText`, the
    declaration `D_aliasCheck`, in the environment before chunk `dIdx` of
    `dSess`), and of each changed caller chunk `(session, chunk index, new
    text)`. A caller runs after `dStub` (the declaration with `sorry` for a
    theorem's proof: the callers need its type only) is added before it. -/
def check (c : Repl.Client) (dSess : Session) (dIdx : Nat) (dText dStub : String)
    (callers : Array (Session × Nat × String)) : IO (Array String × Array String) := do
  let line0 := dSess.lineOf dSess.ranges[dIdx]!.1
  let (_, dErrs) ← c.cmd dText (some dSess.envs[dIdx - 1]!)
  let declErrs := dErrs.map fun m => s!"{dSess.rel}:{line0 + m.line - 1}:{m.col}: {m.text}"
  unless declErrs.isEmpty do return (declErrs, #[])
  let dFrames := dSess.frames[dIdx]!
  let mut callErrs : Array String := #[]
  for (s, k, text) in callers do
    let l0 := s.lineOf s.ranges[k]!.1
    let (envB, bErrs) ← c.cmd (bridge s.frames[k]! dFrames dStub) (some s.envs[k - 1]!)
    unless bErrs.isEmpty do
      callErrs := callErrs ++ bErrs.map fun m => s!"{s.rel}:{l0}: the declaration does not elaborate before this command: {m.text}"
      continue
    let (_, errs) ← c.cmd text (some envB)
    callErrs := callErrs ++ errs.map fun m => s!"{s.rel}:{l0 + m.line - 1}:{m.col}: {m.text}"
  return (#[], callErrs)

end LeanTemper.ReplCheck
