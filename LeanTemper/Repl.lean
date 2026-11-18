/-
  A client for the Lean REPL (https://github.com/leanprover-community/repl,
  built at the target's toolchain; see ../README.md, "Alias mode").

  The client starts `lake env <repl>` in the target checkout and sends one
  JSON command per request: `{"cmd": text}` (a new environment from the
  imports in `text`) or `{"cmd": text, "env": n}` (the commands of `text`
  run in the saved environment `n`, with its scopes: namespaces, sections,
  `open`s, `variable`s). Each response names the new environment and the
  messages of `text` alone, at positions in `text`.
-/
import Lean
import LeanTemper.Proc

open Lean

namespace LeanTemper.Repl

structure Client where
  child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .inherit }
  stdin : IO.FS.Stream
  stdout : IO.FS.Stream
  log : IO.FS.Handle

/-- One error message of a command: the position in the command's text (line 1-based). -/
structure Msg where
  line : Nat
  col : Nat
  text : String
  deriving Inhabited

/-- Start the REPL with the target's `LEAN_PATH` (`LeanTemper.targetSearchPath`). -/
def start (repl : System.FilePath) (leanPath : List System.FilePath) (logPath : System.FilePath) : IO Client := do
  let lp := ":".intercalate (leanPath.map (·.toString))
  let child ← IO.Process.spawn {
    cmd := repl.toString, env := (← leanEnv).push ("LEAN_PATH", some lp),
    stdin := .piped, stdout := .piped, stderr := .inherit }
  let log ← IO.FS.Handle.mk logPath .write
  return { child, stdin := IO.FS.Stream.ofHandle child.stdin, stdout := IO.FS.Stream.ofHandle child.stdout, log }

def Client.stop (c : Client) : IO Unit := do
  c.child.kill
  let _ ← c.child.wait
  c.log.flush

/-- Send one request; the response ends with an empty line. -/
partial def Client.request (c : Client) (req : Json) : IO Json := do
  c.stdin.putStr (req.compress ++ "\n\n")
  c.stdin.flush
  let rec read (acc : String) : IO String := do
    let line ← c.stdout.getLine
    if line.isEmpty then throw (IO.userError s!"the REPL stopped; the last request: {(req.compress).take 300}")
    if line.trimAscii.isEmpty then
      if acc.trimAscii.isEmpty then read acc else return acc
    else read (acc ++ line)
  let out ← read ""
  match Json.parse out with
  | .ok j => return j
  | .error e => throw (IO.userError s!"the REPL answered with no JSON ({e}): {out.take 500}")

/-- Run `text` in environment `env` (with no `env`: `text` starts with its
    imports). Returns the new environment and the error messages. -/
def Client.cmd (c : Client) (text : String) (env : Option Nat) : IO (Nat × Array Msg) := do
  let req := Json.mkObj ([("cmd", toJson text)] ++ (env.map fun n => ("env", toJson n)).toList)
  let t0 ← IO.monoMsNow
  let j ← c.request req
  c.log.putStrLn s!"[repl] env {env} {text.utf8ByteSize} bytes in {(← IO.monoMsNow) - t0} ms"
  if let .ok m := j.getObjValAs? String "message" then
    throw (IO.userError s!"the REPL refused a command: {m}")
  let some n := (j.getObjValAs? Nat "env").toOption
    | throw (IO.userError s!"the REPL answered with no environment: {j.compress.take 500}")
  let msgs := match j.getObjVal? "messages" with
    | .ok (.arr ms) => ms
    | _ => #[]
  let errs := msgs.filterMap fun m =>
    if m.getObjValD "severity" == toJson "error" then
      let pos := m.getObjValD "pos"
      some { line := (pos.getObjValAs? Nat "line").toOption.getD 0, col := (pos.getObjValAs? Nat "column").toOption.getD 0,
             text := (m.getObjValAs? String "data").toOption.getD "" }
    else none
  return (n, errs)

end LeanTemper.Repl
