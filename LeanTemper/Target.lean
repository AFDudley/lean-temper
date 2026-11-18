/-
  The target checkout (see ../README.md): a module name from its file path,
  its `LEAN_PATH`, and the imports of one file from its header.
-/
import Lean
import LeanTemper.Proc

open Lean

namespace LeanTemper

/-- `ArmadaLean/Nitro/Value.lean` → `ArmadaLean.Nitro.Value`. -/
def moduleName (rel : String) : Name :=
  let noExt := if rel.endsWith ".lean" then (rel.dropEnd 5).copy else rel
  (noExt.splitOn "/").foldl (fun n c => Name.str n c) Name.anonymous

/-- `LEAN_PATH` of the target checkout, from `lake env`. -/
def targetSearchPath (root : System.FilePath) : IO (List System.FilePath) := do
  let sa : IO.Process.SpawnArgs := { cmd := "lake", args := #["env", "printenv", "LEAN_PATH"], cwd := root, env := ← leanEnv }
  let out ← IO.Process.output sa
  if out.exitCode != 0 then throw (IO.userError s!"lake env printenv LEAN_PATH failed: {out.stderr}")
  return (out.stdout.trimAscii.copy.splitOn ":").filter (· ≠ "") |>.map System.FilePath.mk

/-- The imports of a file, from its header only (no environment needed). -/
def fileImports (path : System.FilePath) : IO (Array Name) := do
  let text ← IO.FS.readFile path
  let (imports, _, _) ← Lean.Elab.parseImports text (some path.toString)
  return imports.map (·.module)

end LeanTemper
