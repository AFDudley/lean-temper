import Lake
open Lake DSL

-- `lean-temper` (see README.md): compiles Lean that elaborates but is
-- badly structured to a declared type-doctrine form. A target project's
-- rules are a `--config` JSON file (`examples/armada-lean.json`), not code.
package «lean-temper»

lean_lib LeanTemper

@[default_target]
lean_exe leanTemper where
  root := `Main
  exeName := "lean-temper"
  supportInterpreter := true

lean_exe tests where
  root := `Tests
  supportInterpreter := true
