import Lake
open Lake DSL

package lean_phase1 where
  version := v!"0.1.0"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib LeanPhase1

@[default_target]
lean_exe lean_phase1 where
  root := `Main
