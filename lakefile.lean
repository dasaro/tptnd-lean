import Lake
open Lake DSL

package tptnd where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib TPTND

lean_exe tptnd_tests where
  root := `TPTND.Tests

lean_exe compas_audit where
  root := `TPTND.COMPASAudit

lean_exe compas_from_data where
  root := `TPTND.COMPASFromData

lean_exe hmda_showcase where
  root := `TPTND.HMDAShowcase

lean_exe pp_diverse where
  root := `TPTND.PPDiverse
