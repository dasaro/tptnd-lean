import Lake
open Lake DSL

package tptnd where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib TPTND

/-- Builds the whole development including all proofs; see TPTNDLean.lean. -/
@[default_target]
lean_lib TPTNDLean

lean_exe tptnd_tests where
  root := `TPTND.Tests

lean_exe compas_audit where
  root := `TPTND.COMPASAudit

lean_exe compas_from_data where
  root := `TPTND.COMPASFromData

lean_exe adversarial where
  root := `TPTND.Adversarial

lean_exe adversarial2 where
  root := `TPTND.Adversarial2

lean_exe adversarial3 where
  root := `TPTND.Adversarial3

lean_exe adversarial_final where
  root := `TPTND.AdversarialFinal

lean_exe hmda_showcase where
  root := `TPTND.HMDAShowcase

lean_exe tptnd_check where
  root := `TPTND.Check

lean_exe tptnd_examples where
  root := `TPTND.Examples

lean_exe soundness_regression where
  root := `TPTND.SoundnessRegression



lean_exe deep_trees where
  root := `TPTND.DeepTrees
