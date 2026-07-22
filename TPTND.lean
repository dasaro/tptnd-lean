import TPTND.Syntax
import TPTND.Judgement
import TPTND.Arithmetic
import TPTND.WellFormedness
import TPTND.CheckM
import TPTND.Rules.OutputDist
import TPTND.Rules.AtomicLeaves
import TPTND.Rules.SamplingSum
import TPTND.Rules.ProductArrow
import TPTND.Rules.Bayesian
import TPTND.Rules.Trust
import TPTND.Rules.Comparison
import TPTND.Rules.Structural

namespace TPTND

/-! # Top-level derivation checker

`checkDerivation` dispatches on the rule name to the appropriate family
checker and then recurses into each premise (design doc §6). -/

/-- Dispatch a single node to its rule checker (no recursion). -/
def checkNode (d : Derivation) : CheckM Unit :=
  match d.ruleName with
  -- Output & distribution (Table 1)
  | "output_atom"  => checkOutputAtom d
  | "output_neg"   => checkOutputNeg d
  | "output_sum"   => checkOutputSum d
  | "output_prod"  => checkOutputProd d
  | "output_arr"   => checkOutputArr d
  | "base"         => checkBase d
  | "extend"       => checkExtend d
  | "extend_det"   => checkExtendDet d
  | "unknown"      => checkUnknown d
  -- Atomic leaves (Table 2)
  | "identity"      => checkIdentity d
  | "identity_star" => checkIdentityStar d
  | "identity_model" => checkIdentityModel d
  | "obs"           => checkObs d
  | "experiment"    => checkExperiment d
  | "expectation"   => checkExpectation d
  -- Sampling & sum (Table 3)
  | "sampling" => checkSampling d
  | "update"   => checkUpdate d
  | "I+"       => checkIPlus d
  | "E+L"      => checkEPlusL d
  | "E+R"      => checkEPlusR d
  -- Product & arrow (Table 4)
  | "I×"  => checkIProd d
  | "E×L" => checkEProdL d
  | "E×R" => checkEProdR d
  | "I→"  => checkIArr d
  | "E→"  => checkEArr d
  -- Bayesian (Table 5)
  | "I-P" => checkIPrior d
  | "E-P" => checkEPosterior d
  -- Trust (Tables 5–6)
  | "IT"   => checkIT d
  | "IUT"  => checkIUT d
  | "IT2"  => checkIT2 d
  | "IUT2" => checkIUT2 d
  | "ET"   => checkET d
  | "EUT"  => checkEUT d
  | "ETex" => checkETex d
  -- Comparison (Table 6)
  | "IEx"  => checkIEx d
  | "INEx" => checkINEx d
  | "EEx"  => checkEEx d
  | "ENEx" => checkENEx d
  -- Structural (Table 7)
  | "WeakeningD"  => checkWeakeningD d
  | "WeakeningS"  => checkWeakeningS d
  | "Contraction" => checkContraction d
  -- Unknown rule
  | other => throw s!"unknown rule: {other}"

mutual
/-- Check a full derivation tree: verify the current node's rule and then
    recurse into every premise.  Total (structurally recursive on the tree),
    which is what lets us reason about it in Lean's logic (see `Derivable`
    and `checker_sound`); `partial` would make it logically opaque. -/
def checkDerivation : Derivation → CheckM Unit
  | d@(.node _ ps _ _) => do
    -- 1. Global admissibility: the conclusion context must be well-formed
    --    (every support nonempty, every constraint valid, per-variable mass ≤ 1).
    ensure (contextWF (getCtx d)) "wf(Γ): conclusion context is not well-formed"
    -- 2. Check this node's rule-specific side conditions
    checkNode d
    -- 3. Recurse into each premise
    checkPremisesList ps
/-- Check every premise sub-tree (recursion partner for `checkDerivation`). -/
def checkPremisesList : List Derivation → CheckM Unit
  | [] => pure ()
  | p :: ps => do
    checkDerivation p
    checkPremisesList ps
end

end TPTND
