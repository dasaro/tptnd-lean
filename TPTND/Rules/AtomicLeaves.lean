import TPTND.CheckM
import TPTND.WellFormedness
import TPTND.Arithmetic
import Mathlib.Data.Finset.Card

namespace TPTND

/-! # Atomic Leaf Rules (Table 2)

`identity`, `identity_star`, `obs`, `experiment`, `expectation`.
Design doc §7.2. -/

def isAtomicTerm : Term → Bool
  | .atom _ => true
  | _       => false

/-- Find entries in Γ supporting term `t` at output `α`: the paper's
    `∃! x:α_c ∈ Γ` fixes α to the conclusion's output, so uniqueness is
    among entries matching both the term name and the output. -/
def supportEntries (Γ : Context) (t : Term) (α : Output) :
    List ContextEntry :=
  match t with
  | .atom s => Γ.filter (fun e => e.name == s && e.output == α)
  | _       => []

-- ============================================================================
-- identity  (IDENTITY*₂ in PDF): |Γ| = 1, entry matches conclusion
-- ============================================================================

def checkIdentity (d : Derivation) : CheckM Unit := do
  let _ ← expectPremises d 0 "identity"
  let Γ := getCtx d
  ensure (Γ.length == 1) "identity: context must be a singleton"
  match Γ, getClaim d with
  | [e], .identity e' =>
    ensure (e == e') "identity: context entry must match conclusion entry"
  | _, _ => throw "identity: conclusion must be an identity claim"

-- ============================================================================
-- identity_model (IDENTITY*₂ in PDF): wf(Γ), |Γ| = 1, Γ = {x : α_a} ⊢ y : β_b
-- ============================================================================

/-- The paper's IDENTITY*₂: from a singleton context `{x : α_a}` conclude an
    exact model judgement `y : β_b` whose value need NOT equal `a`.  This is
    the "Lean-level exact model import retained for the Bayesian fragment",
    and it is what makes I-P's general prior families `(a_i, b_i)` (with
    `b_i ≠ a_i`) derivable at all.  Because it can introduce an unconstrained
    exact value, the trust and comparison rules explicitly refuse it as a
    model premise (see `checkIT`/`checkIUT`/`checkEEx`/`checkENEx`). -/
def checkIdentityModel (d : Derivation) : CheckM Unit := do
  let _ ← expectPremises d 0 "identity_model"
  ensure ((getCtx d).length == 1) "identity_model: context must be a singleton"
  match getCtx d, getClaim d with
  | [e], .identity e' =>
    ensure (match e.constraint with | .exact _ => true | _ => false)
      "identity_model: the context assumption must be exact"
    ensure (match e'.constraint with | .exact _ => true | _ => false)
      "identity_model: the imported model value must be exact"
  | _, _ => throw "identity_model: conclusion must be an identity claim"

-- ============================================================================
-- identity_star (IDENTITY* in PDF): lookup x : αc ∈ Γ
-- ============================================================================

def checkIdentityStar (d : Derivation) : CheckM Unit := do
  let _ ← expectPremises d 0 "identity_star"
  match getClaim d with
  | .identity e =>
    ensure (e ∈ getCtx d)
      "identity_star: entry not found in context"
  | _ => throw "identity_star: conclusion must be an identity claim"

-- ============================================================================
-- obs (OBS* in PDF)
-- ============================================================================

def checkObs (d : Derivation) : CheckM Unit := do
  let _ ← expectPremises d 0 "obs"
  match getClaim d with
  | .term tc => do
    ensure (tc.mode == .frequency) "obs: must be frequency mode"
    ensure tc.prov.Nonempty "obs: provenance must be nonempty"
    ensure (tc.samples > 0) "obs: sample size must be positive"
    ensure (isAtomicTerm tc.term) "obs: term must be atomic"
    -- nf ∈ ℕ: samples * frequency must be a natural number
    let nf := (tc.samples : ℚ) * tc.value.val
    ensure (nf.den == 1 && nf.num ≥ 0)
      "obs: n·f must be a non-negative integer"
    -- Exactly one support entry for term t at output α
    ensure ((supportEntries (getCtx d) tc.term tc.output).length == 1)
      "obs: exactly one support entry required for term at this output"
  | _ => throw "obs: conclusion must be a term claim"

-- ============================================================================
-- experiment (EXPERIMENT in PDF)
-- ============================================================================

def checkExperiment (d : Derivation) : CheckM Unit := do
  let _ ← expectPremises d 0 "experiment"
  match getClaim d with
  | .term tc => do
    ensure (tc.prov.card == 1) "experiment: provenance must be singleton"
    ensure (isAtomicTerm tc.term) "experiment: term must be atomic"
    -- The calculus's EXPERIMENT judgement `Γ ⊢_ρ t : α` is a SINGLE run with
    -- no frequency: encode it as one sample that certainly produced α.
    ensure (tc.mode == .frequency) "experiment: must be frequency mode"
    ensure (tc.samples == 1) "experiment: a single run has exactly one sample"
    ensure (decide (tc.value.val == 1))
      "experiment: a single run's outcome has value 1"
    ensure ((supportEntries (getCtx d) tc.term tc.output).length == 1)
      "experiment: exactly one support entry required for term at this output"
  | _ => throw "experiment: conclusion must be a term claim"

-- ============================================================================
-- expectation (EXPECTATION in PDF)
-- ============================================================================

def checkExpectation (d : Derivation) : CheckM Unit := do
  let _ ← expectPremises d 0 "expectation"
  match getClaim d with
  | .term tc => do
    ensure (tc.mode == .expected) "expectation: must be expected mode"
    ensure (tc.prov.card == 1) "expectation: provenance must be singleton"
    ensure (tc.samples > 0) "expectation: sample size must be positive"
    ensure (isAtomicTerm tc.term) "expectation: term must be atomic"
    -- Exactly one EXACT support entry at output α, whose value the claim carries
    match supportEntries (getCtx d) tc.term tc.output with
    | [e] =>
      match e.constraint with
      | .exact a =>
        ensure (decide (tc.value.val == a.val))
          "expectation: expected value must equal the entry's exact probability"
      | _ => throw "expectation: support entry must have exact constraint"
    | _ => throw "expectation: exactly one support entry required at this output"
  | _ => throw "expectation: conclusion must be a term claim"

end TPTND
