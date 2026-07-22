import TPTND.Syntax

namespace TPTND

/-! # TPTND Judgement Forms and Derivation Trees

Sequent forms, claims, and the derivation tree type.
Follows Section 3 of the TPTND Lean Design Document.

## Sequent forms mapped from the calculus (PDF §1)

1. `⊢ α :: output`                          → `Claim.outputDecl`
2. `⊢ Γ`                                    → `Claim.distDecl`
3. `Γ ⊢ x : αc`                             → `Claim.identity`
4. `Γ ⊢_σ tₙ : α_ã`  (expected mode)       → `Claim.term` with `TermMode.expected`
5. `Γ ⊢_σ tₙ : α_f`  (frequency mode)      → `Claim.term` with `TermMode.frequency`
6. `Trust_P(...)`                            → `Claim.trust (.trust ...)`
7. `UTrust_P(...)`                           → `Claim.trust (.untrust ...)`
8. `Excess_Q(...)`                           → `Claim.comparison (.excess ...)`
9. `NoExcess_Q(...)`                         → `Claim.comparison (.noExcess ...)`
-/

-- ============================================================================
-- 3.1 Claims (right-hand sides of sequents)
-- ============================================================================

inductive TermMode where
  | expected
  | frequency
  deriving Repr, DecidableEq

structure TermClaim where
  mode    : TermMode
  term    : Term
  samples : Nat           -- n > 0 enforced by rule checkers
  output  : Output
  value   : Prob          -- expected probability ã or frequency f
  prov    : Provenance    -- σ
  deriving Repr, DecidableEq

/-- Which confidence interval a trust certificate is built on:
    `oneSample` = 𝒫(n,f,p) around a probability (IT/IUT); `twoSample` = 𝒬
    around a rate difference f−g (IT2/IUT2).  This tag is what stops a
    two-sample (difference) interval from being eliminated by ET/EUT/ETex,
    which would inject a difference interval as a probability constraint. -/
inductive CIKind where
  | oneSample
  | twoSample
  deriving Repr, DecidableEq

/-- A trust certificate.  It carries the provenance of the observation it
    certifies: the eliminations (ET/EUT/ETex) read it from the claim itself
    rather than digging into the premise *tree*, which a claim-preserving
    structural wrapper could reshape (the old `obsProvOf` walked the premises
    and silently found nothing — or the wrong term — behind a wrapper). -/
inductive TrustClaim where
  | trust   : (kind : CIKind) → (term : Term) → (samples : Nat) → (output : Output)
              → (observed : Prob) → (model : Prob)
              → (interval : Constraint) → (prov : Provenance) → TrustClaim
  | untrust : (kind : CIKind) → (term : Term) → (samples : Nat) → (output : Output)
              → (observed : Prob) → (model : Prob)
              → (interval : Constraint) → (prov : Provenance) → TrustClaim
  deriving Repr, DecidableEq

inductive ComparisonClaim where
  | excess   : TermClaim → TermClaim → Prob → Constraint → ComparisonClaim
  | noExcess : TermClaim → TermClaim → Prob → Constraint → ComparisonClaim
  deriving Repr, DecidableEq

/-- A Bayesian prior family.

    The printed rule is `{⊢ [x]y : (α → β)_{[aᵢ]bᵢ} | 1 ≤ i ≤ m}`, so the
    hypothesis variable and output `(x, α)` and the target variable and output
    `(y, β)` are part of the judgement, not incidental to it.  Carrying only
    the `(aᵢ, bᵢ)` values let `E-P` select its supporting hypothesis by output
    alone and left its conclusion entirely unconstrained. -/
structure PriorFamily where
  /-- hypothesis variable `x` -/
  xName  : String
  /-- hypothesis output `α` -/
  alpha  : Output
  /-- target variable `y` -/
  yName  : String
  /-- target output `β` -/
  beta   : Output
  /-- the family `(aᵢ, bᵢ)`, in premise order -/
  points : List (Prob × Prob)
  deriving Repr, DecidableEq

inductive Claim where
  | outputDecl : Output → Claim
  | distDecl   : Context → Claim
  | identity   : ContextEntry → Claim
  | term       : TermClaim → Claim
  | trust      : TrustClaim → Claim
  | comparison : ComparisonClaim → Claim
  -- Prior family produced by I-P: the list of (value aᵢ, weight bᵢ) pairs.
  | priorFamily : PriorFamily → Claim
  deriving Repr, DecidableEq

-- ============================================================================
-- 3.2 Sequents and derivation trees
-- ============================================================================

structure Sequent where
  context : Context
  claim   : Claim
  deriving Repr

/-- A derivation tree node. `hasIndependenceWitness` models the explicit `#w`
    witness required by I×, WeakeningD, and WeakeningS (design doc §9.4). -/
inductive Derivation where
  | node : (ruleName : String)
           → (premises : List Derivation)
           → (conclusion : Sequent)
           → (hasIndependenceWitness : Bool)
           → Derivation
  deriving Repr

def Derivation.conclusion : Derivation → Sequent
  | .node _ _ s _ => s

def Derivation.premises : Derivation → List Derivation
  | .node _ ps _ _ => ps

def Derivation.ruleName : Derivation → String
  | .node r _ _ _ => r

def Derivation.hasIndependenceWitness : Derivation → Bool
  | .node _ _ _ w => w

end TPTND
