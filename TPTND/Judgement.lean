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

inductive TrustClaim where
  | trust   : (term : Term) → (samples : Nat) → (output : Output)
              → (observed : Prob) → (model : Prob)
              → (interval : Constraint) → TrustClaim
  | untrust : (term : Term) → (samples : Nat) → (output : Output)
              → (observed : Prob) → (model : Prob)
              → (interval : Constraint) → TrustClaim
  deriving Repr, DecidableEq

inductive ComparisonClaim where
  | excess   : TermClaim → TermClaim → Prob → Constraint → ComparisonClaim
  | noExcess : TermClaim → TermClaim → Prob → Constraint → ComparisonClaim
  deriving Repr, DecidableEq

inductive Claim where
  | outputDecl : Output → Claim
  | distDecl   : Context → Claim
  | identity   : ContextEntry → Claim
  | term       : TermClaim → Claim
  | trust      : TrustClaim → Claim
  | comparison : ComparisonClaim → Claim
  deriving Repr, DecidableEq

-- ============================================================================
-- 3.2 Rule names
-- ============================================================================

/-- Closed enumeration of every rule the checker dispatches on.
    Replacing the previous `String` rule-name field with this inductive
    turns rule-name typos into compile-time errors and makes the
    `checkNode` dispatch in `TPTND.lean` exhaustive. -/
inductive RuleName where
  -- Output & distribution
  | outputAtom | outputNeg | outputSum | outputProd | outputArr
  | base | extend | unknown
  -- Atomic leaves
  | identity | identityStar | obs | experiment | expectation
  -- Sampling & sum
  | sampling | update | iPlus | ePlusL | ePlusR
  -- Product & arrow
  | iProd | eProdL | eProdR | iArr | eArr
  -- Bayesian
  | iPrior | ePosterior
  -- Trust
  | iT | iUT | iT2 | iUT2 | eT | eUT | eTex
  -- Comparison
  | iEx | iNEx | eEx | eNEx
  -- Structural
  | weakeningD | weakeningS | contraction
  deriving Repr, DecidableEq

/-- Pretty display string for a rule name, used by case-study tree
    renderers and error messages.  Matches the names appearing in the
    paper's rule tables. -/
def RuleName.toString : RuleName → String
  | .outputAtom => "output_atom"
  | .outputNeg => "output_neg"
  | .outputSum => "output_sum"
  | .outputProd => "output_prod"
  | .outputArr => "output_arr"
  | .base => "base"
  | .extend => "extend"
  | .unknown => "unknown"
  | .identity => "identity"
  | .identityStar => "identity_star"
  | .obs => "obs"
  | .experiment => "experiment"
  | .expectation => "expectation"
  | .sampling => "sampling"
  | .update => "update"
  | .iPlus => "I+"
  | .ePlusL => "E+L"
  | .ePlusR => "E+R"
  | .iProd => "I×"
  | .eProdL => "E×L"
  | .eProdR => "E×R"
  | .iArr => "I→"
  | .eArr => "E→"
  | .iPrior => "I-P"
  | .ePosterior => "E-P"
  | .iT => "IT"
  | .iUT => "IUT"
  | .iT2 => "IT2"
  | .iUT2 => "IUT2"
  | .eT => "ET"
  | .eUT => "EUT"
  | .eTex => "ETex"
  | .iEx => "IEx"
  | .iNEx => "INEx"
  | .eEx => "EEx"
  | .eNEx => "ENEx"
  | .weakeningD => "WeakeningD"
  | .weakeningS => "WeakeningS"
  | .contraction => "Contraction"

instance : ToString RuleName := ⟨RuleName.toString⟩

-- ============================================================================
-- 3.3 Sequents and derivation trees
-- ============================================================================

structure Sequent where
  context : Context
  claim   : Claim
  deriving Repr

/-- A derivation tree node. `hasIndependenceWitness` models the explicit `#w`
    witness required by I×, WeakeningD, and WeakeningS (design doc §9.4). -/
inductive Derivation where
  | node : (ruleName : RuleName)
           → (premises : List Derivation)
           → (conclusion : Sequent)
           → (hasIndependenceWitness : Bool)
           → Derivation
  deriving Repr

def Derivation.conclusion : Derivation → Sequent
  | .node _ _ s _ => s

def Derivation.premises : Derivation → List Derivation
  | .node _ ps _ _ => ps

def Derivation.ruleName : Derivation → RuleName
  | .node r _ _ _ => r

def Derivation.hasIndependenceWitness : Derivation → Bool
  | .node _ _ _ w => w

/-- Tree depth: leaves count 1; internal nodes are 1 + max child depth. -/
def Derivation.depth : Derivation → Nat
  | .node _ ps _ _ =>
    1 + (ps.map Derivation.depth).foldl Nat.max 0

/-- Total number of nodes in the derivation tree. -/
def Derivation.nodeCount : Derivation → Nat
  | .node _ ps _ _ =>
    1 + (ps.map Derivation.nodeCount).foldl (· + ·) 0

end TPTND
