import TPTND.Syntax
import TPTND.Judgement

namespace TPTND

/-! # TPTND Checking Monad

The error-reporting monad used by every rule checker, plus shared helpers.
Follows Section 6 of the TPTND Lean Design Document.

The top-level `checkDerivation` dispatch is defined separately (after all
rule families are available) to avoid circular imports. -/

-- ============================================================================
-- The monad
-- ============================================================================

abbrev CheckM := ExceptT String Id

/-- Gate: throw `msg` unless `cond` holds. -/
def ensure (cond : Bool) (msg : String) : CheckM Unit :=
  if cond then pure () else throw msg

-- ============================================================================
-- Helpers used by multiple rule families
-- ============================================================================

/-- Extract the conclusion claim from a derivation. -/
def getClaim (d : Derivation) : Claim := d.conclusion.claim

/-- Extract the conclusion context from a derivation. -/
def getCtx (d : Derivation) : Context := d.conclusion.context

/-- Demand exactly `n` premises; return them on success. -/
def expectPremises (d : Derivation) (n : Nat) (rule : String) :
    CheckM (List Derivation) := do
  let ps := d.premises
  ensure (ps.length == n)
    s!"{rule}: expected {n} premise(s), got {ps.length}"
  pure ps

/-- Demand at least `n` premises; return them on success. -/
def expectAtLeastPremises (d : Derivation) (n : Nat) (rule : String) :
    CheckM (List Derivation) := do
  let ps := d.premises
  ensure (ps.length ≥ n)
    s!"{rule}: expected at least {n} premise(s), got {ps.length}"
  pure ps

/-- Extract a `TermClaim` from a `Claim`, or throw. -/
def expectTermClaim (c : Claim) (ctx : String) : CheckM TermClaim :=
  match c with
  | .term tc => pure tc
  | _        => throw s!"{ctx}: expected a term claim"

/-- Extract a `TrustClaim` from a `Claim`, or throw. -/
def expectTrustClaim (c : Claim) (ctx : String) : CheckM TrustClaim :=
  match c with
  | .trust tc => pure tc
  | _         => throw s!"{ctx}: expected a trust claim"

/-- Extract a `ComparisonClaim` from a `Claim`, or throw. -/
def expectComparisonClaim (c : Claim) (ctx : String) : CheckM ComparisonClaim :=
  match c with
  | .comparison cc => pure cc
  | _              => throw s!"{ctx}: expected a comparison claim"

/-- Extract an identity claim's entry, or throw `msg`. -/
def expectIdentity (c : Claim) (msg : String) : CheckM ContextEntry :=
  match c with
  | .identity e => pure e
  | _           => throw msg

/-- Extract an exact constraint's probability, or throw `msg`. -/
def expectExact (c : Constraint) (msg : String) : CheckM Prob :=
  match c with
  | .exact p => pure p
  | _        => throw msg

/-- Extract the value of a `some`, or throw `msg`. -/
def expectSome {A : Type} (o : Option A) (msg : String) : CheckM A :=
  match o with
  | some a => pure a
  | none   => throw msg

/-- If a provenance was recovered, require `σ` to equal it. -/
def provPinned (o : Option Provenance) (σ : Provenance) (msg : String) :
    CheckM Unit :=
  match o with
  | some σ0 => ensure (σ == σ0) msg
  | none    => pure ()


/-- The variable designated to an observed term.  The paper writes `x_u` for
    the assumption belonging to the observed term `u`, so the name is read off
    the term itself rather than chosen freely. -/
def designatedName (rule : String) (t : Term) : CheckM String :=
  match t with
  | .atom u => pure u
  | _       => throw s!"{rule}: observed term must be atomic to name x_u"

end TPTND
