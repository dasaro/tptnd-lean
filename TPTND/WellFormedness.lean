import TPTND.Syntax
import TPTND.Judgement
import TPTND.Arithmetic

namespace TPTND

/-! # TPTND Well-Formedness Predicates

Entry-level and context-level well-formedness, independence witnesses,
provenance checks, and context merging.
Follows Section 5 of the TPTND Lean Design Document. -/

-- ============================================================================
-- Entry well-formedness
-- ============================================================================

/-- A constraint is well-formed when its endpoints satisfy ℓ ≤ h. -/
def constraintWF (c : Constraint) : Bool :=
  match c with
  | .exact _             => true
  | .interval lo hi      => decide (lo.val ≤ hi.val)
  | .outsideInterval lo hi => decide (lo.val ≤ hi.val)
  | .unknown             => true

/-- An entry is well-formed when its support is nonempty and its
    constraint is well-formed. -/
def entryWF (e : ContextEntry) : Bool :=
  e.support.Nonempty && constraintWF e.constraint

-- ============================================================================
-- Context well-formedness (global admissibility)
-- ============================================================================

/-- Exact mass of an entry: the `val` if the constraint is `.exact`, else 0. -/
def exactMass (e : ContextEntry) : ℚ :=
  match e.constraint with
  | .exact p => p.val
  | _        => 0

/-- Lower bound contributed by an interval constraint, else 0. -/
def intervalLower (e : ContextEntry) : ℚ :=
  match e.constraint with
  | .interval lo _ => lo.val
  | _              => 0

/-- The mass one `(variable, output)` group commits to: the LARGEST commitment
    any of its competing hypotheses makes.

    Max, not min: every satisfied entry individually bounds the event's
    probability from below, so the group's strongest claim is still a valid
    lower bound (`Semantics.groupMass_le_prob`) — and taking the minimum was
    exploitable: adding a trivial `x : α_[0,1]` entry to a group dropped its
    committed mass to 0, laundering a genuine mass overflow past `wf(Γ)`.
    Contraction's premise shape still passes: `{x : α_{0.4}, x : α_{[0.3,0.5]}}`
    commits max(0.4, 0.3) = 0.4. -/
def groupMass (entries : List ContextEntry) (α : Output) : ℚ :=
  let masses :=
    (entries.filter (fun e => e.output == α)).map (fun e => exactMass e + intervalLower e)
  match masses with
  | []      => 0
  | m :: ms => ms.foldl max m

/-- Per-variable total committed mass.

    Entries for the SAME (variable, output) pair are competing hypotheses
    about one event, not disjoint events, so they must not be summed — the
    committed mass for that output is the least any of them commits to.
    Only distinct outputs add.

    Summing them was a real bug: it made `Contraction`'s own premise shape
    `Γ, x : α_{c₁}, …, x : α_{cₖ}` violate `wf(Γ)` whenever the `cᵢ` summed
    past 1 (e.g. 0.4 and 0.7), so the rule could never fire on the very
    contexts it exists to contract. -/
def variableMass (Γ : Context) (x : String) : ℚ :=
  let entries := Γ.filter (fun e => e.name == x)
  (((entries.map (·.output)).dedup).map (groupMass entries)).sum

/-- `variableMass` unfolded, as an equation usable by `rw`. -/
theorem variableMass_eq (Γ : Context) (x : String) :
    variableMass Γ x
      = ((((Γ.filter (fun e => e.name == x)).map (·.output)).dedup).map
          (groupMass (Γ.filter (fun e => e.name == x)))).sum := rfl

/-- Distinct variable names in a context. -/
def variableNames (Γ : Context) : List String :=
  (Γ.map (·.name)).dedup

/-- A context is well-formed when every entry is well-formed and, for each
    variable, exact masses plus interval lower bounds do not exceed 1. -/
def contextWF (Γ : Context) : Bool :=
  Γ.all entryWF &&
  (variableNames Γ).all (fun x => decide (variableMass Γ x ≤ 1))

-- ============================================================================
-- Independence witness
-- ============================================================================

/-- Conservative structural test for the paper's independence witness `Γ #w Δ`.

    Two contexts may be treated as independent only when they constrain
    disjoint sets of random variables.  If some variable `x` is assumed on
    both sides, the two judgements may concern the very same underlying
    variable and their probabilities must not be multiplied.

    This is what blocks `⟨x, x⟩ : (α × α)_{a²}`: independence is a property
    of distinct variables, so the test must not hold vacuously when the two
    contexts coincide.

    The explicit witness flag on the node is still required — the witness is
    the producer's claim, this predicate is the checker's own sanity check
    (cf. Table 7, "explicit independence witness and conservative support
    sanity check"). -/
def independentContexts (Γ Δ : Context) : Bool :=
  (variableNames Γ).all (fun x => !((variableNames Δ).contains x))

-- ============================================================================
-- Provenance checks
-- ============================================================================

/-- Extract provenance from a term claim inside a derivation's conclusion. -/
private def claimProv (c : Claim) : Option Provenance :=
  match c with
  | .term tc => some tc.prov
  | _        => none

/-- All premises share the same provenance.  Returns `true` when the list is
    empty or when provenance is not applicable to every premise. -/
def sameProvenance (ps : List Derivation) : Bool :=
  let provs := ps.filterMap (fun d => claimProv d.conclusion.claim)
  match provs with
  | []     => true
  | p :: rest => rest.all (· == p)

-- ============================================================================
-- Context merging
-- ============================================================================

/-- Merge a list of contexts by concatenation and deduplication.
    Two entries are considered equal when all four fields match
    (`DecidableEq ContextEntry`).  Order follows the input order with
    later duplicates removed. -/
def mergeContexts (cs : List Context) : Context :=
  (cs.flatten).eraseDups

/-- Check whether two contexts are equal up to ordering (set equality). -/
def contextEqSet (Γ Δ : Context) : Bool :=
  Γ.all (· ∈ Δ) && Δ.all (· ∈ Γ)


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

end TPTND
