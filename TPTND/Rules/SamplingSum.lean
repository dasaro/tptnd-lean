import TPTND.CheckM
import TPTND.WellFormedness
import TPTND.Arithmetic
import Mathlib.Data.Finset.Card

namespace TPTND

/-! # Sampling and Sum Rules (Table 3)

`sampling`, `update`, `I+`, `E+L`, `E+R`.  Design doc §7.3. -/

-- ============================================================================
-- Helper: extract TermClaim from each premise
-- ============================================================================

private def premiseTermClaims (ps : List Derivation) (rule : String) :
    CheckM (List TermClaim) :=
  ps.mapM (fun p => expectTermClaim (getClaim p) rule)

-- ============================================================================
-- sampling
-- ============================================================================

def checkSampling (d : Derivation) : CheckM Unit := do
  let ps ← expectAtLeastPremises d 1 "sampling"
  let conc ← expectTermClaim (getClaim d) "sampling"
  ensure (conc.mode == .frequency) "sampling: conclusion must be frequency mode"
  ensure (ps.all (fun p => contextEqSet (getCtx p) (getCtx d)))
    "sampling: all premises must share the conclusion's context Γ"
  let premTCs ← premiseTermClaims ps "sampling"
  -- Premises must be single-run EXPERIMENT-form judgements (Table 3 reads
  -- `Γ ⊢_ρi t : αi`), else n and f could be fabricated from richer claims.
  ensure (premTCs.all (fun tc =>
      tc.prov.card == 1 && tc.samples == 1 && tc.mode == .frequency))
    "sampling: every premise must be a single-run experiment (|ρ| = 1, one sample)"
  -- All premises must have the same term
  ensure (premTCs.all (·.term == conc.term))
    "sampling: all premises must share the same term"
  -- Pairwise disjoint provenances
  let provs := premTCs.map (·.prov)
  let rec pairwiseDisjoint : List Provenance → Bool
    | [] => true
    | p :: rest => rest.all (Provenance.disjoint p ·) && pairwiseDisjoint rest
  ensure (pairwiseDisjoint provs)
    "sampling: premise provenances must be pairwise disjoint"
  -- Conclusion provenance = union of all premise provenances
  let unionProv := provs.foldl (· ∪ ·) ∅
  ensure (conc.prov == unionProv)
    "sampling: conclusion provenance must be union of premise provenances"
  -- n = number of premises
  ensure (conc.samples == ps.length)
    "sampling: conclusion sample size must equal number of premises"
  -- f = |{i | αᵢ = α}| / n
  let matchCount := premTCs.filter (·.output == conc.output) |>.length
  let expectedF := (matchCount : ℚ) / (ps.length : ℚ)
  ensure (decide (conc.value.val == expectedF))
    "sampling: frequency mismatch"

-- ============================================================================
-- update
-- ============================================================================

def checkUpdate (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "update"
  match ps with
  | [p1, p2] => do
    let tc1 ← expectTermClaim (getClaim p1) "update"
    let tc2 ← expectTermClaim (getClaim p2) "update"
    let conc ← expectTermClaim (getClaim d) "update"
    ensure (tc1.mode == .frequency && tc2.mode == .frequency && conc.mode == .frequency)
      "update: all three must be frequency mode"
    -- A zero-sample batch carries no evidence and makes the weighted average
    -- degenerate (it would let f' be anything at weight 0).
    ensure (tc1.samples > 0 && tc2.samples > 0)
      "update: both batches must have positive sample size"
    ensure (contextEqSet (getCtx p1) (getCtx d) && contextEqSet (getCtx p2) (getCtx d))
      "update: premises and conclusion must share the same context Γ"
    ensure (tc1.term == tc2.term && tc1.term == conc.term)
      "update: all three must share the same term"
    ensure (tc1.output == tc2.output && tc1.output == conc.output)
      "update: all three must share the same output"
    ensure (Provenance.disjoint tc1.prov tc2.prov)
      "update: provenances must be disjoint"
    ensure (conc.prov == tc1.prov ∪ tc2.prov)
      "update: conclusion provenance must be union of premise provenances"
    ensure (conc.samples == tc1.samples + tc2.samples)
      "update: conclusion sample size must be sum"
    match weightedFreq tc1.samples tc1.value tc2.samples tc2.value with
    | some wf =>
      ensure (decide (conc.value.val == wf.val))
        "update: weighted frequency mismatch"
    | none => throw "update: weighted frequency computation failed"
  | _ => throw "update: internal error"

-- ============================================================================
-- I+  (sum introduction)
-- ============================================================================

def checkIPlus (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "I+"
  match ps with
  | [p1, p2] => do
    let tc1 ← expectTermClaim (getClaim p1) "I+"
    let tc2 ← expectTermClaim (getClaim p2) "I+"
    let conc ← expectTermClaim (getClaim d) "I+"
    ensure (tc1.mode == tc2.mode && tc1.mode == conc.mode)
      "I+: all must share the same mode"
    ensure (tc1.samples == tc2.samples && tc1.samples == conc.samples)
      "I+: all must share the same sample size"
    ensure (tc1.prov == tc2.prov && tc1.prov == conc.prov)
      "I+: all must share the same provenance"
    ensure (tc1.term == tc2.term && tc1.term == conc.term)
      "I+: all must share the same term"
    ensure (contextEqSet (getCtx p1) (getCtx d) && contextEqSet (getCtx p2) (getCtx d))
      "I+: premises and conclusion must share the same context Γ"
    ensure (tc1.output != tc2.output)
      "I+: premise outputs must be distinct"
    ensure (Output.syntacticallyDisjoint tc1.output tc2.output)
      "I+: premise outputs must be syntactically disjoint"
    ensure (conc.output == Output.sum tc1.output tc2.output)
      "I+: conclusion output must be sum of premise outputs"
    match probAdd tc1.value tc2.value with
    | some s =>
      ensure (decide (conc.value.val == s.val))
        "I+: conclusion value must be p + q"
    | none => throw "I+: p + q exceeds 1"
  | _ => throw "I+: internal error"

-- ============================================================================
-- E+L  (sum elimination left)
-- ============================================================================

def checkEPlusL (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "E+L"
  match ps with
  | [p1, p2] => do
    let tc1 ← expectTermClaim (getClaim p1) "E+L"   -- (α+β)_r
    let tc2 ← expectTermClaim (getClaim p2) "E+L"   -- α_p
    let conc ← expectTermClaim (getClaim d) "E+L"   -- β_{r-p}
    ensure (tc1.mode == tc2.mode && tc1.mode == conc.mode)
      "E+L: all must share the same mode"
    ensure (tc1.samples == tc2.samples && tc1.samples == conc.samples)
      "E+L: all must share the same sample size"
    ensure (tc1.prov == tc2.prov && tc1.prov == conc.prov)
      "E+L: all must share the same provenance"
    ensure (tc1.term == tc2.term && tc1.term == conc.term)
      "E+L: all three sequents must share the same term"
    -- Sound subtraction needs disjoint summands (cf. Semantics.prob_EPlusL).
    ensure (Output.syntacticallyDisjoint tc2.output conc.output)
      "E+L: the two summands must be syntactically disjoint"
    ensure (contextEqSet (getCtx p1) (getCtx d) && contextEqSet (getCtx p2) (getCtx d))
      "E+L: premises and conclusion must share the same context Γ"
    -- tc1 output must be sum of tc2 output and conc output
    ensure (tc1.output == Output.sum tc2.output conc.output)
      "E+L: first premise must be sum of second premise and conclusion outputs"
    -- 0 ≤ p ≤ r ≤ 1
    ensure (decide (tc2.value.val ≤ tc1.value.val))
      "E+L: p must be ≤ r"
    match probSub tc1.value tc2.value with
    | some diff =>
      ensure (decide (conc.value.val == diff.val))
        "E+L: conclusion value must be r - p"
    | none => throw "E+L: r - p is negative"
  | _ => throw "E+L: internal error"

-- ============================================================================
-- E+R  (sum elimination right)
-- ============================================================================

def checkEPlusR (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "E+R"
  match ps with
  | [p1, p2] => do
    let tc1 ← expectTermClaim (getClaim p1) "E+R"   -- (α+β)_r
    let tc2 ← expectTermClaim (getClaim p2) "E+R"   -- β_q
    let conc ← expectTermClaim (getClaim d) "E+R"   -- α_{r-q}
    ensure (tc1.mode == tc2.mode && tc1.mode == conc.mode)
      "E+R: all must share the same mode"
    ensure (tc1.samples == tc2.samples && tc1.samples == conc.samples)
      "E+R: all must share the same sample size"
    ensure (tc1.prov == tc2.prov && tc1.prov == conc.prov)
      "E+R: all must share the same provenance"
    ensure (tc1.term == tc2.term && tc1.term == conc.term)
      "E+R: all three sequents must share the same term"
    ensure (Output.syntacticallyDisjoint conc.output tc2.output)
      "E+R: the two summands must be syntactically disjoint"
    ensure (contextEqSet (getCtx p1) (getCtx d) && contextEqSet (getCtx p2) (getCtx d))
      "E+R: premises and conclusion must share the same context Γ"
    ensure (tc1.output == Output.sum conc.output tc2.output)
      "E+R: first premise must be sum of conclusion and second premise outputs"
    ensure (decide (tc2.value.val ≤ tc1.value.val))
      "E+R: q must be ≤ r"
    match probSub tc1.value tc2.value with
    | some diff =>
      ensure (decide (conc.value.val == diff.val))
        "E+R: conclusion value must be r - q"
    | none => throw "E+R: r - q is negative"
  | _ => throw "E+R: internal error"

end TPTND
