import TPTND.CheckM
import TPTND.Spec
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

/-- Variadic premise extraction, carrying the map equation (forward mode).
    Public so the operational bridge can evaluate `checkSampling` symbolically. -/
def premiseTermClaimsC (ps : List Derivation) (rule : String) :
    CheckM {tcs : List TermClaim // ps.map getClaim = tcs.map .term} :=
  match ps with
  | [] => pure ⟨[], rfl⟩
  | p :: rest =>
    match htc : getClaim p with
    | .term tc => do
      let ⟨tcs, hrest⟩ ← premiseTermClaimsC rest rule
      pure ⟨tc :: tcs, by rw [List.map_cons, List.map_cons, htc, hrest]⟩
    | _ => throw s!"{rule}: expected a term claim"

def checkSamplingC (d : Derivation) :
    CheckM (PLift ((∀ p ∈ d.premises, Derivable p.conclusion)
                   → contextWF (getCtx d) = true
                   → Derivable d.conclusion)) := do
  let ⟨hlen1⟩ ← ensure' (d.premises.length ≥ 1)
    s!"sampling: expected at least 1 premise(s), got {d.premises.length}"
  match hcc : getClaim d with
  | .term conc => do
    let ⟨hmode⟩ ← ensure' (conc.mode == .frequency)
      "sampling: conclusion must be frequency mode"
    let ⟨hctxs⟩ ← ensure' (d.premises.all (fun p => contextEqSet (getCtx p) (getCtx d)))
      "sampling: all premises must share the conclusion's context Γ"
    let ⟨tcs, hmap⟩ ← premiseTermClaimsC d.premises "sampling"
    -- Premises must be single-run EXPERIMENT-form judgements (Table 3 reads
    -- `Γ ⊢_ρi t : αi`), else n and f could be fabricated from richer claims.
    let ⟨hexp⟩ ← ensure' (tcs.all (fun tc =>
        tc.prov.card == 1 && tc.samples == 1 && tc.mode == .frequency))
      "sampling: every premise must be a single-run experiment (|ρ| = 1, one sample)"
    -- All premises must have the same term
    let ⟨hterm⟩ ← ensure' (tcs.all (·.term == conc.term))
      "sampling: all premises must share the same term"
    -- Pairwise disjoint provenances
    let provs := tcs.map (·.prov)
    let ⟨hdisj⟩ ← ensure' (Provenance.pairwiseDisjoint provs)
      "sampling: premise provenances must be pairwise disjoint"
    -- Conclusion provenance = union of all premise provenances
    let unionProv := provs.foldl (· ∪ ·) ∅
    let ⟨hprov⟩ ← ensure' (conc.prov == unionProv)
      "sampling: conclusion provenance must be union of premise provenances"
    -- n = number of premises
    let ⟨hn⟩ ← ensure' (conc.samples == d.premises.length)
      "sampling: conclusion sample size must equal number of premises"
    -- f = |{i | αᵢ = α}| / n
    let ⟨hval⟩ ← ensure' (decide (conc.value.val ==
        (((tcs.filter (·.output == conc.output)).length : ℚ)
          / (d.premises.length : ℚ))))
      "sampling: frequency mismatch"
    pure ⟨fun hprem hwf => by
      have hplen : d.premises.length = tcs.length := by
        have := congrArg List.length hmap
        simpa using this
      -- positional claim equations from the map equation
      have hclaims : ∀ pr ∈ d.premises.zip tcs, getClaim pr.1 = .term pr.2 := by
        intro pr hpr
        obtain ⟨i, hi, hpri⟩ := List.getElem_of_mem hpr
        have hip : i < d.premises.length := by
          rw [List.length_zip, hplen] at hi; omega
        have hit : i < tcs.length := by rw [← hplen]; exact hip
        have hz : (d.premises.zip tcs)[i]'hi = (d.premises[i], tcs[i]) :=
          List.getElem_zip
        rw [← hpri, hz]
        have h1 : (d.premises.map getClaim)[i]'(by simpa using hip)
            = (tcs.map Claim.term)[i]'(by simpa using hit) := by
          simp only [hmap]
        simpa using h1
      have hprems : ∀ pr ∈ (d.premises.map getCtx).zip tcs,
          Derivable ⟨pr.1, .term pr.2⟩ := by
        intro pr hpr
        rw [List.zip_map_left] at hpr
        obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hpr
        have hqmem : q.1 ∈ d.premises := (List.of_mem_zip hq).1
        have hD := hprem q.1 hqmem
        rw [conclusion_eta, hclaims q hq] at hD
        rw [← hqe]; exact hD
      have hne : tcs ≠ [] := by
        have : 0 < tcs.length := by
          rw [← hplen]; exact Nat.lt_of_lt_of_le Nat.zero_lt_one
            (of_decide_eq_true hlen1)
        exact List.ne_nil_of_length_pos this
      rw [beq_iff_eq] at hmode hprov hn
      have hcv : conc.value.val
          = (((tcs.filter (·.output == conc.output)).length : ℚ)
              / (tcs.length : ℚ)) := by
        have := beq_iff_eq.mp (of_decide_eq_true hval)
        rwa [hplen] at this
      have hctxs' : (d.premises.map getCtx).all
          (fun Δ => contextEqSet Δ (getCtx d)) = true := by
        simpa [List.all_map, Function.comp] using hctxs
      have hconc_eq : conc = ⟨.frequency, conc.term, tcs.length,
          conc.output, conc.value, (tcs.map (·.prov)).foldl (· ∪ ·) ∅⟩ :=
        TermClaim.ext hmode rfl (by rw [hn, hplen]) rfl rfl hprov
      rw [conclusion_eta, hcc, hconc_eq]
      exact .sampling (getCtx d) (d.premises.map getCtx) tcs conc.term
        conc.output conc.value hwf hne (by simp [hplen]) hprems hctxs'
        hexp hterm hdisj hcv⟩
  | _ => throw "sampling: expected a term claim"

def checkSampling (d : Derivation) : CheckM Unit := do
  let _ ← checkSamplingC d

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
