import TPTND.Spec
import TPTND.Semantics
import TPTND.Derivable

/-! # Semantic soundness of the expected fragment

The measure-theoretic reading of an expected-mode judgement
`Γ ⊢ x : α_a` is: in every model satisfying the assumptions `Γ`, the
probability of `x` producing `α` is exactly `a`.  This file proves that
reading for every derivable judgement of that shape — by one induction
over `Derivable`.

The fragment is delimited semantically, not by rule name:

* **frequency-mode** conclusions record observations; their guarantee is
  statistical, not exact, and lives in `Operational/TrustGuarantee` and
  `Operational/Bridge` (`trust_coverage`, `honest_run_certified`);
* **compound-term** conclusions (pairs, projections, abstractions) have
  no atomic event to evaluate — the induction passes through them
  vacuously;
* the **Bayesian identity** conclusions (`identity_model`, `E-P`) carry
  subjective weights, deliberately not pinned to the model.

What remains — `expectation`, `ETex`, the sum rules at expected mode,
the weakenings and `Contraction` — is exactly the fragment whose
conclusions claim a model probability, and for it the claim is true. -/

namespace TPTND

open MeasureTheory

-- ============================================================================
-- Bridging helpers
-- ============================================================================

/-- The checker's rational membership test implies real satisfaction. -/
theorem Constraint.sat_of_contains {c : Constraint} {q : Prob}
    (h : c.contains q = true) : c.sat ((q.val : ℚ) : ℝ) := by
  cases c with
  | exact v =>
      simp only [Constraint.contains, decide_eq_true_eq] at h
      simp only [Constraint.sat]
      exact_mod_cast h.symm
  | interval lo hi =>
      simp only [Constraint.contains, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  | outsideInterval lo hi =>
      simp only [Constraint.contains, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (by exact_mod_cast h)
  | unknown => trivial

/-- Set-equal contexts satisfy together. -/
theorem Model.satCtx_of_eqSet (M : Model) {Γ1 Γ2 : Context}
    (h : contextEqSet Γ1 Γ2 = true) (hsat : M.satCtx Γ2) : M.satCtx Γ1 := by
  intro e he
  rw [contextEqSet, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  exact hsat e (of_decide_eq_true (h.1 e he))

/-- A component of a merge is satisfied whenever a set-equal copy of the
    merge is. -/
theorem Model.satCtx_of_mergePart (M : Model) {Γ Δ ctx : Context}
    (hmem : ∀ e ∈ Γ, e ∈ Γ ∨ e ∈ Δ)
    (hctx : contextEqSet ctx (mergeContexts [Γ, Δ]) = true)
    (hsat : M.satCtx ctx) : M.satCtx Γ := by
  intro e he
  have hflat : e ∈ ([Γ, Δ] : List Context).flatten := by
    simp only [List.flatten, List.mem_append]
    rcases hmem e he with h | h
    · exact List.mem_append.mpr (Or.inl h)
    · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl h)))
  have hmerge : e ∈ mergeContexts [Γ, Δ] := by
    rw [mergeContexts]
    exact List.mem_eraseDups.mpr hflat
  rw [contextEqSet, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
    at hctx
  exact hsat e (of_decide_eq_true (hctx.2 e hmerge))

theorem probAdd_val {a b s : Prob} (h : probAdd a b = some s) :
    s.val = a.val + b.val := by
  unfold probAdd at h
  split_ifs at h
  injection h with h'
  rw [← h']

theorem probSub_val {a b d : Prob} (h : probSub a b = some d) :
    d.val = a.val - b.val := by
  unfold probSub at h
  split_ifs at h
  injection h with h'
  rw [← h']

-- ============================================================================
-- The soundness theorem
-- ============================================================================

/-- **Semantic soundness of the expected fragment.**  In any model with
    disjoint atoms that satisfies the context, a derivable expected-mode
    judgement about an atomic term claims the model's own probability. -/
theorem Model.sound_expected (M : Model) (hM : ∀ y, M.AtomsDisjoint y)
    {s : Sequent} (h : Derivable s) :
    ∀ (tc : TermClaim) (xn : String),
      s.claim = Claim.term tc → tc.mode = TermMode.expected →
      tc.term = Term.atom xn → M.satCtx s.context →
      M.prob xn tc.output = ((tc.value.val : ℚ) : ℝ) := by
  induction h
  all_goals intro tc xn hclaim hmode hterm hsat
  all_goals dsimp only at hclaim
  all_goals try (exact Claim.noConfusion hclaim)
  all_goals try (injection hclaim with hinj; subst hinj; simp_all; done)
  case expectation Γ tc0 e a hwf hm0 hprov hn hatom hsupp hexact hval =>
    injection hclaim with hinj; subst hinj
    rw [hterm] at hsupp
    simp only [supportEntries] at hsupp
    have hemem : e ∈ Γ.filter (fun e' =>
        e'.name == xn && e'.output == tc0.output) := by
      rw [hsupp]; exact List.mem_singleton_self e
    obtain ⟨heΓ, hpred⟩ := List.mem_filter.mp hemem
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hpred
    have hsatE := hsat e heΓ
    rw [Model.satEntry, hexact] at hsatE
    simp only [Constraint.sat] at hsatE
    rw [hpred.1, hpred.2] at hsatE
    rw [hsatE]
    exact_mod_cast hval.symm
  case eTex Γp ctx t n α f p interval σ eOld eNew hwf hp hold hnew hname
      houts holdα hnewc hnonexact hcont hdesig ihp =>
    injection hclaim with hinj; subst hinj
    dsimp only at hterm hmode ⊢
    have hnewmem : eNew ∈ ctx := by
      have : eNew ∈ ctx.filter (· ∉ Γp) := by
        rw [hnew]; exact List.mem_singleton_self eNew
      exact List.mem_of_mem_filter this
    have hsatE := hsat eNew hnewmem
    rw [Model.satEntry, hnewc] at hsatE
    simp only [Constraint.sat] at hsatE
    have hxn : eNew.name = xn := by
      rw [hdesig] at hterm
      injection hterm
    have hout : eNew.output = α := by rw [← houts]; exact holdα
    rw [hxn, hout] at hsatE
    exact hsatE
  case iPlus Γ Γ1 Γ2 tc1 tc2 sm hwf h1 h2 hc1 hc2 hmode0 hsamp hprov0
      hterm0 hdisj hadd ih1 ih2 =>
    injection hclaim with hinj; subst hinj
    dsimp only at hmode hterm ⊢
    have hp1 := ih1 tc1 xn rfl hmode hterm (M.satCtx_of_eqSet hc1 hsat)
    have hp2 := ih2 tc2 xn rfl (hmode0.symm.trans hmode)
      (hterm0.symm.trans hterm) (M.satCtx_of_eqSet hc2 hsat)
    have hsum := M.sound_IPlus xn (hM xn) hdisj
    have hval := probAdd_val hadd
    rw [hsum, hp1, hp2]
    push_cast [hval]
    ring
  case ePlusL Γ Γ1 Γ2 tc1 tc2 γ diff hwf h1 h2 hc1 hc2 hmode0 hsamp hprov0
      hterm0 hdisj hsum0 hsub ih1 ih2 =>
    injection hclaim with hinj; subst hinj
    dsimp only at hmode hterm ⊢
    have hp1 := ih1 tc1 xn rfl hmode hterm (M.satCtx_of_eqSet hc1 hsat)
    have hp2 := ih2 tc2 xn rfl (hmode0.symm.trans hmode)
      (hterm0.symm.trans hterm) (M.satCtx_of_eqSet hc2 hsat)
    have hsum := M.sound_IPlus xn (hM xn) hdisj
    rw [hsum0] at hp1
    have hval := probSub_val hsub
    rw [hsum] at hp1
    push_cast [hval]
    linarith [hp1, hp2]
  case ePlusR Γ Γ1 Γ2 tc1 tc2 γ diff hwf h1 h2 hc1 hc2 hmode0 hsamp hprov0
      hterm0 hdisj hsum0 hsub ih1 ih2 =>
    injection hclaim with hinj; subst hinj
    dsimp only at hmode hterm ⊢
    have hp1 := ih1 tc1 xn rfl hmode hterm (M.satCtx_of_eqSet hc1 hsat)
    have hp2 := ih2 tc2 xn rfl (hmode0.symm.trans hmode)
      (hterm0.symm.trans hterm) (M.satCtx_of_eqSet hc2 hsat)
    -- symmetric recovery: γ = (γ + β) − β
    have hsum := M.sound_IPlus xn (hM xn) hdisj
    rw [hsum0] at hp1
    have hval := probSub_val hsub
    rw [hsum] at hp1
    push_cast [hval]
    linarith [hp1, hp2]
  case weakeningS Γ Δ ctx J K hwf hJ hK hindep hctx ihJ ihK =>
    have hsatΓ : M.satCtx Γ :=
      M.satCtx_of_mergePart (fun e he => Or.inl he) hctx hsat
    exact ihJ tc xn hclaim hmode hterm hsatΓ
  case weakeningD Γ ctx Δ J hwf hJ hindep hΔ hctx ihJ =>
    have hsatΓ : M.satCtx Γ :=
      M.satCtx_of_mergePart (fun e he => Or.inl he) hctx hsat
    exact ihJ tc xn hclaim hmode hterm hsatΓ
  case contraction Γp ctx J k repl a hwf hp hgroup hrest hrepl hexact hinf
      hin ihp =>
    have hreplmem : repl ∈ ctx := by
      have : repl ∈ ctx.filter (fun e => (e.name, e.output) == k) := by
        rw [hrepl]; exact List.mem_singleton_self repl
      exact List.mem_of_mem_filter this
    have hreplkey : ((repl.name, repl.output) == k) = true := by
      have : repl ∈ ctx.filter (fun e => (e.name, e.output) == k) := by
        rw [hrepl]; exact List.mem_singleton_self repl
      exact (List.mem_filter.mp this).2
    have hsatRepl := hsat repl hreplmem
    rw [Model.satEntry, hexact] at hsatRepl
    simp only [Constraint.sat] at hsatRepl
    have hsatΓp : M.satCtx Γp := by
      intro e he
      by_cases hkey : ((e.name, e.output) == k) = true
      · -- inside the contracted group: the model value is `a`, and `a`
        -- lies in the entry's constraint
        have hkeys : e.name = repl.name ∧ e.output = repl.output := by
          rw [beq_iff_eq] at hkey hreplkey
          have hpair : (e.name, e.output) = (repl.name, repl.output) :=
            hkey.trans hreplkey.symm
          exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
        have hgrp : e ∈ Γp.filter (fun e' => (e'.name, e'.output) == k) :=
          List.mem_filter.mpr ⟨he, hkey⟩
        have hcont : e.constraint.contains a = true := by
          rw [List.all_eq_true] at hin
          exact hin e hgrp
        rw [Model.satEntry, hkeys.1, hkeys.2, hsatRepl]
        exact Constraint.sat_of_contains hcont
      · -- outside the group: carried over unchanged
        have hef : e ∈ Γp.filter (fun e' => (e'.name, e'.output) != k) :=
          List.mem_filter.mpr ⟨he, by
            simp only [bne_iff_ne, ne_eq]
            intro hc
            exact hkey (by rw [hc]; exact beq_self_eq_true k)⟩
        rw [contextEqSet, Bool.and_eq_true, List.all_eq_true,
            List.all_eq_true] at hrest
        have := of_decide_eq_true (hrest.1 e hef)
        exact hsat e (List.mem_of_mem_filter this)
    exact ihp tc xn hclaim hmode hterm hsatΓp

/-- **Checker-level corollary.**  Whatever the checker accepts as an
    expected-mode judgement about an atomic term states the model's own
    probability, in every satisfying model with disjoint atoms. -/
theorem Model.checker_sound_expected (M : Model)
    (hM : ∀ y, M.AtomsDisjoint y)
    (d : Derivation) (hacc : checkDerivation d = Except.ok ())
    (tc : TermClaim) (xn : String)
    (hclaim : getClaim d = Claim.term tc) (hmode : tc.mode = .expected)
    (hterm : tc.term = .atom xn) (hsat : M.satCtx (getCtx d)) :
    M.prob xn tc.output = ((tc.value.val : ℚ) : ℝ) :=
  M.sound_expected hM (checker_sound d hacc) tc xn hclaim hmode hterm hsat

end TPTND