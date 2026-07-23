import TPTND.Derivable
import TPTND.Operational.Reduction
import TPTND.Operational.Convergence

/-! # The operational→static bridge

The ↦ layer (`Reduces`) deliberately carries no provenance: a run claim
`tₙ : α_f` records what happened, not how the evidence is labelled.  The
static rules, by contrast, are provenance-aware — `sampling` demands
pairwise-disjoint runs and concludes their union.  This file supplies the
missing piece: a mapping from a list of single-run claims to a static
derivation tree that *assigns* provenance positionally — the i-th run
receives the token `ρ i` for an injective naming scheme `ρ` — and a proof
that `checkDerivation` **accepts** the resulting certificate.

Position-indexed tokens make the disjointness side conditions provable
where they belong: distinct positions have distinct tokens, so the
singleton provenances are pairwise disjoint by construction.

Together with `checker_sound` this closes the loop: real runs (a
`Model.runList` history) map to a certificate the checker accepts, whose
conclusion is therefore `Derivable`, and whose frequency is exactly the
run space's observed frequency (`Model.sampling_adequate`) — which
converges almost surely to the model probability (`observedFreq_limit`).
-/

namespace TPTND

/-- The static claim assigned to the i-th run: a single-sample frequency
    judgement carrying the positional token `ρ i`. -/
def runTC (x : String) (ρ : ℕ → String) (out : Output) (i : ℕ) : TermClaim :=
  ⟨.frequency, .atom x, 1, out, Prob.one, {ρ i}⟩

/-- The experiment leaf for the i-th run. -/
def expNode (Γ : Context) (x : String) (ρ : ℕ → String) (out : Output)
    (i : ℕ) : Derivation :=
  .node "experiment" [] ⟨Γ, .term (runTC x ρ out i)⟩ false

/-- Experiment leaves for a run list, indexed from `i`. -/
def expNodes (Γ : Context) (x : String) (ρ : ℕ → String) :
    List RunClaim → ℕ → List Derivation
  | [], _ => []
  | r :: rs, i => expNode Γ x ρ r.output i :: expNodes Γ x ρ rs (i + 1)

/-- The claims of `expNodes`, kept in step with it. -/
def expClaims (x : String) (ρ : ℕ → String) :
    List RunClaim → ℕ → List TermClaim
  | [], _ => []
  | r :: rs, i => runTC x ρ r.output i :: expClaims x ρ rs (i + 1)

/-- The observed relative frequency of `α` in a run list, as a `Prob`. -/
def obsFreq (runs : List RunClaim) (α : Output) : Prob :=
  ⟨((runs.filter (·.output == α)).length : ℚ) / (runs.length : ℚ),
   by positivity,
   by
     rcases Nat.eq_zero_or_pos runs.length with h | h
     · simp [h]
     · rw [div_le_one (by exact_mod_cast h)]
       exact_mod_cast List.length_filter_le _ _⟩

/-- The union of the assigned tokens, in the shape the checker computes. -/
def batchProv (x : String) (ρ : ℕ → String) (runs : List RunClaim) :
    Provenance :=
  ((expClaims x ρ runs 0).map (·.prov)).foldl (· ∪ ·) ∅

/-- The conclusion claim of a certified batch. -/
def batchTC (x : String) (α : Output) (ρ : ℕ → String)
    (runs : List RunClaim) : TermClaim :=
  ⟨.frequency, .atom x, runs.length, α, obsFreq runs α, batchProv x ρ runs⟩

/-- The full certificate: the runs as experiment leaves, collected by
    `sampling`. -/
def batchNode (Γ : Context) (x : String) (α : Output) (ρ : ℕ → String)
    (runs : List RunClaim) : Derivation :=
  .node "sampling" (expNodes Γ x ρ runs 0) ⟨Γ, .term (batchTC x α ρ runs)⟩
    false

-- ============================================================================
-- Structural facts about the mapping (all by the same induction)
-- ============================================================================

theorem expNodes_length (Γ : Context) (x : String) (ρ : ℕ → String) :
    ∀ (rs : List RunClaim) (i : ℕ), (expNodes Γ x ρ rs i).length = rs.length
  | [], _ => rfl
  | _ :: rs, i => by simp [expNodes, expNodes_length Γ x ρ rs (i + 1)]

theorem expClaims_length (x : String) (ρ : ℕ → String) :
    ∀ (rs : List RunClaim) (i : ℕ), (expClaims x ρ rs i).length = rs.length
  | [], _ => rfl
  | _ :: rs, i => by simp [expClaims, expClaims_length x ρ rs (i + 1)]

theorem expNodes_map_getClaim (Γ : Context) (x : String) (ρ : ℕ → String) :
    ∀ (rs : List RunClaim) (i : ℕ),
      (expNodes Γ x ρ rs i).map getClaim
        = (expClaims x ρ rs i).map Claim.term
  | [], _ => rfl
  | _ :: rs, i => by
      simp [expNodes, expClaims, expNode, getClaim, Derivation.conclusion,
            expNodes_map_getClaim Γ x ρ rs (i + 1)]

theorem expNodes_ctx (Γ : Context) (x : String) (ρ : ℕ → String) :
    ∀ (rs : List RunClaim) (i : ℕ),
      ∀ p ∈ expNodes Γ x ρ rs i, getCtx p = Γ
  | _ :: rs, i, p, hp => by
      rcases List.mem_cons.mp hp with h | h
      · subst h; rfl
      · exact expNodes_ctx Γ x ρ rs (i + 1) p h

/-- Every claim in the batch has the experiment shape, the shared term, and
    a token indexed at or above the starting index. -/
theorem expClaims_shape (x : String) (ρ : ℕ → String) :
    ∀ (rs : List RunClaim) (i : ℕ),
      ∀ tc ∈ expClaims x ρ rs i,
        tc.mode = .frequency ∧ tc.samples = 1 ∧ tc.term = .atom x ∧
        tc.value = Prob.one ∧ ∃ j, i ≤ j ∧ tc.prov = {ρ j}
  | _ :: rs, i, tc, htc => by
      rcases List.mem_cons.mp htc with h | h
      · subst h
        exact ⟨rfl, rfl, rfl, rfl, i, le_refl i, rfl⟩
      · obtain ⟨h1, h2, h3, h4, j, hj, h5⟩ :=
          expClaims_shape x ρ rs (i + 1) tc h
        exact ⟨h1, h2, h3, h4, j, by omega, h5⟩

/-- The match count is preserved by the mapping. -/
theorem expClaims_count (x : String) (ρ : ℕ → String) (α : Output) :
    ∀ (rs : List RunClaim) (i : ℕ),
      ((expClaims x ρ rs i).filter (·.output == α)).length
        = (rs.filter (·.output == α)).length
  | [], _ => rfl
  | r :: rs, i => by
      by_cases h : r.output == α
      · simp [expClaims, runTC, h, expClaims_count x ρ α rs (i + 1)]
      · simp only [Bool.not_eq_true] at h
        simp [expClaims, runTC, h, expClaims_count x ρ α rs (i + 1)]

/-- Distinct positions receive disjoint tokens. -/
theorem expClaims_disjoint (x : String) (ρ : ℕ → String)
    (hinj : Function.Injective ρ) :
    ∀ (rs : List RunClaim) (i : ℕ),
      Provenance.pairwiseDisjoint
        ((expClaims x ρ rs i).map (·.prov)) = true
  | [], _ => rfl
  | r :: rs, i => by
      simp only [expClaims, runTC, List.map_cons,
                 Provenance.pairwiseDisjoint, Bool.and_eq_true]
      refine ⟨?_, expClaims_disjoint x ρ hinj rs (i + 1)⟩
      rw [List.all_eq_true]
      intro σ hσ
      obtain ⟨tc, htc, rfl⟩ := List.mem_map.mp hσ
      obtain ⟨_, _, _, _, j, hj, hprov⟩ :=
        expClaims_shape x ρ rs (i + 1) tc htc
      rw [hprov]
      have hne : ρ i ≠ ρ j := fun hc => by
        have := hinj hc; omega
      simp only [Provenance.disjoint, decide_eq_true_eq]
      ext c; simp; rintro rfl; exact hne

-- ============================================================================
-- Symbolic evaluation helpers
-- ============================================================================

/-- A passed forward-mode gate. -/
theorem ensure'_ok (c : Bool) (m : String) (h : c = true) :
    ensure' c m = Except.ok ⟨h⟩ := by
  subst h; rfl

/-- Compose `bind` with a known-ok head. -/
theorem bind_ok_ex {A B : Type} {m : CheckM A} {f : A → CheckM B}
    (a : A) (hm : m = Except.ok a) (hf : ∃ b, f a = Except.ok b) :
    ∃ b, (m >>= f) = Except.ok b := by
  obtain ⟨b, hb⟩ := hf
  exact ⟨b, by rw [hm]; exact hb⟩

theorem contextEqSet_refl (Γ : Context) : contextEqSet Γ Γ = true := by
  simp [contextEqSet, List.all_eq_true]

/-- A premise list of accepted derivations is accepted. -/
theorem checkPremisesList_ok :
    ∀ (ps : List Derivation),
      (∀ p ∈ ps, checkDerivation p = Except.ok ()) →
      checkPremisesList ps = Except.ok ()
  | [], _ => rfl
  | q :: qs, h => by
      have hq := h q (List.mem_cons_self ..)
      have hqs := checkPremisesList_ok qs (fun p hp => h p (List.mem_cons_of_mem _ hp))
      unfold checkPremisesList
      rw [hq]
      exact hqs

/-- An accepted node with accepted premises is an accepted derivation. -/
theorem checkDerivation_node_ok (r : String) (ps : List Derivation)
    (concl : Sequent) (w : Bool)
    (hwf : contextWF concl.context = true)
    (hnode : checkNode (.node r ps concl w) = Except.ok ())
    (hps : checkPremisesList ps = Except.ok ()) :
    checkDerivation (.node r ps concl w) = Except.ok () := by
  unfold checkDerivation
  rw [show getCtx (Derivation.node r ps concl w) = concl.context from rfl,
      (ensure_eq_ok _ _).mpr hwf, hnode]
  exact hps

-- ============================================================================
-- Acceptance of the experiment leaves
-- ============================================================================

theorem expNode_accepted (Γ : Context) (x : String) (ρ : ℕ → String)
    (out : Output) (i : ℕ)
    (hwf : contextWF Γ = true)
    (hsupp : (supportEntries Γ (.atom x) out).length = 1) :
    checkDerivation (expNode Γ x ρ out i) = Except.ok () := by
  refine checkDerivation_node_ok _ _ _ _ hwf ?_ rfl
  rw [show checkNode (Derivation.node "experiment" []
          ⟨Γ, .term (runTC x ρ out i)⟩ false)
        = checkExperiment (Derivation.node "experiment" []
          ⟨Γ, .term (runTC x ρ out i)⟩ false) from rfl]
  simp [checkExperiment, expectPremises, getClaim, Derivation.premises,
        Derivation.conclusion, runTC, ensure, getCtx, hsupp, Prob.one,
        isAtomicTerm]
  rfl

-- ============================================================================
-- Acceptance of the sampling node
-- ============================================================================

theorem ptc_expNodes (Γ : Context) (x : String) (ρ : ℕ → String) :
    ∀ (rs : List RunClaim) (i : ℕ),
      premiseTermClaimsC (expNodes Γ x ρ rs i) "sampling"
        = Except.ok ⟨expClaims x ρ rs i, expNodes_map_getClaim Γ x ρ rs i⟩
  | [], _ => rfl
  | r :: rs, i => by
      have ih := ptc_expNodes Γ x ρ rs (i + 1)
      simp only [expNodes, expClaims, premiseTermClaimsC, getClaim,
                 Derivation.conclusion, expNode, ih]
      rfl

theorem expNodes_ctxAll (Γ : Context) (x : String) (ρ : ℕ → String)
    (rs : List RunClaim) (i : ℕ) :
    (expNodes Γ x ρ rs i).all (fun p => contextEqSet (getCtx p) Γ) = true := by
  rw [List.all_eq_true]
  intro p hp
  rw [expNodes_ctx Γ x ρ rs i p hp]
  exact contextEqSet_refl Γ

theorem expClaims_expAll (x : String) (ρ : ℕ → String)
    (rs : List RunClaim) (i : ℕ) :
    (expClaims x ρ rs i).all (fun tc =>
      tc.prov.card == 1 && tc.samples == 1 && tc.mode == .frequency) = true := by
  rw [List.all_eq_true]
  intro tc htc
  obtain ⟨h1, h2, _, _, j, _, h5⟩ := expClaims_shape x ρ rs i tc htc
  simp [h1, h2, h5]

theorem expClaims_termAll (x : String) (ρ : ℕ → String)
    (rs : List RunClaim) (i : ℕ) :
    (expClaims x ρ rs i).all (fun tc => tc.term == Term.atom x) = true := by
  rw [List.all_eq_true]
  intro tc htc
  obtain ⟨_, _, h3, _, _, _, _⟩ := expClaims_shape x ρ rs i tc htc
  simp [h3]

theorem expNodes_mem (Γ : Context) (x : String) (ρ : ℕ → String) :
    ∀ (rs : List RunClaim) (i : ℕ) (p : Derivation),
      p ∈ expNodes Γ x ρ rs i →
      ∃ r ∈ rs, ∃ j, p = expNode Γ x ρ r.output j
  | r :: rs, i, p, hp => by
      rcases List.mem_cons.mp hp with h | h
      · exact ⟨r, by simp, i, h⟩
      · obtain ⟨r', hr', j, hj⟩ := expNodes_mem Γ x ρ rs (i + 1) p h
        exact ⟨r', by simp [hr'], j, hj⟩

/-- **Acceptance.**  `checkDerivation` accepts the batch certificate built
    from any nonempty run list, under any injective token scheme and any
    well-formed context supporting each observed output uniquely. -/
theorem batchNode_accepted (Γ : Context) (x : String) (α : Output)
    (ρ : ℕ → String) (runs : List RunClaim)
    (hwf : contextWF Γ = true)
    (hne : runs ≠ [])
    (hinj : Function.Injective ρ)
    (hsupp : ∀ r ∈ runs, (supportEntries Γ (.atom x) r.output).length = 1) :
    checkDerivation (batchNode Γ x α ρ runs) = Except.ok () := by
  have hlen1 : (decide ((expNodes Γ x ρ runs 0).length ≥ 1)) = true := by
    rw [expNodes_length]
    exact decide_eq_true (List.length_pos_of_ne_nil hne)
  have hsamp : (runs.length == (expNodes Γ x ρ runs 0).length) = true := by
    rw [expNodes_length]
    exact beq_self_eq_true _
  have hval : (decide ((obsFreq runs α).val ==
      (((expClaims x ρ runs 0).filter (·.output == α)).length : ℚ)
        / ((expNodes Γ x ρ runs 0).length : ℚ))) = true := by
    rw [expClaims_count, expNodes_length]
    simp [obsFreq]
  have hC : ∃ w, checkSamplingC (Derivation.node "sampling"
      (expNodes Γ x ρ runs 0) ⟨Γ, .term (batchTC x α ρ runs)⟩ false)
      = Except.ok w := by
    unfold checkSamplingC
    refine bind_ok_ex _ (ensure'_ok _ _ hlen1) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ rfl) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ (expNodes_ctxAll Γ x ρ runs 0)) ?_
    refine bind_ok_ex _ (ptc_expNodes Γ x ρ runs 0) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ (expClaims_expAll x ρ runs 0)) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ (expClaims_termAll x ρ runs 0)) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ (expClaims_disjoint x ρ hinj runs 0)) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ (beq_self_eq_true _)) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ hsamp) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ hval) ?_
    exact ⟨_, rfl⟩
  refine checkDerivation_node_ok _ _ _ _ hwf ?_ ?_
  · rw [show checkNode (Derivation.node "sampling" (expNodes Γ x ρ runs 0)
          ⟨Γ, .term (batchTC x α ρ runs)⟩ false)
        = checkSampling (Derivation.node "sampling" (expNodes Γ x ρ runs 0)
          ⟨Γ, .term (batchTC x α ρ runs)⟩ false) from rfl]
    obtain ⟨w, hw⟩ := hC
    unfold checkSampling
    rw [hw]
    rfl
  · refine checkPremisesList_ok _ ?_
    intro p hp
    obtain ⟨r, hr, j, rfl⟩ := expNodes_mem Γ x ρ runs 0 p hp
    exact expNode_accepted Γ x ρ r.output j hwf (hsupp r hr)

-- ============================================================================
-- From acceptance to derivability
-- ============================================================================

/-- Whatever the mapping certifies is derivable in the calculus. -/
theorem batchNode_derivable (Γ : Context) (x : String) (α : Output)
    (ρ : ℕ → String) (runs : List RunClaim)
    (hwf : contextWF Γ = true)
    (hne : runs ≠ [])
    (hinj : Function.Injective ρ)
    (hsupp : ∀ r ∈ runs, (supportEntries Γ (.atom x) r.output).length = 1) :
    Derivable ⟨Γ, .term (batchTC x α ρ runs)⟩ :=
  checker_sound _ (batchNode_accepted Γ x α ρ runs hwf hne hinj hsupp)

-- ============================================================================
-- Instantiation: real runs certify
-- ============================================================================

/-- The canonical observation context for a process `x` that may produce
    `α` or fail to: both outcomes assumed opaque. -/
def obsContext (x : String) (α : Output) : Context :=
  [⟨x, {x}, α, .unknown⟩, ⟨x, {x}, .neg α, .unknown⟩]

theorem obsContext_wf (x : String) (α : Output) :
    contextWF (obsContext x α) = true := by
  have hg : groupMass
      [⟨x, {x}, α, .unknown⟩, ⟨x, {x}, Output.neg α, .unknown⟩]
      = fun _ => 0 := by
    funext β
    by_cases h1 : (α == β) <;> by_cases h2 : (Output.neg α == β) <;>
      simp [groupMass, List.filter, h1, h2, exactMass, intervalLower]
  simp [contextWF, obsContext, entryWF, constraintWF, variableNames,
        variableMass, hg]

theorem obsContext_supports (x : String) (α : Output) :
    (supportEntries (obsContext x α) (.atom x) α).length = 1 ∧
    (supportEntries (obsContext x α) (.atom x) (.neg α)).length = 1 := by
  have h1 : (Output.neg α == α) = false :=
    beq_eq_false_iff_ne.mpr (Output.neg_ne_self α)
  have h2 : (α == Output.neg α) = false :=
    beq_eq_false_iff_ne.mpr (Output.neg_ne_self α).symm
  constructor <;> simp [supportEntries, obsContext, List.filter, h1, h2]

/-- Every run in a history is uniquely supported by the canonical context. -/
theorem runList_supported (M : Model) (x : String) (α : Output)
    (ω : ℕ → M.Ω) (n : ℕ) :
    ∀ r ∈ M.runList x α ω n,
      (supportEntries (obsContext x α) (.atom x) r.output).length = 1 := by
  intro r hr
  simp only [Model.runList, List.mem_map] at hr
  obtain ⟨i, _, rfl⟩ := hr
  by_cases h : ω i ∈ M.hitSet x α
  · simpa [h] using (obsContext_supports x α).1
  · simpa [h] using (obsContext_supports x α).2

/-- **The bridge, end to end.**  The history of `n` real runs of `x`
    certifies: the checker accepts the batch, its conclusion is derivable,
    and the certified frequency is the run space's observed frequency —
    which converges almost surely to the model probability
    (`Model.observedFreq_limit`). -/
theorem Model.runList_certified (M : Model) (x : String) (α : Output)
    (ω : ℕ → M.Ω) (n : ℕ) (hn : 0 < n) (ρ : ℕ → String)
    (hinj : Function.Injective ρ) :
    checkDerivation (batchNode (obsContext x α) x α ρ (M.runList x α ω n))
      = Except.ok () ∧
    Derivable ⟨obsContext x α, .term (batchTC x α ρ (M.runList x α ω n))⟩ ∧
    (((batchTC x α ρ (M.runList x α ω n)).value.val : ℝ))
      = M.observedFreq x α n ω := by
  have hne : M.runList x α ω n ≠ [] := by
    intro hcon
    have := M.runList_length x α ω n
    rw [hcon] at this
    simp at this
    omega
  have hacc := batchNode_accepted (obsContext x α) x α ρ (M.runList x α ω n)
    (obsContext_wf x α) hne hinj (runList_supported M x α ω n)
  refine ⟨hacc, checker_sound _ hacc, ?_⟩
  have hlen := M.runList_length x α ω n
  have hval : (batchTC x α ρ (M.runList x α ω n)).value.val
      = (((M.runList x α ω n).filter (·.output == α)).length : ℚ)
        / (((M.runList x α ω n).length : ℚ)) := rfl
  rw [hval]
  simp only [hlen]
  push_cast
  exact M.sampling_adequate x α ω n

end TPTND