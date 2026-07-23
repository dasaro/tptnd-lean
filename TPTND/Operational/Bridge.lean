import TPTND.Derivable
import TPTND.Operational.Reduction
import TPTND.Operational.Convergence
import TPTND.Operational.TrustGuarantee

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

Beyond single batches, the trace steps of the ↦ layer are covered:

* `update` — two batches drawing on disjoint token ranges of one naming
  scheme pool into an accepted `update` node whose value is the observed
  frequency of the concatenated history (`updateNode_accepted`);
* `sumIntro` — two counts of one history, under the SAME tokens, join
  into an accepted sum node — sharing the history is exactly the
  shared-provenance side condition (`sumNode_accepted`);
* `pairIntro` — the realised joint frequency of a paired draw is a
  datum, not a product, so the frequency layer has no introduction for
  it; the certifiable counterpart lives at the expected layer, where an
  explicit independence witness multiplies the coordinates'
  expectations (`pairNode_accepted`).
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
def batchProv (x : String) (ρ : ℕ → String) (runs : List RunClaim)
    (i : ℕ) : Provenance :=
  ((expClaims x ρ runs i).map (·.prov)).foldl (· ∪ ·) ∅

/-- The conclusion claim of a certified batch. -/
def batchTC (x : String) (α : Output) (ρ : ℕ → String)
    (runs : List RunClaim) (i : ℕ) : TermClaim :=
  ⟨.frequency, .atom x, runs.length, α, obsFreq runs α, batchProv x ρ runs i⟩

/-- The full certificate: the runs as experiment leaves, collected by
    `sampling`, with tokens indexed from `i` (so that several batches can
    draw from disjoint token ranges of one naming scheme). -/
def batchNode (Γ : Context) (x : String) (α : Output) (ρ : ℕ → String)
    (runs : List RunClaim) (i : ℕ) : Derivation :=
  .node "sampling" (expNodes Γ x ρ runs i) ⟨Γ, .term (batchTC x α ρ runs i)⟩
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
        tc.value = Prob.one ∧
        ∃ j, i ≤ j ∧ j < i + rs.length ∧ tc.prov = {ρ j}
  | _ :: rs, i, tc, htc => by
      rcases List.mem_cons.mp htc with h | h
      · subst h
        exact ⟨rfl, rfl, rfl, rfl, i, le_refl i, by simp, rfl⟩
      · obtain ⟨h1, h2, h3, h4, j, hj, hju, h5⟩ :=
          expClaims_shape x ρ rs (i + 1) tc h
        exact ⟨h1, h2, h3, h4, j, by omega, by simp at hju ⊢; omega, h5⟩

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
      obtain ⟨_, _, _, _, j, hj, _, hprov⟩ :=
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
  obtain ⟨h1, h2, _, _, j, _, _, h5⟩ := expClaims_shape x ρ rs i tc htc
  simp [h1, h2, h5]

theorem expClaims_termAll (x : String) (ρ : ℕ → String)
    (rs : List RunClaim) (i : ℕ) :
    (expClaims x ρ rs i).all (fun tc => tc.term == Term.atom x) = true := by
  rw [List.all_eq_true]
  intro tc htc
  obtain ⟨_, _, h3, _, _, _, _, _⟩ := expClaims_shape x ρ rs i tc htc
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
    (ρ : ℕ → String) (runs : List RunClaim) (i : ℕ)
    (hwf : contextWF Γ = true)
    (hne : runs ≠ [])
    (hinj : Function.Injective ρ)
    (hsupp : ∀ r ∈ runs, (supportEntries Γ (.atom x) r.output).length = 1) :
    checkDerivation (batchNode Γ x α ρ runs i) = Except.ok () := by
  have hlen1 : (decide ((expNodes Γ x ρ runs i).length ≥ 1)) = true := by
    rw [expNodes_length]
    exact decide_eq_true (List.length_pos_of_ne_nil hne)
  have hsamp : (runs.length == (expNodes Γ x ρ runs i).length) = true := by
    rw [expNodes_length]
    exact beq_self_eq_true _
  have hval : (decide ((obsFreq runs α).val ==
      (((expClaims x ρ runs i).filter (·.output == α)).length : ℚ)
        / ((expNodes Γ x ρ runs i).length : ℚ))) = true := by
    rw [expClaims_count, expNodes_length]
    simp [obsFreq]
  have hC : ∃ w, checkSamplingC (Derivation.node "sampling"
      (expNodes Γ x ρ runs i) ⟨Γ, .term (batchTC x α ρ runs i)⟩ false)
      = Except.ok w := by
    unfold checkSamplingC
    refine bind_ok_ex _ (ensure'_ok _ _ hlen1) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ rfl) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ (expNodes_ctxAll Γ x ρ runs i)) ?_
    refine bind_ok_ex _ (ptc_expNodes Γ x ρ runs i) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ (expClaims_expAll x ρ runs i)) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ (expClaims_termAll x ρ runs i)) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ (expClaims_disjoint x ρ hinj runs i)) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ (beq_self_eq_true _)) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ hsamp) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ hval) ?_
    exact ⟨_, rfl⟩
  refine checkDerivation_node_ok _ _ _ _ hwf ?_ ?_
  · rw [show checkNode (Derivation.node "sampling" (expNodes Γ x ρ runs i)
          ⟨Γ, .term (batchTC x α ρ runs i)⟩ false)
        = checkSampling (Derivation.node "sampling" (expNodes Γ x ρ runs i)
          ⟨Γ, .term (batchTC x α ρ runs i)⟩ false) from rfl]
    obtain ⟨w, hw⟩ := hC
    unfold checkSampling
    rw [hw]
    rfl
  · refine checkPremisesList_ok _ ?_
    intro p hp
    obtain ⟨r, hr, j, rfl⟩ := expNodes_mem Γ x ρ runs i p hp
    exact expNode_accepted Γ x ρ r.output j hwf (hsupp r hr)

-- ============================================================================
-- From acceptance to derivability
-- ============================================================================

/-- Whatever the mapping certifies is derivable in the calculus. -/
theorem batchNode_derivable (Γ : Context) (x : String) (α : Output)
    (ρ : ℕ → String) (runs : List RunClaim) (i : ℕ)
    (hwf : contextWF Γ = true)
    (hne : runs ≠ [])
    (hinj : Function.Injective ρ)
    (hsupp : ∀ r ∈ runs, (supportEntries Γ (.atom x) r.output).length = 1) :
    Derivable ⟨Γ, .term (batchTC x α ρ runs i)⟩ :=
  checker_sound _ (batchNode_accepted Γ x α ρ runs i hwf hne hinj hsupp)

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
    checkDerivation (batchNode (obsContext x α) x α ρ (M.runList x α ω n) 0)
      = Except.ok () ∧
    Derivable ⟨obsContext x α, .term (batchTC x α ρ (M.runList x α ω n) 0)⟩ ∧
    (((batchTC x α ρ (M.runList x α ω n) 0).value.val : ℝ))
      = M.observedFreq x α n ω := by
  have hne : M.runList x α ω n ≠ [] := by
    intro hcon
    have := M.runList_length x α ω n
    rw [hcon] at this
    simp at this
    omega
  have hacc := batchNode_accepted (obsContext x α) x α ρ (M.runList x α ω n)
    0 (obsContext_wf x α) hne hinj (runList_supported M x α ω n)
  refine ⟨hacc, checker_sound _ hacc, ?_⟩
  have hlen := M.runList_length x α ω n
  have hval : (batchTC x α ρ (M.runList x α ω n) 0).value.val
      = (((M.runList x α ω n).filter (·.output == α)).length : ℚ)
        / (((M.runList x α ω n).length : ℚ)) := rfl
  rw [hval]
  simp only [hlen]
  push_cast
  exact M.sampling_adequate x α ω n

-- ============================================================================
-- Token ranges: batches over disjoint index ranges have disjoint provenance
-- ============================================================================

theorem mem_foldl_union (l : List Provenance) (acc : Provenance) (a : String) :
    a ∈ l.foldl (· ∪ ·) acc ↔ a ∈ acc ∨ ∃ σ ∈ l, a ∈ σ := by
  induction l generalizing acc with
  | nil => simp
  | cons σ rest ih =>
      simp only [List.foldl_cons, ih, Finset.mem_union, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨τ, hτ, ha⟩)
        · exact Or.inl h
        · exact Or.inr ⟨σ, Or.inl rfl, h⟩
        · exact Or.inr ⟨τ, Or.inr hτ, ha⟩
      · rintro (h | ⟨τ, (rfl | hτ), ha⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr ha)
        · exact Or.inr ⟨τ, hτ, ha⟩

/-- Every token of a batch comes from its index range. -/
theorem mem_batchProv (x : String) (ρ : ℕ → String) (runs : List RunClaim)
    (i : ℕ) (a : String) (ha : a ∈ batchProv x ρ runs i) :
    ∃ j, i ≤ j ∧ j < i + runs.length ∧ a = ρ j := by
  rw [batchProv, mem_foldl_union] at ha
  rcases ha with h | ⟨σ, hσ, haσ⟩
  · simp at h
  · obtain ⟨tc, htc, rfl⟩ := List.mem_map.mp hσ
    obtain ⟨_, _, _, _, j, hj, hju, hprov⟩ :=
      expClaims_shape x ρ runs i tc htc
    rw [hprov, Finset.mem_singleton] at haσ
    exact ⟨j, hj, by simpa using hju, haσ⟩

/-- Batches drawing on disjoint index ranges have disjoint provenance. -/
theorem batchProv_disjoint (x : String) (ρ : ℕ → String)
    (runs1 runs2 : List RunClaim) (i1 i2 : ℕ)
    (hinj : Function.Injective ρ)
    (hrange : i1 + runs1.length ≤ i2) :
    Provenance.disjoint (batchProv x ρ runs1 i1) (batchProv x ρ runs2 i2)
      = true := by
  simp only [Provenance.disjoint, decide_eq_true_eq]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro a ha
  rw [Finset.mem_inter] at ha
  obtain ⟨j1, hj1, hj1u, rfl⟩ := mem_batchProv x ρ runs1 i1 a ha.1
  obtain ⟨j2, hj2, _, he⟩ := mem_batchProv x ρ runs2 i2 (ρ j1) ha.2
  have := hinj he
  omega

-- ============================================================================
-- update: two batches pooled
-- ============================================================================

/-- The pooled claim: sample sizes add, provenances union, and the value is
    the observed frequency of the concatenated history — which is exactly
    the sample-size-weighted average the `update` rule demands. -/
def updateTC (x : String) (α : Output) (ρ : ℕ → String)
    (runs1 runs2 : List RunClaim) : TermClaim :=
  ⟨.frequency, .atom x, runs1.length + runs2.length, α,
   obsFreq (runs1 ++ runs2) α,
   batchProv x ρ runs1 0 ∪ batchProv x ρ runs2 runs1.length⟩

/-- Certificate for an `update` trace step: the two batches draw on the
    token ranges `[0, |runs1|)` and `[|runs1|, |runs1| + |runs2|)`. -/
def updateNode (Γ : Context) (x : String) (α : Output) (ρ : ℕ → String)
    (runs1 runs2 : List RunClaim) : Derivation :=
  .node "update"
    [batchNode Γ x α ρ runs1 0, batchNode Γ x α ρ runs2 runs1.length]
    ⟨Γ, .term (updateTC x α ρ runs1 runs2)⟩ false

/-- Pooling observed frequencies by sample-size weighting is observing the
    concatenated history. -/
theorem weightedFreq_obsFreq (runs1 runs2 : List RunClaim) (α : Output)
    (h1 : runs1 ≠ []) (h2 : runs2 ≠ []) :
    weightedFreq runs1.length (obsFreq runs1 α)
                 runs2.length (obsFreq runs2 α)
      = some (obsFreq (runs1 ++ runs2) α) := by
  have hn1 : (0 : ℚ) < runs1.length := by
    exact_mod_cast List.length_pos_of_ne_nil h1
  have hn2 : (0 : ℚ) < runs2.length := by
    exact_mod_cast List.length_pos_of_ne_nil h2
  have hq : ((runs1.length : ℚ) * (obsFreq runs1 α).val
      + (runs2.length : ℚ) * (obsFreq runs2 α).val)
      / (((runs1.length + runs2.length : ℕ)) : ℚ)
      = (obsFreq (runs1 ++ runs2) α).val := by
    simp only [obsFreq, List.filter_append, List.length_append]
    push_cast
    field_simp
  unfold weightedFreq
  have hnm : ¬(runs1.length + runs2.length = 0) := by
    have := List.length_pos_of_ne_nil h1; omega
  rw [if_neg hnm, hq]
  simp only [dif_pos (obsFreq (runs1 ++ runs2) α).hlo,
             dif_pos (obsFreq (runs1 ++ runs2) α).hhi]

/-- **Acceptance for `update` traces.**  Pooling two certified batches
    over disjoint token ranges is accepted by the checker. -/
theorem updateNode_accepted (Γ : Context) (x : String) (α : Output)
    (ρ : ℕ → String) (runs1 runs2 : List RunClaim)
    (hwf : contextWF Γ = true)
    (h1 : runs1 ≠ []) (h2 : runs2 ≠ [])
    (hinj : Function.Injective ρ)
    (hsupp1 : ∀ r ∈ runs1, (supportEntries Γ (.atom x) r.output).length = 1)
    (hsupp2 : ∀ r ∈ runs2, (supportEntries Γ (.atom x) r.output).length = 1) :
    checkDerivation (updateNode Γ x α ρ runs1 runs2) = Except.ok () := by
  have hp1 : 0 < runs1.length := List.length_pos_of_ne_nil h1
  have hp2 : 0 < runs2.length := List.length_pos_of_ne_nil h2
  refine checkDerivation_node_ok _ _ _ _ hwf ?_ ?_
  · rw [show checkNode (Derivation.node "update"
          [batchNode Γ x α ρ runs1 0, batchNode Γ x α ρ runs2 runs1.length]
          ⟨Γ, .term (updateTC x α ρ runs1 runs2)⟩ false)
        = checkUpdate (Derivation.node "update"
          [batchNode Γ x α ρ runs1 0, batchNode Γ x α ρ runs2 runs1.length]
          ⟨Γ, .term (updateTC x α ρ runs1 runs2)⟩ false) from rfl]
    simp only [checkUpdate, expectPremises, Derivation.premises,
               Derivation.conclusion, getClaim, getCtx, batchNode, batchTC,
               updateTC, ensure, expectTermClaim]
    simp [contextEqSet_refl,
          batchProv_disjoint x ρ runs1 runs2 0 runs1.length hinj (by omega),
          hp1, hp2]
    rw [weightedFreq_obsFreq runs1 runs2 α h1 h2]
    simp only [if_pos rfl]
    rfl
  · refine checkPremisesList_ok _ ?_
    intro p hp
    rcases List.mem_cons.mp hp with h | h
    · subst h
      exact batchNode_accepted Γ x α ρ runs1 0 hwf h1 hinj hsupp1
    · rw [List.mem_singleton] at h
      subst h
      exact batchNode_accepted Γ x α ρ runs2 runs1.length hwf h2 hinj hsupp2

/-- The pooled conclusion is derivable. -/
theorem updateNode_derivable (Γ : Context) (x : String) (α : Output)
    (ρ : ℕ → String) (runs1 runs2 : List RunClaim)
    (hwf : contextWF Γ = true)
    (h1 : runs1 ≠ []) (h2 : runs2 ≠ [])
    (hinj : Function.Injective ρ)
    (hsupp1 : ∀ r ∈ runs1, (supportEntries Γ (.atom x) r.output).length = 1)
    (hsupp2 : ∀ r ∈ runs2, (supportEntries Γ (.atom x) r.output).length = 1) :
    Derivable ⟨Γ, .term (updateTC x α ρ runs1 runs2)⟩ :=
  checker_sound _ (updateNode_accepted Γ x α ρ runs1 runs2 hwf h1 h2 hinj
    hsupp1 hsupp2)

-- ============================================================================
-- sumIntro: two counts over one history
-- ============================================================================

/-- Two filters that cannot both match a single element count at most the
    whole list between them. -/
theorem length_filter_two_le {A : Type} (p q : A → Bool) (l : List A)
    (h : ∀ a, ¬(p a = true ∧ q a = true)) :
    (l.filter p).length + (l.filter q).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
      by_cases hp : p a <;> by_cases hq : q a
      · exact absurd ⟨hp, hq⟩ (h a)
      all_goals simp [List.filter_cons, hp, hq]; omega

/-- For distinct outputs the two observed frequencies fit together. -/
theorem probAdd_obsFreq (runs : List RunClaim) (α β : Output)
    (hab : α ≠ β) :
    probAdd (obsFreq runs α) (obsFreq runs β)
      = some ⟨(obsFreq runs α).val + (obsFreq runs β).val,
              add_nonneg (obsFreq runs α).hlo (obsFreq runs β).hlo, by
        rcases Nat.eq_zero_or_pos runs.length with h | h
        · simp [obsFreq, h, List.length_eq_zero_iff.mp h]
        · have hcnt := length_filter_two_le (·.output == α) (·.output == β)
            runs (by
              intro r ⟨ha, hb⟩
              rw [beq_iff_eq] at ha hb
              exact hab (ha ▸ hb))
          have hq : (obsFreq runs α).val + (obsFreq runs β).val
              = (((runs.filter (·.output == α)).length
                  + (runs.filter (·.output == β)).length : ℕ) : ℚ)
                / (runs.length : ℚ) := by
            simp only [obsFreq]
            push_cast
            field_simp
          rw [hq, div_le_one (by exact_mod_cast h)]
          exact_mod_cast hcnt⟩ := by
  unfold probAdd
  rw [dif_pos]

/-- The sum claim over one history: frequency of `α + β` as the sum of the
    two observed frequencies, with the history's own provenance. -/
def sumTC (x : String) (α β : Output) (ρ : ℕ → String)
    (runs : List RunClaim) : TermClaim :=
  ⟨.frequency, .atom x, runs.length, .sum α β,
   (probAdd (obsFreq runs α) (obsFreq runs β)).getD Prob.zero,
   batchProv x ρ runs 0⟩

/-- Certificate for a `sumIntro` trace step: both counts read the SAME
    history under the SAME tokens, which is exactly the shared-provenance
    side condition of the sum rule. -/
def sumNode (Γ : Context) (x : String) (α β : Output) (ρ : ℕ → String)
    (runs : List RunClaim) : Derivation :=
  .node "I+" [batchNode Γ x α ρ runs 0, batchNode Γ x β ρ runs 0]
    ⟨Γ, .term (sumTC x α β ρ runs)⟩ false

/-- **Acceptance for `sumIntro` traces.** -/
theorem sumNode_accepted (Γ : Context) (x : String) (α β : Output)
    (ρ : ℕ → String) (runs : List RunClaim)
    (hwf : contextWF Γ = true)
    (hne : runs ≠ [])
    (hinj : Function.Injective ρ)
    (hab : α ≠ β)
    (hdisj : Output.syntacticallyDisjoint α β = true)
    (hsupp : ∀ r ∈ runs, (supportEntries Γ (.atom x) r.output).length = 1) :
    checkDerivation (sumNode Γ x α β ρ runs) = Except.ok () := by
  refine checkDerivation_node_ok _ _ _ _ hwf ?_ ?_
  · rw [show checkNode (Derivation.node "I+"
          [batchNode Γ x α ρ runs 0, batchNode Γ x β ρ runs 0]
          ⟨Γ, .term (sumTC x α β ρ runs)⟩ false)
        = checkIPlus (Derivation.node "I+"
          [batchNode Γ x α ρ runs 0, batchNode Γ x β ρ runs 0]
          ⟨Γ, .term (sumTC x α β ρ runs)⟩ false) from rfl]
    simp only [checkIPlus, expectPremises, Derivation.premises,
               Derivation.conclusion, getClaim, getCtx, batchNode, batchTC,
               sumTC, ensure, expectTermClaim]
    simp [contextEqSet_refl, hdisj, hab, bne_iff_ne.mpr hab]
    rw [probAdd_obsFreq runs α β hab]
    simp only [Option.getD_some, if_pos rfl]
    rfl
  · refine checkPremisesList_ok _ ?_
    intro p hp
    rcases List.mem_cons.mp hp with h | h
    · subst h
      exact batchNode_accepted Γ x α ρ runs 0 hwf hne hinj hsupp
    · rw [List.mem_singleton] at h
      subst h
      exact batchNode_accepted Γ x β ρ runs 0 hwf hne hinj hsupp

/-- The summed conclusion is derivable. -/
theorem sumNode_derivable (Γ : Context) (x : String) (α β : Output)
    (ρ : ℕ → String) (runs : List RunClaim)
    (hwf : contextWF Γ = true)
    (hne : runs ≠ [])
    (hinj : Function.Injective ρ)
    (hab : α ≠ β)
    (hdisj : Output.syntacticallyDisjoint α β = true)
    (hsupp : ∀ r ∈ runs, (supportEntries Γ (.atom x) r.output).length = 1) :
    Derivable ⟨Γ, .term (sumTC x α β ρ runs)⟩ :=
  checker_sound _ (sumNode_accepted Γ x α β ρ runs hwf hne hinj hab hdisj hsupp)

-- ============================================================================
-- pairIntro: the expected layer is where independence multiplies
-- ============================================================================

/-! A `pairIntro` trace step records the joint frequency of a paired draw
as a **datum**: at any finite sample the realised joint frequency need not
be the product of the marginals, so the frequency layer has no
introduction for it (design point 3 of the ↦ layer).  What IS certifiable
is the expected-layer counterpart: under an explicit independence witness,
the expected probabilities of the two coordinates multiply.  The bridge
therefore certifies a paired draw through `expectation` leaves. -/

/-- The exact assumption a coordinate's expectation reads. -/
def expectEntry (x : String) (α : Output) (a : Prob) : ContextEntry :=
  ⟨x, {x}, α, .exact a⟩

/-- An `expectation` leaf: `x : α` at its assumed exact probability. -/
def expectLeaf (x : String) (α : Output) (a : Prob) (tok : String)
    (n : ℕ) : Derivation :=
  .node "expectation" []
    ⟨[expectEntry x α a], .term ⟨.expected, .atom x, n, α, a, {tok}⟩⟩ false

/-- The paired claim: expected mode, product output, multiplied value. -/
def pairTC (x y : String) (α β : Output) (a b : Prob) (tok : String)
    (n : ℕ) : TermClaim :=
  ⟨.expected, .pair (.atom x) (.atom y), n, .prod α β, probMul a b, {tok}⟩

/-- Certificate for a paired draw: two expectation leaves joined by the
    product rule under an explicit independence witness. -/
def pairNode (x y : String) (α β : Output) (a b : Prob) (tok : String)
    (n : ℕ) : Derivation :=
  .node "I×" [expectLeaf x α a tok n, expectLeaf y β b tok n]
    ⟨mergeContexts [[expectEntry x α a], [expectEntry y β b]],
     .term (pairTC x y α β a b tok n)⟩ true

theorem merge_two (e1 e2 : ContextEntry) (hne : (e2 == e1) = false) :
    mergeContexts [[e1], [e2]] = [e1, e2] := by
  simp [mergeContexts, List.eraseDups, List.eraseDupsBy,
        List.eraseDupsBy.loop, hne]

theorem expectEntry_wf (x : String) (α : Output) (a : Prob) :
    contextWF [expectEntry x α a] = true := by
  simp [contextWF, expectEntry, entryWF, constraintWF, variableNames,
        variableMass, groupMass, exactMass, intervalLower, a.hhi]

theorem pairCtx_wf (x y : String) (α β : Output) (a b : Prob)
    (hxy : x ≠ y) :
    contextWF [expectEntry x α a, expectEntry y β b] = true := by
  have hyx : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hxy)
  have hxy' : (x == y) = false := beq_eq_false_iff_ne.mpr hxy
  simp [contextWF, expectEntry, entryWF, constraintWF, variableNames,
        variableMass, groupMass, exactMass, intervalLower, hyx, hxy',
        a.hhi, b.hhi]

theorem expectLeaf_accepted (x : String) (α : Output) (a : Prob)
    (tok : String) (n : ℕ) (hn : 0 < n) :
    checkDerivation (expectLeaf x α a tok n) = Except.ok () := by
  refine checkDerivation_node_ok _ _ _ _ (expectEntry_wf x α a) ?_ rfl
  rw [show checkNode (Derivation.node "expectation" []
        ⟨[expectEntry x α a], .term ⟨.expected, .atom x, n, α, a, {tok}⟩⟩
        false)
      = checkExpectation (Derivation.node "expectation" []
        ⟨[expectEntry x α a], .term ⟨.expected, .atom x, n, α, a, {tok}⟩⟩
        false) from rfl]
  simp [checkExpectation, expectPremises, Derivation.premises,
        Derivation.conclusion, getClaim, getCtx, ensure, isAtomicTerm,
        supportEntries, expectEntry, hn]
  rfl

/-- **Acceptance for paired draws** at the expected layer. -/
theorem pairNode_accepted (x y : String) (α β : Output) (a b : Prob)
    (tok : String) (n : ℕ) (hxy : x ≠ y) (hn : 0 < n) :
    checkDerivation (pairNode x y α β a b tok n) = Except.ok () := by
  have hee : ((expectEntry y β b == expectEntry x α a)) = false := by
    refine beq_eq_false_iff_ne.mpr ?_
    intro hcon
    exact hxy (by
      have := congrArg ContextEntry.name hcon
      simpa [expectEntry] using this.symm)
  have hyx : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hxy)
  have hxy' : (x == y) = false := beq_eq_false_iff_ne.mpr hxy
  have hwf : contextWF (mergeContexts
      [[expectEntry x α a], [expectEntry y β b]]) = true := by
    rw [merge_two _ _ hee]
    exact pairCtx_wf x y α β a b hxy
  refine checkDerivation_node_ok _ _ _ _ hwf ?_ ?_
  · rw [show checkNode (Derivation.node "I×"
          [expectLeaf x α a tok n, expectLeaf y β b tok n]
          ⟨mergeContexts [[expectEntry x α a], [expectEntry y β b]],
           .term (pairTC x y α β a b tok n)⟩ true)
        = checkIProd (Derivation.node "I×"
          [expectLeaf x α a tok n, expectLeaf y β b tok n]
          ⟨mergeContexts [[expectEntry x α a], [expectEntry y β b]],
           .term (pairTC x y α β a b tok n)⟩ true) from rfl]
    simp only [checkIProd, expectPremises, Derivation.premises,
               Derivation.conclusion, getClaim, getCtx, pairNode, pairTC,
               expectLeaf, ensure, expectTermClaim,
               Derivation.hasIndependenceWitness]
    simp [independentContexts, variableNames, expectEntry, hxy', hyx,
          Ne.symm hxy, contextEqSet_refl]
    rfl
  · refine checkPremisesList_ok _ ?_
    intro p hp
    rcases List.mem_cons.mp hp with h | h
    · subst h
      exact expectLeaf_accepted x α a tok n hn
    · rw [List.mem_singleton] at h
      subst h
      exact expectLeaf_accepted y β b tok n hn

/-- The paired conclusion is derivable. -/
theorem pairNode_derivable (x y : String) (α β : Output) (a b : Prob)
    (tok : String) (n : ℕ) (hxy : x ≠ y) (hn : 0 < n) :
    Derivable ⟨mergeContexts [[expectEntry x α a], [expectEntry y β b]],
      .term (pairTC x y α β a b tok n)⟩ :=
  checker_sound _ (pairNode_accepted x y α β a b tok n hxy hn)

-- ============================================================================
-- The trust guarantee for the implemented test, at the artifact level
-- ============================================================================

open MeasureTheory

/-- The certified value of a run history IS the run space's observed
    frequency. -/
theorem obsFreq_runList_val (M : Model) (x : String) (α : Output)
    (ω : ℕ → M.Ω) (n : ℕ) :
    (((obsFreq (M.runList x α ω n) α).val : ℝ)) = M.observedFreq x α n ω := by
  have hlen := M.runList_length x α ω n
  rw [show (obsFreq (M.runList x α ω n) α).val
      = (((M.runList x α ω n).filter (·.output == α)).length : ℚ)
        / (((M.runList x α ω n).length : ℚ)) from rfl]
  simp only [hlen]
  push_cast
  exact M.sampling_adequate x α ω n

/-- **The implemented test has a provable 5 % level.**  If the model is
    correct, the probability that a run history's frequency falls outside
    the very interval `binomialCI` computes — the interval a checker-accepted
    IT certificate carries — is at most 1/20. -/
theorem Model.certified_trust_coverage (M : Model) (x : String) (α : Output)
    {n : ℕ} (hn : n ≠ 0) (p : Prob)
    (hp : ((p.val : ℝ)) = (M.μ (M.hitSet x α)).toReal)
    (hpos : 0 < (M.μ (M.hitSet x α)).toReal
              * (1 - (M.μ (M.hitSet x α)).toReal)) :
    M.runSpace {ω |
        (binomialCI n (obsFreq (M.runList x α ω n) α) p).contains p = false}
      ≤ ENNReal.ofReal (1 / 20) := by
  have hz20 : (20 : ℝ) ≤ ((zCheb : ℚ) : ℝ) ^ 2 := by
    have : (20 : ℚ) ≤ zCheb ^ 2 := by norm_num [zCheb]
    exact_mod_cast this
  have hzpos : (0 : ℝ) < ((zCheb : ℚ) : ℝ) := by
    have : (0 : ℚ) < zCheb := by norm_num [zCheb]
    exact_mod_cast this
  have hsub : {ω | (binomialCI n (obsFreq (M.runList x α ω n) α) p).contains p
        = false}
      ⊆ {ω | ((zCheb : ℚ) : ℝ) * Real.sqrt
          ((M.μ (M.hitSet x α)).toReal * (1 - (M.μ (M.hitSet x α)).toReal) / n)
          ≤ |M.observedFreq x α n ω - (M.μ (M.hitSet x α)).toReal|} := by
    intro ω hω
    have h := binomialCI_reject hn (obsFreq (M.runList x α ω n) α) p hω
    rw [hp, obsFreq_runList_val] at h
    exact h
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (M.trust_coverage x α hn hzpos hpos) ?_
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 20)]
  linarith

/-- The same bound, read as the false-alarm rate of the UNtrust test: honest
    evidence supports an IUT certificate against the true model probability
    with probability at most 1/20. -/
theorem Model.certified_untrust_rate (M : Model) (x : String) (α : Output)
    {n : ℕ} (hn : n ≠ 0) (p : Prob)
    (hp : ((p.val : ℝ)) = (M.μ (M.hitSet x α)).toReal)
    (hpos : 0 < (M.μ (M.hitSet x α)).toReal
              * (1 - (M.μ (M.hitSet x α)).toReal)) :
    M.runSpace {ω |
        notInConstraint p (binomialCI n (obsFreq (M.runList x α ω n) α) p)
          = true}
      ≤ ENNReal.ofReal (1 / 20) := by
  have := M.certified_trust_coverage x α hn p hp hpos
  refine le_trans (le_of_eq ?_) this
  congr 1
  ext ω
  simp [notInConstraint]

-- ============================================================================
-- A full IT certificate from honest runs
-- ============================================================================

/-- The complete trust certificate for a run history: the model assumption
    cited by identity, the history collected by `sampling`, and the two
    joined by `IT`. -/
def itNode (m x : String) (α : Output) (p : Prob) (ρ : ℕ → String)
    (runs : List RunClaim) : Derivation :=
  .node "IT"
    [.node "identity" [] ⟨[expectEntry m α p], .identity (expectEntry m α p)⟩
       false,
     batchNode (obsContext x α) x α ρ runs 0]
    ⟨mergeContexts [[expectEntry m α p], obsContext x α],
     .trust (.trust .oneSample (.atom x) runs.length α (obsFreq runs α) p
       (binomialCI runs.length (obsFreq runs α) p) (batchProv x ρ runs 0))⟩
    false

theorem merge_one_two (me e1 e2 : ContextEntry)
    (h1 : (e1 == me) = false) (h2 : (e2 == me) = false)
    (h3 : (e2 == e1) = false) :
    mergeContexts [[me], [e1, e2]] = [me, e1, e2] := by
  simp [mergeContexts, List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop,
        h1, h2, h3]

theorem itCtx_wf (m x : String) (α : Output) (p : Prob) (hmx : m ≠ x) :
    contextWF (expectEntry m α p :: obsContext x α) = true := by
  have hxm : (x == m) = false := beq_eq_false_iff_ne.mpr (Ne.symm hmx)
  have hmx' : (m == x) = false := beq_eq_false_iff_ne.mpr hmx
  have hg : groupMass
      [⟨x, {x}, α, .unknown⟩, ⟨x, {x}, Output.neg α, .unknown⟩]
      = fun _ => 0 := by
    funext β
    by_cases hb1 : (α == β) <;> by_cases hb2 : (Output.neg α == β) <;>
      simp [groupMass, List.filter, hb1, hb2, exactMass, intervalLower]
  simp [contextWF, obsContext, expectEntry, entryWF, constraintWF,
        variableNames, variableMass, hxm, hmx', hg, groupMass, exactMass,
        intervalLower, p.hhi]

/-- **Honest runs certify with probability at least 95 %.**  If the model is
    correct, the probability that a run history fails to yield a
    checker-accepted IT certificate is at most 1/20.  (The only data-dependent
    side condition is the CI test; everything else holds by construction.) -/
theorem itNode_accepted (m x : String) (α : Output) (p : Prob)
    (ρ : ℕ → String) (runs : List RunClaim)
    (hmx : m ≠ x) (hne : runs ≠ []) (hinj : Function.Injective ρ)
    (hsupp : ∀ r ∈ runs,
      (supportEntries (obsContext x α) (.atom x) r.output).length = 1)
    (hpass : (binomialCI runs.length (obsFreq runs α) p).contains p = true) :
    checkDerivation (itNode m x α p ρ runs) = Except.ok () := by
  have hee1 : ((⟨x, {x}, α, .unknown⟩ : ContextEntry)
      == expectEntry m α p) = false := by
    refine beq_eq_false_iff_ne.mpr ?_
    intro hcon
    exact hmx (by
      have := congrArg ContextEntry.name hcon
      simpa [expectEntry] using this.symm)
  have hee2 : ((⟨x, {x}, Output.neg α, .unknown⟩ : ContextEntry)
      == expectEntry m α p) = false := by
    refine beq_eq_false_iff_ne.mpr ?_
    intro hcon
    exact hmx (by
      have := congrArg ContextEntry.name hcon
      simpa [expectEntry] using this.symm)
  have hee3 : ((⟨x, {x}, Output.neg α, .unknown⟩ : ContextEntry)
      == (⟨x, {x}, α, .unknown⟩ : ContextEntry)) = false := by
    refine beq_eq_false_iff_ne.mpr ?_
    intro hcon
    have := congrArg ContextEntry.output hcon
    exact Output.neg_ne_self α (by simpa using this)
  have hmerge : mergeContexts [[expectEntry m α p], obsContext x α]
      = expectEntry m α p :: obsContext x α := by
    rw [show obsContext x α
        = [⟨x, {x}, α, .unknown⟩, ⟨x, {x}, Output.neg α, .unknown⟩] from rfl]
    exact merge_one_two _ _ _ hee1 hee2 hee3
  have hwf : contextWF (mergeContexts
      [[expectEntry m α p], obsContext x α]) = true := by
    rw [hmerge]
    exact itCtx_wf m x α p hmx
  refine checkDerivation_node_ok _ _ _ _ hwf ?_ ?_
  · rw [show checkNode (Derivation.node "IT"
          [.node "identity" []
             ⟨[expectEntry m α p], .identity (expectEntry m α p)⟩ false,
           batchNode (obsContext x α) x α ρ runs 0]
          ⟨mergeContexts [[expectEntry m α p], obsContext x α],
           .trust (.trust .oneSample (.atom x) runs.length α (obsFreq runs α)
             p (binomialCI runs.length (obsFreq runs α) p)
             (batchProv x ρ runs 0))⟩ false)
        = checkIT (Derivation.node "IT"
          [.node "identity" []
             ⟨[expectEntry m α p], .identity (expectEntry m α p)⟩ false,
           batchNode (obsContext x α) x α ρ runs 0]
          ⟨mergeContexts [[expectEntry m α p], obsContext x α],
           .trust (.trust .oneSample (.atom x) runs.length α (obsFreq runs α)
             p (binomialCI runs.length (obsFreq runs α) p)
             (batchProv x ρ runs 0))⟩ false) from rfl]
    simp only [checkIT, expectPremises, Derivation.premises,
               Derivation.conclusion, getClaim, getCtx, batchNode, batchTC,
               expectEntry, ensure, expectIdentity, expectExact,
               expectTermClaim, inConstraint]
    simp [contextEqSet_refl, hpass, expectEntry]
    rfl
  · refine checkPremisesList_ok _ ?_
    intro q hq
    rcases List.mem_cons.mp hq with h | h
    · subst h
      refine checkDerivation_node_ok _ _ _ _ (expectEntry_wf m α p) ?_ rfl
      rw [show checkNode (Derivation.node "identity" []
            ⟨[expectEntry m α p], .identity (expectEntry m α p)⟩ false)
          = checkIdentity (Derivation.node "identity" []
            ⟨[expectEntry m α p], .identity (expectEntry m α p)⟩ false)
          from rfl]
      simp [checkIdentity, expectPremises, Derivation.premises,
            Derivation.conclusion, getClaim, getCtx, ensure]
      rfl
    · rw [List.mem_singleton] at h
      subst h
      exact batchNode_accepted (obsContext x α) x α ρ runs 0
        (obsContext_wf x α) hne hinj hsupp

/-- **The end-to-end guarantee for the artifact.**  For a correct model, the
    probability that `n` honest runs fail to produce a checker-accepted IT
    certificate is at most 1/20 — and by `checker_sound`, every certificate
    that IS produced has a derivable conclusion. -/
theorem Model.honest_run_certified (M : Model) (m x : String) (α : Output)
    {n : ℕ} (hn : n ≠ 0) (p : Prob) (ρ : ℕ → String)
    (hinj : Function.Injective ρ) (hmx : m ≠ x)
    (hp : ((p.val : ℝ)) = (M.μ (M.hitSet x α)).toReal)
    (hpos : 0 < (M.μ (M.hitSet x α)).toReal
              * (1 - (M.μ (M.hitSet x α)).toReal)) :
    M.runSpace {ω |
        checkDerivation (itNode m x α p ρ (M.runList x α ω n))
          ≠ Except.ok ()}
      ≤ ENNReal.ofReal (1 / 20) := by
  refine le_trans (measure_mono ?_)
    (M.certified_trust_coverage x α hn p hp hpos)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hcon
  have hpass : (binomialCI n (obsFreq (M.runList x α ω n) α) p).contains p
      = true := by
    cases hb : (binomialCI n (obsFreq (M.runList x α ω n) α) p).contains p
    · exact absurd hb hcon
    · rfl
  have hne : M.runList x α ω n ≠ [] := by
    intro hnil
    have := M.runList_length x α ω n
    rw [hnil] at this
    simp at this
    omega
  have hlen := M.runList_length x α ω n
  exact hω (itNode_accepted m x α p ρ (M.runList x α ω n) hmx hne hinj
    (runList_supported M x α ω n) (by rw [hlen]; exact hpass))

end TPTND