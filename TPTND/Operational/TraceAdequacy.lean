import TPTND.Operational.Bridge

/-! # General trace adequacy

`Operational/Bridge.lean` certifies the canonical evidence shapes — a
batch, a pooling of two batches, two counts of one history.  This file
closes the general question: **every claim produced by an arbitrary
reduction sequence certifies**, however the steps nest.

The ↦ layer is deliberately provenance-free, so a reduction sequence may
reuse evidence — pool a batch with itself, say — and the static layer's
provenance discipline exists precisely to refuse the resulting
certificates.  The right general statement therefore quantifies over
**labelled traces** (`CertTrace`): reduction sequences that carry a
provenance assignment making the bookkeeping explicit — fresh draws,
unions at pooling, a shared label for two counts of one history, and
disjointness exactly where the static rules demand it.

* `CertTrace.reduces` (erasure): forgetting the labels of a labelled
  trace yields a genuine reduction sequence — `CertTrace` proves
  nothing the ↦ layer cannot do.
* `CertTrace.certified` (adequacy): every cell of a labelled trace has a
  checker-accepted certificate concluding its claim at its label, in one
  induction over the trace; `CertTrace.derivable` composes with
  `checker_sound`.

`pairIntro` is deliberately absent: a paired draw's realised joint
frequency is a datum, not a product, and the frequency layer has no
introduction for it (design point 3 of the ↦ layer; see
`pairNode_accepted` for the expected-layer counterpart). -/

namespace TPTND

-- ============================================================================
-- Arithmetic: the checkers' Option-valued operations, from value equations
-- ============================================================================

theorem probAdd_eq (f g s : Prob) (hs : s.val = f.val + g.val) :
    probAdd f g = some s := by
  unfold probAdd
  rw [dif_pos (by rw [← hs]; exact s.hhi)]
  exact congrArg some (Prob.val_inj hs.symm)

theorem probSub_eq (r q dd : Prob) (hd : dd.val = r.val - q.val) :
    probSub r q = some dd := by
  unfold probSub
  rw [dif_pos (by rw [← hd]; exact dd.hlo)]
  exact congrArg some (Prob.val_inj hd.symm)

theorem weightedFreq_eq (n m : ℕ) (f g h : Prob) (hn : 0 < n) (hm : 0 < m)
    (hh : h.val = (f.val * n + g.val * m) / ((n : ℚ) + m)) :
    weightedFreq n f m g = some h := by
  have hq : ((n : ℚ) * f.val + (m : ℚ) * g.val) / (((n + m : ℕ)) : ℚ)
      = h.val := by
    rw [hh]
    push_cast
    ring_nf
  unfold weightedFreq
  rw [if_neg (by omega), hq,
      dif_pos h.hlo, dif_pos h.hhi]

-- ============================================================================
-- Outputs: syntactic disjointness separates
-- ============================================================================

theorem Output.atoms_nonempty_of_isPositive :
    ∀ α : Output, α.isPositive = true → α.atoms.Nonempty
  | .atom a, _ => ⟨a, by simp [Output.atoms]⟩
  | .sum α β, h => by
      simp only [Output.isPositive, Bool.and_eq_true] at h
      obtain ⟨a, ha⟩ := Output.atoms_nonempty_of_isPositive α h.1
      exact ⟨a, by simp [Output.atoms, ha]⟩
  | .prod α β, h => by
      simp only [Output.isPositive, Bool.and_eq_true] at h
      obtain ⟨a, ha⟩ := Output.atoms_nonempty_of_isPositive α h.1
      exact ⟨a, by simp [Output.atoms, ha]⟩

theorem Output.ne_of_syntacticallyDisjoint {α β : Output}
    (h : Output.syntacticallyDisjoint α β = true) : α ≠ β := by
  unfold Output.syntacticallyDisjoint at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hpos, _⟩, hdisj⟩ := h
  intro hcon
  subst hcon
  obtain ⟨a, ha⟩ := Output.atoms_nonempty_of_isPositive α hpos
  have : a ∈ α.atoms ∩ α.atoms := Finset.mem_inter.mpr ⟨ha, ha⟩
  rw [hdisj] at this
  exact Finset.notMem_empty a this

-- ============================================================================
-- Support uniqueness at a supported pair
-- ============================================================================

theorem supportEntries_length_one {Γ : Context} {u : String} {α : Output}
    (hs : supports Γ u α)
    (huniq : (supportEntries Γ (.atom u) α).length ≤ 1) :
    (supportEntries Γ (.atom u) α).length = 1 := by
  obtain ⟨e, heΓ, hn, ho⟩ := hs
  have hmem : e ∈ supportEntries Γ (.atom u) α := by
    simp only [supportEntries]
    exact List.mem_filter.mpr ⟨heΓ, by
      rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
      exact ⟨hn, ho⟩⟩
  have hpos : 0 < (supportEntries Γ (.atom u) α).length :=
    List.length_pos_of_mem hmem
  omega

-- ============================================================================
-- Generic premise extraction from conclusion equations
-- ============================================================================

theorem ptc_of_map (rule : String) :
    ∀ (ds : List Derivation) (tcs : List TermClaim)
      (hmap : ds.map getClaim = tcs.map Claim.term),
      premiseTermClaimsC ds rule = Except.ok ⟨tcs, hmap⟩
  | [], [], _ => rfl
  | [], _ :: _, hmap => by simp at hmap
  | _ :: _, [], hmap => by simp at hmap
  | d :: ds, tc :: tcs, hmap => by
      have hmap' := hmap
      simp only [List.map_cons, List.cons.injEq] at hmap'
      obtain ⟨hd, hds⟩ := hmap'
      have ih := ptc_of_map rule ds tcs hds
      obtain ⟨r, ps, ⟨ctx, cl⟩, w⟩ := d
      dsimp only [getClaim, Derivation.conclusion] at hd
      subst hd
      simp only [premiseTermClaimsC, ih]
      rfl

-- ============================================================================
-- Generic node acceptance: sampling over arbitrary accepted premises
-- ============================================================================

theorem samplingNode_ok (Γ : Context) (t : Term) (α : Output)
    (ds : List Derivation) (tcs : List TermClaim) (f : Prob)
    (hwf : contextWF Γ = true)
    (hne : ds ≠ [])
    (hmap : ds.map getClaim = tcs.map Claim.term)
    (hctx : ∀ d ∈ ds, getCtx d = Γ)
    (hacc : ∀ d ∈ ds, checkDerivation d = Except.ok ())
    (hshape : ∀ tc ∈ tcs,
      tc.prov.card = 1 ∧ tc.samples = 1 ∧ tc.mode = .frequency)
    (hterm : ∀ tc ∈ tcs, tc.term = t)
    (hdisj : Provenance.pairwiseDisjoint (tcs.map (·.prov)) = true)
    (hf : f.val = ((tcs.filter (·.output == α)).length : ℚ)
                    / ((ds.length : ℚ))) :
    checkDerivation (.node "sampling" ds
      ⟨Γ, .term ⟨.frequency, t, ds.length, α, f,
        ((tcs.map (·.prov)).foldl (· ∪ ·) ∅)⟩⟩ false)
      = Except.ok () := by
  have hlen1 : (decide (ds.length ≥ 1)) = true :=
    decide_eq_true (List.length_pos_of_ne_nil hne)
  have hctxall : ds.all (fun p => contextEqSet (getCtx p) Γ) = true := by
    rw [List.all_eq_true]
    intro p hp
    rw [hctx p hp]
    exact contextEqSet_refl Γ
  have hexpall : tcs.all (fun tc =>
      tc.prov.card == 1 && tc.samples == 1 && tc.mode == .frequency) = true := by
    rw [List.all_eq_true]
    intro tc htc
    obtain ⟨h1, h2, h3⟩ := hshape tc htc
    simp [h1, h2, h3]
  have htermall : tcs.all (fun tc => tc.term == t) = true := by
    rw [List.all_eq_true]
    intro tc htc
    simp [hterm tc htc]
  have hsamp : (ds.length == ds.length) = true := beq_self_eq_true _
  have hval : (decide (f.val ==
      ((tcs.filter (·.output == α)).length : ℚ) / ((ds.length : ℚ))))
      = true := by
    simp [hf]
  have hC : ∃ w, checkSamplingC (Derivation.node "sampling" ds
      ⟨Γ, .term ⟨.frequency, t, ds.length, α, f,
        ((tcs.map (·.prov)).foldl (· ∪ ·) ∅)⟩⟩ false)
      = Except.ok w := by
    unfold checkSamplingC
    refine bind_ok_ex _ (ensure'_ok _ _ hlen1) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ rfl) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ hctxall) ?_
    refine bind_ok_ex _ (ptc_of_map "sampling" ds tcs hmap) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ hexpall) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ htermall) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ hdisj) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ (beq_self_eq_true _)) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ hsamp) ?_
    refine bind_ok_ex _ (ensure'_ok _ _ hval) ?_
    exact ⟨_, rfl⟩
  refine checkDerivation_node_ok _ _ _ _ hwf ?_ (checkPremisesList_ok _ hacc)
  rw [show checkNode (Derivation.node "sampling" ds
        ⟨Γ, .term ⟨.frequency, t, ds.length, α, f,
          ((tcs.map (·.prov)).foldl (· ∪ ·) ∅)⟩⟩ false)
      = checkSampling (Derivation.node "sampling" ds
        ⟨Γ, .term ⟨.frequency, t, ds.length, α, f,
          ((tcs.map (·.prov)).foldl (· ∪ ·) ∅)⟩⟩ false) from rfl]
  obtain ⟨w, hw⟩ := hC
  unfold checkSampling
  rw [hw]
  rfl

-- ============================================================================
-- Generic node acceptance: the two-premise steps
-- ============================================================================

theorem updateNode_ok (Γ : Context) (d1 d2 : Derivation) (t : Term)
    (α : Output) (n m : ℕ) (f g h : Prob) (σf σg : Provenance)
    (hwf : contextWF Γ = true)
    (h1 : checkDerivation d1 = Except.ok ())
    (h2 : checkDerivation d2 = Except.ok ())
    (hc1 : d1.conclusion = ⟨Γ, .term ⟨.frequency, t, n, α, f, σf⟩⟩)
    (hc2 : d2.conclusion = ⟨Γ, .term ⟨.frequency, t, m, α, g, σg⟩⟩)
    (hn : 0 < n) (hm : 0 < m)
    (hdisj : Provenance.disjoint σf σg = true)
    (hh : h.val = (f.val * n + g.val * m) / ((n : ℚ) + m)) :
    checkDerivation (.node "update" [d1, d2]
      ⟨Γ, .term ⟨.frequency, t, n + m, α, h, σf ∪ σg⟩⟩ false)
      = Except.ok () := by
  obtain ⟨r1, ps1, c1, w1⟩ := d1
  obtain ⟨r2, ps2, c2, w2⟩ := d2
  dsimp only [Derivation.conclusion] at hc1 hc2
  subst hc1
  subst hc2
  refine checkDerivation_node_ok _ _ _ _ hwf ?_ (checkPremisesList_ok _ ?_)
  · rw [show checkNode (Derivation.node "update"
          [.node r1 ps1 ⟨Γ, .term ⟨.frequency, t, n, α, f, σf⟩⟩ w1,
           .node r2 ps2 ⟨Γ, .term ⟨.frequency, t, m, α, g, σg⟩⟩ w2]
          ⟨Γ, .term ⟨.frequency, t, n + m, α, h, σf ∪ σg⟩⟩ false)
        = checkUpdate (Derivation.node "update"
          [.node r1 ps1 ⟨Γ, .term ⟨.frequency, t, n, α, f, σf⟩⟩ w1,
           .node r2 ps2 ⟨Γ, .term ⟨.frequency, t, m, α, g, σg⟩⟩ w2]
          ⟨Γ, .term ⟨.frequency, t, n + m, α, h, σf ∪ σg⟩⟩ false) from rfl]
    simp only [checkUpdate, expectPremises, Derivation.premises,
               Derivation.conclusion, getClaim, getCtx, ensure,
               expectTermClaim]
    simp [contextEqSet_refl, hdisj, hn, hm]
    rw [weightedFreq_eq n m f g h hn hm hh]
    simp only [if_pos rfl]
    rfl
  · intro p hp
    rcases List.mem_cons.mp hp with hp1 | hp1
    · subst hp1; exact h1
    · rw [List.mem_singleton] at hp1; subst hp1; exact h2

theorem iPlusNode_ok (Γ : Context) (d1 d2 : Derivation) (t : Term)
    (α β : Output) (n : ℕ) (f g h : Prob) (σ : Provenance)
    (hwf : contextWF Γ = true)
    (h1 : checkDerivation d1 = Except.ok ())
    (h2 : checkDerivation d2 = Except.ok ())
    (hc1 : d1.conclusion = ⟨Γ, .term ⟨.frequency, t, n, α, f, σ⟩⟩)
    (hc2 : d2.conclusion = ⟨Γ, .term ⟨.frequency, t, n, β, g, σ⟩⟩)
    (hdisj : Output.syntacticallyDisjoint α β = true)
    (hh : h.val = f.val + g.val) :
    checkDerivation (.node "I+" [d1, d2]
      ⟨Γ, .term ⟨.frequency, t, n, .sum α β, h, σ⟩⟩ false)
      = Except.ok () := by
  have hne := Output.ne_of_syntacticallyDisjoint hdisj
  obtain ⟨r1, ps1, c1, w1⟩ := d1
  obtain ⟨r2, ps2, c2, w2⟩ := d2
  dsimp only [Derivation.conclusion] at hc1 hc2
  subst hc1
  subst hc2
  refine checkDerivation_node_ok _ _ _ _ hwf ?_ (checkPremisesList_ok _ ?_)
  · rw [show checkNode (Derivation.node "I+"
          [.node r1 ps1 ⟨Γ, .term ⟨.frequency, t, n, α, f, σ⟩⟩ w1,
           .node r2 ps2 ⟨Γ, .term ⟨.frequency, t, n, β, g, σ⟩⟩ w2]
          ⟨Γ, .term ⟨.frequency, t, n, .sum α β, h, σ⟩⟩ false)
        = checkIPlus (Derivation.node "I+"
          [.node r1 ps1 ⟨Γ, .term ⟨.frequency, t, n, α, f, σ⟩⟩ w1,
           .node r2 ps2 ⟨Γ, .term ⟨.frequency, t, n, β, g, σ⟩⟩ w2]
          ⟨Γ, .term ⟨.frequency, t, n, .sum α β, h, σ⟩⟩ false) from rfl]
    simp only [checkIPlus, expectPremises, Derivation.premises,
               Derivation.conclusion, getClaim, getCtx, ensure,
               expectTermClaim]
    simp [contextEqSet_refl, hdisj, hne]
    rw [probAdd_eq f g h hh]
    simp only [if_pos rfl]
    rfl
  · intro p hp
    rcases List.mem_cons.mp hp with hp1 | hp1
    · subst hp1; exact h1
    · rw [List.mem_singleton] at hp1; subst hp1; exact h2

theorem ePlusRNode_ok (Γ : Context) (d1 d2 : Derivation) (t : Term)
    (α β : Output) (n : ℕ) (r q h : Prob) (σ : Provenance)
    (hwf : contextWF Γ = true)
    (h1 : checkDerivation d1 = Except.ok ())
    (h2 : checkDerivation d2 = Except.ok ())
    (hc1 : d1.conclusion = ⟨Γ, .term ⟨.frequency, t, n, .sum α β, r, σ⟩⟩)
    (hc2 : d2.conclusion = ⟨Γ, .term ⟨.frequency, t, n, β, q, σ⟩⟩)
    (hdisj : Output.syntacticallyDisjoint α β = true)
    (hh : h.val = r.val - q.val) :
    checkDerivation (.node "E+R" [d1, d2]
      ⟨Γ, .term ⟨.frequency, t, n, α, h, σ⟩⟩ false)
      = Except.ok () := by
  have hqr : q.val ≤ r.val := by
    have := h.hlo
    linarith [hh]
  obtain ⟨r1, ps1, c1, w1⟩ := d1
  obtain ⟨r2, ps2, c2, w2⟩ := d2
  dsimp only [Derivation.conclusion] at hc1 hc2
  subst hc1
  subst hc2
  refine checkDerivation_node_ok _ _ _ _ hwf ?_ (checkPremisesList_ok _ ?_)
  · rw [show checkNode (Derivation.node "E+R"
          [.node r1 ps1 ⟨Γ, .term ⟨.frequency, t, n, .sum α β, r, σ⟩⟩ w1,
           .node r2 ps2 ⟨Γ, .term ⟨.frequency, t, n, β, q, σ⟩⟩ w2]
          ⟨Γ, .term ⟨.frequency, t, n, α, h, σ⟩⟩ false)
        = checkEPlusR (Derivation.node "E+R"
          [.node r1 ps1 ⟨Γ, .term ⟨.frequency, t, n, .sum α β, r, σ⟩⟩ w1,
           .node r2 ps2 ⟨Γ, .term ⟨.frequency, t, n, β, q, σ⟩⟩ w2]
          ⟨Γ, .term ⟨.frequency, t, n, α, h, σ⟩⟩ false) from rfl]
    simp only [checkEPlusR, expectPremises, Derivation.premises,
               Derivation.conclusion, getClaim, getCtx, ensure,
               expectTermClaim]
    simp [contextEqSet_refl, hdisj, hqr]
    rw [probSub_eq r q h hh]
    simp only [if_pos rfl]
    rfl
  · intro p hp
    rcases List.mem_cons.mp hp with hp1 | hp1
    · subst hp1; exact h1
    · rw [List.mem_singleton] at hp1; subst hp1; exact h2

-- ============================================================================
-- Labelled traces
-- ============================================================================

/-- The static claim of a labelled trace cell. -/
def cellTC (c : RunClaim × Provenance) : TermClaim :=
  ⟨.frequency, c.1.term, c.1.samples, c.1.output, c.1.freq, c.2⟩

/-- A **labelled trace**: a reduction sequence carrying the provenance
    bookkeeping the static layer audits — fresh tokens for draws, unions at
    pooling, a shared label for two counts of one history, disjointness
    where evidence must not be reused.  `CertTrace.reduces` erases the
    labels back to `ReducesMany`; `CertTrace.certified` certifies every
    cell.  (`pairIntro` is absent by design — see the module docstring.) -/
inductive CertTrace (Γ : Context) : List (RunClaim × Provenance) → Prop
  | nil : CertTrace Γ []
  | event (T : List (RunClaim × Provenance)) (u a tok : String)
      (ht : CertTrace Γ T)
      (hsupp : supports Γ u (.atom a)) :
      CertTrace Γ (T ++ [(⟨.atom u, 1, .atom a, Prob.one⟩, {tok})])
  | sampling (T : List (RunClaim × Provenance)) (t : Term) (α : Output)
      (sources : List (RunClaim × Provenance)) (f : Prob)
      (ht : CertTrace Γ T)
      (hmem : ∀ s ∈ sources, s ∈ T)
      (hterm : ∀ s ∈ sources, s.1.term = t)
      (hsingle : ∀ s ∈ sources, s.1.samples = 1)
      (hprov1 : ∀ s ∈ sources, s.2.card = 1)
      (hdisj : Provenance.pairwiseDisjoint (sources.map (·.2)) = true)
      (hne : sources ≠ [])
      (hatom : ∃ b, α = .atom b)
      (hgr : Grounds Γ t α)
      (hf : f.val = ((sources.filter (fun s => s.1.output == α)).length : ℚ)
                      / ((sources.length : ℚ))) :
      CertTrace Γ (T ++ [(⟨t, sources.length, α, f⟩,
        ((sources.map (·.2)).foldl (· ∪ ·) ∅))])
  | update (T : List (RunClaim × Provenance)) (t : Term) (α : Output)
      (n m : ℕ) (f g h : Prob) (σf σg : Provenance)
      (ht : CertTrace Γ T)
      (hn : 0 < n) (hm : 0 < m)
      (hfmem : (⟨t, n, α, f⟩, σf) ∈ T)
      (hgmem : (⟨t, m, α, g⟩, σg) ∈ T)
      (hdisj : Provenance.disjoint σf σg = true)
      (hh : h.val = (f.val * n + g.val * m) / ((n : ℚ) + m)) :
      CertTrace Γ (T ++ [(⟨t, n + m, α, h⟩, σf ∪ σg)])
  | sumIntro (T : List (RunClaim × Provenance)) (t : Term) (n : ℕ)
      (α β : Output) (f g h : Prob) (σ : Provenance)
      (ht : CertTrace Γ T)
      (hdisj : Output.syntacticallyDisjoint α β = true)
      (hfmem : (⟨t, n, α, f⟩, σ) ∈ T)
      (hgmem : (⟨t, n, β, g⟩, σ) ∈ T)
      (hh : h.val = f.val + g.val) :
      CertTrace Γ (T ++ [(⟨t, n, .sum α β, h⟩, σ)])
  | sumElim (T : List (RunClaim × Provenance)) (t : Term) (n : ℕ)
      (α β : Output) (r q h : Prob) (σ : Provenance)
      (ht : CertTrace Γ T)
      (hdisj : Output.syntacticallyDisjoint α β = true)
      (hsmem : (⟨t, n, .sum α β, r⟩, σ) ∈ T)
      (hqmem : (⟨t, n, β, q⟩, σ) ∈ T)
      (hh : h.val = r.val - q.val) :
      CertTrace Γ (T ++ [(⟨t, n, α, h⟩, σ)])

-- ============================================================================
-- Erasure: labelled traces are reduction sequences
-- ============================================================================

theorem ReducesMany.snoc {Γ : Context} {L L' L'' : List RunClaim}
    (h : ReducesMany Γ L L') (hstep : Reduces Γ L' L'') :
    ReducesMany Γ L L'' := by
  induction h with
  | refl => exact .step hstep .refl
  | step h1 _ ih => exact .step h1 (ih hstep)

theorem length_filter_map {A B : Type _} (f : A → B) (p : B → Bool)
    (l : List A) :
    ((l.map f).filter p).length = (l.filter (fun a => p (f a))).length := by
  induction l with
  | nil => rfl
  | cons a t ih => by_cases h : p (f a) <;> simp [h, ih]

/-- **Erasure.**  Forgetting the labels of a labelled trace yields a genuine
    reduction sequence from the empty evaluation list. -/
theorem CertTrace.reduces {Γ : Context}
    {T : List (RunClaim × Provenance)} (h : CertTrace Γ T) :
    ReducesMany Γ [] (T.map (·.1)) := by
  induction h with
  | nil => exact .refl
  | event T u a tok ht hsupp ih =>
      rw [List.map_append]
      exact ih.snoc (by simpa using Reduces.event (L := T.map (·.1)) hsupp)
  | sampling T t α sources f ht hmem hterm hsingle hprov1 hdisj hne hatom
      hgr hf ih =>
      rw [List.map_append]
      have hstep := Reduces.sampling (Γ := Γ) (L := T.map (·.1))
        (t := t) (α := α) (runs := sources.map (·.1)) (f := f)
        (fun r hr => by
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
          exact List.mem_map_of_mem (hmem s hs))
        (fun r hr => by
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
          exact hterm s hs)
        (fun r hr => by
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
          exact hsingle s hs)
        (fun hcon => hne (List.map_eq_nil_iff.mp hcon))
        hatom hgr
        (by
          rw [length_filter_map, List.length_map]
          exact hf)
      simpa using ih.snoc hstep
  | update T t α n m f g h σf σg ht hn hm hfmem hgmem hdisj hh ih =>
      rw [List.map_append]
      exact ih.snoc (Reduces.update hn hm
        (List.mem_map_of_mem hfmem) (List.mem_map_of_mem hgmem) hh)
  | sumIntro T t n α β f g h σ ht hdisj hfmem hgmem hh ih =>
      rw [List.map_append]
      exact ih.snoc (Reduces.sumIntro hdisj
        (List.mem_map_of_mem hfmem) (List.mem_map_of_mem hgmem) hh)
  | sumElim T t n α β r q h σ ht hdisj hsmem hqmem hh ih =>
      rw [List.map_append]
      exact ih.snoc (Reduces.sumElim hdisj
        (List.mem_map_of_mem hsmem) (List.mem_map_of_mem hqmem) hh)

-- ============================================================================
-- Adequacy: every cell of a labelled trace certifies
-- ============================================================================

theorem exists_certs {P : (RunClaim × Provenance) → Derivation → Prop} :
    ∀ (ss : List (RunClaim × Provenance)),
      (∀ s ∈ ss, ∃ d, P s d) → ∃ ds, List.Forall₂ P ss ds
  | [], _ => ⟨[], .nil⟩
  | s :: ss, h => by
      obtain ⟨d, hd⟩ := h s (by simp)
      obtain ⟨ds, hds⟩ := exists_certs ss (fun s' hs' => h s' (by simp [hs']))
      exact ⟨d :: ds, .cons hd hds⟩

theorem forall₂_cert_facts {Γ : Context} :
    ∀ {ss : List (RunClaim × Provenance)} {ds : List Derivation},
      List.Forall₂ (fun s d => checkDerivation d = Except.ok () ∧
        d.conclusion = ⟨Γ, .term (cellTC s)⟩) ss ds →
      ds.map getClaim = (ss.map cellTC).map Claim.term ∧
      (∀ d ∈ ds, getCtx d = Γ) ∧
      (∀ d ∈ ds, checkDerivation d = Except.ok ()) ∧
      ds.length = ss.length
  | _, _, .nil => ⟨rfl, by simp, by simp, rfl⟩
  | _ :: _, _ :: _, .cons h hrest => by
      obtain ⟨hm, hctx, hacc, hlen⟩ := forall₂_cert_facts hrest
      refine ⟨?_, ?_, ?_, by simp [hlen]⟩
      · simp only [List.map_cons, hm, List.cons.injEq]
        exact ⟨congrArg Sequent.claim h.2, trivial⟩
      · intro d hd
        rcases List.mem_cons.mp hd with hd | hd
        · subst hd; exact congrArg Sequent.context h.2
        · exact hctx d hd
      · intro d hd
        rcases List.mem_cons.mp hd with hd | hd
        · subst hd; exact h.1
        · exact hacc d hd

/-- **General trace adequacy.**  Every cell of a labelled trace has a
    checker-accepted certificate concluding its claim at its label. -/
theorem CertTrace.certified {Γ : Context}
    (hwf : contextWF Γ = true)
    (huniq : ∀ u α', (supportEntries Γ (.atom u) α').length ≤ 1)
    {T : List (RunClaim × Provenance)} (h : CertTrace Γ T) :
    ∀ c ∈ T, ∃ d : Derivation,
      checkDerivation d = Except.ok () ∧
      d.conclusion = ⟨Γ, .term (cellTC c)⟩ := by
  induction h with
  | nil => intro c hc; exact absurd hc (List.not_mem_nil)
  | event T u a tok ht hsupp ih =>
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ih c hc
      · rw [List.mem_singleton] at hc
        subst hc
        refine ⟨expNode Γ u (fun _ => tok) (.atom a) 0, ?_, rfl⟩
        exact expNode_accepted Γ u (fun _ => tok) (.atom a) 0 hwf
          (supportEntries_length_one hsupp (huniq u (.atom a)))
  | sampling T t α sources f ht hmem hterm hsingle hprov1 hdisj hne hatom
      hgr hf ih =>
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ih c hc
      · rw [List.mem_singleton] at hc
        subst hc
        obtain ⟨ds, hf2⟩ := exists_certs sources
          (fun s hs => ih s (hmem s hs))
        obtain ⟨hm, hctx, hacc, hlen⟩ := forall₂_cert_facts hf2
        have hprovs : (sources.map cellTC).map (·.prov)
            = sources.map (·.2) := by
          simp [List.map_map, cellTC, Function.comp]
        have hcount : ((sources.map cellTC).filter (·.output == α)).length
            = (sources.filter (fun s => s.1.output == α)).length := by
          rw [length_filter_map]
          rfl
        have hok := samplingNode_ok Γ t α ds (sources.map cellTC) f hwf
          (by
            intro hcon
            rw [hcon] at hlen
            exact hne (List.length_eq_zero_iff.mp hlen.symm))
          hm hctx hacc
          (by
            intro tc htc
            obtain ⟨s, hs, rfl⟩ := List.mem_map.mp htc
            exact ⟨hprov1 s hs, hsingle s hs, rfl⟩)
          (by
            intro tc htc
            obtain ⟨s, hs, rfl⟩ := List.mem_map.mp htc
            exact hterm s hs)
          (by rw [hprovs]; exact hdisj)
          (by rw [hcount, hlen]; exact hf)
        refine ⟨_, hok, ?_⟩
        rw [hprovs, hlen]
        rfl
  | update T t α n m f g h σf σg ht hn hm hfmem hgmem hdisj hh ih =>
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ih c hc
      · rw [List.mem_singleton] at hc
        subst hc
        obtain ⟨d1, hacc1, hc1⟩ := ih _ hfmem
        obtain ⟨d2, hacc2, hc2⟩ := ih _ hgmem
        exact ⟨_, updateNode_ok Γ d1 d2 t α n m f g h σf σg hwf
          hacc1 hacc2 hc1 hc2 hn hm hdisj hh, rfl⟩
  | sumIntro T t n α β f g h σ ht hdisj hfmem hgmem hh ih =>
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ih c hc
      · rw [List.mem_singleton] at hc
        subst hc
        obtain ⟨d1, hacc1, hc1⟩ := ih _ hfmem
        obtain ⟨d2, hacc2, hc2⟩ := ih _ hgmem
        exact ⟨_, iPlusNode_ok Γ d1 d2 t α β n f g h σ hwf
          hacc1 hacc2 hc1 hc2 hdisj hh, rfl⟩
  | sumElim T t n α β r q h σ ht hdisj hsmem hqmem hh ih =>
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ih c hc
      · rw [List.mem_singleton] at hc
        subst hc
        obtain ⟨d1, hacc1, hc1⟩ := ih _ hsmem
        obtain ⟨d2, hacc2, hc2⟩ := ih _ hqmem
        exact ⟨_, ePlusRNode_ok Γ d1 d2 t α β n r q h σ hwf
          hacc1 hacc2 hc1 hc2 hdisj hh, rfl⟩

/-- Every cell of a labelled trace is derivable in the calculus. -/
theorem CertTrace.derivable {Γ : Context}
    (hwf : contextWF Γ = true)
    (huniq : ∀ u α', (supportEntries Γ (.atom u) α').length ≤ 1)
    {T : List (RunClaim × Provenance)} (h : CertTrace Γ T) :
    ∀ c ∈ T, Derivable ⟨Γ, .term (cellTC c)⟩ := by
  intro c hc
  obtain ⟨d, hacc, hconc⟩ := h.certified hwf huniq c hc
  have := checker_sound d hacc
  rwa [hconc] at this

end TPTND