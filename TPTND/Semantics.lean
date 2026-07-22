import TPTND
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # A measure-theoretic semantics for the TPTND core fragment

This file gives the calculus a model theory, in three honestly-scoped
layers:

1. **Event semantics for outputs.**  A `Model` is a probability space
   together with, for every variable, an interpretation of atomic
   outputs as measurable events.  Compound outputs evaluate by
   complement/union/intersection; a variable's probability of an output
   is the measure of its event.

2. **Counting semantics for the data layer.**  Frequency judgements are
   records about *realized samples*, not probabilistic claims; their
   aggregation rules (`update`) are exact statements about counting,
   proven as such (`freq_append`).

3. **What is deliberately excluded.**  The trust layer internalizes a
   frequentist hypothesis test: its "95%" is a property of the
   *procedure* under repeated sampling, not a truth condition of any
   single certificate, so `Trust`/`UTrust` judgements have no
   truth-functional semantics to be sound against (see the paper's
   discussion).  The arrow annotation is a conditional probability and
   is likewise deferred; `eval` gives `⇒` its material reading only so
   that evaluation is total, and no soundness lemma below uses it.

The payoff is that the audit-critical side conditions of the checker
are *semantically certified*:

* `eval_disjoint_of_syntacticallyDisjoint` — the checker's
  `Output.syntacticallyDisjoint` (positivity + disjoint atoms) really
  implies event-disjointness, in every model whose atoms are disjoint.
  Positivity is essential: with `α = ¬a`, `β = b` the atom sets are
  disjoint but the events overlap, which is exactly the unsoundness the
  audit found and the checker now rejects.
* `sound_IPlus` / `prob_EPlusL` — the I+/E+ arithmetic is measure
  additivity.
* `prob_prod_of_indep` — the I× product is exactly the independence
  equation recorded by the `#w` witness.
* `prob_neg` — output negation is complement probability.
* `mass_le_one_of_disjoint_pair` — the wf(Γ) mass bound is a necessary
  condition for satisfiability: two satisfied exact assumptions about
  disjoint events cannot carry total mass above 1.
-/

namespace TPTND

open MeasureTheory

/-- A model of the core fragment: a probability space and, for each
    variable name, an interpretation of atomic outputs as measurable
    events. -/
structure Model where
  Ω : Type*
  mΩ : MeasurableSpace Ω
  μ : @Measure Ω mΩ
  isProb : IsProbabilityMeasure μ
  interp : String → String → Set Ω
  measurable_interp : ∀ x a, MeasurableSet (interp x a)

attribute [instance] Model.mΩ Model.isProb

/-- Evaluate an output to an event, relative to a variable.
    (`⇒` gets the material reading purely for totality; no lemma in this
    file relies on it.) -/
def Model.eval (M : Model) (x : String) : Output → Set M.Ω
  | .atom a   => M.interp x a
  | .neg α    => (M.eval x α)ᶜ
  | .sum α β  => M.eval x α ∪ M.eval x β
  | .prod α β => M.eval x α ∩ M.eval x β
  | .arr α _ β => (M.eval x α)ᶜ ∪ M.eval x β

theorem Model.measurable_eval (M : Model) (x : String) :
    ∀ α : Output, MeasurableSet (M.eval x α)
  | .atom a   => M.measurable_interp x a
  | .neg α    => (M.measurable_eval x α).compl
  | .sum α β  => (M.measurable_eval x α).union (M.measurable_eval x β)
  | .prod α β => (M.measurable_eval x α).inter (M.measurable_eval x β)
  | .arr α _ β => ((M.measurable_eval x α).compl).union (M.measurable_eval x β)

/-- The probability a model assigns to variable `x` producing output `α`. -/
noncomputable def Model.prob (M : Model) (x : String) (α : Output) : ℝ :=
  (M.μ (M.eval x α)).toReal

/-- Truth of a probability constraint at a real value. -/
def Constraint.sat (c : Constraint) (r : ℝ) : Prop :=
  match c with
  | .exact p               => r = (p.val : ℝ)
  | .interval lo hi        => (lo.val : ℝ) ≤ r ∧ r ≤ (hi.val : ℝ)
  | .outsideInterval lo hi => r < (lo.val : ℝ) ∨ (hi.val : ℝ) < r
  | .unknown               => True

/-- A model satisfies a context entry when the entry's constraint holds
    of the model's probability for that variable and output. -/
def Model.satEntry (M : Model) (e : ContextEntry) : Prop :=
  e.constraint.sat (M.prob e.name e.output)

/-- A model satisfies a context when it satisfies every entry. -/
def Model.satCtx (M : Model) (Γ : Context) : Prop :=
  ∀ e ∈ Γ, M.satEntry e

/-- The intended reading of atoms: for a fixed variable, distinct atomic
    outputs name pairwise-disjoint elementary events. -/
def Model.AtomsDisjoint (M : Model) (x : String) : Prop :=
  ∀ a b, a ≠ b → M.interp x a ∩ M.interp x b = ∅

-- ============================================================================
-- The syntactic-disjointness bridge (justifies the I+ side condition)
-- ============================================================================

/-- Every point of a *positive* output's event lies in the event of one
    of its atoms.  (Fails for `neg`/`arr`, which is why the checker's
    disjointness test requires positivity.) -/
theorem Model.eval_pos_subset (M : Model) (x : String) :
    ∀ α : Output, α.isPositive = true →
      ∀ ω ∈ M.eval x α, ∃ a ∈ α.atoms, ω ∈ M.interp x a := by
  intro α
  induction α with
  | atom a =>
      intro _ ω hω
      exact ⟨a, by simp [Output.atoms], hω⟩
  | neg α ih =>
      intro h; simp [Output.isPositive] at h
  | arr α β ih1 ih2 =>
      intro h; simp [Output.isPositive] at h
  | sum α β ih1 ih2 =>
      intro h ω hω
      simp only [Output.isPositive, Bool.and_eq_true] at h
      rcases hω with hω | hω
      · obtain ⟨a, ha, hmem⟩ := ih1 h.1 ω hω
        exact ⟨a, by simp [Output.atoms, Finset.mem_union, ha], hmem⟩
      · obtain ⟨a, ha, hmem⟩ := ih2 h.2 ω hω
        exact ⟨a, by simp [Output.atoms, Finset.mem_union, ha], hmem⟩
  | prod α β ih1 ih2 =>
      intro h ω hω
      simp only [Output.isPositive, Bool.and_eq_true] at h
      obtain ⟨a, ha, hmem⟩ := ih1 h.1 ω hω.1
      exact ⟨a, by simp [Output.atoms, Finset.mem_union, ha], hmem⟩

/-- **Soundness of the checker's disjointness test.**  In any model whose
    atoms are pairwise disjoint, `Output.syntacticallyDisjoint α β = true`
    implies the events of `α` and `β` are disjoint. -/
theorem Model.eval_disjoint_of_syntacticallyDisjoint
    (M : Model) (x : String) (hM : M.AtomsDisjoint x)
    {α β : Output} (h : Output.syntacticallyDisjoint α β = true) :
    M.eval x α ∩ M.eval x β = ∅ := by
  unfold Output.syntacticallyDisjoint at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hposα, hposβ⟩, hatoms⟩ := h
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hα hβ
  obtain ⟨a, ha, hmema⟩ := M.eval_pos_subset x α hposα ω hα
  obtain ⟨b, hb, hmemb⟩ := M.eval_pos_subset x β hposβ ω hβ
  by_cases hab : a = b
  · subst hab
    have : a ∈ α.atoms ∩ β.atoms := Finset.mem_inter.mpr ⟨ha, hb⟩
    rw [hatoms] at this
    exact Finset.notMem_empty a this
  · have := hM a b hab
    have hmem : ω ∈ M.interp x a ∩ M.interp x b := ⟨hmema, hmemb⟩
    rw [this] at hmem
    exact hmem

-- ============================================================================
-- Measure-level soundness of the connective arithmetic
-- ============================================================================

/-- I+ arithmetic is measure additivity: for disjoint events,
    `P(α + β) = P(α) + P(β)`. -/
theorem Model.prob_sum_of_disjoint (M : Model) (x : String) {α β : Output}
    (hdisj : M.eval x α ∩ M.eval x β = ∅) :
    M.prob x (.sum α β) = M.prob x α + M.prob x β := by
  unfold Model.prob
  have hd : Disjoint (M.eval x α) (M.eval x β) :=
    Set.disjoint_iff_inter_eq_empty.mpr hdisj
  have : M.eval x (.sum α β) = M.eval x α ∪ M.eval x β := rfl
  rw [this, measure_union hd (M.measurable_eval x β)]
  exact ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)

/-- **Semantic soundness of the I+ side conditions**: syntactic
    disjointness (as the checker tests it) licenses the probability sum,
    in every atoms-disjoint model. -/
theorem Model.sound_IPlus (M : Model) (x : String) (hM : M.AtomsDisjoint x)
    {α β : Output} (h : Output.syntacticallyDisjoint α β = true) :
    M.prob x (.sum α β) = M.prob x α + M.prob x β :=
  M.prob_sum_of_disjoint x (M.eval_disjoint_of_syntacticallyDisjoint x hM h)

/-- E+ arithmetic: recover a summand by subtraction. -/
theorem Model.prob_EPlusL (M : Model) (x : String) (hM : M.AtomsDisjoint x)
    {α β : Output} (h : Output.syntacticallyDisjoint α β = true) :
    M.prob x β = M.prob x (.sum α β) - M.prob x α := by
  have := M.sound_IPlus x hM h
  linarith

/-- I× arithmetic under the independence equation recorded by the `#w`
    witness (this equation is Mathlib's characterization of independent
    events): `P(α × β) = P(α) · P(β)`. -/
theorem Model.prob_prod_of_indep (M : Model) (x : String) {α β : Output}
    (h : M.μ (M.eval x α ∩ M.eval x β)
           = M.μ (M.eval x α) * M.μ (M.eval x β)) :
    M.prob x (.prod α β) = M.prob x α * M.prob x β := by
  unfold Model.prob
  have : M.eval x (.prod α β) = M.eval x α ∩ M.eval x β := rfl
  rw [this, h, ENNReal.toReal_mul]

/-- Output negation is complement probability: `P(¬α) = 1 − P(α)`. -/
theorem Model.prob_neg (M : Model) (x : String) (α : Output) :
    M.prob x (.neg α) = 1 - M.prob x α := by
  unfold Model.prob
  have hcompl : M.eval x (.neg α) = (M.eval x α)ᶜ := rfl
  have hadd := measure_add_measure_compl (μ := M.μ) (M.measurable_eval x α)
  rw [measure_univ] at hadd
  have := congrArg ENNReal.toReal hadd
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ENNReal.toReal_one] at this
  rw [hcompl]
  linarith

-- ============================================================================
-- Semantic necessity of the wf(Γ) mass bound
-- ============================================================================

/-- **The wf(Γ) gate is semantically necessary**: if a model satisfies two
    exact assumptions about the same variable whose events are disjoint,
    their masses cannot sum above 1.  (The n-ary generalization is a
    routine induction; the two-entry case is the shape exercised by the
    checker's duplicate-assumption scenarios.) -/
theorem Model.mass_le_one_of_disjoint_pair (M : Model)
    {x : String} {α β : Output} {p q : Prob}
    (hα : M.prob x α = (p.val : ℝ)) (hβ : M.prob x β = (q.val : ℝ))
    (hdisj : M.eval x α ∩ M.eval x β = ∅) :
    (p.val : ℝ) + (q.val : ℝ) ≤ 1 := by
  have hsum := M.prob_sum_of_disjoint x hdisj
  rw [hα, hβ] at hsum
  have hle : M.μ (M.eval x (.sum α β)) ≤ 1 := prob_le_one
  have := ENNReal.toReal_mono ENNReal.one_ne_top hle
  rw [ENNReal.toReal_one] at this
  unfold Model.prob at hsum
  linarith

-- ============================================================================
-- Counting semantics for the data layer (UPDATE is exact on samples)
-- ============================================================================

/-- **UPDATE is semantically exact on realized data**: the frequency of a
    property in the concatenation of two sample lists is precisely the
    sample-size-weighted average that the `update` rule computes.
    Frequency judgements are records about data; their aggregation is
    counting, not probability. -/
theorem freq_append {ω : Type*} (p : ω → Bool) (l₁ l₂ : List ω)
    (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    ((l₁ ++ l₂).countP p : ℚ) / ((l₁ ++ l₂).length : ℚ)
      = ((l₁.length : ℚ) * ((l₁.countP p : ℚ) / (l₁.length : ℚ))
         + (l₂.length : ℚ) * ((l₂.countP p : ℚ) / (l₂.length : ℚ)))
        / ((l₁.length : ℚ) + (l₂.length : ℚ)) := by
  have hn₁ : (l₁.length : ℚ) ≠ 0 := by
    exact_mod_cast fun h => h₁ (List.length_eq_zero_iff.mp (by exact_mod_cast h))
  have hn₂ : (l₂.length : ℚ) ≠ 0 := by
    exact_mod_cast fun h => h₂ (List.length_eq_zero_iff.mp (by exact_mod_cast h))
  rw [List.countP_append, List.length_append]
  push_cast
  field_simp

-- ============================================================================
-- 7a. Semantic justification of wf(Γ)
-- ============================================================================

/-- Folding `max` stays below any bound that dominates every input. -/
private theorem foldl_max_le {B : ℝ} :
    ∀ (ms : List ℚ) (m : ℚ), ((m : ℚ) : ℝ) ≤ B → (∀ a ∈ ms, ((a : ℚ) : ℝ) ≤ B) →
      ((ms.foldl max m : ℚ) : ℝ) ≤ B
  | [], _, hm, _ => hm
  | a :: t, m, hm, hms => by
      rw [List.foldl_cons]
      exact foldl_max_le t (max m a)
        (by rw [Rat.cast_max]; exact max_le hm (hms a (List.mem_cons_self)))
        (fun b hb => hms b (List.mem_cons_of_mem a hb))

/-- Probabilities are non-negative. -/
theorem Model.prob_nonneg (M : Model) (x : String) (α : Output) :
    0 ≤ M.prob x α := ENNReal.toReal_nonneg

/-- A finite family of pairwise-disjoint events carries total mass at most 1. -/
theorem Model.sum_prob_le_one (M : Model) (x : String) (O : Finset Output)
    (hdisj : ∀ α ∈ O, ∀ β ∈ O, α ≠ β → M.eval x α ∩ M.eval x β = ∅) :
    ∑ α ∈ O, M.prob x α ≤ 1 := by
  have hpd : (O : Set Output).PairwiseDisjoint (fun α => M.eval x α) := by
    intro α hα β hβ hne
    rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
    exact hdisj α hα β hβ hne
  have hmeas : ∀ α ∈ O, MeasurableSet (M.eval x α) := fun α _ => M.measurable_eval x α
  have hunion : M.μ (⋃ α ∈ O, M.eval x α) = ∑ α ∈ O, M.μ (M.eval x α) :=
    measure_biUnion_finset hpd hmeas
  have hfin : ∀ α ∈ O, M.μ (M.eval x α) ≠ ⊤ := fun α _ => measure_ne_top _ _
  have hcast : ∑ α ∈ O, M.prob x α = (∑ α ∈ O, M.μ (M.eval x α)).toReal := by
    unfold Model.prob
    rw [ENNReal.toReal_sum hfin]
  rw [hcast, ← hunion]
  have hle : M.μ (⋃ α ∈ O, M.eval x α) ≤ 1 := prob_le_one
  have := ENNReal.toReal_mono ENNReal.one_ne_top hle
  simpa using this

/-- A satisfied assumption never commits more mass than the event actually
    has: `exact p` commits exactly `p`, an interval commits its lower bound,
    and `¬[ℓ,h]` / unknown commit nothing. -/
theorem Model.contribution_le_prob (M : Model) {e : ContextEntry}
    (hsat : M.satEntry e) :
    ((exactMass e + intervalLower e : ℚ) : ℝ) ≤ M.prob e.name e.output := by
  unfold Model.satEntry Constraint.sat at hsat
  unfold exactMass intervalLower
  cases hc : e.constraint with
  | exact p => rw [hc] at hsat; simp [hsat]
  | interval lo hi => rw [hc] at hsat; push_cast; simpa using hsat.1
  | outsideInterval lo hi => simpa using M.prob_nonneg e.name e.output
  | unknown => simpa using M.prob_nonneg e.name e.output

/-- The mass a `(variable, output)` group commits is at most the event's
    probability: the group's least commitment is bounded by any member's, and
    each member is bounded by satisfaction. -/
theorem Model.groupMass_le_prob (M : Model) (entries : List ContextEntry)
    (x : String) (α : Output)
    (hname : ∀ e ∈ entries, e.name = x)
    (hsat : ∀ e ∈ entries, M.satEntry e) :
    ((groupMass entries α : ℚ) : ℝ) ≤ M.prob x α := by
  unfold groupMass
  rcases hgrp : (entries.filter (fun e => e.output == α)).map
      (fun e => exactMass e + intervalLower e) with _ | ⟨m, ms⟩
  · simpa using M.prob_nonneg x α
  · -- every member's commitment is bounded by the event's probability,
    -- so the group's maximum is too
    have hbound : ∀ v ∈ (entries.filter (fun e => e.output == α)).map
        (fun e => exactMass e + intervalLower e), ((v : ℚ) : ℝ) ≤ M.prob x α := by
      intro v hv
      obtain ⟨e, he, hev⟩ := List.mem_map.mp hv
      rw [List.mem_filter] at he
      have hout : e.output = α := by simpa using he.2
      have := M.contribution_le_prob (hsat e he.1)
      rw [hname e he.1, hout] at this
      rw [← hev]; exact this
    rw [hgrp] at hbound
    exact foldl_max_le ms m (hbound m (List.mem_cons_self))
      (fun a ha => hbound a (List.mem_cons_of_mem m ha))

/-- **`wf(Γ)`'s mass bound is semantically necessary.**  If a model satisfies
    `Γ` and the outputs `Γ` constrains for one variable name pairwise-disjoint
    events, then the per-variable committed mass really is at most 1.

    The checker gates every node on `contextWF`, and the paper's admissibility
    discipline rests on this bound; nothing previously connected it to a model.
    (`mass_le_one_of_disjoint_pair` covered only two exact entries.) -/
theorem Model.variableMass_le_one (M : Model) (Γ : Context) (x : String)
    (hsat : M.satCtx Γ)
    (hdisj : ∀ α ∈ (Γ.filter (fun e => e.name == x)).map (·.output),
             ∀ β ∈ (Γ.filter (fun e => e.name == x)).map (·.output),
             α ≠ β → M.eval x α ∩ M.eval x β = ∅) :
    ((variableMass Γ x : ℚ) : ℝ) ≤ 1 := by
  classical
  have hname : ∀ e ∈ Γ.filter (fun e => e.name == x), e.name = x := by
    intro e he; rw [List.mem_filter] at he; simpa using he.2
  have hsat' : ∀ e ∈ Γ.filter (fun e => e.name == x), M.satEntry e := by
    intro e he; rw [List.mem_filter] at he; exact hsat e he.1
  rw [variableMass_eq]
  push_cast
  simp only [List.map_map, Function.comp_def]
  have h1 :
      ((((Γ.filter (fun e => e.name == x)).map (·.output)).dedup).map
        (fun α => ((groupMass (Γ.filter (fun e => e.name == x)) α : ℚ) : ℝ))).sum
      ≤ ((((Γ.filter (fun e => e.name == x)).map (·.output)).dedup).map
        (fun α => M.prob x α)).sum :=
    List.sum_le_sum (fun α _ =>
      M.groupMass_le_prob (Γ.filter (fun e => e.name == x)) x α hname hsat')
  refine le_trans h1 ?_
  rw [← List.sum_toFinset _ (List.nodup_dedup _)]
  refine M.sum_prob_le_one x _ ?_
  intro α hα β hβ hne
  rw [List.mem_toFinset, List.mem_dedup] at hα hβ
  exact hdisj α hα β hβ hne

-- ============================================================================
-- (b) Independence of distinct variables — justifying the I× witness
-- ============================================================================

/-- **Distinct variables denote independent events.**

    This is the semantic content of the paper's `Γ #w Δ` witness, and it must
    be a hypothesis on the model rather than a theorem about it: in an
    arbitrary `Model` the sets `interp x a` and `interp y b` are unconstrained,
    so variable-disjointness alone implies nothing.  The situation is exactly
    parallel to `AtomsDisjoint`, which is what makes the syntactic disjointness
    test sound for `I+`. -/
def Model.VarsIndependent (M : Model) : Prop :=
  ∀ x y : String, x ≠ y → ∀ α β : Output,
    M.μ (M.eval x α ∩ M.eval y β) = M.μ (M.eval x α) * M.μ (M.eval y β)

/-- The product law for events of distinct variables. -/
theorem Model.prob_inter_of_varsIndep (M : Model) (hM : M.VarsIndependent)
    {x y : String} (hxy : x ≠ y) (α β : Output) :
    (M.μ (M.eval x α ∩ M.eval y β)).toReal = M.prob x α * M.prob y β := by
  unfold Model.prob
  rw [hM x y hxy α β, ENNReal.toReal_mul]

/-- **Soundness of the checker's independence test.**

    `independentContexts` accepts only when Γ and Δ constrain disjoint sets of
    variables.  Every assumption of Γ then concerns a different variable from
    every assumption of Δ, so in any model where distinct variables are
    independent the product law applies to their events.

    This is the analogue, for `I×`, of `eval_disjoint_of_syntacticallyDisjoint`
    for `I+`: it is what turns a syntactic side condition into a semantic
    guarantee, rather than leaving the producer's `#w` witness unchecked. -/
theorem Model.sound_independentContexts (M : Model) (hM : M.VarsIndependent)
    {Γ Δ : Context} (h : independentContexts Γ Δ = true)
    {e e' : ContextEntry} (he : e ∈ Γ) (he' : e' ∈ Δ) :
    (M.μ (M.eval e.name e.output ∩ M.eval e'.name e'.output)).toReal
      = M.prob e.name e.output * M.prob e'.name e'.output := by
  refine M.prob_inter_of_varsIndep hM ?_ _ _
  -- the syntactic test forces the two variable names apart
  unfold independentContexts at h
  rw [List.all_eq_true] at h
  have hmemΓ : e.name ∈ variableNames Γ := by
    unfold variableNames
    rw [List.mem_dedup]
    exact List.mem_map_of_mem he
  have hmemΔ : e'.name ∈ variableNames Δ := by
    unfold variableNames
    rw [List.mem_dedup]
    exact List.mem_map_of_mem he'
  have := h e.name hmemΓ
  simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at this
  intro hEq
  exact this (hEq ▸ hmemΔ)

-- ============================================================================
-- (a) Conditional probability — what E×L/E×R actually compute
-- ============================================================================

/-- `P(α | β)` for a single variable.  The calculus has no conditional
    judgement, but the product elimination rules compute this quantity whether
    or not they say so. -/
noncomputable def Model.condProb (M : Model) (x : String) (α β : Output) : ℝ :=
  (M.μ (M.eval x α ∩ M.eval x β)).toReal / M.prob x β

/-- **The multiplication law**: `P(α × β) = P(α | β) · P(β)`. -/
theorem Model.prob_prod_eq_condProb_mul (M : Model) (x : String) (α β : Output)
    (hβ : M.prob x β ≠ 0) :
    M.prob x (.prod α β) = M.condProb x α β * M.prob x β := by
  unfold Model.condProb
  have hev : M.prob x (.prod α β) = (M.μ (M.eval x α ∩ M.eval x β)).toReal := rfl
  rw [hev]
  field_simp

/-- **What `E×L`/`E×R` actually compute.**

    Dividing the joint probability by one component yields the CONDITIONAL
    probability `P(α | β)`, not the marginal `P(α)`.  The two coincide exactly
    when the components are independent.

    This is the precise reason for the expected-mode restriction on the
    product eliminations: `r/q` is a marginal only under independence, a
    conditional otherwise.  A conditional judgement in the syntax would let
    the calculus say directly what the division derives. -/
theorem Model.condProb_eq_prob_of_indep (M : Model) (x : String) {α β : Output}
    (hβ : M.prob x β ≠ 0)
    (hindep : M.μ (M.eval x α ∩ M.eval x β)
      = M.μ (M.eval x α) * M.μ (M.eval x β)) :
    M.condProb x α β = M.prob x α := by
  unfold Model.condProb
  rw [hindep, ENNReal.toReal_mul]
  unfold Model.prob at hβ ⊢
  field_simp

/-- Conditioning on the whole space changes nothing: `P(α | β) = P(α)` when
    `β` is almost sure. -/
theorem Model.condProb_of_prob_one (M : Model) (x : String) {α β : Output}
    (hβ : M.μ (M.eval x β) = 1) :
    M.condProb x α β = (M.μ (M.eval x α ∩ M.eval x β)).toReal := by
  unfold Model.condProb Model.prob
  rw [hβ]
  simp

end TPTND
