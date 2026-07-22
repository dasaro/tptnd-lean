import TPTND.Semantics
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw

/-! # The run space: repeated sampling from a model

This is the measure-theoretic foundation the operational layer needs.  A
`Model` (see `TPTND.Semantics`) describes ONE draw.  A derivation, though,
talks about `tₙ : α_f` — the frequency of `α` over `n` runs — so to say what
that frequency *means* we need a probability space of infinite run sequences.

The construction is the standard one and Mathlib carries it: the countable
product `Measure.infinitePi` of copies of the model's measure.  Notably it
needs only `MeasurableSpace` and `IsProbabilityMeasure` on the factor — no
standard-Borel or Polish hypothesis — so it applies to an arbitrary `Model.Ω`.

The payoff is `Model.frequency_tendsto_prob` at the bottom: the observed
frequency of `α` over the first `n` runs converges almost surely to its
probability under the model.  The tie between an operational "run produced
`α`" and the semantic event is definitional: `hit` is *defined* from
`Model.eval`.
-/

namespace TPTND

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

/-- The run space of a model: countably many independent repetitions.
    A point `ω : ℕ → M.Ω` is one infinite sequence of runs. -/
noncomputable def Model.runSpace (M : Model) : Measure (ℕ → M.Ω) :=
  Measure.infinitePi (fun _ : ℕ => M.μ)

instance (M : Model) : IsProbabilityMeasure M.runSpace := by
  unfold Model.runSpace; infer_instance

/-- The event that a single draw produces `α`, for variable `x`. -/
noncomputable def Model.hitSet (M : Model) (x : String) (α : Output) : Set M.Ω :=
  M.eval x α

/-- `hit x α i ω = 1` when run `i` of `ω` produced `α`, else `0`.

    This is the bridge between the syntax and the measure: the indicator is
    built from `Model.eval`, so an operational "run produced α" and the
    semantic event `eval x α` are the same thing by definition rather than by
    stipulation. -/
noncomputable def Model.hit (M : Model) (x : String) (α : Output) (i : ℕ) :
    (ℕ → M.Ω) → ℝ :=
  fun ω => Set.indicator (M.hitSet x α) (fun _ => (1 : ℝ)) (ω i)

theorem Model.measurableSet_hitSet (M : Model) (x : String) (α : Output) :
    MeasurableSet (M.hitSet x α) :=
  M.measurable_eval x α

/-- The single-draw indicator is measurable. -/
theorem Model.measurable_indicator (M : Model) (x : String) (α : Output) :
    Measurable (fun o : M.Ω => Set.indicator (M.hitSet x α) (fun _ => (1 : ℝ)) o) :=
  (measurable_const.indicator (M.measurableSet_hitSet x α))

theorem Model.measurable_hit (M : Model) (x : String) (α : Output) (i : ℕ) :
    Measurable (M.hit x α i) :=
  (M.measurable_indicator x α).comp (measurable_pi_apply i)

/-- Pointwise unfolding, as a genuine equation (`rw` cannot use a bare def). -/
theorem Model.hit_apply (M : Model) (x : String) (α : Output) (i : ℕ)
    (ω : ℕ → M.Ω) :
    M.hit x α i ω = Set.indicator (M.hitSet x α) (fun _ => (1 : ℝ)) (ω i) := rfl

/-- `hit i` factors as the single-draw indicator after the `i`-th projection.
    Every measure-level fact below is this factorisation plus the fact that
    projections of a product measure are measure preserving. -/
theorem Model.hit_eq_comp (M : Model) (x : String) (α : Output) (i : ℕ) :
    M.hit x α i
      = (fun o : M.Ω => Set.indicator (M.hitSet x α) (fun _ => (1 : ℝ)) o)
        ∘ (fun ω : ℕ → M.Ω => ω i) := rfl

/-- Distinct runs are independent: this is exactly the coordinate
    independence of an infinite product measure. -/
theorem Model.iIndepFun_hit (M : Model) (x : String) (α : Output) :
    iIndepFun (M.hit x α) M.runSpace :=
  iIndepFun_infinitePi (fun _ => M.measurable_indicator x α)

/-- Every run is distributed like the first: the coordinate projections of a
    product measure are measure preserving. -/
theorem Model.identDistrib_hit (M : Model) (x : String) (α : Output) (i : ℕ) :
    IdentDistrib (M.hit x α i) (M.hit x α 0) M.runSpace M.runSpace := by
  have hmp : ∀ j : ℕ, MeasurePreserving (fun ω : ℕ → M.Ω => ω j) M.runSpace M.μ :=
    fun j => measurePreserving_eval_infinitePi (fun _ : ℕ => M.μ) j
  refine ⟨(M.measurable_hit x α i).aemeasurable,
          (M.measurable_hit x α 0).aemeasurable, ?_⟩
  have key : ∀ j : ℕ, M.runSpace.map (M.hit x α j)
      = M.μ.map (fun o : M.Ω => Set.indicator (M.hitSet x α) (fun _ => (1 : ℝ)) o) := by
    intro j
    rw [Model.hit_eq_comp,
        ← Measure.map_map (M.measurable_indicator x α) (measurable_pi_apply j),
        (hmp j).map_eq]
  rw [key i, key 0]

/-- Indicators are bounded, hence integrable on a probability space. -/
theorem Model.integrable_hit (M : Model) (x : String) (α : Output) (i : ℕ) :
    Integrable (M.hit x α i) M.runSpace := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (M.measurable_hit x α i).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Model.hit_apply]
  by_cases h : ω i ∈ M.hitSet x α
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- The expected value of one run's indicator is the probability of `α`. -/
theorem Model.integral_hit (M : Model) (x : String) (α : Output) :
    ∫ ω, M.hit x α 0 ω ∂M.runSpace = (M.μ (M.hitSet x α)).toReal := by
  have hmp : MeasurePreserving (fun ω : ℕ → M.Ω => ω 0) M.runSpace M.μ :=
    measurePreserving_eval_infinitePi (fun _ : ℕ => M.μ) 0
  have key : ∫ o, Set.indicator (M.hitSet x α) (fun _ => (1 : ℝ)) o ∂M.μ
      = ∫ ω, Set.indicator (M.hitSet x α) (fun _ => (1 : ℝ)) (ω 0) ∂M.runSpace := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map (measurable_pi_apply 0).aemeasurable
      (M.measurable_indicator x α).aestronglyMeasurable
  calc ∫ ω, M.hit x α 0 ω ∂M.runSpace
      = ∫ ω, Set.indicator (M.hitSet x α) (fun _ => (1 : ℝ)) (ω 0) ∂M.runSpace := by
        simp only [Model.hit_apply]
    _ = ∫ o, Set.indicator (M.hitSet x α) (fun _ => (1 : ℝ)) o ∂M.μ := key.symm
    _ = (M.μ (M.hitSet x α)).toReal := by
        rw [integral_indicator_const (1 : ℝ) (M.measurableSet_hitSet x α)]
        simp [measureReal_def]

/-- The observed frequency of `α` in the first `n` runs: the number of
    successful runs divided by `n`.

    This is deliberately the calculus's own definition — the `sampling` rule
    carries the side condition `f = |{i | αⁱ = α}| / n` — so that the limit
    theorem below is visibly about the `f` that appears in a judgement
    `tₙ : α_f`, and not about some other average that merely resembles it. -/
noncomputable def Model.observedFreq (M : Model) (x : String) (α : Output)
    (n : ℕ) (ω : ℕ → M.Ω) : ℝ :=
  open scoped Classical in
  (n : ℝ)⁻¹ * (((range n).filter (fun i => ω i ∈ M.hitSet x α)).card : ℝ)

/-- Counting successful runs is averaging the indicators. -/
theorem Model.observedFreq_eq (M : Model) (x : String) (α : Output)
    (n : ℕ) (ω : ℕ → M.Ω) :
    M.observedFreq x α n ω = (n : ℝ)⁻¹ • (∑ i ∈ range n, M.hit x α i ω) := by
  classical
  simp only [Model.observedFreq, Model.hit_apply, Set.indicator_apply, smul_eq_mul]
  congr 1
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
      nsmul_eq_mul, mul_one]

/-- **The observed frequency converges to the model probability.**

    `(1/n) · Σ_{i<n} hit x α i ω` is precisely the frequency of `α` in the
    first `n` runs of `ω`, so this says: almost surely, the frequency a
    derivation would record converges to the probability the context
    assumes. -/
theorem Model.frequency_tendsto_prob (M : Model) (x : String) (α : Output) :
    ∀ᵐ ω ∂M.runSpace,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • (∑ i ∈ range n, M.hit x α i ω)) atTop
        (𝓝 (M.μ (M.hitSet x α)).toReal) := by
  have h := strong_law_ae (X := M.hit x α) (μ := M.runSpace)
    (M.integrable_hit x α 0)
    (fun i j hij => (M.iIndepFun_hit x α).indepFun hij)
    (fun i => M.identDistrib_hit x α i)
  simpa [Model.integral_hit] using h

/-- The same statement in the calculus's own vocabulary: the `f` that a
    derivation records for `tₙ : α_f` converges almost surely to the
    probability its context assigns to `α`.

    The connection between the recorded `f` and the context's probability is
    by construction: `hit` is defined from `Model.eval`, so a draw counts as
    producing `α` exactly when it lands in the event the context's assumption
    denotes. -/
theorem Model.observedFreq_tendsto_prob (M : Model) (x : String) (α : Output) :
    ∀ᵐ ω ∂M.runSpace,
      Tendsto (fun n : ℕ => M.observedFreq x α n ω) atTop
        (𝓝 (M.μ (M.hitSet x α)).toReal) := by
  filter_upwards [M.frequency_tendsto_prob x α] with ω hω
  simpa only [Model.observedFreq_eq] using hω

end TPTND
