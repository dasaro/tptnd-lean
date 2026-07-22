import TPTND.Operational.RunSpace
import Mathlib.Probability.Moments.Variance

/-! # What a Trust certificate guarantees

`IT` fires when the model probability `p` lies in the interval
`f ± z·√(p(1−p)/n)` computed from the data — equivalently, when

  `|f − p| ≤ z · √(p(1−p)/n)`.

Up to now that was pure arithmetic: nothing connected the test to any
statistical property of the model, even though trust certificates are the
whole point of the calculus.  This file supplies the missing guarantee.

The result is a **Chebyshev bound**, not a normal approximation:

  if the model is correct, the probability that the test *fails* is at
  most `1/z²`.

The checker uses `z = √20 ≈ 4.4721` (`Arithmetic.zCheb`), for which the
bound is exactly `1/20 = 0.05` — a genuine 5 % level, at every finite `n`,
for every distribution, with no central limit theorem.  A certificate is
therefore not vacuous: a correct model is accepted with probability at
least `1 − 1/z² = 0.95`.

Two honest caveats.

* The theorem is about the **exact** acceptance region
  `|f − p| ≤ c·√(p(1−p)/n)`.  `Arithmetic.binomialCI` implements it with a
  rational Newton approximation of the square root; the error analysis of
  that approximation is not formalised, so the link between this theorem and
  the implemented interval is exact only up to that approximation.
* Chebyshev is loose.  Sharpening `1/z²` towards the nominal level needs a
  Berry–Esseen or exact-binomial argument, which is a separate project.
-/

namespace TPTND

open MeasureTheory ProbabilityTheory Filter Finset

/-- Indicators are bounded, hence square-integrable on a probability space. -/
theorem Model.memLp_hit (M : Model) (x : String) (α : Output) (i : ℕ) :
    MemLp (M.hit x α i) 2 M.runSpace := by
  refine MemLp.of_bound (M.measurable_hit x α i).aestronglyMeasurable 1 ?_
  filter_upwards with ω
  rw [Model.hit_apply]
  by_cases h : ω i ∈ M.hitSet x α
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- Every run has the same expectation: the probability of `α`. -/
theorem Model.integral_hit_eq (M : Model) (x : String) (α : Output) (i : ℕ) :
    ∫ ω, M.hit x α i ω ∂M.runSpace = (M.μ (M.hitSet x α)).toReal := by
  rw [(M.identDistrib_hit x α i).integral_eq]
  exact M.integral_hit x α

/-- An indicator squared is itself. -/
theorem Model.hit_sq (M : Model) (x : String) (α : Output) (i : ℕ) (ω : ℕ → M.Ω) :
    M.hit x α i ω * M.hit x α i ω = M.hit x α i ω := by
  rw [Model.hit_apply]
  by_cases h : ω i ∈ M.hitSet x α
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- **The variance of one run is `p(1−p)`.**  For an indicator `X² = X`, so
    `Var[X] = E[X] − E[X]² = p − p²`. -/
theorem Model.variance_hit (M : Model) (x : String) (α : Output) (i : ℕ) :
    variance (M.hit x α i) M.runSpace
      = (M.μ (M.hitSet x α)).toReal * (1 - (M.μ (M.hitSet x α)).toReal) := by
  have hsq : ∫ ω, (M.hit x α i ^ 2) ω ∂M.runSpace
      = (M.μ (M.hitSet x α)).toReal := by
    have hpt : ∀ ω, (M.hit x α i ^ 2) ω = M.hit x α i ω := by
      intro ω; simp only [Pi.pow_apply, sq]; exact M.hit_sq x α i ω
    simp only [hpt]
    exact M.integral_hit_eq x α i
  rw [variance_eq_sub (M.memLp_hit x α i), hsq, M.integral_hit_eq x α i]
  ring

/-- **The variance of the sample mean is `p(1−p)/n`.**

    Independence is what makes this work: the covariances between distinct
    runs vanish, so the variance of the sum is the sum of the variances. -/
theorem Model.variance_observedFreq (M : Model) (x : String) (α : Output)
    {n : ℕ} (hn : n ≠ 0) :
    variance (fun ω => M.observedFreq x α n ω) M.runSpace
      = (M.μ (M.hitSet x α)).toReal * (1 - (M.μ (M.hitSet x α)).toReal) / n := by
  classical
  set p := (M.μ (M.hitSet x α)).toReal with hp
  -- variance of the sum: off-diagonal covariances vanish by independence
  have hdiag : ∀ i ∈ range n,
      ∑ j ∈ range n, covariance (M.hit x α i) (M.hit x α j) M.runSpace
        = p * (1 - p) := by
    intro i hi
    rw [Finset.sum_eq_single i]
    · rw [covariance_self (M.measurable_hit x α i).aemeasurable]
      exact M.variance_hit x α i
    · intro j _ hji
      exact ((M.iIndepFun_hit x α).indepFun (Ne.symm hji)).covariance_eq_zero
        (M.memLp_hit x α i) (M.memLp_hit x α j)
    · intro hni; exact absurd hi hni
  have hsum : variance (fun ω => ∑ i ∈ range n, M.hit x α i ω) M.runSpace
      = n * (p * (1 - p)) := by
    rw [variance_fun_sum' (fun i _ => M.memLp_hit x α i),
        Finset.sum_congr rfl hdiag, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
  have hfun : (fun ω => M.observedFreq x α n ω)
      = fun ω => (n : ℝ)⁻¹ * (∑ i ∈ range n, M.hit x α i ω) := by
    funext ω; rw [M.observedFreq_eq]; simp
  rw [hfun, variance_const_mul, hsum]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp

/-- The sample mean is measurable. -/
theorem Model.measurable_observedFreq (M : Model) (x : String) (α : Output)
    (n : ℕ) : Measurable (fun ω => M.observedFreq x α n ω) := by
  have hfun : (fun ω => M.observedFreq x α n ω)
      = fun ω => (n : ℝ)⁻¹ * (∑ i ∈ range n, M.hit x α i ω) := by
    funext ω; rw [M.observedFreq_eq]; simp
  rw [hfun]
  exact measurable_const.mul (Finset.measurable_sum _ (fun i _ => M.measurable_hit x α i))

/-- The sample mean lies in `[0,1]`, hence is square-integrable. -/
theorem Model.memLp_observedFreq (M : Model) (x : String) (α : Output) (n : ℕ) :
    MemLp (fun ω => M.observedFreq x α n ω) 2 M.runSpace := by
  classical
  refine MemLp.of_bound (M.measurable_observedFreq x α n).aestronglyMeasurable 1 ?_
  filter_upwards with ω
  have hle : ((range n).filter (fun i => ω i ∈ M.hitSet x α)).card ≤ n := by
    simpa using Finset.card_filter_le (range n) (fun i => ω i ∈ M.hitSet x α)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Model.observedFreq]
  · have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      rw [Model.observedFreq]; positivity)]
    rw [Model.observedFreq]
    rw [inv_mul_le_iff₀ hnR, mul_one]
    exact_mod_cast hle

/-- The sample mean is unbiased: its expectation is exactly `p`. -/
theorem Model.integral_observedFreq (M : Model) (x : String) (α : Output)
    {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, M.observedFreq x α n ω ∂M.runSpace = (M.μ (M.hitSet x α)).toReal := by
  have hfun : (fun ω => M.observedFreq x α n ω)
      = fun ω => (n : ℝ)⁻¹ * (∑ i ∈ range n, M.hit x α i ω) := by
    funext ω; rw [M.observedFreq_eq]; simp
  rw [hfun, integral_const_mul,
      integral_finset_sum _ (fun i _ => M.integrable_hit x α i)]
  simp only [M.integral_hit_eq, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp

/-- `V / (c²·V) = 1/c²`, stated over plain reals so the rewrite is not
    obstructed by the local definitions in the proof below. -/
private theorem chebyshev_ratio {V c : ℝ} (hV : V ≠ 0) (hc : c ≠ 0) :
    V / (c ^ 2 * V) ≤ 1 / c ^ 2 := by
  refine le_of_eq ?_
  field_simp

/-- **A Trust certificate is not vacuous.**

    If the model is correct, the probability that the observed frequency
    falls outside the acceptance region `|f − p| ≤ c·√(p(1−p)/n)` is at most
    `1/c²`.  At the checker's `c = √20` that is exactly `0.05`.

    This is Chebyshev, so it holds at every finite `n` with no normality
    assumption; it is correspondingly looser than the nominal level. -/
theorem Model.trust_coverage (M : Model) (x : String) (α : Output)
    {n : ℕ} (hn : n ≠ 0) {c : ℝ} (hc : 0 < c)
    (hpos : 0 < (M.μ (M.hitSet x α)).toReal * (1 - (M.μ (M.hitSet x α)).toReal)) :
    M.runSpace {ω | c * Real.sqrt
        ((M.μ (M.hitSet x α)).toReal * (1 - (M.μ (M.hitSet x α)).toReal) / n)
        ≤ |M.observedFreq x α n ω - (M.μ (M.hitSet x α)).toReal| }
      ≤ ENNReal.ofReal (1 / c ^ 2) := by
  classical
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  set p := (M.μ (M.hitSet x α)).toReal with hp
  clear_value p
  have hVpos : 0 < p * (1 - p) / n := div_pos hpos hnR
  have hcV : 0 < c * Real.sqrt (p * (1 - p) / n) :=
    mul_pos hc (Real.sqrt_pos.mpr hVpos)
  have hE : ∫ ω, M.observedFreq x α n ω ∂M.runSpace = p := by
    rw [hp]; exact M.integral_observedFreq x α hn
  have hcheb := meas_ge_le_variance_div_sq (μ := M.runSpace)
    (M.memLp_observedFreq x α n) hcV
  rw [hE] at hcheb
  refine le_trans hcheb ?_
  apply ENNReal.ofReal_le_ofReal
  rw [M.variance_observedFreq x α hn, ← hp, mul_pow, Real.sq_sqrt hVpos.le]
  exact chebyshev_ratio (ne_of_gt hVpos) (ne_of_gt hc)

-- ============================================================================
-- Reaching the canonical 5% level, and power
-- ============================================================================

/-- **A provable 5% level.**  `trust_coverage` bounds the failure probability
    by `1/c²` for *any* `c`, so the canonical level is a matter of the
    constant: at `c = √20 ≈ 4.472` the bound is exactly `1/20 = 0.05`.

    This is the distribution-free price.  The familiar `z = 1.96` reaches 5%
    only through a normal approximation; justifying it would need a central
    limit theorem with a finite-`n` error term (Berry–Esseen), which is not
    available here.  Chebyshev buys an honest 5% at every finite `n` and for
    every distribution, in exchange for an interval `√20/1.96 ≈ 2.28` times
    wider. -/
theorem Model.trust_coverage_05 (M : Model) (x : String) (α : Output)
    {n : ℕ} (hn : n ≠ 0)
    (hpos : 0 < (M.μ (M.hitSet x α)).toReal * (1 - (M.μ (M.hitSet x α)).toReal)) :
    M.runSpace {ω | Real.sqrt 20 * Real.sqrt
        ((M.μ (M.hitSet x α)).toReal * (1 - (M.μ (M.hitSet x α)).toReal) / n)
        ≤ |M.observedFreq x α n ω - (M.μ (M.hitSet x α)).toReal| }
      ≤ ENNReal.ofReal (1 / 20) := by
  have h20 : (0 : ℝ) < Real.sqrt 20 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (Real.sqrt 20) ^ 2 = 20 := Real.sq_sqrt (by norm_num)
  have := M.trust_coverage x α hn h20 hpos
  rwa [hsq] at this

/-- **Type II error, hence power.**

    Suppose the test accepts when `|f̂ − p₀| ≤ w`, for a hypothesised `p₀` and
    half-width `w`, but the process's true probability is `p`.  If the gap
    `|p − p₀|` exceeds `w`, the probability of wrongly accepting is at most
    `p(1−p)/n / (|p − p₀| − w)²`.

    The argument is the triangle inequality plus Chebyshev: accepting forces
    `f̂` to be at least `|p − p₀| − w` away from its own mean. -/
theorem Model.type_II_bound (M : Model) (x : String) (α : Output)
    {n : ℕ} (hn : n ≠ 0) {w p₀ : ℝ}
    (hw : w < |(M.μ (M.hitSet x α)).toReal - p₀|) :
    M.runSpace {ω | |M.observedFreq x α n ω - p₀| ≤ w}
      ≤ ENNReal.ofReal
          ((M.μ (M.hitSet x α)).toReal * (1 - (M.μ (M.hitSet x α)).toReal) / n
            / (|(M.μ (M.hitSet x α)).toReal - p₀| - w) ^ 2) := by
  classical
  set p := (M.μ (M.hitSet x α)).toReal with hp
  clear_value p
  set c := |p - p₀| - w with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hE : ∫ ω, M.observedFreq x α n ω ∂M.runSpace = p := by
    rw [hp]; exact M.integral_observedFreq x α hn
  -- accepting puts the sample mean far from its own expectation
  have hsub : {ω | |M.observedFreq x α n ω - p₀| ≤ w}
      ⊆ {ω | c ≤ |M.observedFreq x α n ω - p|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have htri : |p - p₀| ≤ |M.observedFreq x α n ω - p₀|
        + |M.observedFreq x α n ω - p| := by
      have := abs_sub_abs_le_abs_sub (M.observedFreq x α n ω - p₀)
        (M.observedFreq x α n ω - p)
      calc |p - p₀| = |(M.observedFreq x α n ω - p₀) - (M.observedFreq x α n ω - p)| := by
            ring_nf
        _ ≤ |M.observedFreq x α n ω - p₀| + |M.observedFreq x α n ω - p| :=
            abs_sub _ _
    rw [hc]; linarith
  refine le_trans (measure_mono hsub) ?_
  have hcheb := meas_ge_le_variance_div_sq (μ := M.runSpace)
    (M.memLp_observedFreq x α n) hcpos
  rw [hE] at hcheb
  refine le_trans hcheb ?_
  apply ENNReal.ofReal_le_ofReal
  rw [M.variance_observedFreq x α hn, ← hp]

end TPTND
