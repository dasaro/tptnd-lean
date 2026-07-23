import TPTND.Operational.TrustGuarantee
import Mathlib.MeasureTheory.Integral.Prod

/-! # What a two-sample certificate guarantees

`IT2` fires when `0` lies in the interval `(f − g) ± z·√(¼(1/n + 1/m))`;
`IUT2`, `IEx` and `INEx` read the same interval.  The width uses the
worst-case null variance — `¼` bounds `p(1−p)` for every common rate `p` —
so no estimate of that rate enters the test and the Chebyshev argument
applies verbatim: for two independent run histories of processes with the
SAME probability, the difference of observed frequencies exceeds the
width with probability at most `1/z² = 1/20`.

`twoSampleCI_reject` transfers the bound to the implemented interval
(the rational square root only ever rounds up), so the level holds for
the very test the checker runs. -/

namespace TPTND

open MeasureTheory ProbabilityTheory Finset

/-- The joint space of two independent run histories. -/
noncomputable def pairSpace (M1 M2 : Model) :
    Measure ((ℕ → M1.Ω) × (ℕ → M2.Ω)) :=
  M1.runSpace.prod M2.runSpace

instance (M1 M2 : Model) : IsProbabilityMeasure (pairSpace M1 M2) := by
  rw [pairSpace]; infer_instance

-- ============================================================================
-- Bounds and integrability
-- ============================================================================

theorem Model.observedFreq_nonneg (M : Model) (x : String) (α : Output)
    (n : ℕ) (ω : ℕ → M.Ω) : 0 ≤ M.observedFreq x α n ω := by
  classical
  rw [Model.observedFreq]; positivity

theorem Model.observedFreq_le_one (M : Model) (x : String) (α : Output)
    (n : ℕ) (ω : ℕ → M.Ω) : M.observedFreq x α n ω ≤ 1 := by
  classical
  have hle : ((range n).filter (fun i => ω i ∈ M.hitSet x α)).card ≤ n := by
    simpa using Finset.card_filter_le (range n) (fun i => ω i ∈ M.hitSet x α)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Model.observedFreq]
  · have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [Model.observedFreq, inv_mul_le_iff₀ hnR, mul_one]
    exact_mod_cast hle

/-- Bounded measurable functions are integrable on a probability space. -/
theorem integrable_of_bound {Ω : Type _} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) (hf : Measurable f)
    (C : ℝ) (h : ∀ ω, |f ω| ≤ C) : Integrable f P := by
  refine memLp_one_iff_integrable.mp
    (MemLp.of_bound hf.aestronglyMeasurable C ?_)
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact h ω

-- ============================================================================
-- Marginal integrals
-- ============================================================================

theorem integral_fst_comp (M1 M2 : Model) (f : (ℕ → M1.Ω) → ℝ)
    (hf : Measurable f) :
    ∫ ω, f ω.1 ∂(pairSpace M1 M2) = ∫ ω1, f ω1 ∂M1.runSpace := by
  have h := integral_map (φ := Prod.fst)
    (μ := M1.runSpace.prod M2.runSpace)
    measurable_fst.aemeasurable hf.aestronglyMeasurable
  rw [Measure.map_fst_prod] at h
  simp only [measure_univ, one_smul] at h
  rw [pairSpace]
  exact h.symm

theorem integral_snd_comp (M1 M2 : Model) (g : (ℕ → M2.Ω) → ℝ)
    (hg : Measurable g) :
    ∫ ω, g ω.2 ∂(pairSpace M1 M2) = ∫ ω2, g ω2 ∂M2.runSpace := by
  have h := integral_map (φ := Prod.snd)
    (μ := M1.runSpace.prod M2.runSpace)
    measurable_snd.aemeasurable hg.aestronglyMeasurable
  rw [Measure.map_snd_prod] at h
  simp only [measure_univ, one_smul] at h
  rw [pairSpace]
  exact h.symm

-- ============================================================================
-- Moments of the difference of observed frequencies
-- ============================================================================

variable (M1 M2 : Model) (x y : String) (α β : Output)

theorem memLp_diff (n m : ℕ) :
    MemLp (fun ω : (ℕ → M1.Ω) × (ℕ → M2.Ω) =>
      M1.observedFreq x α n ω.1 - M2.observedFreq y β m ω.2) 2
      (pairSpace M1 M2) := by
  refine MemLp.of_bound ?_ 1 ?_
  · exact ((M1.measurable_observedFreq x α n).comp measurable_fst |>.sub
      ((M2.measurable_observedFreq y β m).comp measurable_snd))
      |>.aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := M1.observedFreq_nonneg x α n ω.1
      have := M2.observedFreq_le_one y β m ω.2
      linarith
    · have := M1.observedFreq_le_one x α n ω.1
      have := M2.observedFreq_nonneg y β m ω.2
      linarith

theorem integral_diff {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    ∫ ω, (M1.observedFreq x α n ω.1 - M2.observedFreq y β m ω.2)
        ∂(pairSpace M1 M2)
      = (M1.μ (M1.hitSet x α)).toReal - (M2.μ (M2.hitSet y β)).toReal := by
  have hiX : Integrable (fun ω : (ℕ → M1.Ω) × (ℕ → M2.Ω) =>
      M1.observedFreq x α n ω.1) (pairSpace M1 M2) :=
    integrable_of_bound _ _
      ((M1.measurable_observedFreq x α n).comp measurable_fst) 1
      (fun ω => abs_le.mpr ⟨by linarith [M1.observedFreq_nonneg x α n ω.1],
        M1.observedFreq_le_one x α n ω.1⟩)
  have hiY : Integrable (fun ω : (ℕ → M1.Ω) × (ℕ → M2.Ω) =>
      M2.observedFreq y β m ω.2) (pairSpace M1 M2) :=
    integrable_of_bound _ _
      ((M2.measurable_observedFreq y β m).comp measurable_snd) 1
      (fun ω => abs_le.mpr ⟨by linarith [M2.observedFreq_nonneg y β m ω.2],
        M2.observedFreq_le_one y β m ω.2⟩)
  rw [integral_sub hiX hiY,
      integral_fst_comp M1 M2 _ (M1.measurable_observedFreq x α n),
      integral_snd_comp M1 M2 _ (M2.measurable_observedFreq y β m),
      M1.integral_observedFreq x α hn, M2.integral_observedFreq y β hm]

/-- Independence makes the variances add. -/
theorem variance_diff {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    variance (fun ω : (ℕ → M1.Ω) × (ℕ → M2.Ω) =>
        M1.observedFreq x α n ω.1 - M2.observedFreq y β m ω.2)
      (pairSpace M1 M2)
      = (M1.μ (M1.hitSet x α)).toReal * (1 - (M1.μ (M1.hitSet x α)).toReal) / n
        + (M2.μ (M2.hitSet y β)).toReal
            * (1 - (M2.μ (M2.hitSet y β)).toReal) / m := by
  classical
  set p1 := (M1.μ (M1.hitSet x α)).toReal with hp1
  set p2 := (M2.μ (M2.hitSet y β)).toReal with hp2
  have hp10 : 0 ≤ p1 := ENNReal.toReal_nonneg
  have hp11 : p1 ≤ 1 := by
    rw [hp1]; exact ENNReal.toReal_le_of_le_ofReal one_pos.le
      (by simpa using prob_le_one)
  have hp20 : 0 ≤ p2 := ENNReal.toReal_nonneg
  have hp21 : p2 ≤ 1 := by
    rw [hp2]; exact ENNReal.toReal_le_of_le_ofReal one_pos.le
      (by simpa using prob_le_one)
  set X := fun ω1 => M1.observedFreq x α n ω1 with hX
  set Y := fun ω2 => M2.observedFreq y β m ω2 with hY
  have hXm : Measurable X := M1.measurable_observedFreq x α n
  have hYm : Measurable Y := M2.measurable_observedFreq y β m
  have hX0 : ∀ ω1, 0 ≤ X ω1 := M1.observedFreq_nonneg x α n
  have hX1 : ∀ ω1, X ω1 ≤ 1 := M1.observedFreq_le_one x α n
  have hY0 : ∀ ω2, 0 ≤ Y ω2 := M2.observedFreq_nonneg y β m
  have hY1 : ∀ ω2, Y ω2 ≤ 1 := M2.observedFreq_le_one y β m
  have hEX : ∫ ω1, X ω1 ∂M1.runSpace = p1 := M1.integral_observedFreq x α hn
  have hEY : ∫ ω2, Y ω2 ∂M2.runSpace = p2 := M2.integral_observedFreq y β hm
  -- centered marginal facts
  have hcX : ∫ ω1, (X ω1 - p1) ∂M1.runSpace = 0 := by
    rw [integral_sub (integrable_of_bound _ _ hXm 1
        (fun ω1 => abs_le.mpr ⟨by linarith [hX0 ω1], hX1 ω1⟩))
      (integrable_const p1), hEX, integral_const]
    simp
  have hcY : ∫ ω2, (Y ω2 - p2) ∂M2.runSpace = 0 := by
    rw [integral_sub (integrable_of_bound _ _ hYm 1
        (fun ω2 => abs_le.mpr ⟨by linarith [hY0 ω2], hY1 ω2⟩))
      (integrable_const p2), hEY, integral_const]
    simp
  have hcX2 : ∫ ω1, (X ω1 - p1) ^ 2 ∂M1.runSpace = p1 * (1 - p1) / n := by
    have := variance_eq_integral
      (X := fun ω1 => X ω1) (μ := M1.runSpace) hXm.aemeasurable
    rw [hEX] at this
    rw [← this]
    exact M1.variance_observedFreq x α hn
  have hcY2 : ∫ ω2, (Y ω2 - p2) ^ 2 ∂M2.runSpace = p2 * (1 - p2) / m := by
    have := variance_eq_integral
      (X := fun ω2 => Y ω2) (μ := M2.runSpace) hYm.aemeasurable
    rw [hEY] at this
    rw [← this]
    exact M2.variance_observedFreq y β hm
  -- the centered square splits over the product
  have hD := integral_diff M1 M2 x y α β hn hm
  have hvar := variance_eq_integral
    (X := fun ω : (ℕ → M1.Ω) × (ℕ → M2.Ω) => X ω.1 - Y ω.2)
    (μ := pairSpace M1 M2)
    (((hXm.comp measurable_fst).sub (hYm.comp measurable_snd)).aemeasurable)
  rw [hD, ← hp1, ← hp2] at hvar
  have hsq : (fun ω : (ℕ → M1.Ω) × (ℕ → M2.Ω) =>
        (X ω.1 - Y ω.2 - (p1 - p2)) ^ 2)
      = fun ω => ((X ω.1 - p1) ^ 2
          - 2 * ((X ω.1 - p1) * (Y ω.2 - p2))) + (Y ω.2 - p2) ^ 2 := by
    funext ω; ring
  have hiA2 : Integrable (fun ω : (ℕ → M1.Ω) × (ℕ → M2.Ω) =>
      (X ω.1 - p1) ^ 2) (pairSpace M1 M2) :=
    integrable_of_bound _ _
      (((hXm.comp measurable_fst).sub measurable_const).pow_const 2) 1
      (fun ω => by
        rw [abs_le]
        constructor
        · nlinarith [sq_nonneg (X ω.1 - p1)]
        · nlinarith [hX0 ω.1, hX1 ω.1, hp10, hp11])
  have hiB2 : Integrable (fun ω : (ℕ → M1.Ω) × (ℕ → M2.Ω) =>
      (Y ω.2 - p2) ^ 2) (pairSpace M1 M2) :=
    integrable_of_bound _ _
      (((hYm.comp measurable_snd).sub measurable_const).pow_const 2) 1
      (fun ω => by
        rw [abs_le]
        constructor
        · nlinarith [sq_nonneg (Y ω.2 - p2)]
        · nlinarith [hY0 ω.2, hY1 ω.2, hp20, hp21])
  have hiAB : Integrable (fun ω : (ℕ → M1.Ω) × (ℕ → M2.Ω) =>
      2 * ((X ω.1 - p1) * (Y ω.2 - p2))) (pairSpace M1 M2) :=
    (integrable_of_bound _ _
      (((hXm.comp measurable_fst).sub measurable_const).mul
        ((hYm.comp measurable_snd).sub measurable_const)) 1
      (fun ω => by
        rw [abs_mul]
        have ha : |X ω.1 - p1| ≤ 1 := abs_le.mpr
          ⟨by linarith [hX0 ω.1, hp11], by linarith [hX1 ω.1, hp10]⟩
        have hb : |Y ω.2 - p2| ≤ 1 := abs_le.mpr
          ⟨by linarith [hY0 ω.2, hp21], by linarith [hY1 ω.2, hp20]⟩
        exact mul_le_one₀ ha (abs_nonneg _) hb)).const_mul 2
  have hiAsub : Integrable (fun ω : (ℕ → M1.Ω) × (ℕ → M2.Ω) =>
      (X ω.1 - p1) ^ 2 - 2 * ((X ω.1 - p1) * (Y ω.2 - p2)))
      (pairSpace M1 M2) := hiA2.sub hiAB
  have hcross : ∫ ω, ((X ω.1 - p1) * (Y ω.2 - p2)) ∂(pairSpace M1 M2)
      = 0 := by
    rw [pairSpace]
    rw [MeasureTheory.integral_prod_mul (μ := M1.runSpace)
      (ν := M2.runSpace) (fun ω1 => X ω1 - p1) (fun ω2 => Y ω2 - p2)]
    rw [show ∫ ω1, (X ω1 - p1) ∂M1.runSpace
        = (0 : ℝ) from hcX]
    ring
  rw [hvar, hsq,
      integral_add hiAsub hiB2,
      integral_sub hiA2 hiAB,
      integral_const_mul,
      hcross,
      integral_fst_comp M1 M2 _
        ((hXm.sub measurable_const).pow_const 2),
      integral_snd_comp M1 M2 _
        ((hYm.sub measurable_const).pow_const 2),
      hcX2, hcY2]
  ring

-- ============================================================================
-- Coverage of the exact acceptance region
-- ============================================================================

/-- **Two-sample coverage.**  For two independent run histories of processes
    with the SAME probability, the difference of observed frequencies
    exceeds `z·√(¼(1/n + 1/m))` with probability at most `1/20`. -/
theorem twoSample_coverage {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (h0 : (M1.μ (M1.hitSet x α)).toReal = (M2.μ (M2.hitSet y β)).toReal) :
    (pairSpace M1 M2) {ω | ((zCheb : ℚ) : ℝ)
        * Real.sqrt ((1 / 4 : ℝ) * (1 / n + 1 / m))
        ≤ |M1.observedFreq x α n ω.1 - M2.observedFreq y β m ω.2|}
      ≤ ENNReal.ofReal (1 / 20) := by
  classical
  set p := (M2.μ (M2.hitSet y β)).toReal with hp
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have hVbar : (0 : ℝ) < (1 / 4 : ℝ) * (1 / n + 1 / m) := by positivity
  have hzpos : (0 : ℝ) < ((zCheb : ℚ) : ℝ) := by
    have : (0 : ℚ) < zCheb := by norm_num [zCheb]
    exact_mod_cast this
  have hc : (0 : ℝ) < ((zCheb : ℚ) : ℝ)
      * Real.sqrt ((1 / 4 : ℝ) * (1 / n + 1 / m)) :=
    mul_pos hzpos (Real.sqrt_pos.mpr hVbar)
  have hcheb := meas_ge_le_variance_div_sq (μ := pairSpace M1 M2)
    (memLp_diff M1 M2 x y α β n m) hc
  rw [integral_diff M1 M2 x y α β hn hm, h0, ← hp, sub_self] at hcheb
  simp only [sub_zero] at hcheb
  refine le_trans hcheb (ENNReal.ofReal_le_ofReal ?_)
  rw [variance_diff M1 M2 x y α β hn hm, h0, ← hp]
  have hp0 : (0 : ℝ) ≤ p := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 := by
    rw [hp]
    exact ENNReal.toReal_le_of_le_ofReal one_pos.le
      (by simpa using prob_le_one)
  have hpq : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have hsq : (((zCheb : ℚ) : ℝ)
      * Real.sqrt ((1 / 4 : ℝ) * (1 / n + 1 / m))) ^ 2
      = ((zCheb : ℚ) : ℝ) ^ 2 * ((1 / 4 : ℝ) * (1 / n + 1 / m)) := by
    rw [mul_pow, Real.sq_sqrt hVbar.le]
  rw [hsq]
  have hz20 : (20 : ℝ) ≤ ((zCheb : ℚ) : ℝ) ^ 2 := by
    have : (20 : ℚ) ≤ zCheb ^ 2 := by norm_num [zCheb]
    exact_mod_cast this
  have hnum : p * (1 - p) / n + p * (1 - p) / m
      ≤ (1 / 4 : ℝ) * (1 / n + 1 / m) := by
    have h1 : p * (1 - p) / n ≤ (1 / 4 : ℝ) / n := by gcongr
    have h2 : p * (1 - p) / m ≤ (1 / 4 : ℝ) / m := by gcongr
    calc p * (1 - p) / n + p * (1 - p) / m
        ≤ (1 / 4 : ℝ) / n + (1 / 4 : ℝ) / m := add_le_add h1 h2
      _ = (1 / 4 : ℝ) * (1 / n + 1 / m) := by ring
  calc (p * (1 - p) / n + p * (1 - p) / m)
        / (((zCheb : ℚ) : ℝ) ^ 2 * ((1 / 4 : ℝ) * (1 / n + 1 / m)))
      ≤ ((1 / 4 : ℝ) * (1 / n + 1 / m))
        / (((zCheb : ℚ) : ℝ) ^ 2 * ((1 / 4 : ℝ) * (1 / n + 1 / m))) := by
        gcongr
      _ = 1 / ((zCheb : ℚ) : ℝ) ^ 2 := by
        rw [mul_comm (((zCheb : ℚ) : ℝ) ^ 2)
              ((1 / 4 : ℝ) * (1 / (n : ℝ) + 1 / (m : ℝ))),
            ← div_div, div_self hVbar.ne']
      _ ≤ 1 / 20 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 20)]
        linarith

-- ============================================================================
-- The implemented interval
-- ============================================================================

/-- **Rejection by the implemented two-sample test implies rejection by the
    exact region.**  If `0` falls outside `twoSampleCI`, the observed
    difference exceeds `z·√(¼(1/n + 1/m))`. -/
theorem twoSampleCI_reject {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (f g : Prob)
    (h : (twoSampleCI n m f g).contains Prob.zero = false) :
    ((zCheb : ℚ) : ℝ) * Real.sqrt ((1 / 4 : ℝ) * (1 / n + 1 / m))
      ≤ |((f.val : ℚ) : ℝ) - ((g.val : ℚ) : ℝ)| := by
  unfold twoSampleCI at h
  rw [if_neg (by simp [hn, hm])] at h
  set se : ℚ := ratSqrt ((1 / 4) * (1 / (n : ℚ) + 1 / (m : ℚ))) with hse_def
  simp only [Constraint.contains, clampProb, Bool.and_eq_false_iff,
             decide_eq_false_iff_not, not_le, Prob.zero] at h
  rcases h with hlt | hgt
  · -- 0 below the clamped lower endpoint: the difference is significant
    have hlo : 0 < f.val - g.val - zCheb * se := by
      have h1 : (0 : ℚ) < min 1 (f.val - g.val - zCheb * se) := by
        rcases lt_max_iff.mp hlt with h' | h'
        · exact absurd h' (lt_irrefl 0)
        · exact h'
      exact lt_of_lt_of_le h1 (min_le_right _ _)
    have hse0 : (0 : ℚ) ≤ se := by
      have hs := ratSqrt_ge_sqrt ((1 / 4) * (1 / (n : ℚ) + 1 / (m : ℚ)))
      have h0 := Real.sqrt_nonneg
        ((((1 / 4) * (1 / (n : ℚ) + 1 / (m : ℚ)) : ℚ)) : ℝ)
      rw [hse_def]
      exact_mod_cast le_trans h0 hs
    have hz0 : (0 : ℚ) ≤ zCheb := by norm_num [zCheb]
    -- domination of the exact width
    have hseR : Real.sqrt ((1 / 4 : ℝ) * (1 / n + 1 / m)) ≤ ((se : ℚ) : ℝ) := by
      have hs := ratSqrt_ge_sqrt ((1 / 4) * (1 / (n : ℚ) + 1 / (m : ℚ)))
      rw [hse_def]
      refine le_trans (le_of_eq ?_) hs
      congr 1
      push_cast
      ring
    have hgapQ : zCheb * se < f.val - g.val := by linarith
    have hgapR : ((zCheb : ℚ) : ℝ) * ((se : ℚ) : ℝ)
        < ((f.val : ℚ) : ℝ) - ((g.val : ℚ) : ℝ) := by
      have : ((zCheb * se : ℚ) : ℝ) < (((f.val - g.val) : ℚ) : ℝ) := by
        exact_mod_cast hgapQ
      push_cast at this
      linarith
    have habs : ((f.val : ℚ) : ℝ) - ((g.val : ℚ) : ℝ)
        ≤ |((f.val : ℚ) : ℝ) - ((g.val : ℚ) : ℝ)| := le_abs_self _
    have hwidth : ((zCheb : ℚ) : ℝ)
        * Real.sqrt ((1 / 4 : ℝ) * (1 / n + 1 / m))
        ≤ ((zCheb : ℚ) : ℝ) * ((se : ℚ) : ℝ) :=
      mul_le_mul_of_nonneg_left hseR (by exact_mod_cast hz0)
    linarith
  · -- 0 above the clamped upper endpoint: impossible, the clamp is ≥ 0
    exact absurd (lt_of_le_of_lt (le_max_left 0 _) hgt) (lt_irrefl 0)

end TPTND
