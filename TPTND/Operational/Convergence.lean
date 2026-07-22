import TPTND.Operational.RunSpace
import TPTND.Operational.Reduction

/-! # Convergence, and which arithmetic is exact at finite sample size

`observedFreq_tendsto_prob` gives almost-sure convergence of the observed
frequency for an arbitrary `Output`, since `Model.eval` interprets `+`, `×`
and `¬` structurally.  The finer question is **agreement at finite `n`**:
is the number a connective rule computes the frequency actually observed
for the compound output?

* `+` — exact at every `n` for disjoint summands
  (`observedFreq_sum_of_disjoint`); without disjointness the shared
  outcomes are counted twice.
* `−` — the same lemma, rearranged (`observedFreq_sub_of_disjoint`).
* `¬` — `1 − f`, exact at every `n` (`observedFreq_neg`).
* `×` — `f · g` is **not** the observed joint frequency at any finite `n`.
  It converges to the right limit under independence, but the intermediate
  values differ (`SoundnessRegression` attack 13: two dice, joint frequency
  1/2, product 1/4).  Hence `Reduces.pairIntro` takes the joint frequency
  as a datum.
-/

namespace TPTND

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

variable {M : Model} {x : String}

/-- Negation is exact at every sample size. -/
theorem Model.observedFreq_neg (M : Model) (x : String) (α : Output)
    {n : ℕ} (hn : n ≠ 0) (ω : ℕ → M.Ω) :
    M.observedFreq x (.neg α) n ω = 1 - M.observedFreq x α n ω := by
  classical
  have hset : M.hitSet x (.neg α) = (M.hitSet x α)ᶜ := rfl
  have hsplit :
      ((range n).filter (fun i => ω i ∈ M.hitSet x (.neg α))).card
        = n - ((range n).filter (fun i => ω i ∈ M.hitSet x α)).card := by
    rw [hset]
    have := Finset.card_filter_add_card_filter_not
      (s := range n) (p := fun i => ω i ∈ M.hitSet x α)
    simp only [Finset.card_range] at this
    have hcompl : ∀ i, (ω i ∈ (M.hitSet x α)ᶜ) ↔ ¬ (ω i ∈ M.hitSet x α) := by
      intro i; rfl
    simp only [hcompl]
    omega
  have hle : ((range n).filter (fun i => ω i ∈ M.hitSet x α)).card ≤ n := by
    simpa using Finset.card_filter_le (range n) (fun i => ω i ∈ M.hitSet x α)
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [Model.observedFreq, hsplit]
  rw [Nat.cast_sub hle]
  field_simp

/-- **The `I↦+` arithmetic is exact.**  For disjoint summands the observed
    frequency of `α + β` is the sum of the observed frequencies — at every
    sample size, not just in the limit.  Disjointness is doing all the work:
    drop it and shared outcomes are counted twice. -/
theorem Model.observedFreq_sum_of_disjoint (M : Model) (x : String)
    (hM : M.AtomsDisjoint x) {α β : Output}
    (hdisj : Output.syntacticallyDisjoint α β = true) (n : ℕ) (ω : ℕ → M.Ω) :
    M.observedFreq x (.sum α β) n ω
      = M.observedFreq x α n ω + M.observedFreq x β n ω := by
  classical
  have hinter : M.eval x α ∩ M.eval x β = ∅ :=
    M.eval_disjoint_of_syntacticallyDisjoint x hM hdisj
  have hmem : ∀ i, (ω i ∈ M.hitSet x (.sum α β))
      ↔ (ω i ∈ M.hitSet x α ∨ ω i ∈ M.hitSet x β) := by
    intro i; rfl
  have hdisjF : Disjoint ((range n).filter (fun i => ω i ∈ M.hitSet x α))
      ((range n).filter (fun i => ω i ∈ M.hitSet x β)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [Finset.mem_filter] at hi hi'
    have : ω i ∈ M.eval x α ∩ M.eval x β := ⟨hi.2, hi'.2⟩
    rw [hinter] at this
    exact this
  have hcard :
      ((range n).filter (fun i => ω i ∈ M.hitSet x (.sum α β))).card
        = ((range n).filter (fun i => ω i ∈ M.hitSet x α)).card
          + ((range n).filter (fun i => ω i ∈ M.hitSet x β)).card := by
    simp only [hmem, Finset.filter_or]
    rw [Finset.card_union_of_disjoint hdisjF]
  simp only [Model.observedFreq, hcard, Nat.cast_add]
  ring

/-- `E↦+`: the same fact, rearranged — recovering a summand by subtraction is
    exact under disjointness. -/
theorem Model.observedFreq_sub_of_disjoint (M : Model) (x : String)
    (hM : M.AtomsDisjoint x) {α β : Output}
    (hdisj : Output.syntacticallyDisjoint α β = true) (n : ℕ) (ω : ℕ → M.Ω) :
    M.observedFreq x α n ω
      = M.observedFreq x (.sum α β) n ω - M.observedFreq x β n ω := by
  have := M.observedFreq_sum_of_disjoint x hM hdisj n ω
  linarith

/-- The joint frequency of `α × β` is read off the paired sample: the runs in
    which BOTH occurred.  This is definitional, and it is exactly the datum
    `Reduces.pairIntro` carries — as opposed to `f · g`. -/
theorem Model.hitSet_prod (M : Model) (x : String) (α β : Output) :
    M.hitSet x (.prod α β) = M.hitSet x α ∩ M.hitSet x β := rfl

/-- **Compound convergence.**  For any output — atomic or compound — the
    observed frequency converges almost surely to the probability the model
    assigns it.  With the agreement lemmas above, the numbers the connective
    rules compute for `+`, `−` and `¬` ARE the observed frequencies, so the
    convergence transfers to the rules themselves. -/
theorem Model.observedFreq_limit (M : Model) (x : String) (α : Output) :
    ∀ᵐ ω ∂M.runSpace,
      Tendsto (fun n : ℕ => M.observedFreq x α n ω) atTop
        (𝓝 (M.μ (M.hitSet x α)).toReal) :=
  M.observedFreq_tendsto_prob x α

/-- Compound convergence for a sum, in the form `sumIntro` uses: the rule's
    own arithmetic `f + g` converges to the probability of `α + β`. -/
theorem Model.observedFreq_limit_sum (M : Model) (x : String) (hM : M.AtomsDisjoint x)
    {α β : Output} (hdisj : Output.syntacticallyDisjoint α β = true) :
    ∀ᵐ ω ∂M.runSpace,
      Tendsto (fun n : ℕ =>
          M.observedFreq x α n ω + M.observedFreq x β n ω) atTop
        (𝓝 (M.μ (M.hitSet x (.sum α β))).toReal) := by
  filter_upwards [M.observedFreq_limit x (.sum α β)] with ω hω
  have hrw : ∀ n : ℕ,
      M.observedFreq x α n ω + M.observedFreq x β n ω
        = M.observedFreq x (.sum α β) n ω :=
    fun n => (M.observedFreq_sum_of_disjoint x hM hdisj n ω).symm
  simpa only [hrw] using hω

/-- **Progress.**  For any threshold `ε > 0`, almost surely the observed
    frequency is eventually within `ε` of the model probability — so
    sampling far enough always reaches the point where `IT`'s side condition
    `|a − f| ≤ ε(n)` holds and a Trust certificate fires.

    The context-indexed reduction is what makes this unconditional: draws
    are tied to the context's assumptions by construction, so the process is
    sampling the distribution the context describes. -/
theorem Model.progress (M : Model) (x : String) (α : Output)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂M.runSpace, ∃ N : ℕ, ∀ n ≥ N,
      |M.observedFreq x α n ω - (M.μ (M.hitSet x α)).toReal| < ε := by
  filter_upwards [M.observedFreq_limit x α] with ω hω
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hω ε hε
  exact ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn⟩

/-- Progress in the shape `IT` consumes it: eventually the gap between the
    model probability and the observed frequency is below the threshold, which
    is exactly that rule's side condition. -/
theorem Model.eventually_trustworthy (M : Model) (x : String) (α : Output)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂M.runSpace, ∀ᶠ n in atTop,
      |(M.μ (M.hitSet x α)).toReal - M.observedFreq x α n ω| < ε := by
  filter_upwards [M.progress x α hε] with ω hω
  obtain ⟨N, hN⟩ := hω
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [abs_sub_comm]
  exact hN n hn

-- ============================================================================
-- Adequacy: the operational layer computes the run space's frequencies
-- ============================================================================

/-- `¬α` is never `α`. -/
theorem Output.neg_ne_self : ∀ α : Output, Output.neg α ≠ α
  | .atom _ => by simp
  | .neg β => by
      intro h
      have : Output.neg β = β := by injection h
      exact Output.neg_ne_self β this
  | .sum _ _ => by simp
  | .prod _ _ => by simp
  | .arr _ _ _ => by simp

/-- **Adequacy.**  The frequency `Reduces.sampling` computes from the runs
    of `ω` is exactly the observed frequency of the run space.

    `runList` abstracts a run history — hits recorded as `α`, misses as
    `¬α` — and the count is invariant to how misses are labelled, which is
    all the `sampling` rule reads.  `RunSpace` says what a frequency
    *means*, `Reduces` says how the calculus *computes* one, and this says
    they agree. -/
noncomputable def Model.runList (M : Model) (x : String) (α : Output)
    (ω : ℕ → M.Ω) (n : ℕ) : List RunClaim :=
  open scoped Classical in
  (List.range n).map (fun i =>
    ⟨.atom x, 1, if ω i ∈ M.hitSet x α then α else .neg α, Prob.one⟩)

theorem Model.runList_length (M : Model) (x : String) (α : Output)
    (ω : ℕ → M.Ω) (n : ℕ) : (M.runList x α ω n).length = n := by
  simp [Model.runList]

/-- Every entry of the list is a single run of `x`, i.e. exactly the premise
    shape `Reduces.sampling` demands. -/
theorem Model.runList_single (M : Model) (x : String) (α : Output)
    (ω : ℕ → M.Ω) (n : ℕ) :
    ∀ r ∈ M.runList x α ω n, r.term = .atom x ∧ r.samples = 1 := by
  intro r hr
  simp only [Model.runList, List.mem_map] at hr
  obtain ⟨i, _, rfl⟩ := hr
  exact ⟨rfl, rfl⟩

/-- **Adequacy.**  The frequency `Reduces.sampling` computes from the runs of
    `ω` is exactly the observed frequency of the run space.

    This closes the loop: `RunSpace` says what a frequency *means*, `Reduces`
    says how the calculus *computes* one, and this says they agree.  With
    `thm_4_4` and `progress` it gives the chain

      real runs  →  the list a reduction consumes  →  the `f` in `tₙ : α_f`
                 →  converges a.s. to the model probability. -/
theorem Model.sampling_adequate (M : Model) (x : String) (α : Output)
    (ω : ℕ → M.Ω) (n : ℕ) :
    ((((M.runList x α ω n).filter (fun r => r.output == α)).length : ℝ)) / (n : ℝ)
      = M.observedFreq x α n ω := by
  classical
  have hbridge : ((range n).filter (fun i => ω i ∈ M.hitSet x α)).card
      = ((List.range n).filter (fun i => decide (ω i ∈ M.hitSet x α))).length := rfl
  have hcount :
      ((M.runList x α ω n).filter (fun r => r.output == α)).length
        = ((range n).filter (fun i => ω i ∈ M.hitSet x α)).card := by
    rw [hbridge]
    simp only [Model.runList, List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro i _
    by_cases h : ω i ∈ M.hitSet x α
    · simp [h]
    · simp [h, Output.neg_ne_self α]
  rw [hcount, Model.observedFreq]
  ring

end TPTND
