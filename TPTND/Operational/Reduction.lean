import TPTND.Syntax
import TPTND.Judgement
import TPTND.Arithmetic

/-! # The ↦ operational layer

Term evaluation `L ↦ L'` acts on lists of typed terms: `event` draws an
outcome, `sampling` collects draws into a frequency, `update` pools batches,
and the logical rules build compound outputs.

Three design points carry the soundness of the layer.

**1. The relation is indexed by the typing context.**  A draw may only
produce an output that `Γ` assigns to the term's variable.  This ties the
operational probabilities to the assumptions the derivation reasons under —
exactly the hypothesis the convergence results need: without the tie, a
process need not be sampling the distribution the context describes, and no
amount of further sampling need approach the assumed probability.

**2. `sumIntro` requires syntactic disjointness.**  Frequencies of
overlapping outputs double-count their shared outcomes, so addition is
sound only for disjoint summands — matching the static `I+`.

**3. `pairIntro` carries the joint frequency as a datum.**  Realised
frequencies do not multiply, even under independence: independence
constrains the *expectation* of the joint frequency, not its observed value
(`SoundnessRegression` attack 13 exhibits the finite-`n` gap concretely).
The joint frequency is read off the paired sample, not computed from the
marginals.
-/

namespace TPTND

/-- A typed term as it appears in an evaluation list: `tₙ : α_f`.
    A single run is `samples = 1`, `freq = 1` — the same uniform shape the
    static calculus uses for its judgements. -/
structure RunClaim where
  term    : Term
  samples : Nat
  output  : Output
  freq    : Prob
  deriving Repr, DecidableEq

/-- `Γ` supports a draw of `α` by the atomic term named `u`. -/
def supports (Γ : Context) (u : String) (α : Output) : Prop :=
  ∃ e ∈ Γ, e.name = u ∧ e.output = α

/-- `Γ` grounds the pair (term, output): every atomic constituent's variable
    carries an assumption in `Γ` for the corresponding output.

    This is the invariant subject reduction preserves.  Because single runs
    share the `RunClaim` shape with frequency claims, the quantification in
    `ListGrounded` is uniform over the whole list — it cannot be vacuously
    satisfied by a list consisting only of single runs. -/
def Grounds (Γ : Context) : Term → Output → Prop
  | t,        .sum α β  => Grounds Γ t α ∧ Grounds Γ t β
  | .pair t u, .prod α β => Grounds Γ t α ∧ Grounds Γ u β
  | .atom u,  α         => supports Γ u α
  | _,        _         => False

/-- Every claim in an evaluation list is grounded in `Γ`. -/
def ListGrounded (Γ : Context) (L : List RunClaim) : Prop :=
  ∀ c ∈ L, Grounds Γ c.term c.output

/-- Term evaluation, indexed by the typing context.

    Every rule appends its conclusion to the list, so a reduction sequence
    records its own history — which is what makes the run auditable. -/
inductive Reduces (Γ : Context) : List RunClaim → List RunClaim → Prop
  /-- `event`: one draw of `u`, which may only produce an output `Γ` assigns
      to `u` (design point 1 above). -/
  | event {L : List RunClaim} {u a : String}
      (hsupp : supports Γ u (.atom a)) :
      Reduces Γ L (L ++ [⟨.atom u, 1, .atom a, Prob.one⟩])
  /-- `sampling↦`: collect single runs of one term into a frequency.
      `f` is computed from the runs, never supplied. -/
  | sampling {L : List RunClaim} {t : Term} {α : Output} {runs : List RunClaim}
      {f : Prob}
      (hmem : ∀ r ∈ runs, r ∈ L)
      (hterm : ∀ r ∈ runs, r.term = t)
      (hsingle : ∀ r ∈ runs, r.samples = 1)
      (hne : runs ≠ [])
      -- The collected output must be ATOMIC.  The filter below matches run
      -- outputs syntactically, and event draws produce atoms — so sampling a
      -- compound (a+b) over runs that all produced `a` would certify the
      -- false frequency 0.  Compound frequencies arise only through the
      -- sumIntro/sumElim arithmetic, which Convergence.lean proves exact.
      (hatom : ∃ s, α = .atom s)
      (hgr : Grounds Γ t α)
      (hf : f.val
        = ((runs.filter (fun r => r.output == α)).length : ℚ) / (runs.length : ℚ)) :
      Reduces Γ L (L ++ [⟨t, runs.length, α, f⟩])
  /-- `update↦`: pool two batches of the same term and output. -/
  | update {L : List RunClaim} {t : Term} {α : Output} {n m : Nat} {f g h : Prob}
      (hn : 0 < n) (hm : 0 < m)
      (hfmem : ⟨t, n, α, f⟩ ∈ L) (hgmem : ⟨t, m, α, g⟩ ∈ L)
      (hh : h.val = (f.val * n + g.val * m) / ((n : ℚ) + m)) :
      Reduces Γ L (L ++ [⟨t, n + m, α, h⟩])
  /-- `I↦+`: add frequencies of **disjoint** outputs.  The printed rule has no
      such requirement, which is what lets it derive `t₄ : (α + β)_{3/2}`. -/
  | sumIntro {L : List RunClaim} {t : Term} {n : Nat} {α β : Output} {f g h : Prob}
      (hdisj : Output.syntacticallyDisjoint α β)
      (hfmem : ⟨t, n, α, f⟩ ∈ L) (hgmem : ⟨t, n, β, g⟩ ∈ L)
      (hh : h.val = f.val + g.val) :
      Reduces Γ L (L ++ [⟨t, n, .sum α β, h⟩])
  /-- `E↦+`: recover a summand, again only when the summands are disjoint. -/
  | sumElim {L : List RunClaim} {t : Term} {n : Nat} {α β : Output} {r q h : Prob}
      (hdisj : Output.syntacticallyDisjoint α β)
      (hsmem : ⟨t, n, .sum α β, r⟩ ∈ L) (hqmem : ⟨t, n, β, q⟩ ∈ L)
      (hh : h.val = r.val - q.val) :
      Reduces Γ L (L ++ [⟨t, n, α, h⟩])
  /-- `I↦×`: pair two terms run the same number of times.

      `h` is the frequency observed **in the paired sample**, supplied as a
      datum rather than computed from `f` and `g`: the product `f · g` is not
      the observed joint frequency at any finite `n`
      (`SoundnessRegression` attack 13). -/
  | pairIntro {L : List RunClaim} {t u : Term} {n : Nat} {α β : Output} {f g h : Prob}
      (hfmem : ⟨t, n, α, f⟩ ∈ L) (hgmem : ⟨u, n, β, g⟩ ∈ L)
      (hne : t ≠ u) :
      Reduces Γ L (L ++ [⟨.pair t u, n, .prod α β, h⟩])

/-- Reflexive–transitive closure: `L ↦* L'`. -/
inductive ReducesMany (Γ : Context) : List RunClaim → List RunClaim → Prop
  | refl {L} : ReducesMany Γ L L
  | step {L L' L''} : Reduces Γ L L' → ReducesMany Γ L' L'' → ReducesMany Γ L L''

/-- Reductions only ever extend the list, so nothing derived is ever lost.
    (The audit-trail property: a run records its own history.) -/
theorem Reduces.exists_append {Γ : Context} {L L' : List RunClaim}
    (h : Reduces Γ L L') : ∃ tail, L' = L ++ tail := by
  cases h with
  | event _ => exact ⟨_, rfl⟩
  | sampling _ _ _ _ _ => exact ⟨_, rfl⟩
  | update _ _ _ _ _ => exact ⟨_, rfl⟩
  | sumIntro _ _ _ _ => exact ⟨_, rfl⟩
  | sumElim _ _ _ _ => exact ⟨_, rfl⟩
  | pairIntro _ _ _ => exact ⟨_, rfl⟩

theorem Reduces.subset {Γ : Context} {L L' : List RunClaim}
    (h : Reduces Γ L L') : L ⊆ L' := by
  obtain ⟨tail, rfl⟩ := h.exists_append
  exact List.subset_append_left _ _

theorem ReducesMany.subset {Γ : Context} {L L' : List RunClaim}
    (h : ReducesMany Γ L L') : L ⊆ L' := by
  induction h with
  | refl => exact fun _ hx => hx
  | step hstep _ ih => exact fun _ hx => ih (hstep.subset hx)

/-- **Subject reduction.**  If every claim in `L` is grounded in `Γ`, so is
    every claim in `L'`.  Each rule carries what it needs: `event` may only
    draw an output `Γ` supports, and `sampling` must name an output `Γ`
    grounds. -/
theorem Reduces.grounded {Γ : Context} {L L' : List RunClaim}
    (hL : ListGrounded Γ L) (h : Reduces Γ L L') : ListGrounded Γ L' := by
  intro c hc
  cases h with
  | event hsupp =>
      rcases List.mem_append.mp hc with h' | h'
      · exact hL c h'
      · simp only [List.mem_singleton] at h'; subst h'
        simpa only [Grounds] using hsupp
  | sampling hmem hterm hsingle hne hatom hgr hf =>
      rcases List.mem_append.mp hc with h' | h'
      · exact hL c h'
      · simp only [List.mem_singleton] at h'; subst h'; exact hgr
  | update hn hm hfmem hgmem hh =>
      rcases List.mem_append.mp hc with h' | h'
      · exact hL c h'
      · simp only [List.mem_singleton] at h'; subst h'
        have hg := hL _ hfmem
        exact hg
  | sumIntro hdisj hfmem hgmem hh =>
      rcases List.mem_append.mp hc with h' | h'
      · exact hL c h'
      · simp only [List.mem_singleton] at h'; subst h'
        have hf' := hL _ hfmem
        have hg' := hL _ hgmem
        exact ⟨hf', hg'⟩
  | sumElim hdisj hsmem hqmem hh =>
      rcases List.mem_append.mp hc with h' | h'
      · exact hL c h'
      · simp only [List.mem_singleton] at h'; subst h'
        have hs := hL _ hsmem
        simp only [Grounds] at hs
        exact hs.1
  | pairIntro hfmem hgmem hne =>
      rcases List.mem_append.mp hc with h' | h'
      · exact hL c h'
      · simp only [List.mem_singleton] at h'; subst h'
        have hf' := hL _ hfmem
        have hg' := hL _ hgmem
        exact ⟨hf', hg'⟩

/-- Subject reduction along a whole reduction sequence. -/
theorem ReducesMany.grounded {Γ : Context} {L L' : List RunClaim}
    (hL : ListGrounded Γ L) (h : ReducesMany Γ L L') : ListGrounded Γ L' := by
  induction h with
  | refl => exact hL
  | step hstep _ ih => exact ih (hstep.grounded hL)

end TPTND
