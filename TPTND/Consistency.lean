import TPTND.Spec

/-! # Consistency: `Derivable` is not the total relation

`checker_sound` says the checker only accepts derivable judgements, but on
its own that leaves open the worry that `Derivable` might hold of *every*
sequent — an "escape-hatch" inductive, against which soundness would be
vacuous. This file rules that out by exhibiting a concrete sequent that is
**not** derivable.

The witness is a Bayesian prior family whose recorded weights do not sum to
1. The enabling lemma — that **every** derivable prior family is normalized —
is a useful metatheorem in its own right: an `I-P` certificate always carries
a genuine probability distribution over its hypotheses, an invariant no rule
can violate (the only rule that concludes a prior family demands it, and the
structural rules that could wrap the judgement preserve its claim). -/

namespace TPTND

/-- The total weight recorded by a prior family. -/
def PriorFamily.weightSum (fam : PriorFamily) : ℚ :=
  (fam.points.map (·.2.val)).foldl (· + ·) 0

/-- **Every derivable prior family is normalized.** -/
theorem derivable_prior_normalized {s : Sequent} (h : Derivable s) :
    ∀ fam, s.claim = .priorFamily fam → fam.weightSum = 1 := by
  induction h with
  | iPrior es es' points fam hne hlen hplen hprems hidx hexact hpoints hsum
      hdistinct ih =>
    intro g heq
    simp only [Claim.priorFamily.injEq] at heq
    subst heq
    simpa [PriorFamily.weightSum, hpoints] using hsum
  | weakeningS Γ Δ ctx J K hwf hJ hK hindep hctx ihJ ihK =>
    intro g heq; exact ihJ g heq
  | weakeningD Γ ctx Δ J hwf hJ hindep hΔ hctx ihJ =>
    intro g heq; exact ihJ g heq
  | contraction Γp ctx J k repl a hwf hp hgroup hrest hrepl hexact hinf hin ihp =>
    intro g heq; exact ihp g heq
  | _ => intro g heq; exact Claim.noConfusion heq

/-- A prior family that is not a distribution: one hypothesis carrying weight
    ½ (any non-normalized family works). -/
def badPrior : PriorFamily :=
  { xName := "h", alpha := .atom "a", yName := "w", beta := .atom "a",
    points := [(clampProb (1 / 2), clampProb (1 / 2))] }

theorem badPrior_not_normalized : badPrior.weightSum ≠ 1 := by
  simp only [PriorFamily.weightSum, badPrior, clampProb, List.map_cons,
             List.map_nil, List.foldl_cons, List.foldl_nil]
  norm_num

/-- **Consistency (concrete).** The un-normalized prior family is not
    derivable in any context. -/
theorem not_derivable_badPrior (Γ : Context) :
    ¬ Derivable ⟨Γ, .priorFamily badPrior⟩ := fun h =>
  badPrior_not_normalized (derivable_prior_normalized h badPrior rfl)

/-- **Consistency (bare).** Some sequent is not derivable: `Derivable` is a
    non-trivial predicate, not the total relation. -/
theorem Derivable_nontrivial : ∃ s : Sequent, ¬ Derivable s :=
  ⟨⟨[], .priorFamily badPrior⟩, not_derivable_badPrior []⟩

end TPTND
