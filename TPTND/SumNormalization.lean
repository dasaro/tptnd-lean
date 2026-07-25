import TPTND.Spec
import Mathlib.Tactic

/-! # Detour elimination in the sum fragment — and the limits of it

Of TPTND's three connective intro/elim pairs only the **sum** admits any detour
elimination.  The arrow is a probabilistic multiplier — `I→` keeps the body value
`p` and `E→` concludes `probMul p q` (see `Derivable.iArr`/`.eArr`) — so `E→∘I→`
computes rather than contracts and there is no β-contractum; and the product's
eliminations require a premise about a projection term (`snd ⟨t,u⟩`) that no rule
derives from leaves.  This file works out exactly how far the sum gets —
including a **negative** result that is the more interesting half.

**The skeleton.**  In a sum derivation the mode, term, sample size and provenance
must agree across premises, and the contexts agree *up to set equality*.  Fixing
one representative context, such a derivation is described by a *tree shape* plus
an `(output, value)` pair per node.  `SumTree` is that shape and `concl` computes
its conclusion (`none` when ill-formed).

*Scope, stated precisely.*  `SumTree.sound` maps a well-formed skeleton with
derivable leaves **into** `Derivable`.  There is deliberately no converse: since
`Derivable` is a `Prop`, its proofs are not data, so "every sum derivation is a
skeleton" is not expressible against the current specification.  Everything below
is therefore a theorem about the *skeleton rewriting*, which `sound` shows denotes
genuine derivations — not a theorem quantified over all derivations of the
calculus.

**What is eliminated.**  The detour `E+L (I+ e₁ e₂) e` contracts only when the
minor premise `e` proves exactly what `e₁` proved.  `normalize` removes every such
*matching* detour, preserving the conclusion (`normalize_concl`) and never growing
the tree (`normalize_size_le`) — structurally, with no termination measure, because
contracting discards a premise instead of substituting (contrast β).

**What is NOT eliminated — the subformula property fails.**  In a well-formed tree
`conclEL` already forces the minor's output to match the introduced summand, so the
*only* thing that can block contraction is a **value** mismatch — and values are
free (`obs` constrains only that `n·f` be integral, so one context derives the same
output at different values).  `normal_admits_maximal_formula` exhibits this: a
`Normal`, `normalize`-fixed tree whose major premise is still an introduction, whose
maximal formula `α + β` is a subformula of neither the conclusion nor any leaf.

So the honest summary is: **the sum fragment does not normalize** in the
proof-theoretic sense; what holds is matching-detour elimination.  The usual
payoffs of normalization (subformula property, "last rule is an introduction")
do not follow, and none is claimed. -/

namespace TPTND

-- ============================================================================
-- The arithmetic of the contraction
-- ============================================================================

private theorem pAdd_val {a b s : Prob} (h : probAdd a b = some s) :
    s.val = a.val + b.val := by
  unfold probAdd at h
  split_ifs at h with hle
  injection h with h; subst h; rfl

private theorem pSub_of_val {a b d : Prob} (hle : (0 : ℚ) ≤ a.val - b.val)
    (hd : d.val = a.val - b.val) : probSub a b = some d := by
  unfold probSub
  rw [dif_pos hle]
  exact congrArg some (Prob.val_inj hd.symm)

/-- `(f + g) − f = g`: the value content of the left sum-detour. -/
theorem probSub_probAdd_left {f g s : Prob} (h : probAdd f g = some s) :
    probSub s f = some g :=
  pSub_of_val (by rw [pAdd_val h]; linarith [g.hlo]) (by rw [pAdd_val h]; ring)

/-- `(f + g) − g = f`: the value content of the right sum-detour. -/
theorem probSub_probAdd_right {f g s : Prob} (h : probAdd f g = some s) :
    probSub s g = some f :=
  pSub_of_val (by rw [pAdd_val h]; linarith [f.hlo]) (by rw [pAdd_val h]; ring)

-- ============================================================================
-- Conclusions, compositionally
-- ============================================================================

/-- The conclusion an `I+` node builds from its premises' conclusions. -/
def conclI : Option (Output × Prob) → Option (Output × Prob) →
    Option (Output × Prob)
  | some (α, f), some (β, g) =>
      if Output.syntacticallyDisjoint α β then
        match probAdd f g with
        | some s => some (Output.sum α β, s)
        | none => none
      else none
  | _, _ => none

/-- The conclusion an `E+L` node builds: major (the sum) and minor (the left
    summand) give the right summand. -/
def conclEL : Option (Output × Prob) → Option (Output × Prob) →
    Option (Output × Prob)
  | some (Output.sum α β, r), some (α', f) =>
      if α' = α ∧ Output.syntacticallyDisjoint α β = true then
        match probSub r f with
        | some g => some (β, g)
        | none => none
      else none
  | _, _ => none

/-- The conclusion an `E+R` node builds: major and the right summand give the
    left summand. -/
def conclER : Option (Output × Prob) → Option (Output × Prob) →
    Option (Output × Prob)
  | some (Output.sum α β, r), some (β', g) =>
      if β' = β ∧ Output.syntacticallyDisjoint α β = true then
        match probSub r g with
        | some f => some (α, f)
        | none => none
      else none
  | _, _ => none

@[simp] theorem conclI_none_left (b) : conclI none b = none := rfl
@[simp] theorem conclI_none_right (a) : conclI a none = none := by
  cases a with
  | none => rfl
  | some p => obtain ⟨α, f⟩ := p; rfl

@[simp] theorem conclEL_none_left (b) : conclEL none b = none := rfl
@[simp] theorem conclEL_none_right (a) : conclEL a none = none := by
  cases a with
  | none => rfl
  | some p => obtain ⟨α, r⟩ := p; cases α <;> rfl

@[simp] theorem conclER_none_left (b) : conclER none b = none := rfl
@[simp] theorem conclER_none_right (a) : conclER a none = none := by
  cases a with
  | none => rfl
  | some p => obtain ⟨α, r⟩ := p; cases α <;> rfl

-- inversion ------------------------------------------------------------------

theorem conclI_eq {a b : Option (Output × Prob)} {c : Output × Prob}
    (h : conclI a b = some c) :
    ∃ α f β g s, a = some (α, f) ∧ b = some (β, g) ∧
      Output.syntacticallyDisjoint α β = true ∧ probAdd f g = some s ∧
      c = (Output.sum α β, s) := by
  cases a with
  | none => simp at h
  | some p =>
    cases b with
    | none => simp at h
    | some q =>
      obtain ⟨α, f⟩ := p
      obtain ⟨β, g⟩ := q
      simp only [conclI] at h
      by_cases hd : Output.syntacticallyDisjoint α β = true
      · rw [if_pos hd] at h
        cases hpa : probAdd f g with
        | none => rw [hpa] at h; simp at h
        | some s =>
          rw [hpa] at h
          simp only [Option.some.injEq] at h
          exact ⟨α, f, β, g, s, rfl, rfl, hd, hpa, h.symm⟩
      · rw [if_neg hd] at h; simp at h

theorem conclEL_eq {a b : Option (Output × Prob)} {c : Output × Prob}
    (h : conclEL a b = some c) :
    ∃ α β r f g, a = some (Output.sum α β, r) ∧ b = some (α, f) ∧
      Output.syntacticallyDisjoint α β = true ∧ probSub r f = some g ∧
      c = (β, g) := by
  cases a with
  | none => simp at h
  | some p =>
    cases b with
    | none => simp at h
    | some q =>
      obtain ⟨α₀, r⟩ := p
      obtain ⟨α', f⟩ := q
      cases α₀ with
      | atom a => simp [conclEL] at h
      | neg a => simp [conclEL] at h
      | prod a b => simp [conclEL] at h
      | arr a b c => simp [conclEL] at h
      | sum α β =>
        simp only [conclEL] at h
        by_cases hcond : α' = α ∧ Output.syntacticallyDisjoint α β = true
        · rw [if_pos hcond] at h
          cases hps : probSub r f with
          | none => rw [hps] at h; simp at h
          | some g =>
            rw [hps] at h
            simp only [Option.some.injEq] at h
            obtain ⟨hα, hdis⟩ := hcond
            subst hα
            exact ⟨α', β, r, f, g, rfl, rfl, hdis, hps, h.symm⟩
        · rw [if_neg hcond] at h; simp at h

theorem conclER_eq {a b : Option (Output × Prob)} {c : Output × Prob}
    (h : conclER a b = some c) :
    ∃ α β r f g, a = some (Output.sum α β, r) ∧ b = some (β, g) ∧
      Output.syntacticallyDisjoint α β = true ∧ probSub r g = some f ∧
      c = (α, f) := by
  cases a with
  | none => simp at h
  | some p =>
    cases b with
    | none => simp at h
    | some q =>
      obtain ⟨α₀, r⟩ := p
      obtain ⟨β', g⟩ := q
      cases α₀ with
      | atom a => simp [conclER] at h
      | neg a => simp [conclER] at h
      | prod a b => simp [conclER] at h
      | arr a b c => simp [conclER] at h
      | sum α β =>
        simp only [conclER] at h
        by_cases hcond : β' = β ∧ Output.syntacticallyDisjoint α β = true
        · rw [if_pos hcond] at h
          cases hps : probSub r g with
          | none => rw [hps] at h; simp at h
          | some f =>
            rw [hps] at h
            simp only [Option.some.injEq] at h
            obtain ⟨hβ, hdis⟩ := hcond
            subst hβ
            exact ⟨α, β', r, f, g, rfl, rfl, hdis, hps, h.symm⟩
        · rw [if_neg hcond] at h; simp at h

/-- **Harmony, at the level of conclusions (left).**  Eliminating an
    introduction against the very premise it used returns the other premise. -/
theorem conclEL_conclI {a b : Option (Output × Prob)}
    (h : (conclI a b).isSome = true) : conclEL (conclI a b) a = b := by
  cases hci : conclI a b with
  | none => rw [hci] at h; simp at h
  | some c =>
    obtain ⟨α, f, β, g, s, ha, hb, hd, hpa, hce⟩ := conclI_eq hci
    subst ha; subst hb; subst hce
    simp [conclEL, hd, probSub_probAdd_left hpa]

/-- **Harmony, at the level of conclusions (right).** -/
theorem conclER_conclI {a b : Option (Output × Prob)}
    (h : (conclI a b).isSome = true) : conclER (conclI a b) b = a := by
  cases hci : conclI a b with
  | none => rw [hci] at h; simp at h
  | some c =>
    obtain ⟨α, f, β, g, s, ha, hb, hd, hpa, hce⟩ := conclI_eq hci
    subst ha; subst hb; subst hce
    simp [conclER, hd, probSub_probAdd_right hpa]

-- ============================================================================
-- Sum-derivation skeletons
-- ============================================================================

/-- The shape of a sum-fragment derivation.  In `plusEL`/`plusER` the first
    argument is the major premise (the sum) and the second the minor. -/
inductive SumTree where
  | leaf (α : Output) (f : Prob)
  | plusI (d₁ d₂ : SumTree)
  | plusEL (d₁ d₂ : SumTree)
  | plusER (d₁ d₂ : SumTree)

namespace SumTree

def concl : SumTree → Option (Output × Prob)
  | .leaf α f => some (α, f)
  | .plusI d₁ d₂ => conclI d₁.concl d₂.concl
  | .plusEL d₁ d₂ => conclEL d₁.concl d₂.concl
  | .plusER d₁ d₂ => conclER d₁.concl d₂.concl

def leaves : SumTree → List (Output × Prob)
  | .leaf α f => [(α, f)]
  | .plusI d₁ d₂ => d₁.leaves ++ d₂.leaves
  | .plusEL d₁ d₂ => d₁.leaves ++ d₂.leaves
  | .plusER d₁ d₂ => d₁.leaves ++ d₂.leaves

def size : SumTree → ℕ
  | .leaf _ _ => 1
  | .plusI d₁ d₂ => 1 + d₁.size + d₂.size
  | .plusEL d₁ d₂ => 1 + d₁.size + d₂.size
  | .plusER d₁ d₂ => 1 + d₁.size + d₂.size

/-- **Normal**: no *matching* detour — no elimination whose major premise is an
    introduction that already proved the eliminated minor premise. -/
def Normal : SumTree → Prop
  | .leaf _ _ => True
  | .plusI d₁ d₂ => d₁.Normal ∧ d₂.Normal
  | .plusEL d₁ d₂ =>
      (match d₁ with
       | .plusI e₁ _ => e₁.concl ≠ d₂.concl
       | _ => True) ∧ d₁.Normal ∧ d₂.Normal
  | .plusER d₁ d₂ =>
      (match d₁ with
       | .plusI _ e₂ => e₂.concl ≠ d₂.concl
       | _ => True) ∧ d₁.Normal ∧ d₂.Normal

/-- Contract a matching left detour; otherwise rebuild the elimination. -/
def contractEL (n₁ n₂ : SumTree) : SumTree :=
  match n₁ with
  | .plusI e₁ e₂ => if e₁.concl = n₂.concl then e₂ else .plusEL (.plusI e₁ e₂) n₂
  | n => .plusEL n n₂

/-- Contract a matching right detour. -/
def contractER (n₁ n₂ : SumTree) : SumTree :=
  match n₁ with
  | .plusI e₁ e₂ => if e₂.concl = n₂.concl then e₁ else .plusER (.plusI e₁ e₂) n₂
  | n => .plusER n n₂

/-- Contract every matching detour.  Structurally recursive: contracting keeps
    a *subderivation* of the already-normalized major premise, so nothing is
    duplicated and no termination measure is needed. -/
def normalize : SumTree → SumTree
  | .leaf α f => .leaf α f
  | .plusI d₁ d₂ => .plusI d₁.normalize d₂.normalize
  | .plusEL d₁ d₂ => contractEL d₁.normalize d₂.normalize
  | .plusER d₁ d₂ => contractER d₁.normalize d₂.normalize

-- ============================================================================
-- The contraction step: normal, conclusion-preserving, non-growing
-- ============================================================================

theorem contractEL_normal {n₁ n₂ : SumTree} (h1 : n₁.Normal) (h2 : n₂.Normal) :
    (contractEL n₁ n₂).Normal := by
  cases n₁ with
  | plusI e₁ e₂ =>
      simp only [contractEL]
      split_ifs with hif
      · exact h1.2
      · exact ⟨hif, h1, h2⟩
  | leaf a b => exact ⟨trivial, h1, h2⟩
  | plusEL a b => exact ⟨trivial, h1, h2⟩
  | plusER a b => exact ⟨trivial, h1, h2⟩

theorem contractER_normal {n₁ n₂ : SumTree} (h1 : n₁.Normal) (h2 : n₂.Normal) :
    (contractER n₁ n₂).Normal := by
  cases n₁ with
  | plusI e₁ e₂ =>
      simp only [contractER]
      split_ifs with hif
      · exact h1.1
      · exact ⟨hif, h1, h2⟩
  | leaf a b => exact ⟨trivial, h1, h2⟩
  | plusEL a b => exact ⟨trivial, h1, h2⟩
  | plusER a b => exact ⟨trivial, h1, h2⟩

theorem contractEL_concl {n₁ n₂ : SumTree}
    (h : (conclEL n₁.concl n₂.concl).isSome = true) :
    (contractEL n₁ n₂).concl = conclEL n₁.concl n₂.concl := by
  cases n₁ with
  | plusI e₁ e₂ =>
      simp only [contractEL]
      split_ifs with hif
      · have hs : (conclI e₁.concl e₂.concl).isSome = true := by
          cases hci : conclI e₁.concl e₂.concl with
          | none => simp only [concl, hci] at h; simp at h
          | some _ => rfl
        simp only [concl]
        rw [← hif, conclEL_conclI hs]
      · rfl
  | leaf a b => rfl
  | plusEL a b => rfl
  | plusER a b => rfl

theorem contractER_concl {n₁ n₂ : SumTree}
    (h : (conclER n₁.concl n₂.concl).isSome = true) :
    (contractER n₁ n₂).concl = conclER n₁.concl n₂.concl := by
  cases n₁ with
  | plusI e₁ e₂ =>
      simp only [contractER]
      split_ifs with hif
      · have hs : (conclI e₁.concl e₂.concl).isSome = true := by
          cases hci : conclI e₁.concl e₂.concl with
          | none => simp only [concl, hci] at h; simp at h
          | some _ => rfl
        simp only [concl]
        rw [← hif, conclER_conclI hs]
      · rfl
  | leaf a b => rfl
  | plusEL a b => rfl
  | plusER a b => rfl

theorem contractEL_size (n₁ n₂ : SumTree) :
    (contractEL n₁ n₂).size ≤ 1 + n₁.size + n₂.size := by
  cases n₁ with
  | plusI e₁ e₂ =>
      simp only [contractEL]
      split_ifs <;> simp only [size] <;> omega
  | leaf a b => simp only [contractEL, size]; omega
  | plusEL a b => simp only [contractEL, size]; omega
  | plusER a b => simp only [contractEL, size]; omega

theorem contractER_size (n₁ n₂ : SumTree) :
    (contractER n₁ n₂).size ≤ 1 + n₁.size + n₂.size := by
  cases n₁ with
  | plusI e₁ e₂ =>
      simp only [contractER]
      split_ifs <;> simp only [size] <;> omega
  | leaf a b => simp only [contractER, size]; omega
  | plusEL a b => simp only [contractER, size]; omega
  | plusER a b => simp only [contractER, size]; omega

theorem contractEL_leaves (n₁ n₂ : SumTree) :
    (contractEL n₁ n₂).leaves ⊆ n₁.leaves ++ n₂.leaves := by
  cases n₁ with
  | plusI e₁ e₂ =>
      simp only [contractEL]
      split_ifs
      · intro x hx
        simp only [leaves, List.mem_append]
        exact Or.inl (Or.inr hx)
      · exact fun x hx => hx
  | leaf a b => exact fun x hx => hx
  | plusEL a b => exact fun x hx => hx
  | plusER a b => exact fun x hx => hx

theorem contractER_leaves (n₁ n₂ : SumTree) :
    (contractER n₁ n₂).leaves ⊆ n₁.leaves ++ n₂.leaves := by
  cases n₁ with
  | plusI e₁ e₂ =>
      simp only [contractER]
      split_ifs
      · intro x hx
        simp only [leaves, List.mem_append]
        exact Or.inl (Or.inl hx)
      · exact fun x hx => hx
  | leaf a b => exact fun x hx => hx
  | plusEL a b => exact fun x hx => hx
  | plusER a b => exact fun x hx => hx

/-- **The subformula property fails: `Normal` admits maximal formulas.**

    Whenever the eliminated minor premise reports a *different value* for the same
    output (which `obs` freely permits), the elimination-of-an-introduction is
    stuck: the tree is well formed, `Normal`, and fixed by `normalize` — yet its
    major premise is an introduction, so the maximal formula `α + β` survives in a
    normal form while being a subformula of neither the conclusion (`β`) nor any
    leaf (`α`, `β`, `α`).

    This is why the file claims detour *elimination* and not normalization. -/
theorem normal_admits_maximal_formula
    (α β : Output) (f f' g s r : Prob)
    (hdisj : Output.syntacticallyDisjoint α β = true)
    (hadd : probAdd f g = some s)
    (hsub : probSub s f' = some r)
    (hne : f ≠ f') :
    -- the tree is well formed, with conclusion β
    (SumTree.plusEL (.plusI (.leaf α f) (.leaf β g)) (.leaf α f')).concl
        = some (β, r) ∧
    -- its major premise is an INTRODUCTION concluding the maximal formula α + β
    (SumTree.plusI (.leaf α f) (.leaf β g)).concl = some (Output.sum α β, s) ∧
    -- yet the tree is Normal and normalization does not touch it
    (SumTree.plusEL (.plusI (.leaf α f) (.leaf β g)) (.leaf α f')).Normal ∧
    (SumTree.plusEL (.plusI (.leaf α f) (.leaf β g)) (.leaf α f')).normalize
        = SumTree.plusEL (.plusI (.leaf α f) (.leaf β g)) (.leaf α f') ∧
    -- and α + β is a subformula of neither the conclusion nor any leaf output
    Output.sum α β ≠ β ∧ Output.sum α β ≠ α := by
  have hci : conclI (some (α, f)) (some (β, g)) = some (Output.sum α β, s) := by
    simp [conclI, hdisj, hadd]
  have hmc : (SumTree.plusI (.leaf α f) (.leaf β g)).concl
      = some (Output.sum α β, s) := by
    simp only [concl, hci]
  have hminor : (SumTree.leaf α f).concl ≠ (SumTree.leaf α f').concl := by
    simp only [concl, ne_eq, Option.some.injEq, Prod.mk.injEq, not_and]
    intro _; exact hne
  refine ⟨?_, hmc, ⟨hminor, ⟨trivial, trivial⟩, trivial⟩, ?_, ?_, ?_⟩
  · simp only [concl, hci]
    simp [conclEL, hdisj, hsub]
  · simp [normalize, contractEL, hminor]
  · intro h; have := congrArg sizeOf h; simp at this; try omega
  · intro h; have := congrArg sizeOf h; simp at this; try omega

-- ============================================================================
-- normalize: normal, conclusion-preserving, non-growing, leaf-discarding
-- ============================================================================

theorem normalize_normal : ∀ d : SumTree, d.normalize.Normal
  | .leaf _ _ => trivial
  | .plusI d₁ d₂ => ⟨normalize_normal d₁, normalize_normal d₂⟩
  | .plusEL d₁ d₂ =>
      contractEL_normal (normalize_normal d₁) (normalize_normal d₂)
  | .plusER d₁ d₂ =>
      contractER_normal (normalize_normal d₁) (normalize_normal d₂)

theorem normalize_concl : ∀ (d : SumTree), d.concl.isSome = true →
    d.normalize.concl = d.concl
  | .leaf _ _, _ => rfl
  | .plusI d₁ d₂, h => by
      simp only [concl] at h
      have h1 : d₁.concl.isSome = true := by
        cases hc : d₁.concl with
        | none => rw [hc] at h; simp at h
        | some _ => rfl
      have h2 : d₂.concl.isSome = true := by
        cases hc : d₂.concl with
        | none => rw [hc] at h; simp at h
        | some _ => rfl
      simp only [normalize, concl, normalize_concl d₁ h1, normalize_concl d₂ h2]
  | .plusEL d₁ d₂, h => by
      simp only [concl] at h
      have h1 : d₁.concl.isSome = true := by
        cases hc : d₁.concl with
        | none => rw [hc] at h; simp at h
        | some _ => rfl
      have h2 : d₂.concl.isSome = true := by
        cases hc : d₂.concl with
        | none => rw [hc] at h; simp at h
        | some _ => rfl
      simp only [normalize, concl]
      rw [contractEL_concl
            (by rw [normalize_concl d₁ h1, normalize_concl d₂ h2]; exact h),
          normalize_concl d₁ h1, normalize_concl d₂ h2]
  | .plusER d₁ d₂, h => by
      simp only [concl] at h
      have h1 : d₁.concl.isSome = true := by
        cases hc : d₁.concl with
        | none => rw [hc] at h; simp at h
        | some _ => rfl
      have h2 : d₂.concl.isSome = true := by
        cases hc : d₂.concl with
        | none => rw [hc] at h; simp at h
        | some _ => rfl
      simp only [normalize, concl]
      rw [contractER_concl
            (by rw [normalize_concl d₁ h1, normalize_concl d₂ h2]; exact h),
          normalize_concl d₁ h1, normalize_concl d₂ h2]

theorem normalize_size_le : ∀ d : SumTree, d.normalize.size ≤ d.size
  | .leaf _ _ => le_refl _
  | .plusI d₁ d₂ => by
      have h1 := normalize_size_le d₁
      have h2 := normalize_size_le d₂
      simp only [normalize, size]; omega
  | .plusEL d₁ d₂ => by
      have h1 := normalize_size_le d₁
      have h2 := normalize_size_le d₂
      have hc := contractEL_size d₁.normalize d₂.normalize
      simp only [normalize, size]; omega
  | .plusER d₁ d₂ => by
      have h1 := normalize_size_le d₁
      have h2 := normalize_size_le d₂
      have hc := contractER_size d₁.normalize d₂.normalize
      simp only [normalize, size]; omega

private theorem sub_app {A : Type} {l₁ l₂ r₁ r₂ : List A}
    (h1 : l₁ ⊆ r₁) (h2 : l₂ ⊆ r₂) : l₁ ++ l₂ ⊆ r₁ ++ r₂ := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_append.mpr (Or.inl (h1 h))
  · exact List.mem_append.mpr (Or.inr (h2 h))

theorem normalize_leaves_subset : ∀ d : SumTree, d.normalize.leaves ⊆ d.leaves
  | .leaf _ _ => fun x hx => hx
  | .plusI d₁ d₂ => by
      simp only [normalize, leaves]
      exact sub_app (normalize_leaves_subset d₁) (normalize_leaves_subset d₂)
  | .plusEL d₁ d₂ => by
      simp only [normalize, leaves]
      exact (contractEL_leaves d₁.normalize d₂.normalize).trans
        (sub_app (normalize_leaves_subset d₁) (normalize_leaves_subset d₂))
  | .plusER d₁ d₂ => by
      simp only [normalize, leaves]
      exact (contractER_leaves d₁.normalize d₂.normalize).trans
        (sub_app (normalize_leaves_subset d₁) (normalize_leaves_subset d₂))

-- ============================================================================
-- Skeletons denote genuine derivations
-- ============================================================================

private theorem ctxEqSet_refl (Γ : Context) : contextEqSet Γ Γ = true := by
  simp [contextEqSet, List.all_eq_true]

/-- A well-formed skeleton whose leaves are derivable denotes a derivation. -/
theorem sound (Γ : Context) (m : TermMode) (t : Term) (n : ℕ) (σ : Provenance)
    (hwf : contextWF Γ = true) :
    ∀ (d : SumTree) (α : Output) (f : Prob), d.concl = some (α, f) →
      (∀ p ∈ d.leaves, Derivable ⟨Γ, .term ⟨m, t, n, p.1, p.2, σ⟩⟩) →
      Derivable ⟨Γ, .term ⟨m, t, n, α, f, σ⟩⟩
  | .leaf α₀ f₀, α, f, h, hl => by
      simp only [concl, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2
      exact hl (α₀, f₀) (by simp only [leaves, List.mem_singleton])
  | .plusI d₁ d₂, α, f, h, hl => by
      simp only [concl] at h
      obtain ⟨α₁, f₁, β₁, g₁, s, hc1, hc2, hd, ha, hce⟩ := conclI_eq h
      have hbuilt : Derivable ⟨Γ, .term ⟨m, t, n, Output.sum α₁ β₁, s, σ⟩⟩ :=
        .iPlus Γ Γ Γ ⟨m, t, n, α₁, f₁, σ⟩ ⟨m, t, n, β₁, g₁, σ⟩ s hwf
          (sound Γ m t n σ hwf d₁ α₁ f₁ hc1
            (fun p hp => hl p (by simp only [leaves, List.mem_append]; tauto)))
          (sound Γ m t n σ hwf d₂ β₁ g₁ hc2
            (fun p hp => hl p (by simp only [leaves, List.mem_append]; tauto)))
          (ctxEqSet_refl Γ) (ctxEqSet_refl Γ) rfl rfl rfl rfl hd ha
      simp only [Prod.mk.injEq] at hce
      obtain ⟨hα, hf⟩ := hce
      subst hα; subst hf
      exact hbuilt
  | .plusEL d₁ d₂, α, f, h, hl => by
      simp only [concl] at h
      obtain ⟨α₁, β₁, r, f₁, g₁, hc1, hc2, hd, hs, hce⟩ := conclEL_eq h
      have hbuilt : Derivable ⟨Γ, .term ⟨m, t, n, β₁, g₁, σ⟩⟩ :=
        .ePlusL Γ Γ Γ ⟨m, t, n, Output.sum α₁ β₁, r, σ⟩
          ⟨m, t, n, α₁, f₁, σ⟩ β₁ g₁ hwf
          (sound Γ m t n σ hwf d₁ _ r hc1
            (fun p hp => hl p (by simp only [leaves, List.mem_append]; tauto)))
          (sound Γ m t n σ hwf d₂ α₁ f₁ hc2
            (fun p hp => hl p (by simp only [leaves, List.mem_append]; tauto)))
          (ctxEqSet_refl Γ) (ctxEqSet_refl Γ) rfl rfl rfl rfl hd rfl hs
      simp only [Prod.mk.injEq] at hce
      obtain ⟨hα, hf⟩ := hce
      subst hα; subst hf
      exact hbuilt
  | .plusER d₁ d₂, α, f, h, hl => by
      simp only [concl] at h
      obtain ⟨α₁, β₁, r, f₁, g₁, hc1, hc2, hd, hs, hce⟩ := conclER_eq h
      have hbuilt : Derivable ⟨Γ, .term ⟨m, t, n, α₁, f₁, σ⟩⟩ :=
        .ePlusR Γ Γ Γ ⟨m, t, n, Output.sum α₁ β₁, r, σ⟩
          ⟨m, t, n, β₁, g₁, σ⟩ α₁ f₁ hwf
          (sound Γ m t n σ hwf d₁ _ r hc1
            (fun p hp => hl p (by simp only [leaves, List.mem_append]; tauto)))
          (sound Γ m t n σ hwf d₂ β₁ g₁ hc2
            (fun p hp => hl p (by simp only [leaves, List.mem_append]; tauto)))
          (ctxEqSet_refl Γ) (ctxEqSet_refl Γ) rfl rfl rfl rfl hd rfl hs
      simp only [Prod.mk.injEq] at hce
      obtain ⟨hα, hf⟩ := hce
      subst hα; subst hf
      exact hbuilt

end SumTree

-- ============================================================================
-- The normalization theorem
-- ============================================================================

/-- **Matching-detour elimination for sum skeletons.**  `normalize` removes every
    matching detour: the result is `Normal`, has the same conclusion, and is no
    larger.  (Derivability is a *separate* statement — `SumTree.sound` — and is
    deliberately not bundled here: `Derivable` is proof-irrelevant, so a
    `Derivable` conjunct would say nothing about the normal form that it does not
    already say about the input.  See `normal_admits_maximal_formula` for what
    this does NOT give you.) -/
theorem sum_detour_elimination (d : SumTree) (α : Output) (f : Prob)
    (hc : d.concl = some (α, f)) :
    d.normalize.Normal ∧
    d.normalize.concl = some (α, f) ∧
    d.normalize.size ≤ d.size := by
  refine ⟨SumTree.normalize_normal d, ?_, SumTree.normalize_size_le d⟩
  rw [SumTree.normalize_concl d (by rw [hc]; rfl), hc]

/-- The normal form denotes a genuine derivation — via `SumTree.sound`, using
    that normalization only ever discards leaves. -/
theorem sum_normal_form_derivable (Γ : Context) (m : TermMode) (t : Term)
    (n : ℕ) (σ : Provenance) (hwf : contextWF Γ = true)
    (d : SumTree) (α : Output) (f : Prob)
    (hc : d.concl = some (α, f))
    (hl : ∀ p ∈ d.leaves, Derivable ⟨Γ, .term ⟨m, t, n, p.1, p.2, σ⟩⟩) :
    Derivable ⟨Γ, .term ⟨m, t, n, α, f, σ⟩⟩ := by
  have hcn : d.normalize.concl = some (α, f) := by
    rw [SumTree.normalize_concl d (by rw [hc]; rfl), hc]
  exact SumTree.sound Γ m t n σ hwf d.normalize α f hcn
    (fun p hp => hl p (SumTree.normalize_leaves_subset d hp))

end TPTND
