import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

namespace TPTND

/-! # TPTND Core Syntax

Outputs, probability values, constraints, terms, provenance indices, and contexts.
Follows Section 2 of the TPTND Lean Design Document. -/

-- ============================================================================
-- 2.1 Probability values
-- ============================================================================

structure Prob where
  val : ℚ
  hlo : 0 ≤ val
  hhi : val ≤ 1
  deriving Repr

instance : DecidableEq Prob := fun a b =>
  if h : a.val = b.val then
    isTrue (by cases a; cases b; simp_all)
  else
    isFalse (fun heq => h (congrArg Prob.val heq))

def Prob.ofRat (q : ℚ) (h₀ : 0 ≤ q) (h₁ : q ≤ 1) : Prob :=
  ⟨q, h₀, h₁⟩

def Prob.zero : Prob :=
  ⟨0, le_refl 0, by norm_num⟩

def Prob.one : Prob :=
  ⟨1, by norm_num, le_refl 1⟩

-- ============================================================================
-- 2.2 Outputs
-- ============================================================================

inductive Output where
  | atom : String → Output
  | neg  : Output → Output
  | sum  : Output → Output → Output
  | prod : Output → Output → Output
  -- `arr α a β` is the paper's (α ⇒_a β): the antecedent annotation `a` is
  -- the exact assumption discharged by I→ and is part of the type.
  | arr  : Output → Prob → Output → Output
  deriving Repr, DecidableEq

/-- Collect every atomic name mentioned in an output type.
    Used by `syntacticallyDisjoint` to enforce the I+ side condition α ⊥_syn β. -/
def Output.atoms : Output → Finset String
  | .atom a   => {a}
  | .neg α    => α.atoms
  | .sum α β  => α.atoms ∪ β.atoms
  | .prod α β => α.atoms ∪ β.atoms
  | .arr α _ β => α.atoms ∪ β.atoms

/-- A positive output mentions no negation or arrow: it is a monotone
    combination (`+`, `×`) of atoms.  For such outputs, distinct atoms name
    disjoint elementary events, so atom-disjointness implies event-disjointness.
    Negation breaks this (`¬a` overlaps every atom `b ≠ a`). -/
def Output.isPositive : Output → Bool
  | .atom _   => true
  | .neg _    => false
  | .arr _ _ _ => false
  | .sum α β  => α.isPositive && β.isPositive
  | .prod α β => α.isPositive && β.isPositive

/-- Sound syntactic disjointness (the `α ⊥_syn β` side condition of I+):
    both outputs are positive and share no atomic name.  Positivity is
    essential — without it `¬a` and `b` share no atoms yet overlap as events
    (`b ⊆ ¬a`), which would let I+ double-count `P(¬a) + P(b)`. -/
def Output.syntacticallyDisjoint (α β : Output) : Bool :=
  α.isPositive && β.isPositive && (α.atoms ∩ β.atoms) = ∅

-- ============================================================================
-- 2.3 Probability constraints
-- ============================================================================

inductive Constraint where
  | exact           : Prob → Constraint
  | interval        : Prob → Prob → Constraint
  | outsideInterval : Prob → Prob → Constraint
  | unknown         : Constraint
  deriving Repr, DecidableEq

/-- The complement of an interval constraint (as used by EUT); other
    constraints pass through unchanged. -/
def Constraint.complementOf : Constraint → Constraint
  | .interval lo hi => .outsideInterval lo hi
  | c => c

def Constraint.contains (c : Constraint) (p : Prob) : Bool :=
  match c with
  | .exact v           => decide (v.val = p.val)
  | .interval lo hi    => decide (lo.val ≤ p.val) && decide (p.val ≤ hi.val)
  | .outsideInterval lo hi =>
      decide (p.val < lo.val) || decide (hi.val < p.val)
  | .unknown           => true

-- ============================================================================
-- 2.4 Terms
-- ============================================================================

inductive Term where
  | atom : String → Term
  | pair : Term → Term → Term
  | fst  : Term → Term
  | snd  : Term → Term
  | lam  : String → Term → Term
  | app  : Term → Term → Term
  deriving Repr, DecidableEq

-- ============================================================================
-- 2.5 Provenance indices
-- ============================================================================

-- Finset String has no computable toList; provide a minimal Repr for display.
instance : Repr (Finset String) where
  reprPrec s _ := if s.Nonempty then .text "{…}" else .text "∅"

abbrev Provenance := Finset String

def Provenance.disjoint (σ τ : Provenance) : Bool :=
  (σ ∩ τ) = ∅

def Provenance.union (σ τ : Provenance) : Provenance := σ ∪ τ

-- ============================================================================
-- 2.6 Context entries and contexts
-- ============================================================================

structure ContextEntry where
  name       : String
  support    : Finset String
  output     : Output
  constraint : Constraint
  deriving Repr, DecidableEq

abbrev Context := List ContextEntry

end TPTND
