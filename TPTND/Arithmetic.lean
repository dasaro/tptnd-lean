import TPTND.Syntax
import Mathlib.Tactic.Linarith

namespace TPTND

/-! # TPTND Arithmetic Helpers

Rational arithmetic in [0,1], confidence intervals, and constraint membership.
Follows Section 4 of the TPTND Lean Design Document.

All arithmetic uses exact rational (`ℚ`) computation.  The CI functions use a
rational Newton's-method approximation for square roots (15 iterations). -/

-- ============================================================================
-- Prob arithmetic staying in [0,1]
-- ============================================================================

/-- a + b, fails if the sum exceeds 1. -/
def probAdd (a b : Prob) : Option Prob :=
  if h : a.val + b.val ≤ 1 then
    some ⟨a.val + b.val, add_nonneg a.hlo b.hlo, h⟩
  else none

/-- a − b, fails if the difference is negative. -/
def probSub (a b : Prob) : Option Prob :=
  if h : 0 ≤ a.val - b.val then
    some ⟨a.val - b.val, h, by linarith [a.hhi, b.hlo]⟩
  else none

/-- a · b — always in [0,1]. -/
def probMul (a b : Prob) : Prob :=
  ⟨a.val * b.val,
   mul_nonneg a.hlo b.hlo,
   by nlinarith [a.hhi, b.hhi, a.hlo, b.hlo]⟩

/-- a / b, fails if b = 0 or the quotient exceeds 1. -/
def probDiv (a b : Prob) : Option Prob :=
  if b.val = 0 then none
  else
    let r := a.val / b.val
    if h₁ : 0 ≤ r then
      if h₂ : r ≤ 1 then
        some ⟨r, h₁, h₂⟩
      else none
    else none

-- ============================================================================
-- Weighted frequency combination  (UPDATE rule formula)
-- ============================================================================

/-- (n · f + m · g) / (n + m).  Fails when n + m = 0. -/
def weightedFreq (n : Nat) (f : Prob) (m : Nat) (g : Prob) : Option Prob :=
  if n + m = 0 then none
  else
    let q := ((n : ℚ) * f.val + (m : ℚ) * g.val) / ((n + m : ℕ) : ℚ)
    if h₁ : 0 ≤ q then
      if h₂ : q ≤ 1 then
        some ⟨q, h₁, h₂⟩
      else none
    else none

-- ============================================================================
-- Rational square-root approximation (Newton's method, 15 iterations)
-- ============================================================================

def ratSqrtAux (x : ℚ) : Nat → ℚ → ℚ
  | 0, y => y
  | n + 1, y =>
    if y = 0 then 0
    else ratSqrtAux x n ((y + x / y) / 2)

/-- Round a non-negative rational UP to the next k/precision.
    Keeps denominators bounded after Newton iteration.

    Ceiling, not nearest: the Newton iterate over-approximates √x (AM–GM),
    and rounding up preserves that, so `ratSqrt x ≥ √x` always.  Rounding to
    nearest could land below √x by up to 5·10⁻⁷, making the implemented
    interval NARROWER than the exact acceptance region — which is exactly the
    case `trust_coverage` does not cover. -/
def roundRatUp (q : ℚ) (precision : Nat) : ℚ :=
  if precision = 0 then q
  else
    -- ⌈q · precision⌉ / precision; for num ≥ 0, den > 0.
    let num := q.num * (precision : ℤ)
    let den := (q.den : ℤ)
    let ceiled := (num + den - 1) / den
    (ceiled : ℚ) / (precision : ℚ)

/-- Rational OVER-approximation of √x.  Returns 0 for x ≤ 0.
    The Newton iterate over-approximates and the rounding is a ceiling, so
    the result never under-approximates the true square root; the implemented
    interval is therefore never narrower than the exact acceptance region,
    and the Chebyshev 5 % level transfers to it. -/
def ratSqrt (x : ℚ) : ℚ :=
  if x ≤ 0 then 0
  else roundRatUp (ratSqrtAux x 15 (max x 1)) 1000000

-- ============================================================================
-- Confidence intervals
-- ============================================================================

/-- The constant of the acceptance region `|f − p| ≤ z·√(p(1−p)/n)`.

    This is `√20 ≈ 4.4721`, **not** the normal quantile 1.96.  With `z = √20`
    Chebyshev's inequality gives a *provable* 5 % level
    (`Operational.TrustGuarantee.trust_coverage_05`): if the model is correct
    the test fails with probability at most `1/z² = 1/20`.  The familiar 1.96
    reaches 5 % only through a normal approximation, which would need a central
    limit theorem with a finite-`n` error term to justify; the price of doing
    without one is an interval about 2.28 times wider.

    The rational is rounded **up** (`4.472136 > √20`) on purpose: the
    implemented interval must never be narrower than the exact acceptance
    region, or the 5 % bound would not transfer to it. -/
def zCheb : ℚ := 559017 / 125000

/-- Clamp a rational to [0,1] and wrap as `Prob`. -/
def clampProb (q : ℚ) : Prob :=
  let c := max 0 (min 1 q)
  ⟨c, le_max_left 0 _, max_le (by norm_num : (0 : ℚ) ≤ 1) (min_le_left 1 q)⟩

/-- Binomial CI  𝒫(n, f, p) = [ℓ, h].
    Score-test (Wald) interval centred at f with variance under p:
      f ± z₉₅ · √(p(1−p)/n)
    Endpoints clamped to [0,1].  Returns `unknown` when n = 0. -/
def binomialCI (n : Nat) (f p : Prob) : Constraint :=
  if n = 0 then .unknown
  else
    let variance := p.val * (1 - p.val) / (n : ℚ)
    let se := ratSqrt variance
    let lo := f.val - zCheb * se
    let hi := f.val + zCheb * se
    .interval (clampProb lo) (clampProb hi)

/-- Two-sample proportion CI  𝒬(n, m, f, g) = [ℓ, h].
    Score-test (pooled) interval for the difference f − g:
      (f − g) ± z₉₅ · √(p̂(1−p̂)(1/n + 1/m))
    where p̂ = (nf + mg)/(n + m) is the pooled rate under H₀: p₁ = p₂.
    This is consistent with `binomialCI` (both use null-hypothesis variance).
    Endpoints clamped to [0,1].  Returns `unknown` when n = 0 or m = 0. -/
def twoSampleCI (n m : Nat) (f g : Prob) : Constraint :=
  if n = 0 || m = 0 then .unknown
  else
    let nq := (n : ℚ)
    let mq := (m : ℚ)
    let pHat := (nq * f.val + mq * g.val) / (nq + mq)
    let variance := pHat * (1 - pHat) * (1 / nq + 1 / mq)
    let se := ratSqrt variance
    let diff := f.val - g.val
    let lo := diff - zCheb * se
    let hi := diff + zCheb * se
    .interval (clampProb lo) (clampProb hi)

-- ============================================================================
-- Constraint membership
-- ============================================================================

/-- Does `p` lie inside `c`? -/
def inConstraint (p : Prob) (c : Constraint) : Bool :=
  c.contains p

/-- Does `p` lie outside `c`? -/
def notInConstraint (p : Prob) (c : Constraint) : Bool :=
  !c.contains p


/-- Single-hypothesis weight: aˢ · (1−a)^{n−s} · b -/
private def bayesWeight (a b : ℚ) (s n : Nat) : ℚ :=
  a ^ s * (1 - a) ^ (n - s) * b

/-- Bayesian posterior for hypothesis j:
    aⱼˢ · (1−aⱼ)^{n−s} · bⱼ  /  Σᵢ aᵢˢ · (1−aᵢ)^{n−s} · bᵢ -/
def bayesianPosterior
    (pairs : List (ℚ × ℚ)) (s n : Nat) (j : Nat) : Option ℚ :=
  let weights := pairs.map (fun ⟨a, b⟩ => bayesWeight a b s n)
  let denom := weights.foldl (· + ·) 0
  if denom == 0 then none
  else match weights[j]? with
    | some w => some (w / denom)
    | none   => none

end TPTND
