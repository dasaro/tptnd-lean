import TPTND

/-! # Deep trees II: the rules the case studies never reach

`DeepTrees.lean`, `COMPASFromData.lean` and `HMDAShowcase.lean` between them
exercise 22 of the 41 dispatched rules — the statistical spine.  The remaining
19 never appear.  Two of those, `E×L`/`E×R`, are *unreachable from leaves*: each
demands a premise about a projection term (`fst v` / `snd v`) and no leaf rule
concludes a projection, so neither can be fed without the other.  This file
exercises the other **17** in two deep, dense trees.

* **Tree A — declarations and the expected layer** (depth 6).  Five output
  declarations feed one opaque `unknown` process; a separate `base`/`extend`/
  `extend_det` chain builds a genuine distribution; the expected layer runs
  `expectation → I× → I→ → E→`; and two `WeakeningD` steps import both
  distributions into scope.
  New rules: output_atom, output_neg, output_sum, output_prod, output_arr,
  unknown, base, extend, extend_det, expectation, I×, WeakeningD.

* **Tree B — sums into the trust layer** (depth 7).  Two sampled batches are
  pooled, read a second time at the other output, combined with `I+`, the left
  summand is stripped back off with `E+L`, that result is certified against a
  model cited by `identity_star`, and `ETex` re-enters the trusted value on the
  expected layer.  `E+R` recovers the other summand from the same `I+` node.
  New rules: I+, E+L, E+R, identity_star, ETex.
  Note the `E+L`/`E+R` inside this tree sit directly on the `I+`, so each is a
  *matching detour* in the sense of `SumNormalization` — a concrete instance of
  `sum_detour_elimination`, which contracts them back to the other `I+` premise.
  `dPlusELdirect` gives the non-detour use: the sum is *observed* at the
  compound event, so `E+L` strips a summand off a sum the calculus never built.

Every node is checked by `checkDerivation`; depths and node counts are measured
by the reported figures, not asserted. -/

open TPTND

private def P (n d : Nat) : Prob := clampProb ((n : ℚ) / d)
private def nd (r : String) (ps : List Derivation) (c : Context) (cl : Claim) :
    Derivation := .node r ps ⟨c, cl⟩ false
private def ndW (r : String) (ps : List Derivation) (c : Context) (cl : Claim) :
    Derivation := .node r ps ⟨c, cl⟩ true
private def S (s : String) : Finset String := {s}

private partial def depth : Derivation → Nat
  | .node _ ps _ _ => 1 + (ps.map depth).foldl max 0
private partial def nodeCount : Derivation → Nat
  | .node _ ps _ _ => 1 + (ps.map nodeCount).foldl (· + ·) 0
private partial def rulesOf : Derivation → List String
  | .node r ps _ _ => r :: (ps.map rulesOf).flatten

private def report (nm : String) (d : Derivation) : IO Unit := do
  match checkDerivation d with
  | .ok () =>
      IO.println s!"  ok   {nm}"
      IO.println s!"         depth {depth d}, {nodeCount d} nodes, \
{(rulesOf d).eraseDups.length} distinct rules"
  | .error m => IO.println s!"  FAIL {nm}\n         ↳ {m}"

-- ════════════════════════════════════════════════════════════════════
--  TREE A — declarations and the expected layer
-- ════════════════════════════════════════════════════════════════════

private def oe : Output := .atom "e"
private def of : Output := .atom "f"
private def og : Output := .atom "g"

-- the five output declarations (Table 1)
private def dOE : Derivation := nd "output_atom" [] [] (.outputDecl oe)
private def dOF : Derivation := nd "output_atom" [] [] (.outputDecl of)
private def dOG : Derivation := nd "output_atom" [] [] (.outputDecl og)
private def dNeg : Derivation :=
  nd "output_neg" [dOE] [] (.outputDecl (.neg oe))
private def dSum : Derivation :=
  nd "output_sum" [dOF, dOG] [] (.outputDecl (.sum of og))
private def dProd : Derivation :=
  nd "output_prod" [dOE, dOF] [] (.outputDecl (.prod oe of))
private def dArr : Derivation :=
  nd "output_arr" [dOE, dOF] [] (.outputDecl (.arr oe (P 1 3) of))

/-- An opaque process `z` whose five possible outputs span every output former:
    an atom, a negation, a sum, a product and an arrow.  `unknown` demands one
    variable, pairwise-distinct outputs, and a declaration for each. -/
private def zE  : ContextEntry := ⟨"z", S "z", oe, .unknown⟩
private def zN  : ContextEntry := ⟨"z", S "z", .neg oe, .unknown⟩
private def zS  : ContextEntry := ⟨"z", S "z", .sum of og, .unknown⟩
private def zP  : ContextEntry := ⟨"z", S "z", .prod oe of, .unknown⟩
private def zA  : ContextEntry := ⟨"z", S "z", .arr oe (P 1 3) of, .unknown⟩
private def Zctx : Context := [zE, zN, zS, zP, zA]
private def dUnknown : Derivation :=
  nd "unknown" [dOE, dNeg, dSum, dProd, dArr] Zctx (.distDecl Zctx)

-- a genuine distribution, built by extension
private def x2a : ContextEntry := ⟨"x2", S "x2", .atom "a", .exact (P 1 3)⟩
private def x2b : ContextEntry := ⟨"x2", S "x2", .atom "b", .exact (P 1 3)⟩
private def y2c : ContextEntry := ⟨"y2", S "y2", .atom "cc", .exact (P 1 1)⟩
private def dBase : Derivation := nd "base" [] [] (.distDecl [])
private def dExt1 : Derivation :=
  nd "extend" [dBase] [x2a] (.distDecl [x2a])
private def dExt2 : Derivation :=
  nd "extend" [dExt1] [x2a, x2b] (.distDecl [x2a, x2b])
private def dExtDet : Derivation :=
  nd "extend_det" [dExt2] [x2a, x2b, y2c] (.distDecl [x2a, x2b, y2c])

-- the expected layer
private def oc : Output := .atom "c"
private def od : Output := .atom "d"
private def xC : ContextEntry := ⟨"x", S "x", oc, .exact (P 1 3)⟩
private def yD : ContextEntry := ⟨"y", S "y", od, .exact (P 1 2)⟩
private def uC : ContextEntry := ⟨"u", S "u", oc, .exact (P 1 4)⟩
private def ρ : Provenance := S "ρ*"

private def dExpX : Derivation :=
  nd "expectation" [] [xC] (.term ⟨.expected, .atom "x", 1, oc, P 1 3, ρ⟩)
private def dExpY : Derivation :=
  nd "expectation" [] [yD] (.term ⟨.expected, .atom "y", 1, od, P 1 2, ρ⟩)
private def dExpU : Derivation :=
  nd "expectation" [] [uC] (.term ⟨.expected, .atom "u", 1, oc, P 1 4, ρ⟩)

/-- `I×` under an explicit independence witness: only *expected* probabilities
    multiply. -/
private def dProdI : Derivation :=
  ndW "I×" [dExpX, dExpY] [xC, yD]
    (.term ⟨.expected, .pair (.atom "x") (.atom "y"), 1, .prod oc od,
      probMul (P 1 3) (P 1 2), ρ⟩)

/-- `I→` discharges `x : c_{1/3}` from the pair judgement, internalising the
    discharged value as the arrow's annotation. -/
private def dArrI : Derivation :=
  nd "I→" [dProdI] [yD]
    (.term ⟨.expected, .lam "x" (.pair (.atom "x") (.atom "y")), 1,
      .arr oc (P 1 3) (.prod oc od), probMul (P 1 3) (P 1 2), ρ⟩)

/-- `E→` applies it to `u : c_{1/4}`; the values multiply. -/
private def dArrE : Derivation :=
  nd "E→" [dArrI, dExpU] [yD, uC]
    (.term ⟨.expected,
      .app (.lam "x" (.pair (.atom "x") (.atom "y"))) (.atom "u"), 1,
      .prod oc od, probMul (probMul (P 1 3) (P 1 2)) (P 1 4), ρ⟩)

/-- `WeakeningD` imports the opaque process `z` into scope (variable-disjoint
    from `y`, `u`), then a second `WeakeningD` imports the built distribution. -/
private def dWD1 : Derivation :=
  ndW "WeakeningD" [dArrE, dUnknown] (mergeContexts [[yD, uC], Zctx])
    (.term ⟨.expected,
      .app (.lam "x" (.pair (.atom "x") (.atom "y"))) (.atom "u"), 1,
      .prod oc od, probMul (probMul (P 1 3) (P 1 2)) (P 1 4), ρ⟩)

private def treeA : Derivation :=
  ndW "WeakeningD" [dWD1, dExtDet]
    (mergeContexts [mergeContexts [[yD, uC], Zctx], [x2a, x2b, y2c]])
    (.term ⟨.expected,
      .app (.lam "x" (.pair (.atom "x") (.atom "y"))) (.atom "u"), 1,
      .prod oc od, probMul (probMul (P 1 3) (P 1 2)) (P 1 4), ρ⟩)

-- ════════════════════════════════════════════════════════════════════
--  TREE B — sums into the trust layer
-- ════════════════════════════════════════════════════════════════════

private def oa : Output := .atom "A"
private def ob : Output := .atom "B"
private def tK : Term := .atom "k"
private def kA : ContextEntry := ⟨"k", S "k", oa, .unknown⟩
private def kB : ContextEntry := ⟨"k", S "k", ob, .unknown⟩
private def kAB : ContextEntry := ⟨"k", S "k", .sum oa ob, .unknown⟩
/-- The process may report `A`, `B`, or the compound event `A + B`; the last
    entry is what `ETex` will later commit to a value. -/
private def ΓB : Context := [kA, kB, kAB]

private def tok (i : Nat) : Provenance := S s!"ρ{i}"
private def provRange (lo hi : Nat) : Provenance :=
  (List.range (hi - lo)).foldl (fun acc i => acc ∪ S s!"ρ{lo + i}") ∅

private def run (i : Nat) (out : Output) : Derivation :=
  nd "experiment" [] ΓB (.term ⟨.frequency, tK, 1, out, P 1 1, tok i⟩)

/-- Four single runs, two hitting `A`. -/
private def batch (base : Nat) : List Derivation :=
  (List.range 4).map (fun i => run (base + i) (if i < 2 then oa else ob))

private def dSamp1 : Derivation :=
  nd "sampling" (batch 0) ΓB
    (.term ⟨.frequency, tK, 4, oa, P 1 2, provRange 0 4⟩)
private def dSamp2 : Derivation :=
  nd "sampling" (batch 4) ΓB
    (.term ⟨.frequency, tK, 4, oa, P 1 2, provRange 4 8⟩)
private def dPool : Derivation :=
  nd "update" [dSamp1, dSamp2] ΓB
    (.term ⟨.frequency, tK, 8, oa, P 1 2, provRange 0 8⟩)

/-- The *same* eight runs read at the other output — hence the same provenance,
    which is exactly what `I+` requires of its premises. -/
private def dObsB : Derivation :=
  nd "obs" [] ΓB (.term ⟨.frequency, tK, 8, ob, P 1 4, provRange 0 8⟩)

/-- `I+`: disjoint outputs over one history, so the rates add. -/
private def dPlusI : Derivation :=
  nd "I+" [dPool, dObsB] ΓB
    (.term ⟨.frequency, tK, 8, .sum oa ob, P 3 4, provRange 0 8⟩)

/-- `E+L` strips the left summand back off: (3/4) − (1/2) = 1/4. -/
private def dPlusEL : Derivation :=
  nd "E+L" [dPlusI, dPool] ΓB
    (.term ⟨.frequency, tK, 8, ob, P 1 4, provRange 0 8⟩)

/-- `E+R` recovers the right summand from the same node: (3/4) − (1/4) = 1/2. -/
private def dPlusER : Derivation :=
  nd "E+R" [dPlusI, dObsB] ΓB
    (.term ⟨.frequency, tK, 8, oa, P 1 2, provRange 0 8⟩)

/-- The `E+L`/`E+R` above sit directly on the `I+`, so each is a *matching
    detour* — `sum_detour_elimination` contracts them straight back to the other
    `I+` premise.  Genuinely non-detour use takes the sum from somewhere the
    calculus did not just build it: here the process is observed at the compound
    event directly, and the left summand is stripped off a sum that was never
    introduced. -/
private def dObsSum : Derivation :=
  nd "obs" [] ΓB (.term ⟨.frequency, tK, 8, .sum oa ob, P 3 4, provRange 0 8⟩)

private def dPlusELdirect : Derivation :=
  nd "E+L" [dObsSum, dPool] ΓB
    (.term ⟨.frequency, tK, 8, ob, P 1 4, provRange 0 8⟩)

/-- The benchmark is cited out of a two-entry model context by `identity_star`. -/
private def mB : ContextEntry := ⟨"m", S "m", ob, .exact (P 1 4)⟩
private def mOther : ContextEntry := ⟨"m2", S "m2", oa, .exact (P 1 2)⟩
private def dModel : Derivation :=
  nd "identity_star" [] [mB, mOther] (.identity mB)

private def ciB : Constraint := binomialCI 8 (P 1 4) (P 1 4)

/-- `IT` certifies the recovered summand against the model. -/
private def dIT : Derivation :=
  nd "IT" [dModel, dPlusEL] (mergeContexts [[mB, mOther], ΓB])
    (.trust (.trust .oneSample tK 8 ob (P 1 4) (P 1 4) ciB (provRange 0 8)))

/-- `ETex` commits the observed variable's own opaque assumption to the trusted
    value and re-enters the expected layer. -/
private def kBex : ContextEntry := ⟨"k", S "k", ob, .exact (P 1 4)⟩
private def treeB : Derivation :=
  nd "ETex" [dIT]
    ((mergeContexts [[mB, mOther], ΓB]).filter (· != kB) ++ [kBex])
    (.term ⟨.expected, tK, 8, ob, P 1 4, provRange 0 8⟩)

-- ════════════════════════════════════════════════════════════════════
--  TREE C — a discriminating audit, feeding a Bayesian update
-- ════════════════════════════════════════════════════════════════════

/-! The Chebyshev half-width is `z·√(p(1−p)/n)` with `z = √20`, so it shrinks
    only as `1/√n`: at small `n` the interval clamps to `[0,1]` and the trust
    test accepts anything.  At `n = 500` it is `𝒫 = [2/5, 3/5]` — narrow enough
    that the *same* observation certifies one model and refutes another:

      m  : FPR_½    →  ½   ∈ [.400, .600]  →  IT   (Trust)
      m′ : FPR_3/10 →  3/10 ∉ [.408, .592]  →  IUT  (UTrust)

    That audited observation is then what the prior family is conditioned on.
    Hypotheses are kept close together (.45 / .50 / .55): with 500 samples a
    coarse prior saturates (the posterior would round to 1.0000), so a
    non-degenerate posterior needs hypotheses the data cannot trivially
    separate. -/

private def FPR : Output := .atom "FPR"
private def tQ : Term := .atom "q"
private def qF : ContextEntry := ⟨"q", S "q", FPR, .unknown⟩
private def ΓQ : Context := [qF]

/-- Two independently-provenanced half-samples of 250 runs each. -/
private def qObs1 : Derivation :=
  nd "obs" [] ΓQ (.term ⟨.frequency, tQ, 250, FPR, P 1 2, S "σ1"⟩)
private def qObs2 : Derivation :=
  nd "obs" [] ΓQ (.term ⟨.frequency, tQ, 250, FPR, P 1 2, S "σ2"⟩)
private def qPool : Derivation :=
  nd "update" [qObs1, qObs2] ΓQ
    (.term ⟨.frequency, tQ, 500, FPR, P 1 2, S "σ1" ∪ S "σ2"⟩)

-- the model that survives the test
private def mQ : ContextEntry := ⟨"m", S "m", FPR, .exact (P 1 2)⟩
private def qModel : Derivation := nd "identity" [] [mQ] (.identity mQ)
private def ciQ : Constraint := binomialCI 500 (P 1 2) (P 1 2)
private def qIT : Derivation :=
  nd "IT" [qModel, qPool] (ΓQ ++ [mQ])
    (.trust (.trust .oneSample tQ 500 FPR (P 1 2) (P 1 2) ciQ (S "σ1" ∪ S "σ2")))
private def qET : Derivation :=
  nd "ET" [qIT] (ΓQ ++ [mQ, ⟨"q", S "q", FPR, ciQ⟩])
    (.term ⟨.frequency, tQ, 500, FPR, P 1 2, S "σ1" ∪ S "σ2"⟩)

-- the model the SAME data refutes
private def mQ' : ContextEntry := ⟨"m'", S "m'", FPR, .exact (P 3 10)⟩
private def qModel' : Derivation := nd "identity" [] [mQ'] (.identity mQ')
private def ciQ' : Constraint := binomialCI 500 (P 1 2) (P 3 10)
private def qIUT : Derivation :=
  nd "IUT" [qModel', qPool] (ΓQ ++ [mQ'])
    (.trust (.untrust .oneSample tQ 500 FPR (P 1 2) (P 3 10) ciQ'
      (S "σ1" ∪ S "σ2")))
private def qEUT : Derivation :=
  nd "EUT" [qIUT]
    (ΓQ ++ [mQ', ⟨"q", S "q", FPR, Constraint.complementOf ciQ'⟩])
    (.term ⟨.frequency, tQ, 500, FPR, P 1 2, S "σ1" ∪ S "σ2"⟩)

/-- Three close hypotheses about the false-positive rate, each carrying a prior
    mass that is **not** the hypothesis value — what `identity_model`
    (IDENTITY*₂) exists to make expressible.  Weights sum to 1. -/
private def hyp (a : Prob) : ContextEntry := ⟨"h", S "h", FPR, .exact a⟩
private def wgt (b : Prob) : ContextEntry := ⟨"w", S "w", FPR, .exact b⟩
private def priorPt (a b : Prob) : Derivation :=
  nd "identity_model" [] [hyp a] (.identity (wgt b))

private def famQ : PriorFamily :=
  { xName := "h", alpha := FPR, yName := "w", beta := FPR,
    points := [(P 9 20, P 1 3), (P 1 2, P 1 3), (P 11 20, P 1 3)] }

private def qPrior : Derivation :=
  nd "I-P" [priorPt (P 9 20) (P 1 3), priorPt (P 1 2) (P 1 3),
            priorPt (P 11 20) (P 1 3)] []
    (.priorFamily famQ)

private def postQ : Prob :=
  clampProb ((bayesianPosterior
    [((P 9 20).val, (P 1 3).val), ((P 1 2).val, (P 1 3).val),
     ((P 11 20).val, (P 1 3).val)] 250 500 1).getD 0)

/-- `E-P` conditions the prior on the **audited** observation (the `ET`
    conclusion), not on a bare leaf. -/
private def treeC : Derivation :=
  nd "E-P" [qPrior, qET]
    (ΓQ ++ [mQ, ⟨"q", S "q", FPR, ciQ⟩] ++ [hyp (P 1 2)])
    (.identity (wgt postQ))

private def dec4 (q : ℚ) : String :=
  let r := (q * 10000).floor
  s!"{r / 10000}.{(r % 10000).toNat.repr.leftpad 4 '0'}"
private def showCI (nm : String) (c : Constraint) : IO Unit :=
  match c with
  | .interval lo hi => IO.println s!"         {nm} = [{dec4 lo.val}, {dec4 hi.val}]"
  | .outsideInterval lo hi =>
      IO.println s!"         {nm} = outside [{dec4 lo.val}, {dec4 hi.val}]"
  | _ => IO.println s!"         {nm} = (not an interval)"

-- ════════════════════════════════════════════════════════════════════

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println " Deep trees II — the rules the case studies never reach"
  IO.println "═══════════════════════════════════════════════════════════\n"
  IO.println "Tree A — declarations and the expected layer"
  report "A.1  unknown over all five output formers" dUnknown
  report "A.2  base → extend → extend → extend_det" dExtDet
  report "A.3  I× (independence witness)" dProdI
  report "A.4  I→ discharging x : c_1/3" dArrI
  report "A.5  E→ applying it to u : c_1/4" dArrE
  report "A.6  TREE A (two WeakeningD imports)" treeA
  IO.println "\nTree B — sums into the trust layer"
  report "B.1  update over two sampled batches" dPool
  report "B.2  I+ over one history" dPlusI
  report "B.3  E+L (strip left summand)" dPlusEL
  report "B.4  E+R (recover right summand)" dPlusER
  report "B.4' E+L on an OBSERVED sum (not a detour)" dPlusELdirect
  report "B.5  identity_star (cite from 2-entry model)" dModel
  report "B.6  TREE B (… → IT → ETex)" treeB
  IO.println "\nTree C — a discriminating audit, feeding a Bayesian update"
  report "C.1  update over two 250-run half-samples" qPool
  report "C.2  IT  — model 1/2 SURVIVES the test" qIT
  showCI "𝒫(500, 1/2, 1/2)" ciQ
  report "C.3  IUT — model 3/10 is REFUTED by the same data" qIUT
  showCI "𝒫(500, 1/2, 3/10)" ciQ'
  report "C.4  ET  (re-enter the audited interval)" qET
  report "C.5  EUT (re-enter the complement)" qEUT
  report "C.6  I-P prior family (weights ≠ hypothesis values)" qPrior
  report "C.7  TREE C (E-P on the audited observation)" treeC
  IO.println s!"         posterior for h : FPR_1/2  ≈  {dec4 postQ.val}  (prior was 1/3)"
  IO.println "\nRule coverage of these trees"
  let covered := ((rulesOf treeA ++ rulesOf treeB ++ rulesOf treeC ++ rulesOf dPlusER ++ rulesOf dPlusELdirect).eraseDups)
  IO.println s!"  {covered.length} distinct rules: {covered}"
