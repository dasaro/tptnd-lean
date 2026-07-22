import TPTND

/-! # Deep derivations: the proof theory at full depth

This file builds and checks derivations that exercise the calculus end to
end: raw single runs collected into batches, batches pooled, the pooled
evidence certified against a model, the certificate audited back into the
context, the competing assumptions contracted to a committed value, and the
committed chain compared across groups.  Every intermediate node is checked,
so the depths reported are measured, not claimed.

The Bayesian branch exercises genuine prior families (weights independent of
the hypothesis values) through `identity_model`.
-/

open TPTND

private def P (n d : Nat) : Prob := clampProb ((n : ℚ) / d)
private def nd (r : String) (ps : List Derivation) (c : Context) (cl : Claim) :
    Derivation := .node r ps ⟨c, cl⟩ false
private def S (s : String) : Finset String := {s}

private partial def depth : Derivation → Nat
  | .node _ ps _ _ => 1 + (ps.map depth).foldl max 0

private partial def nodeCount : Derivation → Nat
  | .node _ ps _ _ => 1 + (ps.map nodeCount).foldl (· + ·) 0

private def HR : Output := Output.atom "HighRisk"
private def LR : Output := Output.atom "LowRisk"

-- ════════════════════════════════════════════════════════════════════
--  Group B: raw runs ⇒ pooled evidence ⇒ certificate ⇒ audit ⇒ commitment
-- ════════════════════════════════════════════════════════════════════

private def rHR : ContextEntry := ⟨"r", S "B", HR, .unknown⟩
private def rLR : ContextEntry := ⟨"r", S "B", LR, .unknown⟩
private def ΓB : Context := [rHR, rLR]
private def tB : Term := Term.atom "r"

/-- One run of `r`, recorded as the single-run experiment judgement. -/
private def runB (ρ : String) (out : Output) : Derivation :=
  nd "experiment" [] ΓB (.term ⟨.frequency, tB, 1, out, P 1 1, S ρ⟩)

/-- Sixteen alternating runs; under the Chebyshev constant `z = √20` a batch
    must carry enough runs for the score-test interval to be informative —
    at the old toy n = 8 the interval was the vacuous `[0, 1]`. -/
private def runsB (base : Nat) : List Derivation :=
  (List.range 16).map (fun i =>
    runB s!"ρ{base + i}" (if i % 2 == 0 then HR else LR))

private def provOf (base count : Nat) : Provenance :=
  (List.range count).foldl (fun acc i => acc ∪ {s!"ρ{base + i}"}) ∅

/-- Batch: sixteen single runs collected into a frequency by `sampling`. -/
private def batchB1 : Derivation :=
  nd "sampling" (runsB 0) ΓB
    (.term ⟨.frequency, tB, 16, HR, P 8 16, provOf 0 16⟩)

private def batchB2 : Derivation :=
  nd "sampling" (runsB 16) ΓB
    (.term ⟨.frequency, tB, 16, HR, P 8 16, provOf 16 16⟩)

private def provB : Provenance := provOf 0 32

/-- The two batches pooled: thirty-two runs, disjoint provenance. -/
private def pooledB : Derivation :=
  nd "update" [batchB1, batchB2] ΓB
    (.term ⟨.frequency, tB, 32, HR, P 1 2, provB⟩)

private def pB : Prob := P 1 2
private def modelE : ContextEntry := ⟨"m", S "model", HR, .exact pB⟩
private def dModel : Derivation := nd "identity" [] [modelE] (.identity modelE)
private def ciB : Constraint := binomialCI 32 (P 1 2) pB

/-- The pooled evidence certified against the model. -/
private def trustB : Derivation :=
  nd "IT" [dModel, pooledB] (ΓB ++ [modelE])
    (.trust (.trust .oneSample tB 32 HR (P 1 2) pB ciB provB))

/-- ET: the audited interval re-enters as an assumption **on `r` itself**. -/
private def auditB : Derivation :=
  nd "ET" [trustB] (ΓB ++ [modelE, ⟨"r", S "B", HR, ciB⟩])
    (.term ⟨.frequency, tB, 32, HR, P 1 2, provB⟩)

/-- Contraction: the two competing assumptions about `r : HighRisk` — the
    opaque one it was observed under, and the audited interval — are reconciled
    into a single committed value. This is the step §3.8 promises and that no
    OVERLAY tree could take. -/
private def commitB : Derivation :=
  nd "Contraction" [auditB] ([⟨"r", S "B", HR, .exact (P 1 2)⟩, rLR] ++ [modelE])
    (.term ⟨.frequency, tB, 32, HR, P 1 2, provB⟩)

-- ════════════════════════════════════════════════════════════════════
--  Group W, and the cross-group comparison
-- ════════════════════════════════════════════════════════════════════

private def sHR : ContextEntry := ⟨"s", S "W", HR, .unknown⟩
private def sLR : ContextEntry := ⟨"s", S "W", LR, .unknown⟩
private def ΓW : Context := [sHR, sLR]
private def tW : Term := Term.atom "s"

private def runW (ρ : String) (out : Output) : Derivation :=
  nd "experiment" [] ΓW (.term ⟨.frequency, tW, 1, out, P 1 1, S ρ⟩)

private def provW : Provenance :=
  (List.range 16).foldl (fun acc i => acc ∪ {s!"τ{i}"}) ∅

private def batchW : Derivation :=
  nd "sampling"
    ((List.range 16).map (fun i =>
      runW s!"τ{i}" (if i % 4 == 0 then HR else LR))) ΓW
    (.term ⟨.frequency, tW, 16, HR, P 4 16, provW⟩)

private def tcB : TermClaim := ⟨.frequency, tB, 32, HR, P 1 2, provB⟩
private def tcW : TermClaim := ⟨.frequency, tW, 16, HR, P 1 4, provW⟩
private def ciCmp : Constraint := twoSampleCI 32 16 (P 1 2) (P 1 4)

/-- INEx: the committed group-B chain compared against group W. The left
    premise is the whole depth-6 audit chain, not a bare observation. -/
private def compare : Derivation :=
  nd "INEx" [commitB, batchW]
    ([⟨"r", S "B", HR, .exact (P 1 2)⟩, rLR, modelE] ++ ΓW)
    (.comparison (.noExcess tcB tcW (P 1 4) ciCmp))

/-- ENEx: eliminate the non-excess certificate against a benchmark for the
    right group, bounding the left group by the shifted interval.  The shifted
    assumption lands on `r` — the left term's own variable. -/
private def pW : Prob := P 1 16
private def modelWE : ContextEntry := ⟨"n", S "modelW", HR, .exact pW⟩
private def dModelW : Derivation := nd "identity" [] [modelWE] (.identity modelWE)

private def shifted : Constraint :=
  match ciCmp with
  | .interval lo hi => .interval (clampProb (pW.val + lo.val)) (clampProb (pW.val + hi.val))
  | c => c

private def bound : Derivation :=
  nd "ENEx" [compare, dModelW]
    ([⟨"r", S "B", HR, .exact (P 1 2)⟩, rLR, modelE] ++ ΓW ++ [modelWE,
      ⟨"r", S "B", HR, shifted⟩])
    (.term tcB)

-- ════════════════════════════════════════════════════════════════════
--  Bayesian: general priors, unlocked by IDENTITY*₂
-- ════════════════════════════════════════════════════════════════════

private def FPR : Output := Output.atom "FPR"
private def hyp (nm : String) (a : Prob) : ContextEntry := ⟨nm, S "hyp", FPR, .exact a⟩
private def wgt (nm : String) (b : Prob) : ContextEntry := ⟨nm, S "prior", FPR, .exact b⟩

/-- `{x : α_a} ⊢ y : β_b` with `b ≠ a` — the IDENTITY*₂ import that makes
    genuine prior weights expressible. -/
private def priorPoint (hn : String) (a b : Prob) : Derivation :=
  nd "identity_model" [] [hyp hn a] (.identity (wgt "w" b))

private def priorFam : Derivation :=
  nd "I-P" [priorPoint "h" (P 1 6) (P 1 2),
            priorPoint "h" (P 1 3) (P 1 3),
            priorPoint "h" (P 1 2) (P 1 6)] []
    (.priorFamily { xName := "h", alpha := FPR, yName := "w", beta := FPR,
                    points := [(P 1 6, P 1 2), (P 1 3, P 1 3), (P 1 2, P 1 6)] })

private def obsEntry : ContextEntry := ⟨"q", S "pilot", FPR, .unknown⟩
private def dObsBayes : Derivation :=
  nd "obs" [] [obsEntry] (.term ⟨.frequency, Term.atom "q", 5, FPR, P 2 5, S "π"⟩)

private def posterior : Prob :=
  clampProb ((bayesianPosterior
    [(P 1 6 |>.val, P 1 2 |>.val), (P 1 3 |>.val, P 1 3 |>.val),
     (P 1 2 |>.val, P 1 6 |>.val)] 2 5 2).getD 0)

private def bayes : Derivation :=
  nd "E-P" [priorFam, dObsBayes] [hyp "h" (P 1 2), obsEntry]
    (.identity ⟨"w", S "prior", FPR, .exact posterior⟩)

-- ════════════════════════════════════════════════════════════════════

private def report (nm : String) (d : Derivation) : IO Unit := do
  match checkDerivation d with
  | .ok () =>
      IO.println s!"  ✓ {nm}"
      IO.println s!"      depth {depth d}, {nodeCount d} nodes"
  | .error m =>
      IO.println s!"  ✗ {nm}\n      ↳ {m}"

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println " Derivations the calculus can build"
  IO.println "═══════════════════════════════════════════════════════════\n"
  IO.println "Group B audit chain — experiment → sampling → update → IT → ET → Contraction"
  report "batch B1 (4 single runs pooled by sampling)" batchB1
  report "batches B1+B2 pooled by update (8 runs)" pooledB
  report "IT: pooled evidence certified against the model" trustB
  report "ET: audited interval re-entered on r itself" auditB
  report "Contraction: competing assumptions reconciled to a value" commitB
  IO.println "\nCross-group comparison over the full chain"
  report "INEx: committed group-B chain vs group W" compare
  report "ENEx: bound group B by the benchmark-shifted interval" bound
  IO.println "\nBayesian fragment with genuine priors (bᵢ ≠ aᵢ)"
  report "I-P: prior family via IDENTITY*₂" priorFam
  report "E-P: posterior for the a = 1/2 hypothesis" bayes
