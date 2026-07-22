import TPTND.JsonCodec

/-! # leaf_examples

Reconstructs the paper's flagship certificates, validates each against
`checkDerivation` (aborting if any expectation is violated), and writes
them as JSON to `web/examples.json` for the HTML interface.

Because the examples are built and validated here, the shipped JSON is
guaranteed to agree with the checker binary.
-/

open TPTND Lean

private def P (n d : Nat) : Prob := clampProb ((n : ℚ) / d)
private def nd (rule : String) (prems : List Derivation)
    (ctx : Context) (claim : Claim) : Derivation :=
  .node rule prems ⟨ctx, claim⟩ false
private def mkS (s : String) : Finset String := {s}
private def mkS2 (a b : String) : Finset String := {a, b}

private def HR := Output.atom "HighRisk"
private def LR := Output.atom "LowRisk"
private def Denied := Output.atom "Denied"

-- ── 1. COMPAS ProPublica headline (IUT, depth 2) ──
private def exProPublica : Derivation :=
  let t := Term.atom "u"
  let p := P 94 427
  let f := P 641 1514
  let ci := binomialCI 1514 f p
  let modelE : ContextEntry := ⟨"w", mkS "WhiteNonRecid", HR, .exact p⟩
  let obsE   : ContextEntry := ⟨"u", mkS "BlackNonRecid", HR, .unknown⟩
  let dModel := nd "identity" [] [modelE] (.identity modelE)
  let dObs := nd "obs" [] [obsE]
    (.term ⟨.frequency, t, 1514, HR, f, mkS2 "σ_m" "σ_f"⟩)
  nd "IUT" [dModel, dObs] [modelE, obsE]
    (.trust (.untrust .oneSample t 1514 HR f p ci (mkS2 "σ_m" "σ_f")))

-- ── 2. COMPAS gender non-finding (IT, depth 2) ──
private def exNonFinding : Derivation :=
  let t := Term.atom "r"
  let p := P 137 486
  let f := P 62 203
  let ci := binomialCI 203 f p
  let modelE : ContextEntry := ⟨"x", mkS "BlackRecidMale", LR, .exact p⟩
  let obsE   : ContextEntry := ⟨"r", mkS "BlackRecidFemale", LR, .unknown⟩
  let dModel := nd "identity" [] [modelE] (.identity modelE)
  let dObs := nd "obs" [] [obsE] (.term ⟨.frequency, t, 203, LR, f, mkS "ρ_f"⟩)
  nd "IT" [dModel, dObs] [modelE, obsE]
    (.trust (.trust .oneSample t 203 LR f p ci (mkS "ρ_f")))

-- ── 3. HMDA Tree A: national benchmark (IT, depth 2) ──
private def exHmdaA : Derivation :=
  let t := Term.atom "d"
  let p := P 1 5
  let f := P 4914 24614
  let ci := binomialCI 24614 f p
  let modelE : ContextEntry := ⟨"w", mkS "NationalBenchmark", Denied, .exact p⟩
  let obsE   : ContextEntry := ⟨"d", mkS "WhiteDE2022", Denied, .unknown⟩
  let dModel := nd "identity" [] [modelE] (.identity modelE)
  let dObs := nd "obs" [] [obsE]
    (.term ⟨.frequency, t, 24614, Denied, f, mkS "σ_W22"⟩)
  nd "IT" [dModel, dObs] [modelE, obsE]
    (.trust (.trust .oneSample t 24614 Denied f p ci (mkS "σ_W22")))

-- ── shared HMDA pooled pieces for Trees B and C ──
private def hmdaPooled :
    Derivation × Derivation × Prob × Prob × Context × Context :=
  let tB := Term.atom "dB"; let tW := Term.atom "dW"
  let ctxB : Context := [⟨"dB", mkS "BlackDE", Denied, .unknown⟩]
  let ctxW : Context := [⟨"dW", mkS "WhiteDE", Denied, .unknown⟩]
  let fB22 := P 2409 7142;   let fB23 := P 2035 5394
  let fW22 := P 4914 24614;  let fW23 := P 3908 17355
  let wfB := P 4444 12536
  let wfW := P 8822 41969
  let dB22 := nd "obs" [] ctxB (.term ⟨.frequency, tB, 7142, Denied, fB22, mkS "σ_B22"⟩)
  let dB23 := nd "obs" [] ctxB (.term ⟨.frequency, tB, 5394, Denied, fB23, mkS "σ_B23"⟩)
  let dW22 := nd "obs" [] ctxW (.term ⟨.frequency, tW, 24614, Denied, fW22, mkS "σ_W22"⟩)
  let dW23 := nd "obs" [] ctxW (.term ⟨.frequency, tW, 17355, Denied, fW23, mkS "σ_W23"⟩)
  let dUpB := nd "update" [dB22, dB23] ctxB
    (.term ⟨.frequency, tB, 12536, Denied, wfB, mkS2 "σ_B22" "σ_B23"⟩)
  let dUpW := nd "update" [dW22, dW23] ctxW
    (.term ⟨.frequency, tW, 41969, Denied, wfW, mkS2 "σ_W22" "σ_W23"⟩)
  (dUpB, dUpW, wfB, wfW, ctxB, ctxW)

-- ── 4. HMDA Tree B: pooled racial disparity (IUT2, depth 3) ──
private def exHmdaB : Derivation :=
  let (dUpB, dUpW, wfB, wfW, ctxB, ctxW) := hmdaPooled
  let ci := twoSampleCI 12536 41969 wfB wfW
  nd "IUT2" [dUpB, dUpW] (ctxB ++ ctxW)
    (.trust (.untrust .twoSample (Term.atom "dB") 12536 Denied wfB wfW ci (mkS2 "σ_B22" "σ_B23" ∪ mkS2 "σ_W22" "σ_W23")))

-- ── 5. HMDA Tree C: full chain UPDATE→IEx→EEx (depth 4) ──
private def exHmdaC : Option Derivation :=
  let (dUpB, dUpW, wfB, wfW, ctxB, ctxW) := hmdaPooled
  let leftTC  : TermClaim :=
    ⟨.frequency, Term.atom "dB", 12536, Denied, wfB, mkS2 "σ_B22" "σ_B23"⟩
  let rightTC : TermClaim :=
    ⟨.frequency, Term.atom "dW", 41969, Denied, wfW, mkS2 "σ_W22" "σ_W23"⟩
  let ci := twoSampleCI 12536 41969 wfB wfW
  match probSub wfB wfW, ci with
  | some diff, .interval lo hi =>
    let dIEx := nd "IEx" [dUpB, dUpW] (ctxB ++ ctxW)
      (.comparison (.excess leftTC rightTC diff ci))
    let modelE : ContextEntry := ⟨"pW", mkS "WhiteDE", Denied, .exact wfW⟩
    let dModel := nd "identity" [] [modelE] (.identity modelE)
    let shiftE : ContextEntry :=
      ⟨"dB", mkS "DE_lending", Denied,
        .interval (clampProb (wfW.val + lo.val)) (clampProb (wfW.val + hi.val))⟩
    some (nd "EEx" [dIEx, dModel]
      (ctxB ++ ctxW ++ [modelE, shiftE]) (.term leftTC))
  | _, _ => none

-- ── 6. HMDA: the SAME national benchmark, rejected for the Black cohort ──
private def exHmdaBlackBenchmark : Derivation :=
  let t := Term.atom "b"
  let p := P 1 5
  let f := P 2409 7142
  let ci := binomialCI 7142 f p
  let modelE : ContextEntry := ⟨"w", mkS "NationalBenchmark", Denied, .exact p⟩
  let obsE   : ContextEntry := ⟨"b", mkS "BlackDE2022", Denied, .unknown⟩
  let dModel := nd "identity" [] [modelE] (.identity modelE)
  let dObs := nd "obs" [] [obsE]
    (.term ⟨.frequency, t, 7142, Denied, f, mkS "σ_B22"⟩)
  nd "IUT" [dModel, dObs] [modelE, obsE]
    (.trust (.untrust .oneSample t 7142 Denied f p ci (mkS "σ_B22")))

-- ── 7. Trust elimination ET: a certificate becomes a reusable assumption ──
private def exETChain : Derivation :=
  let t := Term.atom "r"
  let p := P 137 486
  let f := P 62 203
  let ci := binomialCI 203 f p
  let modelE : ContextEntry := ⟨"x", mkS "BlackRecidMale", LR, .exact p⟩
  let obsE   : ContextEntry := ⟨"r", mkS "BlackRecidFemale", LR, .unknown⟩
  let dModel := nd "identity" [] [modelE] (.identity modelE)
  let dObs := nd "obs" [] [obsE] (.term ⟨.frequency, t, 203, LR, f, mkS "ρ_f"⟩)
  let dIT := nd "IT" [dModel, dObs] [modelE, obsE]
    (.trust (.trust .oneSample t 203 LR f p ci (mkS "ρ_f")))
  let xu : ContextEntry := ⟨"r", mkS "BlackRecidFemale", LR, ci⟩
  nd "ET" [dIT] [modelE, obsE, xu]
    (.term ⟨.frequency, t, 203, LR, f, mkS "ρ_f"⟩)

-- ── 8. Untrust elimination EUT: the complement interval as audit trail ──
private def exEUTChain : Derivation :=
  let t := Term.atom "u"
  let p := P 94 427
  let f := P 641 1514
  let ci := binomialCI 1514 f p
  let modelE : ContextEntry := ⟨"w", mkS "WhiteNonRecid", HR, .exact p⟩
  let obsE   : ContextEntry := ⟨"u", mkS "BlackNonRecid", HR, .unknown⟩
  let dModel := nd "identity" [] [modelE] (.identity modelE)
  let dObs := nd "obs" [] [obsE]
    (.term ⟨.frequency, t, 1514, HR, f, mkS2 "σ_m" "σ_f"⟩)
  let dIUT := nd "IUT" [dModel, dObs] [modelE, obsE]
    (.trust (.untrust .oneSample t 1514 HR f p ci (mkS2 "σ_m" "σ_f")))
  let compl := match ci with
    | .interval lo hi => Constraint.outsideInterval lo hi
    | other => other
  let xu : ContextEntry := ⟨"u", mkS "BlackNonRecid", HR, compl⟩
  nd "EUT" [dIUT] [modelE, obsE, xu]
    (.term ⟨.frequency, t, 1514, HR, f, mkS2 "σ_m" "σ_f"⟩)

-- ── 9. Structural: Contraction reconciles two auditors' assumptions ──
private def exContraction : Derivation :=
  let t := Term.atom "r"
  let rE : ContextEntry := ⟨"r", mkS "pilot", HR, .unknown⟩
  let x1 : ContextEntry := ⟨"x", mkS "auditA", HR, .interval (P 1 5) (P 3 5)⟩
  let x2 : ContextEntry := ⟨"x", mkS "auditB", HR, .interval (P 3 10) (P 1 2)⟩
  let xR : ContextEntry := ⟨"x", mkS "reconciled", HR, .exact (P 2 5)⟩
  let tc : TermClaim := ⟨.frequency, t, 10, HR, P 4 10, mkS "ρ_pilot"⟩
  let dObs := nd "obs" [] [rE, x1, x2] (.term tc)
  nd "Contraction" [dObs] [rE, xR] (.term tc)

-- ── 10. Structural: WeakeningS files a certificate in a wider context ──
private def exWeakening : Derivation :=
  let t := Term.atom "d"
  let p := P 1 5
  let f := P 4914 24614
  let ci := binomialCI 24614 f p
  let modelE : ContextEntry := ⟨"w", mkS "NationalBenchmark", Denied, .exact p⟩
  let obsE   : ContextEntry := ⟨"d", mkS "WhiteDE2022", Denied, .unknown⟩
  let dModel := nd "identity" [] [modelE] (.identity modelE)
  let dObs := nd "obs" [] [obsE]
    (.term ⟨.frequency, t, 24614, Denied, f, mkS "σ_W22"⟩)
  let trustClaim : Claim :=
    .trust (.trust .oneSample t 24614 Denied f p ci (mkS "σ_W22"))
  let dIT := nd "IT" [dModel, dObs] [modelE, obsE] trustClaim
  let bE : ContextEntry := ⟨"b", mkS "BlackDE2022", Denied, .unknown⟩
  let dIdB := nd "identity" [] [bE] (.identity bE)
  -- Explicit independence witness on the weakening node.
  .node "WeakeningS" [dIT, dIdB] ⟨[modelE, obsE, bE], trustClaim⟩ true

-- ── 11. Implication: a conditional policy claim (I→ then E→) ──
private def exImplication : Derivation :=
  let Subprime := Output.atom "Subprime"
  let dT := Term.atom "d"
  let uT := Term.atom "u"
  let ρ := mkS "ρ_batch"
  let dE : ContextEntry := ⟨"d", mkS "batch", Denied, .unknown⟩
  let xE : ContextEntry := ⟨"x", mkS "policy", Subprime, .exact (P 3 10)⟩
  let uE : ContextEntry := ⟨"u", mkS "batch", Subprime, .unknown⟩
  -- Under the assumption x : Subprime_{3/10}, denial runs at 1/2 (n = 200).
  let dObsD := nd "obs" [] [dE, xE]
    (.term ⟨.frequency, dT, 200, Denied, P 1 2, ρ⟩)
  -- I→ discharges the assumption: [x]d : (Subprime ⇒ Denied)_{1/2}
  let arrTC : TermClaim :=
    ⟨.frequency, .lam "x" dT, 200, .arr Subprime (P 3 10) Denied, P 1 2, ρ⟩
  let dIArr := nd "I→" [dObsD] [dE] (.term arrTC)
  -- The antecedent's observed rate: u : Subprime_{3/10} on the same batch.
  let dObsU := nd "obs" [] [uE]
    (.term ⟨.frequency, uT, 200, Subprime, P 3 10, ρ⟩)
  -- E→ composes them: ([x]d · u) : Denied_{3/20}
  nd "E→" [dIArr, dObsU] [dE, uE]
    (.term ⟨.frequency, .app (.lam "x" dT) uT, 200, Denied, P 3 20, ρ⟩)

-- ── 12. Tampered ProPublica certificate (must be REJECTED) ──
private def exTampered : Derivation :=
  let t := Term.atom "u"
  let p := P 94 427
  let f := P 641 1514
  -- Forged interval: narrower than the true CI, placed to look tighter.
  let forged := Constraint.interval (P 41 100) (P 43 100)
  let modelE : ContextEntry := ⟨"w", mkS "WhiteNonRecid", HR, .exact p⟩
  let obsE   : ContextEntry := ⟨"u", mkS "BlackNonRecid", HR, .unknown⟩
  let dModel := nd "identity" [] [modelE] (.identity modelE)
  let dObs := nd "obs" [] [obsE]
    (.term ⟨.frequency, t, 1514, HR, f, mkS2 "σ_m" "σ_f"⟩)
  nd "IUT" [dModel, dObs] [modelE, obsE]
    (.trust (.untrust .oneSample t 1514 HR f p forged (mkS2 "σ_m" "σ_f")))

-- ============================================================================

private structure Example where
  name : String
  description : String
  expectValid : Bool
  cert : Derivation

private def theExamples : List Example :=
  [ ⟨"COMPAS — ProPublica headline (IUT)",
     "Black non-recidivists scored HighRisk at 641/1514 ≈ 42.3% vs the White benchmark 94/427 ≈ 22.0%. The benchmark falls outside the score-test interval, so the hypothesis \"both races share this false-positive rate\" is REJECTED: UTrust. The point: a famous journalistic finding becomes a machine-checkable artifact. Depth 2.",
     true, exProPublica⟩
  , ⟨"COMPAS — a certified non-finding (IT)",
     "Among Black recidivists, the female LowRisk rate 62/203 is statistically consistent with the male benchmark 137/486: Trust. The point: a fairness tool that can only confirm bias is a rubber stamp — Trust certificates make \"no significant disparity\" a checkable claim with its evidence attached. Depth 2.",
     true, exNonFinding⟩
  , ⟨"COMPAS — trust elimination (IT → ET)",
     "After the non-finding is certified, ET re-enters the frequency layer: the audited interval becomes a typed context assumption on the observed variable itself, r : LowRisk_[ℓ,h]. The point: elimination is what makes certificates COMPOSE — downstream derivations can cite the audited interval as an assumption instead of re-deriving the statistics. Depth 3.",
     true, exETChain⟩
  , ⟨"COMPAS — untrust elimination (IUT → EUT)",
     "Extending the ProPublica certificate, EUT places the COMPLEMENT interval ¬[0.4025, 0.4442] in the typing context. The point: the audit trail now carries a standing constraint — any future model claiming a Black false-positive rate inside the rejected band is contradicted by this certificate. Depth 3.",
     true, exEUTChain⟩
  , ⟨"HMDA — Tree A: national benchmark (IT)",
     "White Delaware 2022 denial rate 4914/24614 ≈ 19.96% is consistent with a 20% national benchmark: Trust. Pair this with the next example to see the same hypothesis tested on two cohorts. Depth 2.",
     true, exHmdaA⟩
  , ⟨"HMDA — the SAME benchmark, rejected for the Black cohort (IUT)",
     "The identical 20% national-benchmark hypothesis, now tested against the Black Delaware 2022 denial rate 2409/7142 ≈ 33.7%: the benchmark falls far outside the interval, so the hypothesis is REJECTED: UTrust. The point: Trust for one cohort and UTrust for another, over the same benchmark, makes a disparity legible as a PAIR of machine-checked artifacts. Depth 2.",
     true, exHmdaBlackBenchmark⟩
  , ⟨"HMDA — Tree B: pooled disparity (Update → IUT2)",
     "Two years of observations per racial group are pooled by Update (disjoint provenances), then compared head-to-head: 0 lies outside the two-sample interval, certifying UTrust. The point: composition — evidence accumulated across years feeds a two-sample test, and the certificate carries the whole pipeline. Depth 3.",
     true, exHmdaB⟩
  , ⟨"HMDA — Tree C: full chain (Update → IEx → EEx)",
     "The deepest tree: IEx certifies the pooled Black−White excess; EEx imports the White rate as a benchmark and re-enters the frequency layer with the shifted bound [0.3459, 0.3631] in its typing context. The point: a regulator re-checks the entire four-stage analysis with one call — no re-analysis, no trust in the analyst. Depth 4.",
     true, (exHmdaC.getD exProPublica)⟩
  , ⟨"Structural — Contraction reconciles two audit reports",
     "Two independent auditors bound the same model parameter x: [0.20, 0.60] and [0.30, 0.50]. Contraction merges the duplicated assumption into one exact working hypothesis 2/5, which the checker verifies lies in BOTH intervals — while the pilot observation is carried unchanged. The point: structural rules are bookkeeping with teeth; a reconciled value outside either report would be rejected (as would reconciling two vacuous [0,1] assumptions).",
     true, exContraction⟩
  , ⟨"Structural — Weakening files a certificate in a wider context",
     "The Tree A benchmark certificate is re-filed in a context extended with the Black cohort's assumption, under an explicit independence witness #w. The point: certificates stay valid when the case file grows — and the witness is honestly recorded in the artifact as an operator-supplied assumption, not silently presumed.",
     true, exWeakening⟩
  , ⟨"Implication — a conditional policy claim (I→ then E→)",
     "Under the working assumption x : Subprime_{3/10}, denial in a 200-application batch runs at 1/2; I→ discharges the assumption into a conditional claim [x]d : (Subprime ⇒ Denied)_{1/2}. Observing the antecedent's actual rate u : Subprime_{3/10} on the same batch, E→ composes them: denial-via-subprime prices at 3/20. The point: implication internalizes \"if-then\" policy claims; elimination cashes them out against observed antecedent rates (the antecedent annotation is recorded, not enforced — see the paper).",
     true, exImplication⟩
  , ⟨"Tampered certificate (rejected)",
     "The ProPublica certificate with a forged, narrower interval. The checker recomputes the score-test interval from the leaves and rejects the mismatch. The point: this is the producer/checker split doing its job — certificates cannot assert statistics the checker cannot reproduce.",
     false, exTampered⟩ ]

def main : IO UInt32 := do
  -- Self-validate: every example must match its expected verdict.
  let mut bad := 0
  for ex in theExamples do
    let ok := match checkDerivation ex.cert with
      | .ok () => true
      | .error _ => false
    if ok != ex.expectValid then
      IO.eprintln s!"MISMATCH: '{ex.name}' expected valid={ex.expectValid}, got {ok}"
      bad := bad + 1
    else
      IO.println s!"  ✓ {ex.name} (valid={ok}, as expected)"
  if bad > 0 then
    IO.eprintln s!"{bad} example(s) failed self-validation; not writing output."
    return 1
  let json := Json.arr (theExamples.map (fun ex =>
    Json.mkObj [("name", ex.name), ("description", ex.description),
                ("expectValid", Json.bool ex.expectValid),
                ("certificate", derivationJson ex.cert)])).toArray
  IO.FS.writeFile "web/examples.json" (json.pretty 80)
  IO.println s!"Wrote {theExamples.length} examples to web/examples.json"
  return 0
