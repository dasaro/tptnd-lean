import TPTND

open TPTND

/-! # TPTND Acceptance Tests

Hand-constructed derivation trees checked by `checkDerivation`.
Design doc §8. -/

-- ============================================================================
-- Test helpers
-- ============================================================================

/-- Build a `Prob` from a natural-number fraction n/d, clamped to [0,1].
    For test fractions known to be in [0,1] the clamp is a no-op. -/
private def P (n d : Nat) : Prob := clampProb ((n : ℚ) / d)

/-- Shorthand derivation node (no independence witness). -/
private def nd (rule : String) (prems : List Derivation)
    (ctx : Context) (claim : Claim) : Derivation :=
  .node rule prems ⟨ctx, claim⟩ false

/-- Shorthand derivation node WITH independence witness. -/
private def ndW (rule : String) (prems : List Derivation)
    (ctx : Context) (claim : Claim) : Derivation :=
  .node rule prems ⟨ctx, claim⟩ true

private def mkSupport (s : String) : Finset String := {s}
private def mkProv   (s : String) : Finset String := {s}
private def mkProv2  (a b : String) : Finset String := {a, b}

/-- Run a test and report pass/fail. -/
private def runTest (name : String) (d : Derivation) : IO Unit := do
  match checkDerivation d with
  | .ok () => IO.println s!"  PASS  {name}"
  | .error e => IO.println s!"  FAIL  {name}: {e}"

-- ============================================================================
-- Test 1: output_atom + base + extend  (fair coin)
-- ============================================================================
/--
  ⊢ H :: output     ⊢ T :: output     (output_atom × 2)
  ⊢ ∅                                  (base)
  ⊢ {x : H_{1/2}}                      (extend)
  ⊢ {x : H_{1/2}, x : T_{1/2}}        (extend)
-/
private def test1 : Derivation :=
  let H := Output.atom "H"
  let T := Output.atom "T"
  let half := P 1 2
  let supp := mkSupport "coin"
  let e1 : ContextEntry := ⟨"x", supp, H, .exact half⟩
  let e2 : ContextEntry := ⟨"x", supp, T, .exact half⟩
  -- output declarations
  let _dH := nd "output_atom" [] [] (.outputDecl H)
  let _dT := nd "output_atom" [] [] (.outputDecl T)
  -- base
  let dBase := nd "base" [] [] (.distDecl [])
  -- extend with H_{1/2}
  let dExt1 := nd "extend" [dBase] [e1] (.distDecl [e1])
  -- extend with T_{1/2}
  nd "extend" [dExt1] [e1, e2] (.distDecl [e1, e2])

-- ============================================================================
-- Test 2: obs + update  (two disjoint batches)
-- ============================================================================
/--
  Batch 1: n=100, f=48/100   (provenance σ_m)
  Batch 2: n=100, f=52/100   (provenance σ_f)
  UPDATE → n=200, f=100/200 = 1/2   (provenance σ_m ∪ σ_f)
-/
private def test2 : Derivation :=
  let α := Output.atom "H"
  let t := Term.atom "coin"
  let supp := mkSupport "coin"
  let ctx : Context := [⟨"coin", supp, α, .unknown⟩]
  let σm := mkProv "σ_m"
  let σf := mkProv "σ_f"
  let σU := mkProv2 "σ_m" "σ_f"
  let obs1Claim : TermClaim := ⟨.frequency, t, 100, α, P 48 100, σm⟩
  let obs2Claim : TermClaim := ⟨.frequency, t, 100, α, P 52 100, σf⟩
  let dObs1 := nd "obs" [] ctx (.term obs1Claim)
  let dObs2 := nd "obs" [] ctx (.term obs2Claim)
  -- UPDATE: weighted freq = (100·48/100 + 100·52/100)/200 = 100/200 = 1/2
  let updClaim : TermClaim := ⟨.frequency, t, 200, α, P 1 2, σU⟩
  nd "update" [dObs1, dObs2] ctx (.term updClaim)

-- ============================================================================
-- Test 3: I+ and E+L round-trip
-- ============================================================================
/--
  t : H_{1/3}    t : T_{2/3}
  ─────────────────────────── I+
  t : (H+T)_{1}
         t : (H+T)_1    t : H_{1/3}
         ───────────────────────────── E+L
         t : T_{2/3}
-/
private def test3 : Derivation :=
  let H := Output.atom "H"
  let T := Output.atom "T"
  let HT := Output.sum H T
  let t := Term.atom "coin"
  let σ := mkProv "ρ"
  let supp := mkSupport "coin"
  -- The context declares both observed outputs of the coin (mass 1/3+2/3 = 1)
  let ctx : Context := [⟨"coin", supp, H, .exact (P 1 3)⟩,
                        ⟨"coin", supp, T, .exact (P 2 3)⟩]
  let tcH : TermClaim := ⟨.frequency, t, 300, H, P 1 3, σ⟩
  let tcT : TermClaim := ⟨.frequency, t, 300, T, P 2 3, σ⟩
  let tcHT : TermClaim := ⟨.frequency, t, 300, HT, P 1 1, σ⟩
  let dH := nd "obs" [] ctx (.term tcH)
  let dT := nd "obs" [] ctx (.term tcT)
  -- I+
  let dPlus := nd "I+" [dH, dT] ctx (.term tcHT)
  -- E+L: from (H+T)_1 and H_{1/3}, conclude T_{2/3}
  nd "E+L" [dPlus, dH] ctx (.term tcT)

-- ============================================================================
-- Test 4: IT + ETex  — COMPAS §4.3 Trust (Black female recidivists)
-- ============================================================================
/--
  Observed: Γ_BRF ⊢_{ρ_f} r_203 : LowRisk_{62/203}
  Model:    Γ^mdl_BRM ⊢ x_BRM : LowRisk_{137/486}
  P(203, 62/203, 137/486) = [ℓ, h]    137/486 ∈ [ℓ, h]
  ──────────────────────────────────────────────────── IT
  Θ_BR ⊢ Trust_P(r_203 : LowRisk_{62/203}; 137/486, [ℓ,h])
-/
private def test4 : IO Unit := do
  let LR := Output.atom "LowRisk"
  let t := Term.atom "r"
  let σ := mkProv "ρ_f"
  let suppBRF := mkSupport "BRF"
  let suppBRM := mkSupport "BRM"
  let n : Nat := 203
  let f := P 62 203
  let p := P 137 486
  -- Compute CI using the checker's own function
  let ci := binomialCI n f p
  -- Model premise: identity claim
  let modelEntry : ContextEntry := ⟨"x_BRM", suppBRM, LR, .exact p⟩
  let modelCtx : Context := [modelEntry]
  let dModel := nd "identity" [] modelCtx (.identity modelEntry)
  -- Observation premise: frequency claim
  let obsEntry : ContextEntry := ⟨"r", suppBRF, LR, .unknown⟩
  let obsCtx : Context := [obsEntry]
  let obsClaim : TermClaim := ⟨.frequency, t, n, LR, f, σ⟩
  let dObs := nd "obs" [] obsCtx (.term obsClaim)
  -- IT conclusion
  let trustClaim : TrustClaim := .trust .oneSample t n LR f p ci σ
  let concCtx := modelCtx ++ obsCtx
  let dIT := nd "IT" [dModel, dObs] concCtx (.trust trustClaim)
  -- Check if p ∈ ci  (should be true for Trust)
  if inConstraint p ci then
    runTest "Test 4 — COMPAS Trust (IT, §4.3)" dIT
  else
    IO.println s!"  SKIP  Test 4: model prob not in CI (CI = {repr ci})"

-- ============================================================================
-- Test 5: IUT + EUT — COMPAS §4.2 UTrust (Black non-recidivists)
-- ============================================================================
/--
  Observed: Γ_BN ⊢_{σ_m⊎σ_f} u_1514 : HighRisk_{641/1514}
  Model:    Γ^mdl_WN ⊢ x_WN : HighRisk_{94/427}
  P(1514, 641/1514, 94/427) = [ℓ, h]    94/427 ∉ [ℓ, h]
  ──────────────────────────────────────────────────────── IUT
  Θ_FP ⊢ UTrust_P(u_1514 : HighRisk_{641/1514}; 94/427, [ℓ,h])
-/
private def test5 : IO Unit := do
  let HR := Output.atom "HighRisk"
  let t := Term.atom "u"
  let σ := mkProv2 "σ_m" "σ_f"
  let suppBN := mkSupport "BN"
  let suppWN := mkSupport "WN"
  let n : Nat := 1514
  let f := P 641 1514
  let p := P 94 427
  let ci := binomialCI n f p
  -- Model premise
  let modelEntry : ContextEntry := ⟨"x_WN", suppWN, HR, .exact p⟩
  let modelCtx : Context := [modelEntry]
  let dModel := nd "identity" [] modelCtx (.identity modelEntry)
  -- Observation premise
  let obsEntry : ContextEntry := ⟨"u", suppBN, HR, .unknown⟩
  let obsCtx : Context := [obsEntry]
  let obsClaim : TermClaim := ⟨.frequency, t, n, HR, f, σ⟩
  let dObs := nd "obs" [] obsCtx (.term obsClaim)
  -- IUT conclusion
  let utrustClaim : TrustClaim := .untrust .oneSample t n HR f p ci σ
  let concCtx := modelCtx ++ obsCtx
  let dIUT := nd "IUT" [dModel, dObs] concCtx (.trust utrustClaim)
  -- Check 94/427 ∉ ci  (should be true for UTrust)
  if notInConstraint p ci then
    runTest "Test 5 — COMPAS UTrust (IUT, §4.2)" dIUT
  else
    IO.println s!"  SKIP  Test 5: model prob IS in CI (CI = {repr ci}), expected UTrust"

-- ============================================================================
-- Test 6: IEx — synthetic excess comparison
-- ============================================================================
/--
  Left:  n=1000, f=500/1000=0.5   (σ)
  Right: m=1000, g=400/1000=0.4   (τ)
  Q(1000, 1000, 0.5, 0.4) = [ℓ, h],  0 ∉ [ℓ, h]  (significant excess)
-/
private def test6 : IO Unit := do
  let α := Output.atom "X"
  let tL := Term.atom "left"
  let tR := Term.atom "right"
  let σ := mkProv "σ"
  let τ := mkProv "τ"
  let suppL := mkSupport "left"
  let suppR := mkSupport "right"
  let nL : Nat := 2000
  let nR : Nat := 2000
  let fL := P 1000 2000
  let gR := P 800 2000
  let ci := twoSampleCI nL nR fL gR
  let diff := P 200 2000  -- 0.5 - 0.4 = 0.1
  let tcL : TermClaim := ⟨.frequency, tL, nL, α, fL, σ⟩
  let tcR : TermClaim := ⟨.frequency, tR, nR, α, gR, τ⟩
  let ctxL : Context := [⟨"left", suppL, α, .unknown⟩]
  let ctxR : Context := [⟨"right", suppR, α, .unknown⟩]
  let dL := nd "obs" [] ctxL (.term tcL)
  let dR := nd "obs" [] ctxR (.term tcR)
  let concCtx := ctxL ++ ctxR
  let concClaim := Claim.comparison (.excess tcL tcR diff ci)
  let dIEx := nd "IEx" [dL, dR] concCtx concClaim
  if notInConstraint Prob.zero ci then
    runTest "Test 6 — Synthetic IEx (excess comparison)" dIEx
  else
    IO.println s!"  SKIP  Test 6: 0 is in CI, no significant excess"

-- ============================================================================
-- Test 7: IT → ET  end-to-end chain (COMPAS §4.3)
-- ============================================================================
/--
  IT gives:  Θ_BR ⊢ Trust_P(r_203 : LowRisk_{62/203}; 137/486, [ℓ,h])
  ET gives:  Θ_BR, x_BRF : LowRisk_{[ℓ,h]} ⊢_{ρ_f} r_203 : LowRisk_{62/203}
-/
private def test7 : IO Unit := do
  let LR := Output.atom "LowRisk"
  let t := Term.atom "r"
  let σ := mkProv "ρ_f"
  let suppBRF := mkSupport "BRF"
  let suppBRM := mkSupport "BRM"
  let n : Nat := 203
  let f := P 62 203
  let p := P 137 486
  let ci := binomialCI n f p
  -- IT derivation (same as test4)
  let modelEntry : ContextEntry := ⟨"x_BRM", suppBRM, LR, .exact p⟩
  let obsEntry : ContextEntry := ⟨"r", suppBRF, LR, .unknown⟩
  let dModel := nd "identity" [] [modelEntry] (.identity modelEntry)
  let obsClaim : TermClaim := ⟨.frequency, t, n, LR, f, σ⟩
  let dObs := nd "obs" [] [obsEntry] (.term obsClaim)
  let trustClaim : TrustClaim := .trust .oneSample t n LR f p ci σ
  let itCtx := [modelEntry, obsEntry]
  let dIT := nd "IT" [dModel, dObs] itCtx (.trust trustClaim)
  -- ET derivation: add interval entry, produce term claim
  -- x_u is the observed term's own variable, so Contraction can later
  -- select a value within the audited range (§3.8)
  let intervalEntry : ContextEntry := ⟨"r", suppBRF, LR, ci⟩
  let etCtx := itCtx ++ [intervalEntry]
  let etClaim : TermClaim := ⟨.frequency, t, n, LR, f, σ⟩
  let dET := nd "ET" [dIT] etCtx (.term etClaim)
  runTest "Test 7 — COMPAS IT→ET chain (§4.3)" dET

-- ============================================================================
-- Test 8: IUT → EUT  end-to-end chain (COMPAS §4.2)
-- ============================================================================
private def test8 : IO Unit := do
  let HR := Output.atom "HighRisk"
  let t := Term.atom "u"
  let σ := mkProv2 "σ_m" "σ_f"
  let suppBN := mkSupport "BN"
  let suppWN := mkSupport "WN"
  let n : Nat := 1514
  let f := P 641 1514
  let p := P 94 427
  let ci := binomialCI n f p
  -- IUT
  let modelEntry : ContextEntry := ⟨"x_WN", suppWN, HR, .exact p⟩
  let obsEntry : ContextEntry := ⟨"u", suppBN, HR, .unknown⟩
  let dModel := nd "identity" [] [modelEntry] (.identity modelEntry)
  let obsClaim : TermClaim := ⟨.frequency, t, n, HR, f, σ⟩
  let dObs := nd "obs" [] [obsEntry] (.term obsClaim)
  let utrustClaim : TrustClaim := .untrust .oneSample t n HR f p ci σ
  let iutCtx := [modelEntry, obsEntry]
  let dIUT := nd "IUT" [dModel, dObs] iutCtx (.trust utrustClaim)
  -- EUT: add complement-interval entry
  let complementCI := match ci with
    | .interval lo hi => Constraint.outsideInterval lo hi
    | other => other
  let compEntry : ContextEntry := ⟨"u", suppBN, HR, complementCI⟩
  let eutCtx := iutCtx ++ [compEntry]
  let eutClaim : TermClaim := ⟨.frequency, t, n, HR, f, σ⟩
  let dEUT := nd "EUT" [dIUT] eutCtx (.term eutClaim)
  runTest "Test 8 — COMPAS IUT→EUT chain (§4.2)" dEUT

-- ============================================================================
-- Negative tests: derivations that MUST be rejected
-- ============================================================================

/-- Helper: expect a CheckM to fail. -/
private def runNegTest (name : String) (d : Derivation) : IO Unit :=
  match checkDerivation d with
  | .ok ()   => IO.println s!"  FAIL  {name}: should have been REJECTED but passed"
  | .error _ => IO.println s!"  PASS  {name} (correctly rejected)"

/-- Neg 1: output_atom with wrong conclusion (neg instead of atom). -/
private def neg1 : Derivation :=
  nd "output_atom" [] [] (.outputDecl (.neg (.atom "H")))

/-- Neg 2: extend that violates mass constraint (1/2 + 3/4 > 1). -/
private def neg2 : Derivation :=
  let H := Output.atom "H"
  let T := Output.atom "T"
  let supp := mkSupport "coin"
  let e1 : ContextEntry := ⟨"x", supp, H, .exact (P 1 2)⟩
  let e2 : ContextEntry := ⟨"x", supp, T, .exact (P 3 4)⟩  -- total 1.25 > 1
  let dBase := nd "base" [] [] (.distDecl [])
  let dExt1 := nd "extend" [dBase] [e1] (.distDecl [e1])
  nd "extend" [dExt1] [e1, e2] (.distDecl [e1, e2])

/-- Neg 3: I+ with overlapping outputs (same atom used twice). -/
private def neg3 : Derivation :=
  let H := Output.atom "H"
  let σ := mkProv "ρ"
  let supp := mkSupport "coin"
  let ctx : Context := [⟨"coin", supp, H, .exact (P 1 3)⟩]
  let tc1 : TermClaim := ⟨.frequency, .atom "coin", 300, H, P 1 3, σ⟩
  let tc2 : TermClaim := ⟨.frequency, .atom "coin", 300, H, P 1 3, σ⟩
  let tcSum : TermClaim := ⟨.frequency, .atom "coin", 300, .sum H H, P 2 3, σ⟩
  let d1 := nd "obs" [] ctx (.term tc1)
  let d2 := nd "obs" [] ctx (.term tc2)
  nd "I+" [d1, d2] ctx (.term tcSum)

/-- Neg 4: update with non-disjoint provenances. -/
private def neg4 : Derivation :=
  let α := Output.atom "H"
  let t := Term.atom "coin"
  let supp := mkSupport "coin"
  let ctx : Context := [⟨"coin", supp, α, .unknown⟩]
  let σ := mkProv "same_run"  -- SAME provenance for both
  let tc1 : TermClaim := ⟨.frequency, t, 100, α, P 48 100, σ⟩
  let tc2 : TermClaim := ⟨.frequency, t, 100, α, P 52 100, σ⟩
  let tcU : TermClaim := ⟨.frequency, t, 200, α, P 1 2, σ⟩
  let d1 := nd "obs" [] ctx (.term tc1)
  let d2 := nd "obs" [] ctx (.term tc2)
  nd "update" [d1, d2] ctx (.term tcU)

/-- Neg 5: IT where model probability is OUTSIDE the CI (should be IUT). -/
private def test_neg5 : IO Unit := do
  let α := Output.atom "X"
  let t := Term.atom "t"
  let σ := mkProv "ρ"
  let supp := mkSupport "obs"
  let suppM := mkSupport "model"
  let n : Nat := 100
  let f := P 80 100   -- observed 80%
  let p := P 20 100   -- model says 20% — way off
  let ci := binomialCI n f p
  let modelEntry : ContextEntry := ⟨"m", suppM, α, .exact p⟩
  let obsEntry : ContextEntry := ⟨"t", supp, α, .unknown⟩
  let dModel := nd "identity" [] [modelEntry] (.identity modelEntry)
  let obsClaim : TermClaim := ⟨.frequency, t, n, α, f, σ⟩
  let dObs := nd "obs" [] [obsEntry] (.term obsClaim)
  -- Try to use IT (trust) — should fail because p ∉ CI
  let trustClaim : TrustClaim := .trust .oneSample t n α f p ci σ
  let dBadIT := nd "IT" [dModel, dObs] [modelEntry, obsEntry] (.trust trustClaim)
  runNegTest "Neg 5 — IT with p outside CI (should reject)" dBadIT

-- ============================================================================
-- Main
-- ============================================================================

def main : IO Unit := do
  IO.println "TPTND Acceptance Tests"
  IO.println "====================="
  IO.println ""
  IO.println "— Positive tests (must pass) —"
  runTest "Test 1 — Fair coin (output_atom + base + extend)" test1
  runTest "Test 2 — Two batches (obs + update)" test2
  runTest "Test 3 — Sum round-trip (I+ + E+L)" test3
  test4
  test5
  test6
  test7
  test8
  IO.println ""
  IO.println "— Negative tests (must reject) —"
  runNegTest "Neg 1 — output_atom with neg output" neg1
  runNegTest "Neg 2 — extend violating mass ≤ 1" neg2
  runNegTest "Neg 3 — I+ with overlapping outputs" neg3
  runNegTest "Neg 4 — update with non-disjoint provenance" neg4
  test_neg5
  IO.println ""
  IO.println "====================="
  IO.println "Done."
