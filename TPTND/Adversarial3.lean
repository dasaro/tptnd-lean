import TPTND

open TPTND

/-! # Adversarial Round 2 — deeper probes after the Contraction fix

Probes:
  9.  ETex: `.unknown` context entry bypasses the consistency check
  10. Contraction from `.unknown` + one informative entry (circumvents the new guard?)
  11. WeakeningS + Contraction: inject a wide interval then narrow it
  12. ET chain: materialize interval then re-enter via ETex with different value
  13. EEx shifted interval: clampProb distortion
  14. Sampling with n=1: does it launder provenance?
  15. extend: can we violate mass > 1 with non-exact constraints?
  16. I-P: derive a "prior" then E-P with wrong posterior
-/

private def P (n d : Nat) : Prob := clampProb ((n : ℚ) / d)
private def nd (rule : String) (prems : List Derivation)
    (ctx : Context) (claim : Claim) : Derivation :=
  .node rule prems ⟨ctx, claim⟩ false
private def ndW (rule : String) (prems : List Derivation)
    (ctx : Context) (claim : Claim) : Derivation :=
  .node rule prems ⟨ctx, claim⟩ true
private def mkSupport (s : String) : Finset String := {s}
private def mkProv   (s : String) : Finset String := {s}

private def run (name : String) (d : Derivation) (shouldFail : Bool := true) : IO Unit := do
  match checkDerivation d with
  | .ok () =>
    if shouldFail then IO.println s!"  ⚠ EXPLOIT  {name}"
    else IO.println s!"  ✓ OK       {name}"
  | .error e =>
    if shouldFail then IO.println s!"  ✓ BLOCKED  {name}: {e}"
    else IO.println s!"  ✗ BUG      {name}: {e}"

-- ============================================================================
-- 9. ETex with `.unknown` in premise context (tautological check)
-- ============================================================================
/-
  Build: IT(model=0.5, obs f=0.5, n=100) → Trust → ETex
  The obs context has .unknown. ETex checks modelP ∈ some constraint on α.
  Since .unknown contains everything, the check is trivially true.
  But IT already certified modelP — so is this actually exploitable?
  Try: after IT, use ETex to produce a DIFFERENT value than modelP.
-/

private def attack9_etexUnknown : IO Unit := do
  IO.println "  Attack 9: ETex — can it produce a value ≠ modelP?"
  let α := Output.atom "X"
  let t := Term.atom "r"
  let σ := mkProv "σ"
  let n : Nat := 100
  let f := P 50 100
  let p := P 50 100  -- model = observed → Trust

  let ci := binomialCI n f p
  let modelEntry : ContextEntry := ⟨"m", mkSupport "mdl", α, .exact p⟩
  let obsEntry : ContextEntry := ⟨"r", mkSupport "obs", α, .unknown⟩
  let dModel := nd "identity" [] [modelEntry] (.identity modelEntry)
  let dObs := nd "obs" [] [obsEntry] (.term ⟨.frequency, t, n, α, f, σ⟩)
  let dIT := nd "IT" [dModel, dObs] [modelEntry, obsEntry] (.trust (.trust .oneSample t n α f p ci σ))

  -- ETex: try producing 0.99 instead of 0.50
  let wrongVal := P 99 100
  let wrongEntry : ContextEntry := ⟨"r", mkSupport "obs", α, .exact wrongVal⟩
  let dETex_bad := nd "ETex" [dIT] [wrongEntry] (.term ⟨.expected, t, n, α, wrongVal, σ⟩)
  run "ETex: produce 0.99 when Trust certified 0.50" dETex_bad

-- ============================================================================
-- 10. Contraction with one .unknown + one informative entry
-- ============================================================================
/-
  If one entry is .interval [0.3, 0.7] and the other is .unknown,
  the new guard allows it (not all .unknown).
  Can we narrow to any value in [0.3, 0.7]?
  Yes — and that's CORRECT. The intersection of [0.3,0.7] ∩ [0,1] = [0.3,0.7].
  Any value in [0.3,0.7] is valid.
-/

private def attack10_contractionMixed : IO Unit := do
  IO.println "  Attack 10: Contraction with .unknown + informative"
  let α := Output.atom "X"

  -- Build an interval entry [0.3, 0.7] — from ET (Trust elimination)
  let lo := P 3 10
  let hi := P 7 10
  let infoEntry : ContextEntry := ⟨"x", mkSupport "A", α, .interval lo hi⟩
  let unknownEntry : ContextEntry := ⟨"x", mkSupport "B", α, .unknown⟩

  -- Manually construct a premise with both entries and a simple claim
  let dummyClaim := Claim.identity infoEntry
  let premCtx := [infoEntry, unknownEntry]

  -- Need a valid premise — use identity_star (claim entry must be in context)
  let dPrem := nd "identity_star" [] premCtx dummyClaim

  -- Contraction: narrow to exact 0.5 (in [0.3, 0.7] and in [0,1])
  let exactEntry : ContextEntry := ⟨"x", mkSupport "A", α, .exact (P 5 10)⟩
  let dContract := nd "Contraction" [dPrem] [exactEntry] dummyClaim
  run "Contraction: .unknown + [0.3,0.7] → exact(0.5)" dContract (shouldFail := false)

  -- Contraction: narrow to exact 0.1 (NOT in [0.3, 0.7])
  let badEntry : ContextEntry := ⟨"x", mkSupport "A", α, .exact (P 1 10)⟩
  let dContractBad := nd "Contraction" [dPrem] [badEntry] dummyClaim
  run "Contraction: .unknown + [0.3,0.7] → exact(0.1)" dContractBad

-- ============================================================================
-- 11. WeakeningS: inject interval, then Contraction to narrow it
-- ============================================================================
/-
  Can WeakeningS add a wide interval entry [0, 1] disguised as an
  informative constraint, then Contraction narrow it to anything?
  This is the same as attack 1 but with .interval instead of .unknown.
-/

private def attack11_intervalInject : IO Unit := do
  IO.println "  Attack 11: WeakeningS inject [0,1] interval + Contraction"
  let α := Output.atom "X"

  let wide1 : ContextEntry := ⟨"x", mkSupport "A", α, .interval (P 0 1) (P 1 1)⟩
  let wide2 : ContextEntry := ⟨"x", mkSupport "B", α, .interval (P 0 1) (P 1 1)⟩

  let claim1 := Claim.identity wide1
  let claim2 := Claim.identity wide2

  let dId1 := nd "identity" [] [wide1] claim1
  let dId2 := nd "identity" [] [wide2] claim2

  -- WeakeningS
  let dWeak := ndW "WeakeningS" [dId1, dId2] [wide1, wide2] claim1

  -- Contraction to exact 0.42 — both constraints are [0,1] so it's in both
  let forged : ContextEntry := ⟨"x", mkSupport "A", α, .exact (P 42 100)⟩
  let dContract := nd "Contraction" [dWeak] [forged] claim1
  run "Contraction: [0,1] + [0,1] → exact(0.42)" dContract
  IO.println "    ↳ Note: [0,1] intervals are informative (not .unknown), so guard passes."
  IO.println "    ↳ Is this a problem? The value 0.42 IS in [0,1] ∩ [0,1]."
  IO.println "    ↳ Like Attack 1, this is a PROVENANCE weakness, not soundness."

-- ============================================================================
-- 12. ET → ETex chain: can we change the value mid-chain?
-- ============================================================================

private def attack12_etChain : IO Unit := do
  IO.println "  Attack 12: ET → ETex chain with value change"
  let α := Output.atom "X"
  let t := Term.atom "r"
  let σ := mkProv "σ"
  let n : Nat := 100
  let f := P 50 100
  let p := P 50 100

  let ci := binomialCI n f p
  let modelEntry : ContextEntry := ⟨"m", mkSupport "mdl", α, .exact p⟩
  let obsEntry : ContextEntry := ⟨"r", mkSupport "obs", α, .unknown⟩
  let dModel := nd "identity" [] [modelEntry] (.identity modelEntry)
  let dObs := nd "obs" [] [obsEntry] (.term ⟨.frequency, t, n, α, f, σ⟩)

  -- IT → Trust
  let dIT := nd "IT" [dModel, dObs] [modelEntry, obsEntry]
    (.trust (.trust .oneSample t n α f p ci σ))

  -- ET → materializes interval in context
  let intervalEntry : ContextEntry := ⟨"u", mkSupport "ci", α, ci⟩
  let etClaim : TermClaim := ⟨.frequency, t, n, α, f, σ⟩
  let dET := nd "ET" [dIT] [intervalEntry] (.term etClaim)

  -- Now try: feed this into ANOTHER Trust with a different model
  let p2 := P 45 100  -- different model
  let ci2 := binomialCI n f p2
  let modelEntry2 : ContextEntry := ⟨"m2", mkSupport "mdl2", α, .exact p2⟩
  let dModel2 := nd "identity" [] [modelEntry2] (.identity modelEntry2)
  let dIT2 := nd "IT" [dModel2, dET] [modelEntry2, intervalEntry]
    (.trust (.trust .oneSample t n α f p2 ci2 σ))

  -- This chain is invalid regardless of the CI: ET must preserve Γ and
  -- re-enter the audited interval on the OBSERVED variable r, not a fresh u.
  run "ET→IT chain via a Γ-dropping ET (invalid shape)" dIT2

-- ============================================================================
-- 13. E-P: wrong posterior value
-- ============================================================================

private def attack13_wrongPosterior : IO Unit := do
  IO.println "  Attack 13: E-P with wrong posterior"
  let FPR := Output.atom "FPR"

  -- Prior: H1=1/6 (weight 1/6), H2=1/3 (weight 1/3), H3=1/2 (weight 1/2)
  let a1 := P 1 6; let a2 := P 1 3; let a3 := P 1 2
  let e1 : ContextEntry := ⟨"h1", mkSupport "h", FPR, .exact a1⟩
  let e2 : ContextEntry := ⟨"h2", mkSupport "h", FPR, .exact a2⟩
  let e3 : ContextEntry := ⟨"h3", mkSupport "h", FPR, .exact a3⟩
  let dId1 := nd "identity" [] [e1] (.identity e1)
  let dId2 := nd "identity" [] [e2] (.identity e2)
  let dId3 := nd "identity" [] [e3] (.identity e3)
  let dPrior := nd "I-P" [dId1, dId2, dId3] [] (.distDecl [])

  -- Obs: n=5, f=2/5, s=2
  let obsEntry : ContextEntry := ⟨"r", mkSupport "pilot", FPR, .unknown⟩
  let dObs := nd "obs" [] [obsEntry]
    (.term ⟨.frequency, Term.atom "r", 5, FPR, P 2 5, mkProv "ρ"⟩)

  -- E-P with WRONG posterior (should be 729/1366 ≈ 0.5336, try 1/2 = 0.5)
  let wrongPosterior := P 1 2
  let supportEntry : ContextEntry := ⟨"h3", mkSupport "h", FPR, .exact a3⟩
  let concEntry : ContextEntry := ⟨"res", mkSupport "post", FPR, .exact wrongPosterior⟩
  let dEP := nd "E-P" [dPrior, dObs] [supportEntry] (.identity concEntry)
  run "E-P: wrong posterior 1/2 (correct = 729/1366)" dEP

-- ============================================================================
-- 14. Sampling with n=1: provenance laundering?
-- ============================================================================

private def attack14_samplingLaunder : IO Unit := do
  IO.println "  Attack 14: Sampling with n=1 (provenance laundering?)"
  let α := Output.atom "X"
  let t := Term.atom "r"
  let σ := mkProv "σ"

  -- Single obs: f=0.5, n=100
  let obsEntry : ContextEntry := ⟨"r", mkSupport "obs", α, .unknown⟩
  let obsClaim : TermClaim := ⟨.frequency, t, 100, α, P 50 100, σ⟩
  let dObs := nd "obs" [] [obsEntry] (.term obsClaim)

  -- Sampling with 1 premise: should produce f=1/1=1.0 or f=0/1=0.0?
  -- The sampling rule computes f = matchCount/n where n=#premises
  -- With 1 premise whose output matches α: f = 1/1 = 1.0
  -- But the original f was 0.5. Sampling CHANGES the frequency!
  let sampledClaim : TermClaim := ⟨.frequency, t, 1, α, P 1 1, σ⟩
  let dSampling := nd "sampling" [dObs] [obsEntry] (.term sampledClaim)
  run "Sampling n=1: replaces f=0.5 with f=1.0?" dSampling
  IO.println "    ↳ If accepted: sampling transforms the frequency (not laundering, but new observation)"

-- ============================================================================
-- 15. extend: mass overflow with interval constraints
-- ============================================================================

private def attack15_massOverflow : IO Unit := do
  IO.println "  Attack 15: extend with mass overflow via intervals"
  let H := Output.atom "H"

  -- Already have x:H_{[0.7, 1.0]} in context (mass ≥ 0.7)
  -- Try to extend with x:H_{[0.5, 0.8]} (would push total ≥ 1.2)
  let supp := mkSupport "coin"
  let e1 : ContextEntry := ⟨"x", supp, H, .interval (P 7 10) (P 1 1)⟩
  let e2 : ContextEntry := ⟨"x", supp, H, .interval (P 5 10) (P 8 10)⟩

  let dBase := nd "base" [] [] (.distDecl [])
  let dExt1 := nd "extend" [dBase] [e1] (.distDecl [e1])
  let dExt2 := nd "extend" [dExt1] [e1, e2] (.distDecl [e1, e2])
  run "extend: x:H_{[0.7,1.0]} then x:H_{[0.5,0.8]} (mass overflow?)" dExt2

-- ============================================================================
-- 16. Identity with interval constraint (not exact) — used as IT model?
-- ============================================================================

private def attack16_intervalModel : IO Unit := do
  IO.println "  Attack 16: IT with interval model (not exact)"
  let α := Output.atom "X"
  let t := Term.atom "r"
  let σ := mkProv "σ"

  -- Model with interval constraint (should be rejected — IT requires exact)
  let modelEntry : ContextEntry := ⟨"m", mkSupport "mdl", α, .interval (P 2 10) (P 8 10)⟩
  let dModel := nd "identity" [] [modelEntry] (.identity modelEntry)

  let n : Nat := 100
  let f := P 50 100
  let p := P 50 100  -- even though we compute CI with exact 0.5, the model has interval
  let ci := binomialCI n f p
  let obsEntry : ContextEntry := ⟨"r", mkSupport "obs", α, .unknown⟩
  let dObs := nd "obs" [] [obsEntry] (.term ⟨.frequency, t, n, α, f, σ⟩)
  let dIT := nd "IT" [dModel, dObs] [modelEntry, obsEntry] (.trust (.trust .oneSample t n α f p ci σ))
  run "IT with interval model [0.2, 0.8] (should require exact)" dIT

-- ============================================================================
-- Main
-- ============================================================================

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println " TPTND Adversarial Round 2"
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println ""
  attack9_etexUnknown
  IO.println ""
  attack10_contractionMixed
  IO.println ""
  attack11_intervalInject
  IO.println ""
  attack12_etChain
  IO.println ""
  attack13_wrongPosterior
  IO.println ""
  attack14_samplingLaunder
  IO.println ""
  attack15_massOverflow
  IO.println ""
  attack16_intervalModel
  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════"
