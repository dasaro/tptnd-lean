import TPTND

open TPTND

/-! # TPTND Adversarial Soundness Tests

Attempt to exploit potential weaknesses identified by systematic audit.
Every test here SHOULD fail (the checker should reject).
If any PASSES, we have found a soundness hole. -/

private def P (n d : Nat) : Prob := clampProb ((n : ℚ) / d)

private def nd (rule : String) (prems : List Derivation)
    (ctx : Context) (claim : Claim) : Derivation :=
  .node rule prems ⟨ctx, claim⟩ false

private def ndW (rule : String) (prems : List Derivation)
    (ctx : Context) (claim : Claim) : Derivation :=
  .node rule prems ⟨ctx, claim⟩ true

private def mkSupport (s : String) : Finset String := {s}
private def mkProv   (s : String) : Finset String := {s}

private def runAdversarial (name : String) (d : Derivation) (shouldFail : Bool := true) : IO Unit := do
  match checkDerivation d with
  | .ok () =>
    if shouldFail then
      IO.println s!"  ⚠ EXPLOIT  {name}: ACCEPTED (should have been rejected!)"
    else
      IO.println s!"  ✓ OK       {name}: accepted as expected"
  | .error e =>
    if shouldFail then
      IO.println s!"  ✓ BLOCKED  {name}: {e}"
    else
      IO.println s!"  ✗ BUG      {name}: rejected unexpectedly: {e}"

-- ============================================================================
-- Attack 1: Contraction from two .unknown entries to forge exact value
-- ============================================================================
/-
  Attempt: use WeakeningS to merge two contexts each containing
  {r : α_{[0,1]}} (with different support sets), then Contraction
  to narrow to an arbitrary exact value.
-/

private def attack1_contractionForge : IO Unit := do
  IO.println "  Attack 1: Contraction from two .unknown entries"
  let α := Output.atom "HR"
  let t := Term.atom "r"
  let σ1 := mkProv "σ1"
  let σ2 := mkProv "σ2"

  -- Two obs with different support sets but same variable name
  let entry1 : ContextEntry := ⟨"r", mkSupport "dataA", α, .unknown⟩
  let entry2 : ContextEntry := ⟨"r", mkSupport "dataB", α, .unknown⟩

  let obs1Claim : TermClaim := ⟨.frequency, t, 100, α, P 80 100, σ1⟩
  let obs2Claim : TermClaim := ⟨.frequency, t, 50, α, P 10 50, σ2⟩

  let dObs1 := nd "obs" [] [entry1] (.term obs1Claim)
  let dObs2 := nd "obs" [] [entry2] (.term obs2Claim)

  -- WeakeningS: merge contexts, keep claim from obs1
  let mergedCtx := [entry1, entry2]
  let dWeak := ndW "WeakeningS" [dObs1, dObs2] mergedCtx (.term obs1Claim)

  -- Contraction: narrow two .unknown entries to exact 0.42
  let forgedValue := P 42 100
  let forgedEntry : ContextEntry := ⟨"r", mkSupport "dataA", α, .exact forgedValue⟩
  let contractedCtx := [forgedEntry]
  let dContract := nd "Contraction" [dWeak] contractedCtx (.term obs1Claim)

  runAdversarial "Contraction forge: .unknown → exact(0.42)" dContract

-- ============================================================================
-- Attack 2: Trust + UTrust for same (n, f, p) — should be impossible
-- ============================================================================

private def attack2_trustAndUntrust : IO Unit := do
  IO.println "  Attack 2: Trust AND UTrust for same (n, f, p)"
  let α := Output.atom "HR"
  let t := Term.atom "r"
  let σ := mkProv "σ"
  let n : Nat := 100
  let f := P 50 100    -- observed 50%
  -- Under z=√20 the acceptance band at n=100 is ±0.2049 around f, so the
  -- model must sit further out than the old 0.3 for the dual test to bite.
  let p := P 20 100    -- model says 20%

  let ci := binomialCI n f p

  let modelEntry : ContextEntry := ⟨"m", mkSupport "model", α, .exact p⟩
  let dModel := nd "identity" [] [modelEntry] (.identity modelEntry)

  let obsEntry : ContextEntry := ⟨"r", mkSupport "obs", α, .unknown⟩
  let obsClaim : TermClaim := ⟨.frequency, t, n, α, f, σ⟩
  let dObs := nd "obs" [] [obsEntry] (.term obsClaim)

  -- Try Trust (should fail: 0.3 ∉ CI around 0.5)
  let trustClaim : TrustClaim := .trust .oneSample t n α f p ci σ
  let dIT := nd "IT" [dModel, dObs] [modelEntry, obsEntry] (.trust trustClaim)
  runAdversarial "Trust with p=0.2 for f=0.5, n=100" dIT

  -- UTrust (should succeed: 0.3 ∉ CI)
  let utrustClaim : TrustClaim := .untrust .oneSample t n α f p ci σ
  let dIUT := nd "IUT" [dModel, dObs] [modelEntry, obsEntry] (.trust utrustClaim)
  runAdversarial "UTrust with p=0.2 for f=0.5, n=100" dIUT (shouldFail := false)

-- ============================================================================
-- Attack 3: ETex bypass via .unknown context entry
-- ============================================================================
/-
  Attempt: derive Trust for a model p that IS in the CI, then use ETex
  to get expected-mode value p. Then see if we can somehow get a WRONG
  expected-mode value.
-/

private def attack3_etexBypass : IO Unit := do
  IO.println "  Attack 3: ETex with wrong expected value"
  let α := Output.atom "HR"
  let t := Term.atom "r"
  let σ := mkProv "σ"
  let n : Nat := 100
  let f := P 50 100        -- observed 50%
  let p_correct := P 48 100  -- model says 48% (should be in CI)
  let p_wrong := P 20 100    -- we want to forge expected value 20%

  let ci := binomialCI n f p_correct

  -- Build a valid Trust for p_correct
  let modelEntry : ContextEntry := ⟨"m", mkSupport "model", α, .exact p_correct⟩
  let dModel := nd "identity" [] [modelEntry] (.identity modelEntry)
  let obsEntry : ContextEntry := ⟨"r", mkSupport "obs", α, .unknown⟩
  let obsClaim : TermClaim := ⟨.frequency, t, n, α, f, σ⟩
  let dObs := nd "obs" [] [obsEntry] (.term obsClaim)

  -- IT with correct model
  let trustClaim : TrustClaim := .trust .oneSample t n α f p_correct ci σ
  let dIT := nd "IT" [dModel, dObs] [modelEntry, obsEntry] (.trust trustClaim)

  -- ETex: try to produce expected value p_wrong (should fail)
  let exactEntry : ContextEntry := ⟨"r", mkSupport "obs", α, .exact p_wrong⟩
  let concClaim : TermClaim := ⟨.expected, t, n, α, p_wrong, σ⟩
  let dETex_bad := nd "ETex" [dIT] [modelEntry, exactEntry] (.term concClaim)
  runAdversarial "ETex with forged value 0.20 (Trust certified 0.48)" dETex_bad

  -- ETex with correct value (should succeed)
  let exactEntry2 : ContextEntry := ⟨"r", mkSupport "obs", α, .exact p_correct⟩
  let concClaim2 : TermClaim := ⟨.expected, t, n, α, p_correct, σ⟩
  let dETex_ok := nd "ETex" [dIT] [modelEntry, exactEntry2] (.term concClaim2)
  runAdversarial "ETex with correct value 0.48" dETex_ok (shouldFail := false)

-- ============================================================================
-- Attack 4: Product rule to manufacture p > 1 via E×L division
-- ============================================================================

private def attack4_divisionEscape : IO Unit := do
  IO.println "  Attack 4: E×L division to get value > 1"
  let α := Output.atom "A"
  let β := Output.atom "B"
  let αβ := Output.prod α β
  let t := Term.atom "t"
  let σ := mkProv "σ"
  let supp := mkSupport "obs"

  -- (A×B)_{0.5}  and  B_{0.01}  →  try A_{50} (should fail: 50 > 1)
  let prodClaim : TermClaim := ⟨.frequency, .pair t t, 100, αβ, P 50 100, σ⟩
  let rightClaim : TermClaim := ⟨.frequency, .snd t, 100, β, P 1 100, σ⟩
  let forgedClaim : TermClaim := ⟨.frequency, .fst t, 100, α, P 50 1, σ⟩  -- 50/1 > 1

  -- This should fail at clampProb (50/1 gets clamped to 1) or at probDiv
  let ctx := [⟨"t", supp, αβ, .unknown⟩]
  let dProd := nd "obs" [] ctx (.term prodClaim)
  let dRight := nd "obs" [] [⟨"t", supp, β, .unknown⟩] (.term rightClaim)
  let dDiv := nd "E×L" [dProd, dRight] ctx (.term forgedClaim)
  runAdversarial "E×L: 0.5 / 0.01 = 50 (> 1)" dDiv

-- ============================================================================
-- Attack 5: I× without real independence (flag abuse)
-- ============================================================================

private def attack5_fakeIndependence : IO Unit := do
  IO.println "  Attack 5: I× with hasIndependenceWitness=true (flag abuse)"
  let α := Output.atom "A"
  let β := Output.atom "B"
  let αβ := Output.prod α β
  let t1 := Term.atom "x"
  let t2 := Term.atom "y"
  let σ := mkProv "σ"
  let supp := mkSupport "obs"

  -- Same provenance σ for both — not independent! But flag says they are.
  let tc1 : TermClaim := ⟨.frequency, t1, 100, α, P 80 100, σ⟩
  let tc2 : TermClaim := ⟨.frequency, t2, 100, β, P 60 100, σ⟩
  let prodVal := probMul (P 80 100) (P 60 100)  -- 0.48
  let tcProd : TermClaim := ⟨.frequency, .pair t1 t2, 100, αβ, prodVal, σ⟩

  let ctx1 := [⟨"x", supp, α, .unknown⟩]
  let ctx2 := [⟨"y", supp, β, .unknown⟩]
  let dA := nd "obs" [] ctx1 (.term tc1)
  let dB := nd "obs" [] ctx2 (.term tc2)

  -- I× with flag=true but frequency-mode premises.  The flag is no longer
  -- enough: realised frequencies do not multiply, so the mode gate rejects it.
  let dProd := ndW "I×" [dA, dB] (ctx1 ++ ctx2) (.term tcProd)
  runAdversarial "I× multiplying observed frequencies (flag abuse)" dProd
  IO.println "    ↳ Closed: I× now requires expected mode, and independentContexts"
  IO.println "      is a real variable-disjointness test rather than a stub."

-- ============================================================================
-- Attack 6: Derive two different exact values for same variable
-- ============================================================================

private def attack6_conflictingExact : IO Unit := do
  IO.println "  Attack 6: Two exact values for same variable via Contraction"
  let α := Output.atom "HR"

  -- Can we end up with both {x : α_{0.3}} and {x : α_{0.7}} in a context?
  -- Via identity, each in isolation is fine.
  -- Via WeakeningS, we can merge them (different claims required).
  let e1 : ContextEntry := ⟨"x", mkSupport "A", α, .exact (P 3 10)⟩
  let e2 : ContextEntry := ⟨"x", mkSupport "B", α, .exact (P 7 10)⟩

  let dId1 := nd "identity" [] [e1] (.identity e1)
  let dId2 := nd "identity" [] [e2] (.identity e2)

  -- WeakeningS: merge (requires different claims)
  let merged := [e1, e2]
  let dWeak := ndW "WeakeningS" [dId1, dId2] merged (.identity e1)

  -- Contraction: try to narrow to a single exact value
  -- e1 has .exact(0.3) and e2 has .exact(0.7)
  -- For contraction to succeed, the new value must be in BOTH constraints.
  -- 0.3 ∈ .exact(0.3)? Only if new value == 0.3.
  -- 0.3 ∈ .exact(0.7)? No! So Contraction should REJECT any value.

  let forged : ContextEntry := ⟨"x", mkSupport "A", α, .exact (P 5 10)⟩
  let dContract := nd "Contraction" [dWeak] [forged] (.identity e1)
  runAdversarial "Contraction: merge exact(0.3) + exact(0.7) → exact(0.5)" dContract

-- ============================================================================
-- Attack 7: obs with non-integer n*f
-- ============================================================================

private def attack7_nonIntegerNF : IO Unit := do
  IO.println "  Attack 7: obs with n*f not integer"
  let α := Output.atom "HR"
  let t := Term.atom "r"
  let σ := mkProv "σ"
  -- n=3, f=1/4 → n*f = 3/4 (not an integer)
  let tc : TermClaim := ⟨.frequency, t, 3, α, P 1 4, σ⟩
  let ctx := [⟨"r", mkSupport "obs", α, .unknown⟩]
  let dObs := nd "obs" [] ctx (.term tc)
  runAdversarial "obs: n=3, f=1/4, n*f=3/4 (not integer)" dObs

-- ============================================================================
-- Attack 8: Forge Trust for contradictory model
-- ============================================================================
/-
  Data: 80/100 (80% flagged high risk)
  Model: p = 0.20 (claims only 20% should be)
  CI ≈ [0.72, 0.88] — clearly doesn't contain 0.20.
  Can we STILL derive Trust?
-/

private def attack8_forgedTrust : IO Unit := do
  IO.println "  Attack 8: Trust for model that contradicts data"
  let α := Output.atom "HR"
  let t := Term.atom "r"
  let σ := mkProv "σ"
  let n : Nat := 100
  let f := P 80 100   -- observed 80%
  let p := P 20 100   -- model 20%

  let ci := binomialCI n f p

  let modelEntry : ContextEntry := ⟨"m", mkSupport "model", α, .exact p⟩
  let dModel := nd "identity" [] [modelEntry] (.identity modelEntry)
  let obsEntry : ContextEntry := ⟨"r", mkSupport "obs", α, .unknown⟩
  let dObs := nd "obs" [] [obsEntry] (.term ⟨.frequency, t, n, α, f, σ⟩)

  -- Attempt Trust with the contradictory model
  let trustClaim : TrustClaim := .trust .oneSample t n α f p ci σ
  let dIT := nd "IT" [dModel, dObs] [modelEntry, obsEntry] (.trust trustClaim)
  runAdversarial "Trust: model 20% vs data 80% (n=100)" dIT

-- ============================================================================
-- Main
-- ============================================================================

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println " TPTND Adversarial Soundness Tests"
  IO.println " Every test SHOULD be blocked unless noted otherwise."
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println ""
  attack1_contractionForge
  IO.println ""
  attack2_trustAndUntrust
  IO.println ""
  attack3_etexBypass
  IO.println ""
  attack4_divisionEscape
  IO.println ""
  attack5_fakeIndependence
  IO.println ""
  attack6_conflictingExact
  IO.println ""
  attack7_nonIntegerNF
  IO.println ""
  attack8_forgedTrust
  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println " Summary"
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println ""
  IO.println " ⚠ EXPLOIT = soundness hole found (checker accepts bad proof)"
  IO.println " ✓ BLOCKED = checker correctly rejects attack"
  IO.println " ✓ OK      = legitimately accepted (marked shouldFail=false)"
  IO.println ""
