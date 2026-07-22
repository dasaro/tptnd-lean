import TPTND

open TPTND

/-! # Attack 1 Deep Dive: Full exploit chain from Contraction forge to Trust

  Can the Contraction exploit produce a *false* Trust conclusion? -/

private def P (n d : Nat) : Prob := clampProb ((n : ℚ) / d)
private def nd (rule : String) (prems : List Derivation)
    (ctx : Context) (claim : Claim) : Derivation :=
  .node rule prems ⟨ctx, claim⟩ false
private def ndW (rule : String) (prems : List Derivation)
    (ctx : Context) (claim : Claim) : Derivation :=
  .node rule prems ⟨ctx, claim⟩ true
private def mkSupport (s : String) : Finset String := {s}
private def mkProv   (s : String) : Finset String := {s}

private def runTest (name : String) (d : Derivation) : IO Unit := do
  match checkDerivation d with
  | .ok () => IO.println s!"  ✓ ACCEPTED  {name}"
  | .error e => IO.println s!"  ✗ REJECTED  {name}: {e}"

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println " Attack 1 Deep Dive: Contraction forge → Trust chain"
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println ""

  let α := Output.atom "HR"
  let t := Term.atom "r"
  let σ1 := mkProv "σ1"
  let σ2 := mkProv "σ2"

  -- Step 1: Two obs leaves — one shows 80% and one shows 20%
  -- (REAL data from different populations)
  let entryA : ContextEntry := ⟨"r", mkSupport "popA", α, .unknown⟩
  let entryB : ContextEntry := ⟨"r", mkSupport "popB", α, .unknown⟩
  let obs1 : TermClaim := ⟨.frequency, t, 100, α, P 80 100, σ1⟩  -- 80% in pop A
  let obs2 : TermClaim := ⟨.frequency, t, 100, α, P 20 100, σ2⟩  -- 20% in pop B
  let dObs1 := nd "obs" [] [entryA] (.term obs1)
  let dObs2 := nd "obs" [] [entryB] (.term obs2)

  IO.println "  Step 1: Two valid observations"
  IO.println "    obs1: n=100, f=80/100 (pop A)"
  IO.println "    obs2: n=100, f=20/100 (pop B)"
  runTest "obs1 (pop A, 80%)" dObs1
  runTest "obs2 (pop B, 20%)" dObs2

  -- Step 2: WeakeningS merges contexts
  let mergedCtx := [entryA, entryB]
  let dWeak := ndW "WeakeningS" [dObs1, dObs2] mergedCtx (.term obs1)

  IO.println ""
  IO.println "  Step 2: WeakeningS merges contexts"
  IO.println "    Γ = {r:HR_{[0,1]}@popA, r:HR_{[0,1]}@popB}"
  runTest "WeakeningS merge" dWeak

  -- Step 3: Contraction forge — pick value 0.78 (will be inside the CI)
  let forgedValue := P 78 100
  let forgedEntry : ContextEntry := ⟨"r", mkSupport "popA", α, .exact forgedValue⟩
  let dContract := nd "Contraction" [dWeak] [forgedEntry] (.term obs1)

  IO.println ""
  IO.println "  Step 3: Contraction — forge exact value 0.78 from two unknowns"
  runTest "Contraction forge to exact(0.78)" dContract

  -- Step 4: NOW — can we derive Trust for obs1 (80%) with model 0.78?
  -- CI(100, 0.8, 0.78) should contain 0.78 since 0.78 ≈ 0.8.
  let ci := binomialCI 100 (P 80 100) forgedValue

  IO.println ""
  IO.println "  Step 4: Use forged model in Trust derivation"
  IO.println s!"    CI(100, 0.80, 0.78) = contains 0.78? {inConstraint forgedValue ci}"

  -- identity_star from the contracted context to get model
  let dModel := nd "identity" [] [forgedEntry] (.identity forgedEntry)

  let trustClaim : TrustClaim := .trust .oneSample t 100 α (P 80 100) forgedValue ci σ1
  let dIT := nd "IT" [dModel, dObs1] [forgedEntry, entryA] (.trust trustClaim)
  runTest "IT: Trust(r₁₀₀ : HR_{0.80}; forged 0.78, CI)" dIT

  IO.println ""
  IO.println "  Question: Is this Trust conclusion FALSE?"
  IO.println "  Answer:   NO. The data (80/100) IS consistent with p=0.78."
  IO.println "            The CI [~0.72, ~0.88] correctly contains 0.78."
  IO.println "            Trust is a VALID conclusion."
  IO.println ""
  IO.println "  The weakness: the model p=0.78 was forged via Contraction"
  IO.println "  rather than coming from actual reference data."
  IO.println "  But the Trust/UTrust evaluation is still CORRECT."
  IO.println ""

  -- Step 5: Can we derive Trust for something ACTUALLY false?
  -- E.g., data=80%, forged model=0.20. CI will NOT contain 0.20.
  IO.println "  Step 5: Try forging a contradictory model (0.20 for data 80%)"
  let badModel := P 20 100
  let badCi := binomialCI 100 (P 80 100) badModel
  IO.println s!"    CI(100, 0.80, 0.20) contains 0.20? {inConstraint badModel badCi}"

  let badModelEntry : ContextEntry := ⟨"r", mkSupport "popA", α, .exact badModel⟩
  let dBadModel := nd "identity" [] [badModelEntry] (.identity badModelEntry)
  let badTrust : TrustClaim := .trust .oneSample t 100 α (P 80 100) badModel badCi σ1
  let dBadIT := nd "IT" [dBadModel, dObs1] [badModelEntry, entryA] (.trust badTrust)
  runTest "IT: Trust(r₁₀₀ : HR_{0.80}; forged 0.20, CI)" dBadIT

  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println " VERDICT"
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println ""
  IO.println " Contraction from unknowns IS a rule-level weakness:"
  IO.println "   • Two .unknown entries can be contracted to ANY exact value"
  IO.println "   • This creates model assumptions without data justification"
  IO.println ""
  IO.println " But it CANNOT produce false Trust/UTrust conclusions:"
  IO.println "   • IT/IUT independently verify model vs data via the CI"
  IO.println "   • A forged model that contradicts data → IT rejects it"
  IO.println "   • A forged model consistent with data → Trust is CORRECT"
  IO.println ""
  IO.println " The exploit is a PROVENANCE weakness, not a SOUNDNESS hole:"
  IO.println "   You can forge WHERE a model came from, but not WHETHER"
  IO.println "   the data supports it."
  IO.println ""
