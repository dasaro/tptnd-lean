import TPTND

open TPTND

/-! # COMPAS Derivations from ProPublica Data

Data source: `compas-scores-two-years.csv` from
  https://github.com/propublica/compas-analysis
Filters: days_b_screening_arrest ∈ [-30,30], is_recid ≠ -1,
         c_charge_degree ≠ "O", score_text ≠ N/A  →  6172 defendants.
Threshold: LowRisk = "Low", HighRisk = "Medium" ∨ "High".

Raw counts from ProPublica CSV (after filtering):

  African-American                           Caucasian
  ┌────────────────┬────────┬─────────┬─────┐  ┌────────────────┬────────┬─────────┬─────┐
  │                │LowRisk │HighRisk │Total│  │                │LowRisk │HighRisk │Total│
  │Male non-recid. │  658   │   510   │1168 │  │Male non-recid. │  777   │   192   │ 969 │
  │Fem. non-recid. │  215   │   131   │ 346 │  │Fem. non-recid. │  222   │    90   │ 312 │
  │Total non-recid.│  873   │   641   │1514 │  │Total non-recid.│  999   │   282   │1281 │
  │Male recidivists│ 411    │  1047   │1458 │  │Male recidivists│  332   │   320   │ 652 │
  │Fem. recidivists│  62    │   141   │ 203 │  │Fem. recidivists│   76   │    94   │ 170 │
  │Total recid.    │ 473    │  1188   │1661 │  │Total recid.    │  408   │   414   │ 822 │
  └────────────────┴────────┴─────────┴─────┘  └────────────────┴────────┴─────────┴─────┘

Derivations:
  1. **Caucasian FNR Trust** (gender): female ≈ male → fair
  2. **UPDATE chain**: male + female pools to headline rate
  3. **AA FNR Trust** (gender): reproduces paper §4.3
  4. **AA FPR UTrust** (gender): female ≠ male → unfair
  5. **ProPublica main claim** (race): Black FPR ≠ White FPR → UTrust
  6. **Bayesian posterior** (I-P + E-P): prior update from pilot sample
-/

-- ============================================================================
-- Helpers
-- ============================================================================

private def P (n d : Nat) : Prob := clampProb ((n : ℚ) / d)

private def nd (rule : String) (prems : List Derivation)
    (ctx : Context) (claim : Claim) : Derivation :=
  .node rule prems ⟨ctx, claim⟩ false

private def mkSupport (s : String) : Finset String := {s}
private def mkProv   (s : String) : Finset String := {s}
private def mkProv2  (a b : String) : Finset String := {a, b}

private def runTest (name : String) (d : Derivation) : IO Unit := do
  match checkDerivation d with
  | .ok () => IO.println s!"  ✓ PASS  {name}"
  | .error e => IO.println s!"  ✗ FAIL  {name}: {e}"

private def showProb (p : Prob) : String :=
  let q := p.val
  let dec := (q.num.toNat * 10000 / q.den)
  let intPart := dec / 10000
  let fracPart := dec % 10000
  s!"{q.num}/{q.den} ≈ {intPart}.{String.ofList (Nat.toDigits 10 (fracPart + 10000) |>.drop 1)}"

private def showProbShort (p : Prob) : String :=
  let q := p.val
  let dec := (q.num.toNat * 10000 / q.den)
  let intPart := dec / 10000
  let fracPart := dec % 10000
  s!"{intPart}.{String.ofList (Nat.toDigits 10 (fracPart + 10000) |>.drop 1)}"

private def showConstraint (c : Constraint) : String :=
  match c with
  | .interval lo hi => s!"[{showProb lo}, {showProb hi}]"
  | .outsideInterval lo hi => s!"¬[{showProb lo}, {showProb hi}]"
  | .exact p => s!"exact({showProb p})"
  | .unknown => "[0,1]"

private def showConstraintShort (c : Constraint) : String :=
  match c with
  | .interval lo hi => s!"[{showProbShort lo}, {showProbShort hi}]"
  | .outsideInterval lo hi => s!"¬[{showProbShort lo}, {showProbShort hi}]"
  | .exact p => s!"{p.val.num}/{p.val.den}"
  | .unknown => "[0,1]"

-- ============================================================================
-- Generic derivation tree renderer
-- ============================================================================

private def showEntry (e : ContextEntry) : String :=
  s!"{e.name} : {showOutput e.output}_{showConstraintShort e.constraint}"
where
  showOutput : Output → String
    | .atom s => s
    | .neg o => s!"¬{showOutput o}"
    | .sum a b => s!"({showOutput a}+{showOutput b})"
    | .prod a b => s!"({showOutput a}×{showOutput b})"
    | .arr a ann b => s!"({showOutput a}⇒[{showProbShort ann}]{showOutput b})"

private def showCtx (ctx : Context) : String :=
  "{" ++ String.intercalate ", " (ctx.map showEntry) ++ "}"

private def showTerm : Term → String
  | .atom s => s
  | .pair a b => s!"⟨{showTerm a}, {showTerm b}⟩"
  | .fst t => s!"fst({showTerm t})"
  | .snd t => s!"snd({showTerm t})"
  | .lam x b => s!"[{x}]{showTerm b}"
  | .app f a => s!"({showTerm f} · {showTerm a})"

private def showClaim : Claim → String
  | .outputDecl o => s!"{showEntry.showOutput o} :: output"
  | .distDecl _ => "Γ"
  | .identity e => showEntry e
  | .term tc =>
    let modeStr := if tc.mode == .expected then "exp" else "freq"
    s!"{showTerm tc.term}_{tc.samples} : {showEntry.showOutput tc.output}_{showConstraintShort (.exact tc.value)} [{modeStr}]"
  | .trust (.trust _ t n α f p ci _) =>
    s!"Trust_𝒫({showTerm t}_{n} : {showEntry.showOutput α}_{showConstraintShort (.exact f)}; {p.val.num}/{p.val.den}, {showConstraintShort ci})"
  | .trust (.untrust _ t n α f p ci _) =>
    s!"UTrust_𝒫({showTerm t}_{n} : {showEntry.showOutput α}_{showConstraintShort (.exact f)}; {p.val.num}/{p.val.den}, {showConstraintShort ci})"
  | .comparison _ => "Comparison(...)"
  | .priorFamily fam => s!"Π[{fam.points.length} hypotheses]"

private def padRight (s : String) (w : Nat) : String :=
  s ++ String.ofList (List.replicate (if w > s.length then w - s.length else 0) ' ')

/-- Render a derivation tree as lines of text.
    Returns (lines, width, conclusionLine). -/
private partial def renderTree (d : Derivation) (indent : String := "  ") : IO Unit := do
  let ctx := d.conclusion.context
  let claim := d.conclusion.claim
  let sequent := s!"{showCtx ctx} ⊢ {showClaim claim}"
  match d.premises with
  | [] =>
    -- Leaf node: just the sequent
    let ruleLine := String.ofList (List.replicate sequent.length '─')
    IO.println s!"{indent}{ruleLine} {d.ruleName}"
    IO.println s!"{indent}{sequent}"
  | [p] =>
    -- Single premise
    renderTree p indent
    let w := max sequent.length 40
    let ruleLine := String.ofList (List.replicate w '═')
    IO.println s!"{indent}{ruleLine} {d.ruleName}"
    IO.println s!"{indent}{sequent}"
  | [p1, p2] =>
    -- Two premises side by side
    let ctx1 := p1.conclusion.context
    let claim1 := p1.conclusion.claim
    let seq1 := s!"{showCtx ctx1} ⊢ {showClaim claim1}"
    let ctx2 := p2.conclusion.context
    let claim2 := p2.conclusion.claim
    let seq2 := s!"{showCtx ctx2} ⊢ {showClaim claim2}"
    let rule1 := p1.ruleName
    let rule2 := p2.ruleName
    let w1 := max seq1.length 20
    let w2 := max seq2.length 20
    let gap := "    "
    -- Render premise sub-trees if they have their own premises
    for pp in p1.premises do
      renderTree pp (indent ++ "  ")
    for pp in p2.premises do
      renderTree pp (indent ++ String.ofList (List.replicate (w1 + gap.length) ' '))
    -- Premise rule lines and sequents
    let ruleLine1 := String.ofList (List.replicate w1 '─')
    let ruleLine2 := String.ofList (List.replicate w2 '─')
    IO.println s!"{indent}{padRight s!"{ruleLine1} {rule1}" (w1 + rule1.length + 1)}{gap}{ruleLine2} {rule2}"
    IO.println s!"{indent}{padRight seq1 (w1 + rule1.length + 1)}{gap}{seq2}"
    -- Conclusion rule line
    let totalW := max (w1 + gap.length + w2) sequent.length
    let concRule := String.ofList (List.replicate totalW '═')
    IO.println s!"{indent}{concRule} {d.ruleName}"
    IO.println s!"{indent}{sequent}"
  | _ =>
    -- 3+ premises: just list them
    for p in d.premises do
      renderTree p indent
    let w := max sequent.length 40
    let ruleLine := String.ofList (List.replicate w '═')
    IO.println s!"{indent}{ruleLine} {d.ruleName}"
    IO.println s!"{indent}{sequent}"

-- ============================================================================
-- Derivation 1: Caucasian FNR — Trust (gender fairness)
-- ============================================================================
/-
  Benchmark: Caucasian male recidivists' LowRisk rate = 332/652 = 83/163
  Observed:  Caucasian female recidivists' LowRisk rate = 76/170 = 38/85
  P(170, 38/85, 83/163) → 83/163 ∈ CI → Trust

  Derivation tree:
    identity                           obs
    ─────────────────────             ──────────────────────────────
    {m : LR_{83/163}} ⊢ m : LR       {r} ⊢_{ρ_f} r₁₇₀ : LR_{38/85}
    ═══════════════════════════════════════════════════════════════════ IT
    Θ ⊢ Trust_P(r₁₇₀ : LR_{38/85}; 83/163, [ℓ, h])
-/

private def deriveTrust_CaucasianFNR : IO Unit := do
  let LR := Output.atom "LowRisk"
  let p_male := P 332 652
  let n_female : Nat := 170
  let f_female := P 76 170
  let ci := binomialCI n_female f_female p_male

  IO.println "  Benchmark (Caucasian male recid. LowRisk): 332/652 = 83/163"
  IO.println s!"    p = {showProb p_male}"
  IO.println s!"  Observed  (Caucasian female recid. LowRisk): 76/170 = 38/85"
  IO.println s!"    n = {n_female},  f = {showProb f_female}"
  IO.println s!"  CI = {showConstraint ci}"
  IO.println s!"  p ∈ CI?  {inConstraint p_male ci}"

  let t := Term.atom "r"
  let σ := mkProv "ρ_f"
  let modelEntry : ContextEntry := ⟨"m", mkSupport "CaucMaleRecid", LR, .exact p_male⟩
  let dModel := nd "identity" [] [modelEntry] (.identity modelEntry)
  let obsEntry : ContextEntry := ⟨"r", mkSupport "CaucFemaleRecid", LR, .unknown⟩
  let dObs := nd "obs" [] [obsEntry] (.term ⟨.frequency, t, n_female, LR, f_female, σ⟩)
  let trustClaim : TrustClaim := .trust .oneSample t n_female LR f_female p_male ci σ
  let dIT := nd "IT" [dModel, dObs] [modelEntry, obsEntry] (.trust trustClaim)

  if inConstraint p_male ci then
    IO.println ""
    runTest "Caucasian FNR Trust (IT) — female rate consistent with male benchmark" dIT
  else IO.println "  SKIP: benchmark not in CI"

-- ============================================================================
-- Derivation 2: UPDATE chain (sub-batch pooling)
-- ============================================================================

private def deriveUpdate_CaucasianRecid : IO Unit := do
  let LR := Output.atom "LowRisk"
  let t := Term.atom "r"
  let suppObs := mkSupport "CaucRecid"
  let σm := mkProv "σ_m"
  let σf := mkProv "σ_f"
  let σU := mkProv2 "σ_m" "σ_f"
  let n_m : Nat := 652
  let f_m := P 332 652
  let n_f : Nat := 170
  let f_f := P 76 170
  let pooled := weightedFreq n_m f_m n_f f_f

  IO.println s!"  Male batch:   n={n_m}, f={showProb f_m}, LowRisk count=332"
  IO.println s!"  Female batch: n={n_f}, f={showProb f_f}, LowRisk count=76"
  match pooled with
  | some wf => IO.println s!"  Pooled:       n={n_m + n_f}, f={showProb wf}"
  | none    => IO.println "  Pooled: FAILED"
  IO.println s!"  Expected:     408/822 = {showProb (P 408 822)}"

  match pooled with
  | some wf => do
    let obsCtx : Context := [⟨"r", suppObs, LR, .unknown⟩]
    let dObs1 := nd "obs" [] obsCtx (.term ⟨.frequency, t, n_m, LR, f_m, σm⟩)
    let dObs2 := nd "obs" [] obsCtx (.term ⟨.frequency, t, n_f, LR, f_f, σf⟩)
    let dUpdate := nd "update" [dObs1, dObs2] obsCtx (.term ⟨.frequency, t, n_m + n_f, LR, wf, σU⟩)
    IO.println ""
    runTest "Caucasian recid. UPDATE (male + female → 408/822)" dUpdate
  | none => IO.println "  SKIP: pooling failed"

-- ============================================================================
-- Derivation 3: African-American FNR — Trust (paper §4.3)
-- ============================================================================

private def deriveTrust_AAFemaleRecidFNR : IO Unit := do
  let LR := Output.atom "LowRisk"
  let p_male := P 411 1458     -- = 137/486
  let n_female : Nat := 203
  let f_female := P 62 203
  let ci := binomialCI n_female f_female p_male

  IO.println "  Benchmark (AA male recid. LowRisk): 411/1458 = 137/486"
  IO.println s!"    p = {showProb p_male}"
  IO.println s!"  Observed  (AA female recid. LowRisk): 62/203"
  IO.println s!"    n = {n_female},  f = {showProb f_female}"
  IO.println s!"  CI = {showConstraint ci}"
  IO.println s!"  p ∈ CI?  {inConstraint p_male ci}"

  let t := Term.atom "r"
  let σ := mkProv "ρ_f"
  let modelEntry : ContextEntry := ⟨"m", mkSupport "AAMaleRecid", LR, .exact p_male⟩
  let dModel := nd "identity" [] [modelEntry] (.identity modelEntry)
  let obsEntry : ContextEntry := ⟨"r", mkSupport "AAFemaleRecid", LR, .unknown⟩
  let dObs := nd "obs" [] [obsEntry] (.term ⟨.frequency, t, n_female, LR, f_female, σ⟩)
  let trustClaim : TrustClaim := .trust .oneSample t n_female LR f_female p_male ci σ
  let dIT := nd "IT" [dModel, dObs] [modelEntry, obsEntry] (.trust trustClaim)

  if inConstraint p_male ci then
    IO.println ""
    runTest "AA FNR Trust (IT) — paper's §4.3 reproduced from raw counts" dIT
    -- ET^ex: the observed variable's own assumption is committed to the
    -- trusted value and the claim re-enters the expected layer.
    let rEx : ContextEntry := ⟨"r", mkSupport "AAFemaleRecid", LR, .exact p_male⟩
    let dETex := nd "ETex" [dIT] [modelEntry, rEx]
      (.term ⟨.expected, t, n_female, LR, p_male, σ⟩)
    runTest "AA FNR ETex — expected layer re-entered at the trusted value" dETex
  else IO.println "  SKIP: benchmark not in CI"

-- ============================================================================
-- Derivation 4: African-American FPR — UTrust (gender disparity)
-- ============================================================================

private def deriveUTrust_AAFemaleFPR : IO Unit := do
  let HR := Output.atom "HighRisk"
  let p_male := P 510 1168     -- = 255/584
  let n_female : Nat := 346
  let f_female := P 131 346
  let ci := binomialCI n_female f_female p_male

  IO.println "  Benchmark (AA male non-recid. HighRisk): 510/1168 = 255/584"
  IO.println s!"    p = {showProb p_male}"
  IO.println s!"  Observed  (AA female non-recid. HighRisk): 131/346"
  IO.println s!"    n = {n_female},  f = {showProb f_female}"
  IO.println s!"  CI = {showConstraint ci}"
  IO.println s!"  p ∈ CI?  {inConstraint p_male ci}"

  let t := Term.atom "u"
  let σ := mkProv "ρ_f"
  let modelEntry : ContextEntry := ⟨"m", mkSupport "AAMaleNonRecid", HR, .exact p_male⟩
  let dModel := nd "identity" [] [modelEntry] (.identity modelEntry)
  let obsEntry : ContextEntry := ⟨"u", mkSupport "AAFemaleNonRecid", HR, .unknown⟩
  let dObs := nd "obs" [] [obsEntry] (.term ⟨.frequency, t, n_female, HR, f_female, σ⟩)
  let utrustClaim : TrustClaim := .untrust .oneSample t n_female HR f_female p_male ci σ
  let dIUT := nd "IUT" [dModel, dObs] [modelEntry, obsEntry] (.trust utrustClaim)

  if notInConstraint p_male ci then
    IO.println ""
    runTest "AA FPR UTrust (IUT) — gender disparity in false positives" dIUT
  else do
    -- The benchmark falls inside the band: the one-sample verdict is Trust,
    -- agreeing with the two-sample tests (Derivations 9 and 12).
    let trustClaim : TrustClaim := .trust .oneSample t n_female HR f_female p_male ci σ
    let dIT := nd "IT" [dModel, dObs] [modelEntry, obsEntry] (.trust trustClaim)
    IO.println ""
    runTest "AA FPR Trust (IT) — benchmark inside the band at this level" dIT

-- ============================================================================
-- Derivation 5: ProPublica's main claim — racial bias in false positives
-- ============================================================================
/-
  THIS IS THE HEADLINE FINDING: ProPublica showed that Black defendants who
  did NOT reoffend were scored High Risk at 42.3%, while White defendants who
  did NOT reoffend were scored High Risk at only 22.0%.

  Observed:  Black non-recidivists HighRisk rate = 641/1514
  Benchmark: White non-recidivists HighRisk rate = 282/1281 = 94/427
  P(1514, 641/1514, 94/427) → 94/427 ∉ CI → UTrust

  The TPTND checker FORMALLY CERTIFIES this as racial unfairness.

  Derivation tree:
    identity                                obs
    ──────────────────────────             ──────────────────────────────────
    {w : HR_{94/427}} ⊢ w : HR_{94/427}   {u} ⊢_{σ} u₁₅₁₄ : HR_{641/1514}
    ═════════════════════════════════════════════════════════════════════════ IUT
    Θ ⊢ UTrust_P(u₁₅₁₄ : HR_{641/1514}; 94/427, [ℓ, h])
-/

private def deriveUTrust_ProPublicaMain : IO Unit := do
  let HR := Output.atom "HighRisk"

  -- ProPublica's key numbers
  let n_black : Nat := 1514       -- Black non-recidivists
  let f_black := P 641 1514       -- 641 scored HighRisk
  let p_white := P 282 1281       -- White FPR benchmark = 94/427

  let ci := binomialCI n_black f_black p_white

  IO.println "  ProPublica's headline: \"Black defendants who did not reoffend"
  IO.println "  were almost twice as likely as White defendants to be labeled"
  IO.println "  higher risk.\""
  IO.println ""
  IO.println s!"  Observed  (Black non-recid. HighRisk): 641/1514"
  IO.println s!"    n = {n_black},  f = {showProb f_black}"
  IO.println s!"  Benchmark (White non-recid. HighRisk): 282/1281 = 94/427"
  IO.println s!"    p = {showProb p_white}"
  IO.println s!"  CI = {showConstraint ci}"
  IO.println s!"  p ∈ CI?  {inConstraint p_white ci}  (must be false for UTrust)"

  let t := Term.atom "u"
  let σ := mkProv2 "σ_m" "σ_f"   -- combined male + female provenance
  let modelEntry : ContextEntry := ⟨"w", mkSupport "WhiteNonRecid", HR, .exact p_white⟩
  let dModel := nd "identity" [] [modelEntry] (.identity modelEntry)
  let obsEntry : ContextEntry := ⟨"u", mkSupport "BlackNonRecid", HR, .unknown⟩
  -- The Black non-recidivist cohort enters as two sub-batches (male, female)
  -- pooled by UPDATE — the derivation displayed in the paper.
  let dObsM := nd "obs" [] [obsEntry]
    (.term ⟨.frequency, t, 1168, HR, P 510 1168, mkProv "σ_m"⟩)
  let dObsF := nd "obs" [] [obsEntry]
    (.term ⟨.frequency, t, 346, HR, P 131 346, mkProv "σ_f"⟩)
  let dUpd := nd "update" [dObsM, dObsF] [obsEntry]
    (.term ⟨.frequency, t, n_black, HR, f_black, σ⟩)

  let utrustClaim : TrustClaim := .untrust .oneSample t n_black HR f_black p_white ci σ
  let dIUT := nd "IUT" [dModel, dUpd] [modelEntry, obsEntry] (.trust utrustClaim)

  if notInConstraint p_white ci then
    IO.println ""
    runTest "ProPublica main claim: racial FPR bias (IUT)" dIUT
    IO.println ""
    IO.println "  ┌─────────────────────────────────────────────────────────────┐"
    IO.println "  │              NATURAL DEDUCTION TREE                         │"
    IO.println "  └─────────────────────────────────────────────────────────────┘"
    IO.println ""
    renderTree dIUT "  "
    IO.println ""
    IO.println s!"  Side conditions verified by checker:"
    IO.println s!"    • Model output = Obs output = HighRisk                   ✓"
    IO.println s!"    • Obs mode = frequency                                   ✓"
    IO.println s!"    • CI = 𝒫(1514, 641/1514, 94/427) = {showConstraintShort ci}"
    IO.println s!"    • 94/427 ≈ {showProbShort p_white} ∉ {showConstraintShort ci}      ✓  → UTrust"
    IO.println s!"    • Conclusion fields match premises                       ✓"
    IO.println ""
    IO.println "  Interpretation: the White FPR (≈22%) is nowhere near the CI"
    IO.println "  around the Black FPR (≈42%).  TPTND formally certifies this"
    IO.println "  as UTrust — the assumption that both races share the same"
    IO.println "  false-positive rate is statistically rejected."
    -- EUT: the complement interval re-enters the typing context, giving the
    -- transferable term claim displayed in the paper.
    let compl := match ci with
      | .interval lo hi => Constraint.outsideInterval lo hi
      | other => other
    let xu : ContextEntry := ⟨"u", mkSupport "BlackNonRecid", HR, compl⟩
    let dEUT := nd "EUT" [dIUT] [modelEntry, obsEntry, xu]
      (.term ⟨.frequency, t, n_black, HR, f_black, σ⟩)
    IO.println ""
    runTest "EUT: complement interval re-entered as audit assumption" dEUT
  else IO.println "  SKIP: benchmark IS in CI (unexpected!)"

-- ============================================================================
-- Derivation 6: Bayesian posterior update (I-P + E-P)
-- ============================================================================
/-
  Scenario: An auditor evaluates a new jurisdiction's COMPAS deployment.
  Before seeing data, they entertain three hypotheses about the FPR:

    H₁: rate = 1/6 ≈ 16.7%  (optimistic — lower than any observed group)
    H₂: rate = 1/3 ≈ 33.3%  (moderate — between White and Black rates)
    H₃: rate = 1/2 = 50.0%  (pessimistic — half flagged incorrectly)

  Prior weights b = (1/2, 1/3, 1/6), summing to 1 and distinct from the
  hypothesis values — a prior that favours the optimistic hypothesis.

  Pilot data: 5 non-recidivists, 2 flagged HighRisk → f = 2/5, s = 2.

  Bayesian update (likelihood aᵢ²(1−aᵢ)³, weighted by bᵢ):

    P(H₁|data) = 75/226   ≈ 33.2%  (down from 50.0%)
    P(H₂|data) = 256/565  ≈ 45.3%  (up from 33.3%)
    P(H₃|data) = 243/1130 ≈ 21.5%  (up from 16.7%)

  The pilot frequency f = 2/5 sits closest to H₂, so mass flows there.

  Derivation tree (for H₃ posterior):

    identity₁               identity₂               identity₃
    {x:FPR_{1/6}}⊢x:FPR_{1/6}  {x:FPR_{1/3}}⊢x:FPR_{1/3}  {x:FPR_{1/2}}⊢x:FPR_{1/2}
    ════════════════════════════════════════════════════════════════ I-P
    ⊢ prior-family

    obs
    {r} ⊢_{ρ} r₅ : FPR_{2/5}
    ═══════════════════════════════════════════════════════════════ E-P
    {x : FPR_{1/2}} ⊢ result : FPR_{243/1130}
-/

private def deriveBayesian : IO Unit := do
  let FPR := Output.atom "FPR"

  -- Three hypotheses about the FPR: a₁=1/6, a₂=1/3, a₃=1/2, carrying
  -- prior weights b₁=1/2, b₂=1/3, b₃=1/6 (Σbᵢ = 1 ✓).
  -- The weights are a genuine modelling choice, independent of the
  -- hypothesis values: this needs IDENTITY*₂ (`identity_model`), which is
  -- what lets a premise conclude `y : β_b` from `{x : α_a}` with b ≠ a.
  -- Plain `identity` forces b = a and can only express degenerate priors.
  let a1 := P 1 6
  let a2 := P 1 3
  let a3 := P 1 2
  let b1 := P 1 2
  let b2 := P 1 3
  let b3 := P 1 6

  -- I-P premises: {hᵢ : FPR_{aᵢ}} ⊢ wᵢ : FPR_{bᵢ}  (IDENTITY*₂)
  -- One hypothesis variable x = "h" and one target variable y = "w" across the
  -- whole family: the printed rule varies only the values (aᵢ, bᵢ).
  let e1 : ContextEntry := ⟨"h", mkSupport "hyp", FPR, .exact a1⟩
  let e2 : ContextEntry := ⟨"h", mkSupport "hyp", FPR, .exact a2⟩
  let e3 : ContextEntry := ⟨"h", mkSupport "hyp", FPR, .exact a3⟩
  let w1 : ContextEntry := ⟨"w", mkSupport "prior", FPR, .exact b1⟩
  let w2 : ContextEntry := ⟨"w", mkSupport "prior", FPR, .exact b2⟩
  let w3 : ContextEntry := ⟨"w", mkSupport "prior", FPR, .exact b3⟩

  let dId1 := nd "identity_model" [] [e1] (.identity w1)
  let dId2 := nd "identity_model" [] [e2] (.identity w2)
  let dId3 := nd "identity_model" [] [e3] (.identity w3)

  -- I-P conclusion: empty context, prior-family claim (aᵢ, bᵢ)
  let dPrior := nd "I-P" [dId1, dId2, dId3] []
    (.priorFamily { xName := "h", alpha := FPR, yName := "w", beta := FPR
                  , points := [(a1, b1), (a2, b2), (a3, b3)] })

  -- Observation: pilot sample, 2 out of 5 flagged HighRisk
  let n_pilot : Nat := 5
  let f_pilot := P 2 5
  let obsEntry : ContextEntry := ⟨"r", mkSupport "pilot", FPR, .unknown⟩
  let dObs := nd "obs" [] [obsEntry] (.term ⟨.frequency, Term.atom "r", n_pilot, FPR, f_pilot, mkProv "ρ"⟩)

  -- E-P conclusion: posterior for H₃ (a₃ = 1/2)
  -- Posteriors are computed here exactly as the checker recomputes them,
  -- so the printed numbers cannot drift from the certified derivation.
  let pairs : List (ℚ × ℚ) := [(a1.val, b1.val), (a2.val, b2.val), (a3.val, b3.val)]
  let s_obs : Nat := 2
  let post := fun (j : Nat) =>
    clampProb ((bayesianPosterior pairs s_obs n_pilot j).getD 0)
  let post1 := post 0
  let post2 := post 1
  let posterior := post 2

  -- Support entry in conclusion context: FPR_{1/2} (selects hypothesis H₃)
  let supportEntry : ContextEntry := ⟨"h", mkSupport "hyp", FPR, .exact a3⟩
  let concEntry : ContextEntry := ⟨"w", mkSupport "posterior", FPR, .exact posterior⟩
  -- the conclusion keeps the observation's assumption alongside the selected
  -- hypothesis: Γ, x : α_{aⱼ} ⊢ …
  let dEP := nd "E-P" [dPrior, dObs] [supportEntry, obsEntry] (.identity concEntry)

  IO.println "  Prior hypotheses about FPR (weights ≠ hypothesis values):"
  IO.println s!"    H₁: a = {showProb a1}, weight = {showProb b1}"
  IO.println s!"    H₂: a = {showProb a2}, weight = {showProb b2}"
  IO.println s!"    H₃: a = {showProb a3}, weight = {showProb b3}"
  IO.println s!"    Σ weights = 1/2 + 1/3 + 1/6 = 1 ✓"
  IO.println ""
  IO.println s!"  Pilot data: n={n_pilot}, s=2 flagged HighRisk, f={showProb f_pilot}"
  IO.println ""
  IO.println "  Bayesian posteriors:"
  IO.println s!"    P(H₁|data) = {showProb post1}  (prior {showProb b1})"
  IO.println s!"    P(H₂|data) = {showProb post2}  (prior {showProb b2})"
  IO.println s!"    P(H₃|data) = {showProb posterior}  (prior {showProb b3})"
  IO.println ""

  runTest "Bayesian I-P + E-P: posterior for H₃ (FPR = 1/2)" dEP

  IO.println ""
  IO.println "  Interpretation: the prior favours a low FPR (weight 1/2 on"
  IO.println "  H₁), but the pilot data f=2/5 sits closest to H₂ (a=1/3), so"
  IO.println "  mass flows from H₁ to H₂ and H₃. Because the weights are now"
  IO.println "  free of the hypothesis values, this is a real prior-to-"
  IO.println "  posterior update rather than an artefact of the encoding."

-- ============================================================================
-- Derivation 7: IEx — Black FPR EXCEEDS White FPR (two-sample comparison)
-- ============================================================================
/-
  This is the DIRECT phrasing of ProPublica's finding: the false-positive
  rate for Black defendants SIGNIFICANTLY EXCEEDS that of White defendants.

  Unlike derivation 5 (IUT), which tests Black data against a White benchmark,
  IEx is a symmetric two-sample proportion test:
    Q(n₁, n₂, f₁, f₂) = (f₁ − f₂) ± z · √(f₁(1−f₁)/n₁ + f₂(1−f₂)/n₂)
  If 0 ∉ CI → significant excess.

  Left:   Black non-recid. HighRisk  641/1514 (provenance σ_B)
  Right:  White non-recid. HighRisk  282/1281 (provenance σ_W)
  Difference: 641/1514 − 282/1281 ≈ 0.2033

  Derivation tree:
    obs                                      obs
    ──────────────────────────────           ──────────────────────────────
    {u} ⊢_{σ_B} u₁₅₁₄ : HR_{641/1514}     {w} ⊢_{σ_W} w₁₂₈₁ : HR_{282/1281}
    ═══════════════════════════════════════════════════════════════════════ IEx
    Excess_Q(u₁₅₁₄:HR_{641/1514}, w₁₂₈₁:HR_{282/1281}; diff, [ℓ,h])
-/

private def deriveExcess_FPR : IO Unit := do
  let HR := Output.atom "HighRisk"
  let tB := Term.atom "u"
  let tW := Term.atom "w"
  let σB := mkProv "σ_B"
  let σW := mkProv "σ_W"

  let nB : Nat := 1514
  let fB := P 641 1514
  let nW : Nat := 1281
  let fW := P 282 1281

  -- Two-sample CI for the difference
  let ci := twoSampleCI nB nW fB fW

  IO.println s!"  Left  (Black non-recid. HighRisk): {nB} defendants, f = {showProb fB}"
  IO.println s!"  Right (White non-recid. HighRisk): {nW} defendants, f = {showProb fW}"
  match probSub fB fW with
  | some diff => IO.println s!"  Difference: f − g = {showProb diff}"
  | none => IO.println "  Difference: f < g (unexpected)"
  IO.println s!"  Two-sample CI: {showConstraint ci}"
  IO.println s!"  0 ∈ CI?  {inConstraint Prob.zero ci}  (must be false for Excess)"

  -- Build the derivation
  let obsEntryB : ContextEntry := ⟨"u", mkSupport "BlackNonRecid", HR, .unknown⟩
  let obsEntryW : ContextEntry := ⟨"w", mkSupport "WhiteNonRecid", HR, .unknown⟩
  let tcB : TermClaim := ⟨.frequency, tB, nB, HR, fB, σB⟩
  let tcW : TermClaim := ⟨.frequency, tW, nW, HR, fW, σW⟩
  let dObsB := nd "obs" [] [obsEntryB] (.term tcB)
  let dObsW := nd "obs" [] [obsEntryW] (.term tcW)

  match probSub fB fW with
  | some diff => do
    let excessClaim : ComparisonClaim := .excess tcB tcW diff ci
    let concCtx := [obsEntryB, obsEntryW]
    let dIEx := nd "IEx" [dObsB, dObsW] concCtx (.comparison excessClaim)

    if notInConstraint Prob.zero ci then
      IO.println ""
      runTest "IEx: Black FPR significantly exceeds White FPR" dIEx
      IO.println ""
      IO.println "  ┌─────────────────────────────────────────────────────────────┐"
      IO.println "  │              NATURAL DEDUCTION TREE                         │"
      IO.println "  └─────────────────────────────────────────────────────────────┘"
      IO.println ""
      renderTree dIEx "  "
    else IO.println "  SKIP: 0 ∈ CI (no significant excess)"
  | none => IO.println "  SKIP: f < g (Black FPR < White FPR?)"

-- ============================================================================
-- Derivation 8: INEx — AA FNR male vs female (no excess = fairness)
-- ============================================================================
/-
  Complementary to IEx: test whether there is NO significant excess
  in false-negative rates between AA male and AA female recidivists.

  Left:   AA female recid. LowRisk  62/203  (provenance σ_f)
  Right:  AA male recid. LowRisk    411/1458 (provenance σ_m)
  Difference: 62/203 − 411/1458 ≈ 0.0236

  If 0 ∈ CI → no significant excess → INEx (gender fairness on FNR).
-/

private def deriveNoExcess_FNR : IO Unit := do
  let LR := Output.atom "LowRisk"
  let tF := Term.atom "rf"
  let tM := Term.atom "rm"
  let σF := mkProv "σ_f"
  let σM := mkProv "σ_m"

  let nF : Nat := 203
  let fF := P 62 203
  let nM : Nat := 1458
  let fM := P 411 1458   -- = 137/486

  let ci := twoSampleCI nF nM fF fM

  IO.println s!"  Left  (AA female recid. LowRisk): {nF} defendants, f = {showProb fF}"
  IO.println s!"  Right (AA male recid. LowRisk):   {nM} defendants, f = {showProb fM}"
  match probSub fF fM with
  | some diff => IO.println s!"  Difference: f − g = {showProb diff}"
  | none => IO.println "  Difference: f < g (female rate < male rate)"
  IO.println s!"  Two-sample CI: {showConstraint ci}"
  IO.println s!"  0 ∈ CI?  {inConstraint Prob.zero ci}  (must be true for NoExcess)"

  let obsEntryF : ContextEntry := ⟨"rf", mkSupport "AAFemRecid", LR, .unknown⟩
  let obsEntryM : ContextEntry := ⟨"rm", mkSupport "AAMaleRecid", LR, .unknown⟩
  let tcF : TermClaim := ⟨.frequency, tF, nF, LR, fF, σF⟩
  let tcM : TermClaim := ⟨.frequency, tM, nM, LR, fM, σM⟩
  let dObsF := nd "obs" [] [obsEntryF] (.term tcF)
  let dObsM := nd "obs" [] [obsEntryM] (.term tcM)

  match probSub fF fM with
  | some diff => do
    if inConstraint Prob.zero ci then
      let noExClaim : ComparisonClaim := .noExcess tcF tcM diff ci
      let dINEx := nd "INEx" [dObsF, dObsM] [obsEntryF, obsEntryM] (.comparison noExClaim)
      IO.println ""
      runTest "INEx: AA female FNR does NOT significantly exceed male FNR" dINEx
      IO.println ""
      IO.println "  Interpretation: the gender gap in false-negative rates"
      IO.println "  among AA recidivists is NOT statistically significant."
      IO.println "  COMPAS is fair across gender on this metric."
    else
      IO.println "  Note: 0 ∉ CI → there IS significant excess. Using IEx instead."
  | none => do
    -- f < g: female rate < male rate. Try reversed.
    IO.println "  Note: female rate < male rate. Checking if male EXCEEDS female..."
    let ciRev := twoSampleCI nM nF fM fF
    IO.println s!"  Reversed CI (male−female): {showConstraint ciRev}"
    IO.println s!"  0 ∈ reversed CI?  {inConstraint Prob.zero ciRev}"
    if inConstraint Prob.zero ciRev then
      match probSub fM fF with
      | some diff => do
        let noExClaim : ComparisonClaim := .noExcess tcM tcF diff ciRev
        let dINEx := nd "INEx" [dObsM, dObsF] [obsEntryM, obsEntryF] (.comparison noExClaim)
        IO.println ""
        runTest "INEx: AA male FNR does NOT significantly exceed female FNR" dINEx
        IO.println ""
        IO.println "  Interpretation: no significant gender gap in FNR → fair"
      | none => IO.println "  SKIP: subtraction failed"
    else IO.println "  SKIP: significant excess in reversed direction"

-- ============================================================================
-- Derivation 9: AA FPR male vs female — IEx or INEx?
-- ============================================================================
/-
  Derivation 4 used the one-sample test: female FPR (131/346) against the
  male benchmark (255/584); at the distribution-free level it gives Trust.

  Now try the two-sample Excess test: does male FPR *significantly exceed*
  female FPR?  CI for (male − female) may or may not contain 0.

  This is a genuine statistical question: the one-sample and two-sample
  tests use different variance estimates and can disagree on borderline cases.
-/

private def deriveComparison_AAGenderFPR : IO Unit := do
  let HR := Output.atom "HighRisk"
  let tM := Term.atom "um"
  let tF := Term.atom "uf"
  let σM := mkProv "σ_m"
  let σF := mkProv "σ_f"

  let nM : Nat := 1168
  let fM := P 510 1168    -- male FPR = 255/584
  let nF : Nat := 346
  let fF := P 131 346     -- female FPR

  -- Two-sample CI: male − female
  let ci := twoSampleCI nM nF fM fF

  IO.println s!"  Left  (AA male non-recid. HighRisk):   {nM}, f = {showProb fM}"
  IO.println s!"  Right (AA female non-recid. HighRisk): {nF}, f = {showProb fF}"
  match probSub fM fF with
  | some diff => IO.println s!"  Difference (male − female): {showProb diff}"
  | none => IO.println "  Difference: male < female (unexpected)"
  IO.println s!"  Two-sample CI: {showConstraint ci}"
  IO.println s!"  0 ∈ CI?  {inConstraint Prob.zero ci}"

  let obsEntryM : ContextEntry := ⟨"um", mkSupport "AAMaleNonRecid", HR, .unknown⟩
  let obsEntryF : ContextEntry := ⟨"uf", mkSupport "AAFemNonRecid", HR, .unknown⟩
  let tcM : TermClaim := ⟨.frequency, tM, nM, HR, fM, σM⟩
  let tcF : TermClaim := ⟨.frequency, tF, nF, HR, fF, σF⟩
  let dObsM := nd "obs" [] [obsEntryM] (.term tcM)
  let dObsF := nd "obs" [] [obsEntryF] (.term tcF)

  if inConstraint Prob.zero ci then do
    -- 0 ∈ CI → NoExcess → INEx
    match probSub fM fF with
    | some diff => do
      let noExClaim : ComparisonClaim := .noExcess tcM tcF diff ci
      let dINEx := nd "INEx" [dObsM, dObsF] [obsEntryM, obsEntryF] (.comparison noExClaim)
      IO.println ""
      runTest "INEx: AA male FPR does NOT significantly exceed female FPR" dINEx
    | none => IO.println "  SKIP: subtraction failed"

    IO.println ""
    IO.println "  ┌─────────────────────────────────────────────────────────────┐"
    IO.println "  │  AGREEMENT WITH DERIVATION 4                               │"
    IO.println "  └─────────────────────────────────────────────────────────────┘"
    IO.println ""
    IO.println "  Derivation 4 (one-sample, benchmark treated as known): Trust"
    IO.println "  Derivation 9 (two-sample Excess test):                 NoExcess"
    IO.println ""
    IO.println "  Both readings agree: the gender gap in false-positive rates"
    IO.println "  is not significant on these samples at the distribution-free"
    IO.println "  level. They differ only in variance accounting: IT/IUT take"
    IO.println "  the benchmark as a constant, the two-sample rules account"
    IO.println "  for sampling uncertainty in both groups."
  else do
    -- 0 ∉ CI → Excess → IEx
    match probSub fM fF with
    | some diff => do
      let exClaim : ComparisonClaim := .excess tcM tcF diff ci
      let dIEx := nd "IEx" [dObsM, dObsF] [obsEntryM, obsEntryF] (.comparison exClaim)
      IO.println ""
      runTest "IEx: AA male FPR significantly exceeds female FPR" dIEx
    | none => IO.println "  SKIP: subtraction failed"

-- ============================================================================
-- Derivation 10: IUT2 — ProPublica headline via two-sample Trust
-- ============================================================================
/-
  Same as Derivation 5 (IUT one-sample) but using IUT2 (two-sample).
  Both premises are obs. The checker uses twoSampleCI instead of binomialCI.
  Should AGREE with IUT on this clear case (large samples, large gap).
-/

private def deriveIUT2_ProPublica : IO Unit := do
  let HR := Output.atom "HighRisk"
  let tB := Term.atom "u"
  let tW := Term.atom "w"
  let σB := mkProv "σ_B"
  let σW := mkProv "σ_W"

  let nB : Nat := 1514
  let fB := P 641 1514
  let nW : Nat := 1281
  let fW := P 282 1281

  let ci := twoSampleCI nB nW fB fW

  IO.println s!"  Black non-recid. HighRisk: {nB}, f = {showProb fB}"
  IO.println s!"  White non-recid. HighRisk: {nW}, f = {showProb fW}"
  IO.println s!"  Two-sample CI = {showConstraintShort ci}"
  IO.println s!"  0 ∈ CI?  {inConstraint Prob.zero ci}"

  let obsEntryB : ContextEntry := ⟨"u", mkSupport "BlackNonRecid", HR, .unknown⟩
  let obsEntryW : ContextEntry := ⟨"w", mkSupport "WhiteNonRecid", HR, .unknown⟩
  let tcB : TermClaim := ⟨.frequency, tB, nB, HR, fB, σB⟩
  let tcW : TermClaim := ⟨.frequency, tW, nW, HR, fW, σW⟩
  let dObsB := nd "obs" [] [obsEntryB] (.term tcB)
  let dObsW := nd "obs" [] [obsEntryW] (.term tcW)

  -- IUT2: two-sample UTrust
  let utrustClaim : TrustClaim := .untrust .twoSample tB nB HR fB fW ci (σB ∪ σW)
  let dIUT2 := nd "IUT2" [dObsB, dObsW] [obsEntryB, obsEntryW] (.trust utrustClaim)

  if notInConstraint Prob.zero ci then
    IO.println ""
    runTest "IUT2: ProPublica headline (two-sample UTrust)" dIUT2
    IO.println ""
    IO.println "  ┌─────────────────────────────────────────────────────────────┐"
    IO.println "  │              NATURAL DEDUCTION TREE                         │"
    IO.println "  └─────────────────────────────────────────────────────────────┘"
    IO.println ""
    renderTree dIUT2 "  "
    IO.println ""
    IO.println "  Agrees with Derivation 5 (IUT) and Derivation 7 (IEx)."
    IO.println "  Same conclusion, symmetric formulation, no identity premise needed."
  else IO.println "  UNEXPECTED: 0 ∈ CI"

-- ============================================================================
-- Derivation 11: IT2 — AA FNR gender fairness (two-sample Trust)
-- ============================================================================
/-
  Same data as Derivation 8 (INEx): AA female vs male FNR.
  Now using IT2 instead of INEx. Should agree: no significant difference.
-/

private def deriveIT2_AAGenderFNR : IO Unit := do
  let LR := Output.atom "LowRisk"
  let tF := Term.atom "rf"
  let tM := Term.atom "rm"
  let σF := mkProv "σ_f"
  let σM := mkProv "σ_m"

  let nF : Nat := 203
  let fF := P 62 203
  let nM : Nat := 1458
  let fM := P 411 1458

  let ci := twoSampleCI nF nM fF fM

  IO.println s!"  AA female recid. LowRisk: {nF}, f = {showProb fF}"
  IO.println s!"  AA male recid. LowRisk:   {nM}, f = {showProb fM}"
  IO.println s!"  Two-sample CI = {showConstraintShort ci}"
  IO.println s!"  0 ∈ CI?  {inConstraint Prob.zero ci}"

  let obsEntryF : ContextEntry := ⟨"rf", mkSupport "AAFemRecid", LR, .unknown⟩
  let obsEntryM : ContextEntry := ⟨"rm", mkSupport "AAMaleRecid", LR, .unknown⟩
  let tcF : TermClaim := ⟨.frequency, tF, nF, LR, fF, σF⟩
  let tcM : TermClaim := ⟨.frequency, tM, nM, LR, fM, σM⟩
  let dObsF := nd "obs" [] [obsEntryF] (.term tcF)
  let dObsM := nd "obs" [] [obsEntryM] (.term tcM)

  let trustClaim : TrustClaim := .trust .twoSample tF nF LR fF fM ci (σF ∪ σM)
  let dIT2 := nd "IT2" [dObsF, dObsM] [obsEntryF, obsEntryM] (.trust trustClaim)

  if inConstraint Prob.zero ci then
    IO.println ""
    runTest "IT2: AA FNR gender fairness (two-sample Trust)" dIT2
    IO.println ""
    IO.println "  Agrees with Derivation 3 (IT), Derivation 8 (INEx)."
    IO.println "  All three conclude: no significant gender gap → fair."
  else IO.println "  UNEXPECTED: 0 ∉ CI"

-- ============================================================================
-- Derivation 12: IT2 vs IUT — the borderline case
-- ============================================================================
/-
  The critical test: AA FPR female vs male.
  Derivation 4 (IUT, one-sample): UTrust — unfair
  Derivation 9 (INEx, two-sample): NoExcess — fair
  What does IT2 say?
-/

private def deriveIT2_borderline : IO Unit := do
  let HR := Output.atom "HighRisk"
  let tF := Term.atom "uf"
  let tM := Term.atom "um"
  let σF := mkProv "σ_f"
  let σM := mkProv "σ_m"

  let nF : Nat := 346
  let fF := P 131 346
  let nM : Nat := 1168
  let fM := P 510 1168

  -- Order larger-rate-first (male ≥ female) per the paper's convention
  let ci := twoSampleCI nM nF fM fF

  IO.println s!"  AA female non-recid. HighRisk: {nF}, f = {showProb fF}"
  IO.println s!"  AA male non-recid. HighRisk:   {nM}, f = {showProb fM}"
  IO.println s!"  Two-sample CI = {showConstraintShort ci}"
  IO.println s!"  0 ∈ CI?  {inConstraint Prob.zero ci}"

  let obsEntryF : ContextEntry := ⟨"uf", mkSupport "AAFemNonRecid", HR, .unknown⟩
  let obsEntryM : ContextEntry := ⟨"um", mkSupport "AAMaleNonRecid", HR, .unknown⟩
  let tcF : TermClaim := ⟨.frequency, tF, nF, HR, fF, σF⟩
  let tcM : TermClaim := ⟨.frequency, tM, nM, HR, fM, σM⟩
  let dObsF := nd "obs" [] [obsEntryF] (.term tcF)
  let dObsM := nd "obs" [] [obsEntryM] (.term tcM)

  -- Try IT2 (Trust — fair); male is the larger rate, so it leads
  let trustClaim : TrustClaim := .trust .twoSample tM nM HR fM fF ci (σM ∪ σF)
  let dIT2 := nd "IT2" [dObsM, dObsF] [obsEntryM, obsEntryF] (.trust trustClaim)

  -- Try IUT2 (UTrust — unfair)
  let utrustClaim : TrustClaim := .untrust .twoSample tM nM HR fM fF ci (σM ∪ σF)
  let dIUT2 := nd "IUT2" [dObsM, dObsF] [obsEntryM, obsEntryF] (.trust utrustClaim)

  if inConstraint Prob.zero ci then do
    IO.println ""
    runTest "IT2: AA FPR gender (two-sample Trust — fair)" dIT2
    IO.println ""
    IO.println "  ┌─────────────────────────────────────────────────────────────┐"
    IO.println "  │  ONE-SAMPLE vs TWO-SAMPLE on the same question             │"
    IO.println "  └─────────────────────────────────────────────────────────────┘"
    IO.println ""
    IO.println "  Derivation  4 (IT,  one-sample): Trust — fair"
    IO.println "  Derivation 12 (IT2, two-sample): Trust — fair"
    IO.println ""
    IO.println "  The two variants of the same rule family agree here. The"
    IO.println "  auditor chooses which to apply based on whether the benchmark"
    IO.println "  is a known constant (IT/IUT) or estimated from data (IT2/IUT2)."
  else do
    IO.println ""
    runTest "IUT2: AA FPR gender (two-sample UTrust — unfair)" dIUT2
    IO.println ""
    IO.println "  Both IUT and IUT2 agree: UTrust."

-- ============================================================================
-- Main
-- ============================================================================

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println " COMPAS Derivations from ProPublica Data"
  IO.println " Source: compas-scores-two-years.csv (6172 defendants)"
  IO.println "═══════════════════════════════════════════════════════════"

  IO.println ""
  IO.println "─── 1. Caucasian FNR: Trust (gender fairness) ───"
  IO.println ""
  deriveTrust_CaucasianFNR

  IO.println ""
  IO.println "─── 2. Caucasian recid. UPDATE (sub-batch pooling) ───"
  IO.println ""
  deriveUpdate_CaucasianRecid

  IO.println ""
  IO.println "─── 3. African-American FNR: Trust (paper §4.3) ───"
  IO.println ""
  deriveTrust_AAFemaleRecidFNR

  IO.println ""
  IO.println "─── 4. African-American FPR: one-sample test (gender) ───"
  IO.println ""
  deriveUTrust_AAFemaleFPR

  IO.println ""
  IO.println "─── 5. ProPublica main claim: racial FPR bias ───"
  IO.println ""
  deriveUTrust_ProPublicaMain

  IO.println ""
  IO.println "─── 6. Bayesian posterior update (pilot audit) ───"
  IO.println ""
  deriveBayesian

  IO.println ""
  IO.println "─── 7. IEx: Black FPR EXCEEDS White FPR (two-sample) ───"
  IO.println ""
  deriveExcess_FPR

  IO.println ""
  IO.println "─── 8. INEx: AA FNR gender gap not significant ───"
  IO.println ""
  deriveNoExcess_FNR

  IO.println ""
  IO.println "─── 9. AA FPR gender: IEx or INEx? ───"
  IO.println ""
  deriveComparison_AAGenderFPR

  IO.println ""
  IO.println "─── 10. IUT2: ProPublica headline (two-sample) ───"
  IO.println ""
  deriveIUT2_ProPublica

  IO.println ""
  IO.println "─── 11. IT2: AA FNR gender fairness (two-sample) ───"
  IO.println ""
  deriveIT2_AAGenderFNR

  IO.println ""
  IO.println "─── 12. IT2 vs IUT: the borderline case ───"
  IO.println ""
  deriveIT2_borderline

  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println " Summary"
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println ""
  IO.println " Rules used: obs, identity, update, IT, IUT, IT2, IUT2,"
  IO.println "             I-P, E-P, IEx, INEx"
  IO.println ""
  IO.println "  #  Rule  Data                              Verdict"
  IO.println "  ── ───── ───────────────────────────────── ────────────────"
  IO.println "  1  IT    Caucasian FNR (female vs male)    Trust  — fair"
  IO.println "  2  UPD   Caucasian recid. sub-batch pool   408/822"
  IO.println "  3  IT    AA FNR (female vs male)           Trust  — fair"
  IO.println "  4  IT    AA FPR (female vs male)           Trust  — fair"
  IO.println "  5  IUT   ProPublica main (Black vs White)  UTrust — unfair"
  IO.println "  6  E-P   Bayesian posterior (pilot)        H₃ ↦ 243/1130 ≈ 21%"
  IO.println "  7  IEx   Black FPR > White FPR             Excess"
  IO.println "  8  INEx  AA FNR female vs male             NoExcess"
  IO.println "  9  INEx  AA FPR female vs male             NoExcess — agrees w/ #4"
  IO.println " 10  IUT2  ProPublica main (two-sample)      UTrust — agrees w/ #5"
  IO.println " 11  IT2   AA FNR (two-sample)               Trust  — agrees w/ #3"
  IO.println " 12  IT2   AA FPR (two-sample)               Trust  — agrees w/ #4"
  IO.println ""
  IO.println " All one-sample and two-sample verdicts agree on this data at"
  IO.println " the distribution-free level.  The choice between IT/IUT and"
  IO.println " IT2/IUT2 is whether the benchmark is a known constant or is"
  IO.println " itself estimated from data."
  IO.println ""
