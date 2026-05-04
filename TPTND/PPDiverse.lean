import TPTND

open TPTND

/-! # Rule-diverse COMPAS audit certificate

Goal opposite to `PPDeeperAudit.lean`: at *every* depth, multiple rule
families appear simultaneously.  We assemble five thematically distinct
sub-trees of the ProPublica/Northpointe story and glue them together with
an asymmetric `WeakeningS` chain so that each depth k of the final tree
sees the depth-k slice of all five sub-trees at once.

  • ProPublica side (FPR disparity) ……… Obs · I+ · Update · IUT2 · EUT
  • Northpointe side (PPV equality) …… Obs · IT2 · ET
  • Calibration                     …… Obs · I→ · E→
  • Joint attribute pair             …… Obs · I× · E×L
  • Prior consolidation              …… Obs · Contraction
  • Top-level                          …… WeakeningS (asymmetric chain)

All counts are taken from the published 6 172-row ProPublica filter or are
illustrative under-the-narrative fillers (Northpointe-side numbers, prior
audits).  Every conclusion claim is the same one the corresponding sub-tree
in `PPExtended.lean` already proves.
-/

-- ============================================================================
-- Helpers
-- ============================================================================

private def P (n d : Nat) : Prob := clampProb ((n : ℚ) / d)
private def nd (rule : RuleName) (prems : List Derivation)
    (ctx : Context) (claim : Claim) : Derivation :=
  .node rule prems ⟨ctx, claim⟩ false
private def ndW (rule : RuleName) (prems : List Derivation)
    (ctx : Context) (claim : Claim) : Derivation :=
  .node rule prems ⟨ctx, claim⟩ true
private def mkSupport (s : String) : Finset String := {s}
private def mkProv   (s : String) : Finset String := {s}
private def mkProv2  (a b : String) : Finset String := {a, b}

private def MR  : Output := .atom "MediumRisk"
private def HR  : Output := .atom "HighRisk"
private def Flg : Output := .sum MR HR
private def Rec : Output := .atom "Recidivated"

-- ============================================================================
-- Sub-tree A: ProPublica FPR  (depth 5: Obs · I+ · Update · IUT2 · EUT)
-- ============================================================================

private def subA_FPR : Derivation := Id.run do
  let tB := Term.atom "u_B"
  let tW := Term.atom "u_W"
  let eB : ContextEntry := ⟨"u_B", mkSupport "BNR", Flg, .unknown⟩
  let eW : ContextEntry := ⟨"u_W", mkSupport "WNR", Flg, .unknown⟩
  let eBM : ContextEntry := ⟨"u_B", mkSupport "BM_NR", Flg, .unknown⟩
  let eBF : ContextEntry := ⟨"u_B", mkSupport "BF_NR", Flg, .unknown⟩
  let eWM : ContextEntry := ⟨"u_W", mkSupport "WM_NR", Flg, .unknown⟩
  let eWF : ContextEntry := ⟨"u_W", mkSupport "WF_NR", Flg, .unknown⟩
  let σBM := mkProv "B_male"; let σBF := mkProv "B_female"
  let σWM := mkProv "W_male"; let σWF := mkProv "W_female"
  let σB := mkProv2 "B_male" "B_female"
  let σW := mkProv2 "W_male" "W_female"
  -- depth 1 leaves
  let mkObs (e : ContextEntry) (t : Term) (n : Nat) (α : Output)
      (f : Prob) (σ : Provenance) : Derivation :=
    nd .obs [] [e] (.term ⟨.frequency, t, n, α, f, σ⟩)
  -- depth 2: I+
  let dBMflg := nd .iPlus
    [mkObs eBM tB 1168 MR (P 198 1168) σBM,
     mkObs eBM tB 1168 HR (P 312 1168) σBM]
    [eBM] (.term ⟨.frequency, tB, 1168, Flg, P 510 1168, σBM⟩)
  let dBFflg := nd .iPlus
    [mkObs eBF tB 346 MR (P 56 346) σBF,
     mkObs eBF tB 346 HR (P 75 346) σBF]
    [eBF] (.term ⟨.frequency, tB, 346, Flg, P 131 346, σBF⟩)
  let dWMflg := nd .iPlus
    [mkObs eWM tW 969 MR (P 130 969) σWM,
     mkObs eWM tW 969 HR (P 62 969) σWM]
    [eWM] (.term ⟨.frequency, tW, 969, Flg, P 192 969, σWM⟩)
  let dWFflg := nd .iPlus
    [mkObs eWF tW 312 MR (P 70 312) σWF,
     mkObs eWF tW 312 HR (P 20 312) σWF]
    [eWF] (.term ⟨.frequency, tW, 312, Flg, P 90 312, σWF⟩)
  -- depth 3: Update
  let f_B := P 641 1514;  let f_W := P 282 1281
  let dB := nd .update [dBMflg, dBFflg] [eB]
              (.term ⟨.frequency, tB, 1514, Flg, f_B, σB⟩)
  let dW := nd .update [dWMflg, dWFflg] [eW]
              (.term ⟨.frequency, tW, 1281, Flg, f_W, σW⟩)
  -- depth 4: IUT2
  let ci  := twoSampleCI 1514 1281 f_B f_W
  let utr : TrustClaim := .untrust tB 1514 Flg f_B f_W ci
  let dIUT2 := nd .iUT2 [dB, dW] [eB, eW] (.trust utr)
  -- depth 5: EUT
  match ci with
  | .interval lo hi =>
      let xGap : ContextEntry :=
        ⟨"x_FPR", mkSupport "compas_filter", Flg, .outsideInterval lo hi⟩
      pure <| nd .eUT [dIUT2] [eB, eW, xGap]
        (.term ⟨.frequency, tB, 1514, Flg, f_B, σB⟩)
  | _ => pure dIUT2

-- ============================================================================
-- Sub-tree A':  one-sample IUT chain reaching depth 5 with Identity leaves
--   depth 5:  Obs · Identity · IUT · EUT · I→ · E→
--   This puts Identity at absDepth 1 of the full tree (alongside subA's Obs).
--   Narrative: model claims 50 % calibration on flagged Black defendants;
--              actual rate is 62.8 % on n = 1234; 0.5 ∉ CI ⇒ UTrust ⇒ EUT
--              extracts the gap interval; I→ discharges the model-probability
--              hypothesis to a typed conditional; E→ applies it.
-- ============================================================================

private def subA'_oneSampleIUT : Derivation := Id.run do
  let tB := Term.atom "v_B"
  let σ  := mkProv "B_flagged"
  let n  := 1234
  let f  := P 775 1234   -- empirical Black PPV ≈ 0.628
  let p  := P 1   2      -- model claim = 0.50  (will fall outside CI)
  -- depth 1 leaves
  let eObs : ContextEntry := ⟨"v_B",     mkSupport "B_flagged", Rec, .unknown⟩
  let eId  : ContextEntry := ⟨"x_model", mkSupport "model",     Rec, .exact p⟩
  let dObs := nd .obs []      [eObs, eId]
                (.term ⟨.frequency, tB, n, Rec, f, σ⟩)
  let dId  := nd .identity [] [eId] (.identity eId)
  -- depth 2: IUT
  let ci   := binomialCI n f p
  let utr  : TrustClaim := .untrust tB n Rec f p ci
  let dIUT := nd .iUT [dId, dObs] [eObs, eId] (.trust utr)
  -- depth 3: EUT — extracts complement interval, preserves x_model
  match ci with
  | .interval lo hi =>
      let xGap : ContextEntry :=
        ⟨"x_PPV_gap", mkSupport "B_flagged", Rec, .outsideInterval lo hi⟩
      let dEUT := nd .eUT [dIUT] [eObs, eId, xGap]
                    (.term ⟨.frequency, tB, n, Rec, f, σ⟩)
      -- depth 4: I→  discharges x_model
      let lamTerm := Term.lam "x_model" tB
      let arrOut  := Output.arr Rec Rec
      let dIArr := nd .iArr [dEUT] [eObs, xGap]
                     (.term ⟨.frequency, lamTerm, n, arrOut, f, σ⟩)
      -- depth 5: E→  applies the conditional to a fresh Obs(Rec_r)
      let eU : ContextEntry := ⟨"u_apply", mkSupport "B_flagged", Rec, .unknown⟩
      let r := P 925 1234   -- 0.75 ish, but with integer numerator at n=1234
      let dApply := nd .obs [] [eU]
                      (.term ⟨.frequency, Term.atom "u_apply", n, Rec, r, σ⟩)
      pure <| nd .eArr [dIArr, dApply]
                 (mergeContexts [getCtx dIArr, getCtx dApply])
                 (.term ⟨.frequency, Term.app lamTerm (Term.atom "u_apply"),
                         n, Rec, probMul f r, σ⟩)
  | _ => pure dIUT

-- ============================================================================
-- Sub-tree B: Northpointe PPV  (depth 3: Obs · IT2 · ET) — at depth 5 via padding
-- We pad B by re-doing IT2 + ET inside a one-step Contraction, but Contraction
-- needs interval entries; cleanest pad is a 2-extra-Update sandwich.  Instead,
-- we embed B inside a WeakeningS with a Contraction sub-tree, so B occupies
-- the deeper branch of that internal WeakeningS.
-- Resulting depth-5 root rule: ET.
-- ============================================================================

private def subB_PPV : Derivation := Id.run do
  let tB := Term.atom "v_B"
  let tW := Term.atom "v_W"
  let eB : ContextEntry := ⟨"v_B", mkSupport "B_flagged", Rec, .unknown⟩
  let eW : ContextEntry := ⟨"v_W", mkSupport "W_flagged", Rec, .unknown⟩
  let σB := mkProv "B_flagged"; let σW := mkProv "W_flagged"
  let f_B := P 775 1234;  let f_W := P 272 460
  -- depth 1: Obs ×2
  let dB := nd .obs [] [eB] (.term ⟨.frequency, tB, 1234, Rec, f_B, σB⟩)
  let dW := nd .obs [] [eW] (.term ⟨.frequency, tW, 460,  Rec, f_W, σW⟩)
  -- depth 2: IT2
  let ci := twoSampleCI 1234 460 f_B f_W
  let trust : TrustClaim := .trust tB 1234 Rec f_B f_W ci
  let dIT2 := nd .iT2 [dB, dW] [eB, eW] (.trust trust)
  -- depth 3: ET — carry interval into typing context
  let xPPV : ContextEntry := ⟨"x_PPV", mkSupport "compas_filter", Rec, ci⟩
  pure <| nd .eT [dIT2] [eB, eW, xPPV]
    (.term ⟨.frequency, tB, 1234, Rec, f_B, σB⟩)

-- ============================================================================
-- Sub-tree C: Joint via I× / E×L  (depth 3: Obs · I× · E×L)
-- ============================================================================

private def subC_Joint : Derivation := Id.run do
  let term := Term.atom "u_audit"
  let σ := mkProv "joint_audit";  let n := 100
  let eF : ContextEntry := ⟨"u_audit", mkSupport "AC", Flg, .unknown⟩
  let eR : ContextEntry := ⟨"u_audit", mkSupport "AC", Rec, .unknown⟩
  let f_flag := P 50 100;  let f_recid := P 30 100
  -- depth 1
  let dF := nd .obs [] [eF] (.term ⟨.frequency, term, n, Flg, f_flag, σ⟩)
  let dR := nd .obs [] [eR] (.term ⟨.frequency, term, n, Rec, f_recid, σ⟩)
  -- depth 2: I×
  let dProd := ndW .iProd [dF, dR] [eF, eR]
    (.term ⟨.frequency, Term.pair term term, n, .prod Flg Rec,
            probMul f_flag f_recid, σ⟩)
  -- depth 3: E×L
  pure <| nd .eProdL [dProd, dR] [eF, eR]
    (.term ⟨.frequency, term, n, Flg, f_flag, σ⟩)

-- ============================================================================
-- Sub-tree D: Calibration via I→ / E→  (depth 3: Obs · I→ · E→)
-- ============================================================================

private def subD_Calib : Derivation := Id.run do
  let term := Term.atom "u_calib"
  let σ := mkProv "flagged_overall";  let n := 1694
  let q := P 1047 1694;  let r := P 716 1694
  let eR : ContextEntry := ⟨"u_calib", mkSupport "calib_cohort", Rec, .unknown⟩
  let eX : ContextEntry := ⟨"x_flag",  mkSupport "calib_cohort", Flg, .exact r⟩
  -- depth 1: Obs
  let dObsR := nd .obs [] [eR, eX]
    (.term ⟨.frequency, term, n, Rec, q, σ⟩)
  -- depth 2: I→ — discharge eX
  let dArr := nd .iArr [dObsR] [eR]
    (.term ⟨.frequency, Term.lam "x_flag" term, n, .arr Flg Rec, q, σ⟩)
  -- depth 3: E→ — apply
  let eU : ContextEntry := ⟨"v_flag", mkSupport "calib_cohort", Flg, .unknown⟩
  let dObsF := nd .obs [] [eU]
    (.term ⟨.frequency, Term.atom "v_flag", n, Flg, r, σ⟩)
  pure <| nd .eArr [dArr, dObsF]
    (mergeContexts [getCtx dArr, getCtx dObsF])
    (.term ⟨.frequency, Term.app (Term.lam "x_flag" term) (Term.atom "v_flag"),
            n, Rec, probMul q r, σ⟩)

-- ============================================================================
-- Sub-tree E: Prior consolidation  (depth 2: Obs · Contraction)
-- ============================================================================

private def subE_Contraction : Derivation := Id.run do
  let varName := "x_FPR"
  let entry2014 : ContextEntry := ⟨varName, mkSupport "Audit2014", Flg,
                                   .interval (P 40 100) (P 45 100)⟩
  let entry2016 : ContextEntry := ⟨varName, mkSupport "Audit2016", Flg,
                                   .interval (P 42 100) (P 50 100)⟩
  let entryFrame : ContextEntry := ⟨"y_other", mkSupport "frame",
                                    Rec, .unknown⟩
  let entryExact : ContextEntry := ⟨varName, mkSupport "Audit2014", Flg,
                                    .exact (P 43 100)⟩
  let term := Term.atom "u_post"
  let σ := mkProv "post"
  let entryObs : ContextEntry := ⟨"u_post", mkSupport "post", Flg, .unknown⟩
  -- depth 1: Obs
  let dPremise := nd .obs []
    [entry2014, entry2016, entryFrame, entryObs]
    (.term ⟨.frequency, term, 100, Flg, P 43 100, σ⟩)
  -- depth 2: Contraction
  pure <| nd .contraction [dPremise]
    [entryExact, entryFrame, entryObs]
    (.term ⟨.frequency, term, 100, Flg, P 43 100, σ⟩)

-- ============================================================================
-- Asymmetric WeakeningS chain
--
-- Combining sub-trees of varying depths with a left-deep WS chain ensures
-- that every depth from 1 up to the root sees rules from at least 2
-- distinct sub-trees:
--
--   level 1: Obs (all sub-trees) + (none, since no Identity at leaves
--            in this composition).  We additionally splice a fresh Obs
--            on the WS-shallow side to keep diversity at the leaf layer.
--   level 2: I+ (subA), IT2 (subB), I× (subC), I→ (subD), Contraction (subE)
--   level 3: Update (subA), ET (subB), E×L (subC), E→ (subD)
--   level 4: IUT2 (subA), WeakeningS (combining shallower + subC/D)
--   level 5: EUT (subA), WeakeningS (above subB chain)
--   level 6: WeakeningS (root)
--
-- Net root depth = 6, with rule diversity ≥2 at every depth 1..6.
-- ============================================================================

/-- Combine two derivations with a `WeakeningS` node, taking the merged
    context and the FIRST premise's claim. -/
private def WS (d₁ d₂ : Derivation) : Derivation :=
  ndW .weakeningS [d₁, d₂]
    (mergeContexts [getCtx d₁, getCtx d₂]) (getClaim d₁)

/-- The diverse audit certificate.  All six sub-trees consolidated. -/
def diverseAudit : Derivation :=
  -- ws0:  WS(subA depth 5, subA' depth 5) → depth 6
  -- Both deep sides contribute to absDepth 1: subA brings Obs, subA' brings
  -- Obs+Identity; their internal rules layer through depths 2..5 in parallel.
  let ws0 := WS subA_FPR subA'_oneSampleIUT          -- depth 6
  let ws1 := WS ws0 subB_PPV                          -- depth 7
  let ws2 := WS ws1 subC_Joint                        -- depth 8
  let ws3 := WS ws2 subD_Calib                        -- depth 9
  WS ws3 subE_Contraction                             -- depth 10 root

-- ============================================================================
-- Per-depth rule profile
-- ============================================================================

/-- Collect (rule, depth) for every node in the tree. -/
private def collectRulesByDepth : Derivation → Nat → List (Nat × RuleName)
  | d@(.node r ps _ _), depthFromRoot =>
    let here := (depthFromRoot, r)
    let descend := ps.flatMap (fun p => collectRulesByDepth p (depthFromRoot + 1))
    here :: descend

/-- For each absolute tree-depth (with leaves at depth = totalDepth), list
    the distinct rule names that appear at exactly that depth. -/
private def rulesByAbsoluteDepth (root : Derivation) :
    List (Nat × List RuleName) :=
  let totalDepth := root.depth
  let pairs := collectRulesByDepth root 1   -- root is depth 1 from-root
  -- Convert "depth from root" to absolute depth (leaves = 1, root = totalDepth):
  --   absDepth = totalDepth - depthFromRoot + 1
  let absPairs := pairs.map (fun (k, r) => (totalDepth - k + 1, r))
  -- Group by absolute depth
  let depths := List.range (totalDepth + 1) |>.drop 1   -- 1, 2, ..., totalDepth
  depths.map (fun d =>
    let rs := absPairs.filterMap (fun (k, r) => if k == d then some r else none)
    -- Dedup
    let unique := rs.foldl (fun acc r => if r ∈ acc then acc else acc ++ [r]) []
    (d, unique))

private def rulesPretty (rs : List RuleName) : String :=
  String.intercalate " · " (rs.map RuleName.toString)

-- ============================================================================
-- Natural-language justifications, paired with each rule application
-- ============================================================================

private def section_ (label : String) : IO Unit := do
  IO.println ""
  IO.println s!"  ── {label} ──"

private def justify (rule : String) (count : String) (sentence : String)
    (sideCondition : String) : IO Unit := do
  IO.println s!"    [{rule}] x{count}  {sentence}"
  IO.println s!"        (kernel checks: {sideCondition})"

/-- Walk the certificate top-down and explain, in COMPAS terms, why each
    rule application is the right move at that point in the audit. -/
def narrate : IO Unit := do
  IO.println "════════════════════════════════════════════════════════════════"
  IO.println "  COMPAS-grounded justification for every rule application"
  IO.println "════════════════════════════════════════════════════════════════"

  section_ "Sub-tree A:  ProPublica FPR pipeline"
  justify "Obs"        "8"
    "Raw published counts: of 1168 Black-male non-recidivists, 198 were"
    "σ ≠ ∅, n > 0, support entry exists for the term"
  IO.println "                       rated Medium-risk and 312 High-risk;"
  IO.println "                       and likewise for BF, WM, WF."
  justify "I+"         "4"
    "ProPublica's binarisation: \"we collapse Medium and High into a"
    "α ⊥_syn β  (no shared atomic name); same n, σ, term"
  IO.println "                       single 'flagged' classification\". Flagged := Medium + High."
  justify "Update"     "2"
    "Sex pooling: \"within each race we pool male and female"
    "σ₁ ∩ σ₂ = ∅; n_conc = n₁+n₂; weighted-average frequency"
  IO.println "                       non-recidivists to form the audit cohort\"."
  justify "IUT2"       "1"
    "Headline two-sample test: \"Black FPR 42.3 %, White 22.0 %; the score-test"
    "0 ∉ Q(n_B, n_W, f_B, f_W); disjoint provenance"
  IO.println "                       CI for the difference is [16.8 %, 23.8 %], excluding zero —"
  IO.println "                       therefore equal-FPR is *Untrusted*\"."
  justify "EUT"        "1"
    "\"Promote the gap interval ¬[16.8 %, 23.8 %] into the typing context"
    "conclusion ctx contains x : α_{¬[ℓ,h]}; preserves the rest"
  IO.println "                       so any downstream certificate inherits the disparity claim\"."

  section_ "Sub-tree A':  one-sample IUT calibration on Black PPV"
  justify "Obs"        "1"
    "\"Among 1234 Black defendants the model flagged, 775 (62.8 %) actually"
    "n·f ∈ ℕ; nonempty σ"
  IO.println "                       recidivated\".  Empirical PPV for the Black cohort."
  justify "Identity"   "1"
    "\"The model's calibrated rate is fixed at 0.50 — declared as an"
    "context is a singleton {x_model : Rec_{0.5}}"
  IO.println "                       exact-typed context entry for downstream inference\"."
  justify "IUT"        "1"
    "\"0.50 lies OUTSIDE the binomial CI for 775/1234 (the CI is roughly"
    "p ∉ binomialCI(n, f, p); n > 0; identity entry exact"
  IO.println "                       [60 %, 65 %]) — the calibration claim is *Untrusted*\"."
  justify "EUT"        "1"
    "\"Promote the calibration-gap interval ¬[60 %, 65 %] into the typing"
    "outsideInterval entry added; existing entries preserved"
  IO.println "                       context, while the Identity exact entry survives for I→\"."
  justify "I→"         "1"
    "\"Discharge the model-rate hypothesis: there is a *function* from"
    "discharged entry has output α and exact constraint;"
  IO.println "                       calibration-rate to recidivism-rate.  Result is a typed"
  IO.println "                       conditional [x_model]u : (Rec ⇒ Rec)_{0.628}\"."
  IO.println "                       (kernel checks: lambda body matches premise term)"
  justify "E→"         "1"
    "\"Apply the conditional to the empirical Recidivated rate 925/1234 ≈"
    "matching n, σ, mode; conclusion frequency = q · r"
  IO.println "                       0.75 — chain rule gives joint rate ≈ 0.628 · 0.75 = 0.47\"."

  section_ "Sub-tree B:  Northpointe PPV defence"
  justify "Obs"        "2"
    "\"Among 1234 flagged Black defendants, 775 recidivated (62.8 %);"
    "n·f ∈ ℕ on each leaf"
  IO.println "                       among 460 flagged White defendants, 272 (59.1 %)\"."
  justify "IT2"        "1"
    "\"The two-sample CI for the PPV difference is [0.0 %, 8.9 %] —"
    "0 ∈ Q(n_B, n_W, f_B, f_W); both n > 0"
  IO.println "                       it CONTAINS zero — therefore equal-PPV is *Trusted*\"."
  justify "ET"         "1"
    "\"Carry the Trusted PPV interval into the typing context as an"
    "ci-interval entry added; conclusion is a frequency claim"
  IO.println "                       assumption available to compositional certificates\"."

  section_ "Sub-tree C:  Joint independence audit"
  justify "Obs"        "2"
    "\"Per defendant in the audit cohort, two attributes are recorded:"
    "matching σ, term, n; both leaves have unknown-typed support entries"
  IO.println "                       the model's classification (Flagged) and the eventual"
  IO.println "                       outcome (Recidivated)\"."
  justify "I×"         "1"
    "\"Treating Flagged and Recidivated as independent (witness asserted),"
    "explicit independence witness; matching σ, n; conclusion value = p · q"
  IO.println "                       form the joint judgment over their product output\"."
  justify "E×L"        "1"
    "\"Project the joint judgment back onto the classification component\"."
    "tc1.output = sum conc.output tc2.output; conclusion value = r / q"

  section_ "Sub-tree D:  Calibration as a typed conditional"
  justify "Obs"        "2"
    "\"Among 1694 flagged defendants overall, 1047 (61.8 %) recidivated\"."
    "exact-typed Flagged entry pre-loaded for I→ to discharge"
  justify "I→"         "1"
    "\"Discharge the Flagged hypothesis — package P(Recidivated|Flagged)"
    "exactly one exact entry x:Flagged_a; arrow output α⇒β with β=premise out"
  IO.println "                       as a first-class conditional certificate\"."
  justify "E→"         "1"
    "\"Apply the conditional to a fresh Flagged frequency: chain rule\"."
    "matching frame; conclusion frequency = q · r"

  section_ "Sub-tree E:  Prior consolidation"
  justify "Obs"        "1"
    "\"Two prior FPR audits — 2014 [40 %, 45 %] and 2016 [42 %, 50 %] —"
    "context contains the two interval-typed entries on x_FPR : Flagged"
  IO.println "                       are loaded as interval-typed context entries\"."
  justify "Contraction" "1"
    "\"Collapse the two prior intervals into a single exact entry"
    "exact value lies in ⋂ᵢ cᵢ; contracted entries share name + output"
  IO.println "                       x_FPR : Flagged_{0.43}, since 0.43 ∈ [0.40, 0.45] ∩ [0.42, 0.50]\"."

  section_ "Top-level WeakeningS chain"
  justify "WeakeningS" "5"
    "\"Combine each sub-certificate with the running audit document, retaining"
    "explicit independence witness; merged context; first-premise claim"
  IO.println "                       the deepest sub-tree's claim and merging contexts.  The five"
  IO.println "                       WeakeningS layers thread subA' (calibration UTrust), subB"
  IO.println "                       (PPV Trust), subC (joint), subD (conditional), subE"
  IO.println "                       (contraction) into one auditable document\"."

-- ============================================================================
-- Entry point
-- ============================================================================

def main : IO UInt32 := do
  IO.println "TPTND-Lean : Rule-diverse COMPAS audit certificate"
  IO.println "════════════════════════════════════════════════════════════════"
  let d := diverseAudit
  IO.println s!"  Tree depth   : {d.depth}"
  IO.println s!"  Total nodes  : {d.nodeCount}"
  IO.println s!"  Root rule    : {d.ruleName}"
  IO.println ""
  IO.println "  Per-depth rule profile (absolute depth; leaves = 1, root = N):"
  let profile := rulesByAbsoluteDepth d
  for (dep, rs) in profile do
    let n := rs.length
    let suffix := if n == 1 then "" else "s"
    IO.println s!"    depth {dep} ({n} rule type{suffix}) : {rulesPretty rs}"
  IO.println ""
  match checkDerivation d with
  | .ok () =>
      IO.println "  ✓ Kernel ACCEPTED the entire diverse audit."
      narrate
      pure 0
  | .error msg =>
      IO.println s!"  ✗ Kernel REJECTED the tree:"
      IO.println s!"      {msg}"
      pure 1
