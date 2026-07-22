import TPTND

open TPTND

/-! # COMPAS Numerical Audit

Reconstruct the three COMPAS derivations from the PDF (§4.1–4.3) and
compare the checker's CI values against the paper's stated values. -/

private def P (n d : Nat) : Prob := clampProb ((n : ℚ) / d)

private def showProb (p : Prob) : String :=
  let q := p.val
  -- Show as fraction and approximate decimal
  let dec := (q.num.toNat * 1000000 / q.den) -- 6 decimal digits
  let intPart := dec / 1000000
  let fracPart := dec % 1000000
  s!"{q.num}/{q.den} ≈ {intPart}.{String.mk (Nat.toDigits 10 (fracPart + 1000000) |>.drop 1)}"

private def showConstraint (c : Constraint) : String :=
  match c with
  | .interval lo hi => s!"[{showProb lo}, {showProb hi}]"
  | .outsideInterval lo hi => s!"¬[{showProb lo}, {showProb hi}]"
  | .exact p => s!"exact({showProb p})"
  | .unknown => "[0,1]"

def main : IO Unit := do
  IO.println "========================================================"
  IO.println "COMPAS Numerical Audit — checker vs. paper"
  IO.println "========================================================"

  -- --------------------------------------------------------
  -- §4.1 Headline rates (from Table in PDF p.7)
  -- --------------------------------------------------------
  IO.println ""
  IO.println "§4.1 Headline rates"
  IO.println "--------------------"
  IO.println "  Black non-recid., HighRisk:  641/1514"
  IO.println s!"    checker f = {showProb (P 641 1514)}"
  IO.println s!"    paper   f = 641/1514 ≈ 0.4234"
  IO.println "  White non-recid., HighRisk:  282/1281"
  IO.println s!"    checker f = {showProb (P 282 1281)}"
  IO.println s!"    paper   f = 282/1281 ≈ 0.2201"
  IO.println "  White recid., LowRisk:       408/822"
  IO.println s!"    checker f = {showProb (P 408 822)}"
  IO.println s!"    paper   f = 408/822 ≈ 0.4964"
  IO.println "  Black recid., LowRisk:       473/1661"
  IO.println s!"    checker f = {showProb (P 473 1661)}"
  IO.println s!"    paper   f = 473/1661 ≈ 0.2848"

  -- --------------------------------------------------------
  -- §4.2 UTrust derivation (false-positive direction)
  -- Black non-recidivists HighRisk rate vs White benchmark
  -- --------------------------------------------------------
  IO.println ""
  IO.println "§4.2 UTrust — Black non-recid. HighRisk"
  IO.println "-----------------------------------------"
  let n_BN : Nat := 1514
  let f_BN := P 641 1514     -- observed frequency
  -- Paper says White non-recid HighRisk benchmark = 94/427
  -- But the table says 282/1281. Let me check: 282/1281 ≈ 0.2201 and 94/427 ≈ 0.2201
  -- 94/427 is the reduced form? 282 = 94*3, 1281 = 427*3. Yes, 282/1281 = 94/427.
  let p_WN := P 94 427       -- model probability (= 282/1281 reduced)
  IO.println s!"  n = {n_BN},  f = {showProb f_BN},  p = {showProb p_WN}"
  IO.println s!"  282/1281 reduced: 282/3 = 94, 1281/3 = 427 ✓"
  let ci_BN := binomialCI n_BN f_BN p_WN
  IO.println s!"  P({n_BN}, {showProb f_BN}, {showProb p_WN})"
  IO.println s!"    checker CI = {showConstraint ci_BN}"
  IO.println s!"    paper   CI = [0.398332, 0.448729]"
  IO.println s!"  p ∈ CI?  {inConstraint p_WN ci_BN}   (expect false for UTrust)"
  IO.println s!"  p ∉ CI?  {notInConstraint p_WN ci_BN}   (expect true for UTrust)"

  -- --------------------------------------------------------
  -- §4.2 continued: the UPDATE step for Black non-recid.
  -- male batch: n=1168, f=255/584  (paper says u_1168 : HighRisk_{255/584})
  -- Wait — 255/584? Let me re-read. The paper says:
  --   Γ_BN ⊢_{σ_m} u_1168 : HighRisk_{255/584}
  -- But n=1168 with f=255/584? That means 1168 * 255/584 = 1168*255/584.
  -- 584*2 = 1168. So nf = 1168*255/584 = 2*255 = 510.
  -- female batch: n=346, f=131/346, so nf = 131.
  -- UPDATE: (510 + 131) / (1168 + 346) = 641 / 1514. ✓
  -- --------------------------------------------------------
  IO.println ""
  IO.println "  UPDATE sub-derivation:"
  let n_m : Nat := 1168
  let f_m := P 255 584       -- male sub-batch frequency
  let n_f : Nat := 346
  let f_f := P 131 346       -- female sub-batch frequency
  IO.println s!"    male:   n={n_m}, f={showProb f_m}, nf = {n_m}*255/584 = 510"
  IO.println s!"    female: n={n_f}, f={showProb f_f}, nf = 131"
  match weightedFreq n_m f_m n_f f_f with
  | some wf => IO.println s!"    pooled: n={n_m + n_f}, f={showProb wf}"
  | none    => IO.println "    pooled: FAILED"
  IO.println s!"    expected: 641/1514 = {showProb (P 641 1514)}"

  -- --------------------------------------------------------
  -- §4.3 Trust derivation (Black female recidivists)
  -- --------------------------------------------------------
  IO.println ""
  IO.println "§4.3 Trust — Black female recid. LowRisk"
  IO.println "------------------------------------------"
  let n_BRF : Nat := 203
  let f_BRF := P 62 203      -- observed frequency
  -- Paper: Black male recid model = 137/486
  -- Let me verify: paper says Γ^mdl_BRM ⊢ x_BRM : LowRisk_{137/486}
  -- And 473/1661 ≈ 0.2848 is the Black recid LowRisk headline.
  -- 137/486 ≈ 0.2819. These are different! 137/486 is the MALE rate, not the total.
  let p_BRM := P 137 486
  IO.println s!"  n = {n_BRF},  f = {showProb f_BRF},  p = {showProb p_BRM}"
  let ci_BRF := binomialCI n_BRF f_BRF p_BRM
  IO.println s!"  P({n_BRF}, {showProb f_BRF}, {showProb p_BRM})"
  IO.println s!"    checker CI = {showConstraint ci_BRF}"
  IO.println s!"    paper   CI = [0.242865, 0.373759]"
  IO.println s!"  p ∈ CI?  {inConstraint p_BRM ci_BRF}   (expect true for Trust)"

  -- --------------------------------------------------------
  -- §4.3 continued: ETex re-entry
  -- Original assumption is x_BRF : LowRisk_{[0,1]}
  -- Since 137/486 ∈ [0,1] (trivially), ETex fires.
  -- Conclusion: x_BRF : LowRisk_{137/486} in expected mode.
  -- --------------------------------------------------------
  IO.println ""
  IO.println "  ETex re-entry:"
  IO.println s!"    137/486 ∈ [0,1]?  {inConstraint p_BRM .unknown}   (expect true)"
  IO.println s!"    conclusion: expected-mode LowRisk with value {showProb p_BRM}"

  IO.println ""
  IO.println "========================================================"
  IO.println ""

  -- --------------------------------------------------------
  -- Summary: do the checker's CIs match the paper?
  -- --------------------------------------------------------
  IO.println "CI Comparison Summary"
  IO.println "---------------------"
  -- The paper uses P(1514, 641/1514, 94/427) = [0.398332, 0.448729]
  -- Our score-test CI with z=√20 (Chebyshev) and rational Newton sqrt may differ.
  -- Let me show the raw rational bounds.
  match ci_BN with
  | .interval lo hi =>
    IO.println s!"  §4.2 CI lo: checker = {lo.val}  paper ≈ 0.398332"
    IO.println s!"  §4.2 CI hi: checker = {hi.val}  paper ≈ 0.448729"
  | _ => IO.println "  §4.2 CI: not an interval?!"
  match ci_BRF with
  | .interval lo hi =>
    IO.println s!"  §4.3 CI lo: checker = {lo.val}  paper ≈ 0.242865"
    IO.println s!"  §4.3 CI hi: checker = {hi.val}  paper ≈ 0.373759"
  | _ => IO.println "  §4.3 CI: not an interval?!"

  IO.println ""
  IO.println "Note: Numerical differences are expected — the paper likely uses"
  IO.println "Clopper-Pearson (exact) CIs while the checker uses Wald (normal"
  IO.println "approximation) with z = 559017/125000 ≈ √20 and rational Newton sqrt."
  IO.println "The QUALITATIVE conclusions (Trust vs UTrust) must agree."
