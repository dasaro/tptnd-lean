import TPTND.CheckM
import TPTND.Spec
import TPTND.WellFormedness
import TPTND.Arithmetic

namespace TPTND

/-! # Comparison Rules (Table 6, second half)

`IEx`, `INEx`, `EEx`, `ENEx`.  Design doc §7.7. -/

-- ============================================================================
-- IEx  (excess introduction)
-- ============================================================================

def checkIEx (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "IEx"
  match ps with
  | [p1, p2] => do
    let tc1 ← expectTermClaim (getClaim p1) "IEx"
    let tc2 ← expectTermClaim (getClaim p2) "IEx"
    ensure (tc1.mode == .frequency && tc2.mode == .frequency)
      "IEx: both premises must be frequency mode"
    ensure (tc1.output == tc2.output)
      "IEx: both premises must share the same output"
    ensure (Provenance.disjoint tc1.prov tc2.prov)
      "IEx: provenances must be disjoint"
    let ci := twoSampleCI tc1.samples tc2.samples tc1.value tc2.value
    ensure (notInConstraint Prob.zero ci)
      "IEx: 0 must lie outside the two-sample CI (significant difference)"
    ensure (contextEqSet (getCtx d) (mergeContexts [getCtx p1, getCtx p2]))
      "IEx: conclusion context must be Γ,Δ (merge of premise contexts)"
    match getClaim d with
    | .comparison (.excess left right diff interval) => do
      ensure (left == tc1) "IEx: left claim must match the first premise"
      ensure (right == tc2) "IEx: right claim must match the second premise"
      let d' ← expectSome (probSub tc1.value tc2.value)
        "IEx: f - g is negative (left must exceed right)"
      ensure (decide (diff.val == d'.val))
        "IEx: difference must be f - g"
      ensure (interval == ci) "IEx: interval must match computed CI"
    | _ => throw "IEx: conclusion must be an excess comparison claim"
  | _ => throw "IEx: internal error"

-- ============================================================================
-- INEx  (no-excess introduction)
-- ============================================================================

def checkINEx (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "INEx"
  match ps with
  | [p1, p2] => do
    let tc1 ← expectTermClaim (getClaim p1) "INEx"
    let tc2 ← expectTermClaim (getClaim p2) "INEx"
    ensure (tc1.mode == .frequency && tc2.mode == .frequency)
      "INEx: both premises must be frequency mode"
    ensure (tc1.output == tc2.output) "INEx: outputs must match"
    ensure (Provenance.disjoint tc1.prov tc2.prov) "INEx: provenances must be disjoint"
    ensure (decide (tc1.value.val ≥ tc2.value.val))
      "INEx: premises must be ordered larger-rate-first (f ≥ g)"
    let ci := twoSampleCI tc1.samples tc2.samples tc1.value tc2.value
    ensure (inConstraint Prob.zero ci)
      "INEx: 0 must lie within the two-sample CI (no significant difference)"
    ensure (contextEqSet (getCtx d) (mergeContexts [getCtx p1, getCtx p2]))
      "INEx: conclusion context must be Γ,Δ (merge of premise contexts)"
    match getClaim d with
    | .comparison (.noExcess left right _ interval) => do
      ensure (left == tc1) "INEx: left claim must match the first premise"
      ensure (right == tc2) "INEx: right claim must match the second premise"
      ensure (interval == ci) "INEx: interval must match computed CI"
    | _ => throw "INEx: conclusion must be a noExcess comparison claim"
  | _ => throw "INEx: internal error"

-- ============================================================================
-- EEx  (excess elimination)
-- ============================================================================

def checkEEx (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "EEx"
  match ps with
  | [pExcess, pModel] => do
    let exClaim ← expectComparisonClaim (getClaim pExcess) "EEx"
    match exClaim with
    | .excess leftTC rightTC _ interval => do
      let modelEntry ← expectIdentity (getClaim pModel)
        "EEx: second premise must be an identity claim"
      -- The model must be a genuine context lookup.  Checking the premise's
      -- rule NAME is launderable — a claim-preserving wrapper (WeakeningS/D)
      -- renames any node — so the check is structural: the cited entry must
      -- be assumed in the model premise's own context.  identity/identity_star
      -- conclusions satisfy this; an IDENTITY*₂ fabrication never does,
      -- wrapped or not.
      ensure (modelEntry ∈ getCtx pModel)
        "EEx: the model entry must be assumed in the model premise's context"
      -- ...and it must be the UNIQUE hypothesis for its (variable, output):
      -- citing one of several competing hypotheses would let one context
      -- certify both Trust and UTrust for the same data.
      ensure ((((getCtx pModel).filter (fun e =>
          e.name == modelEntry.name && e.output == modelEntry.output)).length) == 1)
        "EEx: the cited model entry must be the unique hypothesis for its (variable, output)"
      ensure (modelEntry.output == rightTC.output)
        "EEx: model output must match the right (benchmark) group's output"
      let modelP ← expectExact modelEntry.constraint
        "EEx: model entry must have exact constraint"
      match interval with
      | .interval lo hi => do
        -- p + h ≤ 1
        ensure (probAdd modelP hi).isSome "EEx: p + h exceeds 1"
        -- Conclusion must be a term claim preserving the LEFT side data
        let conc ← expectTermClaim (getClaim d) "EEx"
        ensure (conc.mode == .frequency) "EEx: must preserve frequency mode"
        ensure (conc.term == leftTC.term) "EEx: must preserve left term"
        ensure (conc.samples == leftTC.samples) "EEx: must preserve left sample size"
        ensure (conc.output == leftTC.output) "EEx: must preserve left output"
        ensure (decide (conc.value.val == leftTC.value.val))
          "EEx: must preserve left frequency"
        -- Shifted interval [p+ℓ, p+h] must appear in conclusion context
        let shiftedLo := clampProb (modelP.val + lo.val)
        let shiftedHi := clampProb (modelP.val + hi.val)
        let shiftedConstraint := Constraint.interval shiftedLo shiftedHi
        -- Table 6: the conclusion context is Γ,Δ,Θ plus exactly one shifted
        -- assumption — the premise contexts are preserved, not discarded.
        let baseCtx := mergeContexts [getCtx pExcess, getCtx pModel]
        ensure (baseCtx.all (· ∈ getCtx d))
          "EEx: conclusion context must preserve the premise contexts"
        match (getCtx d).filter (· ∉ baseCtx) with
        | [se] => do
          ensure (se.output == leftTC.output && se.constraint == shiftedConstraint)
            "EEx: the added assumption must be x_t : α_[p+ℓ, p+h]"
          -- x_t is the variable designated to the LEFT term: identifying the
          -- assumption by output alone let it be attached to any variable.
          match leftTC.term with
          | .atom tn =>
            ensure (se.name == tn)
              "EEx: the added assumption must be the left term's variable x_t"
          | _ => pure ()
        | _ =>
          throw "EEx: conclusion must add exactly one shifted assumption"
      | _ => throw "EEx: interval must be a proper interval"
    | _ => throw "EEx: first premise must be an excess claim"
  | _ => throw "EEx: internal error"

-- ============================================================================
-- ENEx  (no-excess elimination)
-- ============================================================================

def checkENExC (d : Derivation) :
    CheckM (PLift ((∀ p ∈ d.premises, Derivable p.conclusion)
                   → contextWF (getCtx d) = true
                   → Derivable d.conclusion)) := do
  let ⟨ps, hps_eq⟩ ← expectPremises' d 2 "ENEx"
  match ps with
  | [pNoExcess, pModel] => do
    match hne : getClaim pNoExcess with
    | .comparison (.noExcess leftTC rightTC diff interval) => do
      match hid : getClaim pModel with
      | .identity modelEntry => do
        -- The model must be a genuine context lookup.  Checking the premise's
        -- rule NAME is launderable — a claim-preserving wrapper (WeakeningS/D)
        -- renames any node — so the check is structural: the cited entry must
        -- be assumed in the model premise's own context.  identity/identity_star
        -- conclusions satisfy this; an IDENTITY*₂ fabrication never does,
        -- wrapped or not.
        let ⟨hmem⟩ ← ensure' (modelEntry ∈ getCtx pModel)
          "ENEx: the model entry must be assumed in the model premise's context"
        -- ...and it must be the UNIQUE hypothesis for its (variable, output):
        -- citing one of several competing hypotheses would let one context
        -- certify both Trust and UTrust for the same data.
        let ⟨_⟩ ← ensure' ((((getCtx pModel).filter (fun e =>
            e.name == modelEntry.name && e.output == modelEntry.output)).length) == 1)
          "ENEx: the cited model entry must be the unique hypothesis for its (variable, output)"
        let ⟨hmout⟩ ← ensure' (modelEntry.output == rightTC.output)
          "ENEx: model output must match the right (benchmark) group's output"
        match hexact : modelEntry.constraint with
        | .exact modelP => do
          match hint : interval with
          | .interval lo hi => do
            let ⟨hsum⟩ ← ensure' (probAdd modelP hi).isSome "ENEx: p + h exceeds 1"
            match hcc : getClaim d with
            | .term conc => do
              let ⟨hmode⟩ ← ensure' (conc.mode == .frequency)
                "ENEx: must preserve frequency mode"
              let ⟨ht⟩ ← ensure' (conc.term == leftTC.term)
                "ENEx: must preserve left term"
              let ⟨hn⟩ ← ensure' (conc.samples == leftTC.samples)
                "ENEx: must preserve sample size"
              let ⟨hα⟩ ← ensure' (conc.output == leftTC.output)
                "ENEx: must preserve output"
              let ⟨hval⟩ ← ensure' (decide (conc.value.val == leftTC.value.val))
                "ENEx: must preserve left frequency"
              let shiftedLo := clampProb (modelP.val + lo.val)
              let shiftedHi := clampProb (modelP.val + hi.val)
              let shiftedConstraint := Constraint.interval shiftedLo shiftedHi
              -- Table 6: the conclusion context is Γ,Δ,Θ plus exactly one shifted
              -- assumption — the premise contexts are preserved, not discarded.
              let baseCtx := mergeContexts [getCtx pNoExcess, getCtx pModel]
              let ⟨hbase⟩ ← ensure' (baseCtx.all (· ∈ getCtx d))
                "ENEx: conclusion context must preserve the premise contexts"
              match hf : (getCtx d).filter (· ∉ baseCtx) with
              | [se] => do
                let ⟨hseok⟩ ← ensure' (se.output == leftTC.output &&
                    se.constraint == shiftedConstraint)
                  "ENEx: the added assumption must be x_t : α_[p+ℓ, p+h]"
                -- x_t is the variable designated to the LEFT term: identifying the
                -- assumption by output alone let it be attached to any variable.
                match leftTC.term with
                | .atom tn =>
                  ensure (se.name == tn)
                    "ENEx: the added assumption must be the left term's variable x_t"
                | _ => pure ()
                pure ⟨fun hprem hwf => by
                  have hm1 : pNoExcess ∈ d.premises := by rw [← hps_eq]; simp
                  have hm2 : pModel ∈ d.premises := by rw [← hps_eq]; simp
                  have heD : Derivable ⟨getCtx pNoExcess,
                      .comparison (.noExcess leftTC rightTC diff (.interval lo hi))⟩ := by
                    have := hprem pNoExcess hm1
                    rwa [conclusion_eta, hne] at this
                  have hmD : Derivable ⟨getCtx pModel, .identity modelEntry⟩ := by
                    have := hprem pModel hm2; rwa [conclusion_eta, hid] at this
                  rw [Bool.and_eq_true] at hseok
                  obtain ⟨hseout, hsec⟩ := hseok
                  rw [beq_iff_eq] at hmode ht hn hα hmout hseout hsec
                  have hcv : conc.value = leftTC.value :=
                    Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true hval))
                  have hseD : se ∈ getCtx d := by
                    have : se ∈ (getCtx d).filter (· ∉ baseCtx) := by
                      rw [hf]; exact List.mem_singleton_self se
                    exact List.mem_of_mem_filter this
                  have hconc_eq : conc = ⟨.frequency, leftTC.term, leftTC.samples,
                      leftTC.output, leftTC.value, conc.prov⟩ :=
                    TermClaim.ext hmode ht hn hα hcv rfl
                  rw [conclusion_eta, hcc, hconc_eq]
                  exact .eNEx (getCtx pNoExcess) (getCtx pModel) (getCtx d)
                    leftTC rightTC diff lo hi modelEntry se modelP conc.prov hwf
                    heD hmD hexact hmout hsum hbase hseD hseout hsec
                    (of_decide_eq_true hmem)⟩
              | _ =>
                throw "ENEx: conclusion must add exactly one shifted assumption"
            | _ => throw "ENEx: expected a term claim"
          | _ => throw "ENEx: interval must be a proper interval"
        | _ => throw "ENEx: model entry must have exact constraint"
      | _ => throw "ENEx: second premise must be an identity claim"
    | _ => throw "ENEx: first premise must be a noExcess claim"
  | _ => throw "ENEx: internal error"

def checkENEx (d : Derivation) : CheckM Unit := do
  let _ ← checkENExC d

end TPTND
