import TPTND.CheckM
import TPTND.Spec
import TPTND.WellFormedness
import TPTND.Arithmetic

namespace TPTND

/-! # Trust Rules (Tables 5–6)

`IT`, `IUT`, `ET`, `EUT`, `ETex`.  Design doc §7.6. -/

-- ============================================================================
-- IT  (trust introduction)
-- ============================================================================

def checkIT (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "IT"
  match ps with
  | [pModel, pObs] => do
    let modelEntry ← expectIdentity (getClaim pModel)
      "IT: first premise must be an identity claim (model)"
    -- The model must be a genuine context lookup.  Checking the premise's
    -- rule NAME is launderable — a claim-preserving wrapper (WeakeningS/D)
    -- renames any node — so the check is structural: the cited entry must
    -- be assumed in the model premise's own context.  identity/identity_star
    -- conclusions satisfy this; an IDENTITY*₂ fabrication never does,
    -- wrapped or not.
    ensure (modelEntry ∈ getCtx pModel)
      "IT: the model entry must be assumed in the model premise's context"
    -- ...and it must be the UNIQUE hypothesis for its (variable, output):
    -- citing one of several competing hypotheses would let one context
    -- certify both Trust and UTrust for the same data.
    ensure ((((getCtx pModel).filter (fun e =>
        e.name == modelEntry.name && e.output == modelEntry.output)).length) == 1)
      "IT: the cited model entry must be the unique hypothesis for its (variable, output)"
    let modelP ← expectExact modelEntry.constraint
      "IT: model entry must have exact constraint"
    let obs ← expectTermClaim (getClaim pObs) "IT"
    ensure (obs.mode == .frequency) "IT: observation must be frequency mode"
    ensure (modelEntry.output == obs.output)
      "IT: model output must match observed output"
    let ci := binomialCI obs.samples obs.value modelP
    ensure (inConstraint modelP ci)
      "IT: model probability must lie within binomial CI"
    ensure (contextEqSet (getCtx d) (mergeContexts [getCtx pModel, getCtx pObs]))
      "IT: conclusion context must be Γ,Δ (merge of premise contexts)"
    match getClaim d with
    | .trust (.trust kind t n α f p interval prov) => do
      ensure (kind == CIKind.oneSample) "IT: conclusion must be a one-sample (𝒫) trust"
      ensure (t == obs.term) "IT: trust term mismatch"
      ensure (n == obs.samples) "IT: trust sample size mismatch"
      ensure (α == obs.output) "IT: trust output mismatch"
      ensure (decide (f.val == obs.value.val)) "IT: trust frequency mismatch"
      ensure (decide (p.val == modelP.val)) "IT: trust model prob mismatch"
      ensure (interval == ci) "IT: trust interval mismatch"
      ensure (prov == obs.prov)
        "IT: trust provenance must record the observation provenance"
    | _ => throw "IT: conclusion must be a trust claim"
  | _ => throw "IT: internal error"

-- ============================================================================
-- IUT  (untrust introduction)
-- ============================================================================

def checkIUT (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "IUT"
  match ps with
  | [pModel, pObs] => do
    let modelEntry ← expectIdentity (getClaim pModel)
      "IUT: first premise must be an identity claim"
    -- The model must be a genuine context lookup.  Checking the premise's
    -- rule NAME is launderable — a claim-preserving wrapper (WeakeningS/D)
    -- renames any node — so the check is structural: the cited entry must
    -- be assumed in the model premise's own context.  identity/identity_star
    -- conclusions satisfy this; an IDENTITY*₂ fabrication never does,
    -- wrapped or not.
    ensure (modelEntry ∈ getCtx pModel)
      "IUT: the model entry must be assumed in the model premise's context"
    -- ...and it must be the UNIQUE hypothesis for its (variable, output):
    -- citing one of several competing hypotheses would let one context
    -- certify both Trust and UTrust for the same data.
    ensure ((((getCtx pModel).filter (fun e =>
        e.name == modelEntry.name && e.output == modelEntry.output)).length) == 1)
      "IUT: the cited model entry must be the unique hypothesis for its (variable, output)"
    let modelP ← expectExact modelEntry.constraint
      "IUT: model entry must have exact constraint"
    let obs ← expectTermClaim (getClaim pObs) "IUT"
    ensure (obs.mode == .frequency) "IUT: observation must be frequency mode"
    ensure (modelEntry.output == obs.output) "IUT: output mismatch"
    let ci := binomialCI obs.samples obs.value modelP
    ensure (notInConstraint modelP ci)
      "IUT: model probability must lie OUTSIDE binomial CI"
    ensure (contextEqSet (getCtx d) (mergeContexts [getCtx pModel, getCtx pObs]))
      "IUT: conclusion context must be Γ,Δ (merge of premise contexts)"
    match getClaim d with
    | .trust (.untrust kind t n α f p interval prov) => do
      ensure (kind == CIKind.oneSample) "IUT: conclusion must be a one-sample (𝒫) untrust"
      ensure (t == obs.term) "IUT: term mismatch"
      ensure (n == obs.samples) "IUT: sample size mismatch"
      ensure (α == obs.output) "IUT: output mismatch"
      ensure (decide (f.val == obs.value.val)) "IUT: frequency mismatch"
      ensure (decide (p.val == modelP.val)) "IUT: model prob mismatch"
      ensure (interval == ci) "IUT: interval mismatch"
      ensure (prov == obs.prov)
        "IUT: trust provenance must record the observation provenance"
    | _ => throw "IUT: conclusion must be an untrust claim"
  | _ => throw "IUT: internal error"

-- ============================================================================
-- IT2  (two-sample trust introduction)
-- ============================================================================
/-- Two-sample Trust: both premises are frequency observations.
    Computes the two-sample score-test CI for the difference f − g.
    If 0 ∈ CI → the groups are statistically indistinguishable → Trust.
    The `model` field in the TrustClaim stores the right-hand rate (g). -/

def checkIT2 (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "IT2"
  match ps with
  | [pLeft, pRight] => do
    let tcL ← expectTermClaim (getClaim pLeft) "IT2"
    let tcR ← expectTermClaim (getClaim pRight) "IT2"
    ensure (tcL.mode == .frequency && tcR.mode == .frequency)
      "IT2: both premises must be frequency mode"
    ensure (tcL.output == tcR.output)
      "IT2: both premises must share the same output"
    ensure (Provenance.disjoint tcL.prov tcR.prov)
      "IT2: provenances must be disjoint"
    let ci := twoSampleCI tcL.samples tcR.samples tcL.value tcR.value
    ensure (inConstraint Prob.zero ci)
      "IT2: 0 must lie within two-sample CI (no significant difference)"
    ensure (decide (tcL.value.val ≥ tcR.value.val))
      "IT2: premises must be ordered larger-rate-first (f ≥ g)"
    ensure (contextEqSet (getCtx d) (mergeContexts [getCtx pLeft, getCtx pRight]))
      "IT2: conclusion context must be Γ,Δ (merge of premise contexts)"
    match getClaim d with
    | .trust (.trust kind t n α f p interval prov) => do
      ensure (kind == CIKind.twoSample) "IT2: conclusion must be a two-sample (𝒬) trust"
      ensure (t == tcL.term) "IT2: trust term mismatch"
      ensure (n == tcL.samples) "IT2: trust sample size mismatch"
      ensure (α == tcL.output) "IT2: trust output mismatch"
      ensure (decide (f.val == tcL.value.val)) "IT2: trust frequency mismatch"
      ensure (decide (p.val == tcR.value.val)) "IT2: trust model prob mismatch"
      ensure (interval == ci) "IT2: trust interval mismatch"
      ensure (prov == tcL.prov ∪ tcR.prov)
        "IT2: trust provenance must be the union of the observation provenances"
    | _ => throw "IT2: conclusion must be a trust claim"
  | _ => throw "IT2: internal error"

-- ============================================================================
-- IUT2  (two-sample untrust introduction)
-- ============================================================================
/-- Two-sample UTrust: both premises are frequency observations.
    If 0 ∉ CI → the groups are significantly different → UTrust. -/

def checkIUT2 (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "IUT2"
  match ps with
  | [pLeft, pRight] => do
    let tcL ← expectTermClaim (getClaim pLeft) "IUT2"
    let tcR ← expectTermClaim (getClaim pRight) "IUT2"
    ensure (tcL.mode == .frequency && tcR.mode == .frequency)
      "IUT2: both premises must be frequency mode"
    ensure (tcL.output == tcR.output)
      "IUT2: both premises must share the same output"
    ensure (Provenance.disjoint tcL.prov tcR.prov)
      "IUT2: provenances must be disjoint"
    let ci := twoSampleCI tcL.samples tcR.samples tcL.value tcR.value
    ensure (notInConstraint Prob.zero ci)
      "IUT2: 0 must lie OUTSIDE two-sample CI (significant difference)"
    ensure (decide (tcL.value.val ≥ tcR.value.val))
      "IUT2: premises must be ordered larger-rate-first (f ≥ g)"
    ensure (contextEqSet (getCtx d) (mergeContexts [getCtx pLeft, getCtx pRight]))
      "IUT2: conclusion context must be Γ,Δ (merge of premise contexts)"
    match getClaim d with
    | .trust (.untrust kind t n α f p interval prov) => do
      ensure (kind == CIKind.twoSample) "IUT2: conclusion must be a two-sample (𝒬) untrust"
      ensure (t == tcL.term) "IUT2: term mismatch"
      ensure (n == tcL.samples) "IUT2: sample size mismatch"
      ensure (α == tcL.output) "IUT2: output mismatch"
      ensure (decide (f.val == tcL.value.val)) "IUT2: frequency mismatch"
      ensure (decide (p.val == tcR.value.val)) "IUT2: model prob mismatch"
      ensure (interval == ci) "IUT2: interval mismatch"
      ensure (prov == tcL.prov ∪ tcR.prov)
        "IUT2: trust provenance must be the union of the observation provenances"
    | _ => throw "IUT2: conclusion must be an untrust claim"
  | _ => throw "IUT2: internal error"

-- ============================================================================
-- ET  (trust elimination)
-- ============================================================================

/-- Common context check for ET/EUT: the conclusion context must be the trust
    premise's context Γ plus exactly one fresh entry `x_u : α_c`. -/
def checkElimContext
    (rule : String) (p d : Derivation) (t : Term) (α : Output) (c : Constraint) :
    CheckM Unit := do
  let premCtx := getCtx p
  let concCtx := getCtx d
  ensure (premCtx.all (· ∈ concCtx)) s!"{rule}: conclusion context must preserve Γ"
  match concCtx.filter (· ∉ premCtx) with
  | [xu] => do
    ensure (xu.output == α && xu.constraint == c)
      s!"{rule}: the re-entered entry must be x_u : α with the eliminated constraint"
    -- `x_u` is the variable DESIGNATED TO THE OBSERVED TERM u, not a fresh one.
    -- §3.8 says Contraction "can be applied to select the most appropriate
    -- value within such range", and Contraction merges entries sharing one
    -- (variable, output) — which a fresh variable could never do, leaving the
    -- audited interval attached to a variable nothing else mentions.
    let u ← designatedName rule t
    ensure (xu.name == u)
      s!"{rule}: the re-entered assumption must be the observed term's variable x_u"
  | _ => throw s!"{rule}: conclusion must add exactly one entry x_u"

def checkET (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 1 "ET"
  match ps with
  | [p] => do
    let tc ← expectTrustClaim (getClaim p) "ET"
    match tc with
    | .trust kind t n α f _p interval certProv => do
      ensure (kind == CIKind.oneSample)
        "ET: can only eliminate a one-sample (𝒫) trust certificate"
      let conc ← expectTermClaim (getClaim d) "ET"
      -- Preserve observed data
      ensure (conc.mode == .frequency) "ET: must preserve frequency mode"
      ensure (conc.term == t) "ET: must preserve observed term"
      ensure (conc.samples == n) "ET: must preserve sample size"
      ensure (conc.output == α) "ET: must preserve output"
      ensure (decide (conc.value.val == f.val)) "ET: must preserve frequency value"
      -- Provenance travels IN the certificate; reading it from the premise
      -- tree (the old obsProvOf) was defeated by structural wrappers.
      ensure (conc.prov == certProv)
        "ET: conclusion provenance must match the certificate's provenance"
      -- Context: Γ preserved + one fresh x_u : α_{[ℓ,h]}
      checkElimContext "ET" p d t α interval
    | _ => throw "ET: premise must be a (one-sample) trust claim"
  | _ => throw "ET: internal error"

-- ============================================================================
-- EUT  (untrust elimination)
-- ============================================================================

def checkEUT (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 1 "EUT"
  match ps with
  | [p] => do
    let tc ← expectTrustClaim (getClaim p) "EUT"
    match tc with
    | .untrust kind t n α f _p interval certProv => do
      ensure (kind == CIKind.oneSample)
        "EUT: can only eliminate a one-sample (𝒫) untrust certificate"
      let conc ← expectTermClaim (getClaim d) "EUT"
      ensure (conc.mode == .frequency) "EUT: must preserve frequency mode"
      ensure (conc.term == t) "EUT: must preserve observed term"
      ensure (conc.samples == n) "EUT: must preserve sample size"
      ensure (conc.output == α) "EUT: must preserve output"
      ensure (decide (conc.value.val == f.val)) "EUT: must preserve frequency value"
      -- Provenance: conclusion σ is the observed data's provenance
      ensure (conc.prov == certProv)
        "EUT: conclusion provenance must match the certificate's provenance"
      -- Complement interval: [ℓ,h] → ¬[ℓ,h]
      let complementInterval := match interval with
        | .interval lo hi => Constraint.outsideInterval lo hi
        | other           => other
      -- Context: Γ preserved + one fresh x_u : α_{¬[ℓ,h]}
      checkElimContext "EUT" p d t α complementInterval
    | _ => throw "EUT: premise must be an untrust claim"
  | _ => throw "EUT: internal error"

-- ============================================================================
-- ETex  (trust exact elimination — re-entry to expected layer)
-- ============================================================================

def checkETexC (d : Derivation) :
    CheckM (PLift ((∀ p ∈ d.premises, Derivable p.conclusion)
                   → contextWF (getCtx d) = true
                   → Derivable d.conclusion)) := do
  let ⟨ps, hps_eq⟩ ← expectPremises' d 1 "ETex"
  match ps with
  | [p] => do
    match hcl : getClaim p with
    | .trust (.trust kind t n α f modelP interval certProv) => do
      let ⟨hkind⟩ ← ensure' (kind == CIKind.oneSample)
        "ETex: can only eliminate a one-sample (𝒫) trust certificate"
      let premCtx := getCtx p
      -- Conclusion must be a term claim in EXPECTED mode (re-entry)
      match hcc : getClaim d with
      | .term conc => do
        let ⟨hmode⟩ ← ensure' (conc.mode == .expected)
          "ETex: conclusion must be in expected mode (re-entry)"
        let ⟨ht⟩ ← ensure' (conc.term == t) "ETex: must preserve term"
        let ⟨hn⟩ ← ensure' (conc.samples == n) "ETex: must preserve sample size"
        let ⟨hα⟩ ← ensure' (conc.output == α) "ETex: must preserve output"
        -- Conclusion value = model probability (the trusted exact value)
        let ⟨hval⟩ ← ensure' (decide (conc.value.val == modelP.val))
          "ETex: conclusion value must equal the trusted model probability"
        -- Context: Γ is preserved and the observed variable's own NON-EXACT
        -- assumption x_u : α_c is REPLACED by the trusted exact x_u : α_p,
        -- with p ∈ c (Table 6).  Tying the two by name is what makes the
        -- side condition non-vacuous.
        let concCtx := getCtx d
        match hfold : premCtx.filter (· ∉ concCtx),
              hfnew : concCtx.filter (· ∉ premCtx) with
        | [eOld], [eNew] => do
          let ⟨hsame⟩ ← ensure' (eOld.name == eNew.name && eOld.output == eNew.output)
            "ETex: the replaced assumption must be on the same variable and output"
          let ⟨holdα⟩ ← ensure' (eOld.output == α)
            "ETex: the replaced assumption must be on the observed output"
          let ⟨hnewc⟩ ← ensure' (eNew.constraint == Constraint.exact modelP)
            "ETex: the replacement must be the trusted exact value x_u : α_p"
          let ⟨hnonex⟩ ← ensure' (match eOld.constraint with
            | .exact _ => false | _ => true)
            "ETex: the replaced assumption must be non-exact"
          let ⟨hcont⟩ ← ensure' (eOld.constraint.contains modelP)
            "ETex: p must lie in the replaced constraint c"
          -- The re-entered value must land on the observed term's own
          -- variable: an expected-layer claim about `t` may only cite an
          -- assumption designated to `t`.
          let ⟨hdesig⟩ ← ensure' (t == Term.atom eNew.name)
            "ETex: the replaced assumption must be the observed term's variable x_u"
          let ⟨hprov⟩ ← ensure' (conc.prov == certProv)
            "ETex: conclusion provenance must match the certificate's provenance"
          pure ⟨fun hprem hwf => by
            have hmem : p ∈ d.premises := by
              rw [← hps_eq]; exact List.mem_singleton_self p
            rw [beq_iff_eq] at hkind
            subst hkind
            have hpD : Derivable ⟨getCtx p,
                .trust (.trust .oneSample t n α f modelP interval certProv)⟩ := by
              have := hprem p hmem; rwa [conclusion_eta, hcl] at this
            rw [Bool.and_eq_true] at hsame
            obtain ⟨hnm, hout⟩ := hsame
            rw [beq_iff_eq] at hmode ht hn hα hnm hout holdα hnewc hprov
            have hcv : conc.value = modelP :=
              Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true hval))
            have hconc_eq : conc = ⟨.expected, t, n, α, modelP, certProv⟩ :=
              TermClaim.ext hmode ht hn hα hcv hprov
            rw [conclusion_eta, hcc, hconc_eq]
            exact .eTex (getCtx p) (getCtx d) t n α f modelP interval certProv
              eOld eNew hwf hpD hfold hfnew hnm hout holdα hnewc hnonex hcont
              (beq_iff_eq.mp hdesig)⟩
        | _, _ =>
          throw "ETex: conclusion context must replace exactly one assumption"
      | _ => throw "ETex: expected a term claim"
    | _ => throw "ETex: premise must be a trust claim"
  | _ => throw "ETex: internal error"

def checkETex (d : Derivation) : CheckM Unit := do
  let _ ← checkETexC d

end TPTND
