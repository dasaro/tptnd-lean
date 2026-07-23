import TPTND.CheckM
import TPTND.Spec
import TPTND.WellFormedness
import TPTND.Arithmetic

namespace TPTND

/-! # Structural Rules (Table 7)

`WeakeningD`, `WeakeningS`, `Contraction`.  Design doc §7.8. -/

-- ============================================================================
-- WeakeningD  (distribution weakening)
-- ============================================================================

def checkWeakeningD (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "WeakeningD"
  match ps with
  | [pJ, pDelta] => do
    ensure d.hasIndependenceWitness
      "WeakeningD: explicit independence witness required"
    -- First premise: Γ ⊢ J  (any judgement)
    -- Second premise: ⊢ Δ  (distribution well-formedness)
    match getClaim pDelta with
    | .distDecl Δ => do
      ensure (independentContexts (getCtx pJ) Δ)
        "WeakeningD: Γ and Δ must constrain disjoint variables (Γ #w Δ)"
      -- ⊢ Δ is a distribution judgement: Δ must be admissible on its own,
      -- not merely well-formed after being merged into Γ.
      ensure (contextWF Δ)
        "WeakeningD: the weakening distribution Δ must be well-formed"
      -- Conclusion context must be Γ, Δ
      let merged := mergeContexts [getCtx pJ, Δ]
      ensure (contextEqSet (getCtx d) merged)
        "WeakeningD: conclusion context must be merge of Γ and Δ"
      -- Conclusion claim must match first premise claim
      ensure (getClaim d == getClaim pJ)
        "WeakeningD: conclusion claim must match first premise"
    | _ => throw "WeakeningD: second premise must be distDecl"
  | _ => throw "WeakeningD: internal error"

-- ============================================================================
-- WeakeningS  (strengthening weakening)
-- ============================================================================

def checkWeakeningS (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "WeakeningS"
  match ps with
  | [pJ, pK] => do
    ensure d.hasIndependenceWitness
      "WeakeningS: explicit independence witness required"
    ensure (independentContexts (getCtx pJ) (getCtx pK))
      "WeakeningS: Γ and Δ must constrain disjoint variables (Γ #w Δ)"
    -- Conclusion context = Γ, Δ
    let merged := mergeContexts [getCtx pJ, getCtx pK]
    ensure (contextEqSet (getCtx d) merged)
      "WeakeningS: conclusion context must be merge of premise contexts"
    -- Conclusion claim = first premise claim (J, not K)
    ensure (getClaim d == getClaim pJ)
      "WeakeningS: conclusion claim must match first premise"
  | _ => throw "WeakeningS: internal error"

-- ============================================================================
-- Contraction
-- ============================================================================

def checkContractionC (d : Derivation) :
    CheckM (PLift ((∀ p ∈ d.premises, Derivable p.conclusion)
                   → contextWF (getCtx d) = true
                   → Derivable d.conclusion)) := do
  let ⟨ps, hps_eq⟩ ← expectPremises' d 1 "Contraction"
  match ps with
  | [p] => do
    -- Premise:    Γ, x : α_{c₁}, …, x : α_{cₖ} ⊢ J   (k ≥ 2)
    -- Conclusion: Γ, x : α_a ⊢ J                     with a ∈ ⋂ᵢ cᵢ
    let ⟨hclaim⟩ ← ensure' (getClaim d == getClaim p)
      "Contraction: conclusion claim must match premise claim"
    -- Locate the contracted group by (variable, output) rather than by set
    -- difference.  Set difference fails when the contracted value `a` happens
    -- to equal one of the `cᵢ`: the surviving entry is then present in BOTH
    -- contexts, so nothing looks "added" and the rule could not fire.
    match hgroup : (((getCtx p).map (fun e => (e.name, e.output))).eraseDups).filter
        (fun k' => ((getCtx p).filter (fun e => (e.name, e.output) == k')).length ≥ 2 &&
                   ((getCtx d).filter (fun e => (e.name, e.output) == k')).length == 1) with
    | [k] => do
      -- everything outside the contracted group must be carried over untouched
      let ⟨hrest⟩ ← ensure' (contextEqSet
          ((getCtx p).filter (fun e => (e.name, e.output) != k))
          ((getCtx d).filter (fun e => (e.name, e.output) != k)))
        "Contraction: entries outside the contracted group must be unchanged"
      match hrepl : (getCtx d).filter (fun e => (e.name, e.output) == k) with
      | [replacement] => do
        match hexact : replacement.constraint with
        | .exact a => do
          -- Every contracted entry must carry genuine information.
          let ⟨hinf⟩ ← ensure' (((getCtx p).filter (fun e => (e.name, e.output) == k)).any
              (fun r => !(match r.constraint with
                | .unknown => true
                | .interval lo hi => decide (lo.val == 0 && hi.val == 1)
                | _ => false)))
            "Contraction: at least one entry must have an informative (non-trivial) constraint"
          let ⟨hin⟩ ← ensure' (((getCtx p).filter (fun e => (e.name, e.output) == k)).all
              (fun r => r.constraint.contains a))
            "Contraction: exact value must lie in intersection of all constraints"
          pure ⟨fun hprem hwf => by
            have hmem : p ∈ d.premises := by
              rw [← hps_eq]; exact List.mem_singleton_self p
            have hpD : Derivable ⟨getCtx p, getClaim p⟩ := by
              have := hprem p hmem; rwa [conclusion_eta] at this
            rw [beq_iff_eq] at hclaim
            rw [conclusion_eta, hclaim]
            exact .contraction (getCtx p) (getCtx d) (getClaim p) k replacement a
              hwf hpD hgroup hrest hrepl hexact hinf hin⟩
        | _ => throw "Contraction: replacement must have exact constraint"
      | _ => throw "Contraction: unreachable"
    | [] => throw "Contraction: no (variable, output) group is contracted"
    | _  => throw "Contraction: exactly one group may be contracted at a time"
  | _ => throw "Contraction: internal error"

def checkContraction (d : Derivation) : CheckM Unit := do
  let _ ← checkContractionC d

end TPTND
