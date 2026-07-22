import TPTND.CheckM
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

/-- Does a `Prob` value lie inside a `Constraint`? -/
private def probInConstraint (a : Prob) (c : Constraint) : Bool :=
  c.contains a

def checkContraction (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 1 "Contraction"
  match ps with
  | [p] => do
    -- Premise:    Γ, x : α_{c₁}, …, x : α_{cₖ} ⊢ J   (k ≥ 2)
    -- Conclusion: Γ, x : α_a ⊢ J                     with a ∈ ⋂ᵢ cᵢ
    ensure (getClaim d == getClaim p)
      "Contraction: conclusion claim must match premise claim"
    let premCtx := getCtx p
    let concCtx := getCtx d
    -- Locate the contracted group by (variable, output) rather than by set
    -- difference.  Set difference fails when the contracted value `a` happens
    -- to equal one of the `cᵢ`: the surviving entry is then present in BOTH
    -- contexts, so nothing looks "added" and the rule could not fire.
    let key := fun (e : ContextEntry) => (e.name, e.output)
    let keys := premCtx.map key |>.eraseDups
    let contracted := keys.filter (fun k =>
      (premCtx.filter (fun e => key e == k)).length ≥ 2 &&
      (concCtx.filter (fun e => key e == k)).length == 1)
    match contracted with
    | [k] => do
      let group := premCtx.filter (fun e => key e == k)
      -- everything outside the contracted group must be carried over untouched
      let restPrem := premCtx.filter (fun e => key e != k)
      let restConc := concCtx.filter (fun e => key e != k)
      ensure (contextEqSet restPrem restConc)
        "Contraction: entries outside the contracted group must be unchanged"
      match concCtx.filter (fun e => key e == k) with
      | [replacement] => do
        match replacement.constraint with
        | .exact a => do
          -- Every contracted entry must carry genuine information.
          let isTrivial := fun (c : Constraint) => match c with
            | .unknown => true
            | .interval lo hi => decide (lo.val == 0 && hi.val == 1)
            | _ => false
          ensure (group.any (fun r => !isTrivial r.constraint))
            "Contraction: at least one entry must have an informative (non-trivial) constraint"
          ensure (group.all (fun r => probInConstraint a r.constraint))
            "Contraction: exact value must lie in intersection of all constraints"
        | _ => throw "Contraction: replacement must have exact constraint"
      | _ => throw "Contraction: unreachable"
    | [] => throw "Contraction: no (variable, output) group is contracted"
    | _  => throw "Contraction: exactly one group may be contracted at a time"
  | _ => throw "Contraction: internal error"

end TPTND
