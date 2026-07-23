import TPTND.CheckM
import TPTND.Spec
import TPTND.WellFormedness
import TPTND.Arithmetic

namespace TPTND

/-! # Output and Distribution Rules (Table 1)

`output_atom`, `output_neg`, `output_sum`, `output_prod`, `output_arr`,
`base`, `extend`, `unknown`.  Design doc §7.1. -/

-- ============================================================================
-- Output declaration rules
-- ============================================================================

def checkOutputAtom (d : Derivation) : CheckM Unit := do
  let _ ← expectPremises d 0 "output_atom"
  match getClaim d with
  | .outputDecl (.atom _) => pure ()
  | _ => throw "output_atom: conclusion must be outputDecl(atom _)"

/-- Certifying variant of `output_neg`: the checker returns, alongside its
    acceptance, a proof that the conclusion is derivable (given derivable
    premises and a well-formed context).  `Prop` content erases at compile
    time, so the runtime behaviour of `checkOutputNeg` is exactly the checks
    below and nothing more. -/
def checkOutputNegC (d : Derivation) :
    CheckM (PLift ((∀ p ∈ d.premises, Derivable p.conclusion)
                   → contextWF (getCtx d) = true
                   → Derivable d.conclusion)) := do
  let ⟨ps, hps_eq⟩ ← expectPremises' d 1 "output_neg"
  match ps with
  | [p] => do
    let ⟨α, hα⟩ ← expectOutputDecl' (getClaim p)
      "output_neg: expected outputDecl in premise and conclusion"
    let ⟨δ, hδ⟩ ← expectOutputDecl' (getClaim d)
      "output_neg: expected outputDecl in premise and conclusion"
    match hneg : δ with
    | .neg β => do
      let ⟨hab⟩ ← ensure' (α == β) "output_neg: negated output must match premise"
      pure ⟨fun hprem hwf => by
        rw [beq_iff_eq] at hab; subst hab
        have hmem : p ∈ d.premises := by
          rw [← hps_eq]; exact List.mem_singleton_self p
        have hpD : Derivable ⟨getCtx p, .outputDecl α⟩ := by
          have := hprem p hmem
          rwa [conclusion_eta, hα] at this
        rw [conclusion_eta, hδ]
        exact .outputNeg (getCtx d) (getCtx p) α hwf hpD⟩
    | _ => throw "output_neg: expected outputDecl in premise and conclusion"
  | _ => throw "output_neg: internal error"

def checkOutputNeg (d : Derivation) : CheckM Unit := do
  let _ ← checkOutputNegC d

private def checkOutputBinary (d : Derivation) (rule : String)
    (mk : Output → Output → Output) : CheckM Unit := do
  let ps ← expectPremises d 2 rule
  match ps with
  | [p1, p2] =>
    match getClaim p1, getClaim p2, getClaim d with
    | .outputDecl α, .outputDecl β, .outputDecl γ =>
      ensure (γ == mk α β) s!"{rule}: conclusion output mismatch"
    | _, _, _ => throw s!"{rule}: all three claims must be outputDecl"
  | _ => throw s!"{rule}: internal error"

def checkOutputSum  (d : Derivation) : CheckM Unit :=
  checkOutputBinary d "output_sum"  Output.sum
def checkOutputProd (d : Derivation) : CheckM Unit :=
  checkOutputBinary d "output_prod" Output.prod
/-- Table 1 declares the arrow *shape* `(α ⇒ β) :: output` without fixing the
    antecedent annotation, so any annotation is accepted here; I→ is what pins
    it to the discharged assumption. -/
def checkOutputArr  (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "output_arr"
  match ps with
  | [p1, p2] =>
    match getClaim p1, getClaim p2, getClaim d with
    | .outputDecl α, .outputDecl β, .outputDecl (.arr α' _ β') =>
      ensure (α == α' && β == β') "output_arr: conclusion output mismatch"
    | _, _, _ => throw "output_arr: all three claims must be outputDecl"
  | _ => throw "output_arr: internal error"

-- ============================================================================
-- Distribution rules
-- ============================================================================

def checkBase (d : Derivation) : CheckM Unit := do
  let _ ← expectPremises d 0 "base"
  match getClaim d with
  | .distDecl ctx => ensure (ctx.isEmpty) "base: context must be empty"
  | _ => throw "base: conclusion must be distDecl"

def checkExtend (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 1 "extend"
  match ps with
  | [p] =>
    match getClaim p, getClaim d with
    | .distDecl Γ, .distDecl Γ' => do
      ensure (Γ'.length == Γ.length + 1)
        "extend: conclusion context must have exactly one more entry"
      ensure (Γ'.take Γ.length == Γ)
        "extend: conclusion must be a proper extension of premise"
      match Γ'.getLast? with
      | some e =>
        match e.constraint with
        | .exact a => do
          let existingMass := Γ.foldl (fun acc entry =>
            if entry.name == e.name then
              match entry.constraint with
              | .exact p => acc + p.val
              | _        => acc
            else acc) (0 : ℚ)
          ensure (decide (existingMass + a.val ≤ 1))
            "extend: total exact mass for variable exceeds 1"
        | _ => throw "extend: new entry must carry an exact constraint"
      | none => throw "extend: empty conclusion context (impossible)"
    | _, _ => throw "extend: premise and conclusion must be distDecl"
  | _ => throw "extend: internal error"

/-- `extend_det`: deterministic extension `Γ, x : α :: distribution`.

    A deterministic assignment `x : α` is read as the probabilistic
    assumption `x : α_1` and subjected to the ordinary additivity
    discipline.  A variable therefore carries at most one deterministic
    value (1 + 1 > 1), and a deterministic value cannot coexist with any
    other positive mass for that variable.  Deterministic lookups need no
    rule of their own: they are `identity*` on an entry whose constraint is
    `exact 1`. -/
def checkExtendDet (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 1 "extend_det"
  match ps with
  | [p] =>
    match getClaim p, getClaim d with
    | .distDecl Γ, .distDecl Γ' => do
      ensure (Γ'.length == Γ.length + 1)
        "extend_det: conclusion context must have exactly one more entry"
      ensure (Γ'.take Γ.length == Γ)
        "extend_det: conclusion must be a proper extension of premise"
      match Γ'.getLast? with
      | some e =>
        match e.constraint with
        | .exact a => do
          ensure (decide (a.val == 1))
            "extend_det: a deterministic assignment x : α is x : α_1"
          -- the ordinary additivity condition
          let existingMass := Γ.foldl (fun acc entry =>
            if entry.name == e.name then
              match entry.constraint with
              | .exact p => acc + p.val
              | _        => acc
            else acc) (0 : ℚ)
          ensure (decide (existingMass + a.val ≤ 1))
            "extend_det: total exact mass for variable exceeds 1"
        | _ => throw "extend_det: new entry must carry an exact constraint"
      | none => throw "extend_det: empty conclusion context (impossible)"
    | _, _ => throw "extend_det: premise and conclusion must be distDecl"
  | _ => throw "extend_det: internal error"

/-- `unknown` (Table 1): `{x : α_[0,1] | α ∈ A}` — an opaque distribution
    over ONE process, for a finite support of interest `A`.

    Two things are part of that shape: it is a single variable `x`, and `A`
    is a SET, so the outputs are pairwise distinct.  This matters because
    `unknown` is exactly what produces the opaque `Δ` that IT/IUT admit as
    their observation premise; an entry set spanning several variables is
    not a distribution over one opaque process at all, and repeating an
    output would declare the same event twice. -/
def checkUnknown (d : Derivation) : CheckM Unit := do
  let ps := d.premises
  match getClaim d with
  | .distDecl Γ => do
    ensure (ps.length == Γ.length)
      "unknown: #premises must equal #entries in conclusion context"
    match Γ with
    | [] => throw "unknown: the support of interest A must be non-empty"
    | e :: rest => do
      ensure (rest.all (fun r => r.name == e.name))
        "unknown: every entry must be about the same variable x"
      ensure ((Γ.map (·.output)).eraseDups.length == Γ.length)
        "unknown: the outputs A must be pairwise distinct"
    let pairs := ps.zip Γ
    for ⟨pi, ei⟩ in pairs do
      match getClaim pi with
      | .outputDecl α => do
        ensure (ei.output == α)
          "unknown: premise output ≠ entry output"
        ensure (ei.constraint == .unknown)
          "unknown: entry must have unknown constraint"
      | _ => throw "unknown: every premise must be outputDecl"
  | _ => throw "unknown: conclusion must be distDecl"

end TPTND
