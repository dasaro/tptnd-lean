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

def checkOutputAtomC (d : Derivation) :
    CheckM (PLift ((∀ p ∈ d.premises, Derivable p.conclusion)
                   → contextWF (getCtx d) = true
                   → Derivable d.conclusion)) := do
  let _ ← expectPremises' d 0 "output_atom"
  let ⟨δ, hδ⟩ ← expectOutputDecl' (getClaim d)
    "output_atom: conclusion must be outputDecl(atom _)"
  match δ with
  | .atom a =>
      pure ⟨fun _ hwf => by
        rw [conclusion_eta, hδ]; exact .outputAtom (getCtx d) a hwf⟩
  | _ => throw "output_atom: conclusion must be outputDecl(atom _)"

def checkOutputAtom (d : Derivation) : CheckM Unit := do
  let _ ← checkOutputAtomC d

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

private def checkOutputBinaryC (d : Derivation) (rule : String)
    (mk : Output → Output → Output)
    (K : ∀ (Γ Γ1 Γ2 : Context) (α β : Output), contextWF Γ = true →
         Derivable ⟨Γ1, .outputDecl α⟩ → Derivable ⟨Γ2, .outputDecl β⟩ →
         Derivable ⟨Γ, .outputDecl (mk α β)⟩) :
    CheckM (PLift ((∀ p ∈ d.premises, Derivable p.conclusion)
                   → contextWF (getCtx d) = true
                   → Derivable d.conclusion)) := do
  let ⟨ps, hps_eq⟩ ← expectPremises' d 2 rule
  match ps with
  | [p1, p2] => do
    let ⟨α, h1⟩ ← expectOutputDecl' (getClaim p1) s!"{rule}: all three claims must be outputDecl"
    let ⟨β, h2⟩ ← expectOutputDecl' (getClaim p2) s!"{rule}: all three claims must be outputDecl"
    let ⟨γ, hd⟩ ← expectOutputDecl' (getClaim d) s!"{rule}: all three claims must be outputDecl"
    let ⟨hγ⟩ ← ensure' (γ == mk α β) s!"{rule}: conclusion output mismatch"
    pure ⟨fun hprem hwf => by
      rw [beq_iff_eq] at hγ; subst hγ
      have hm1 : p1 ∈ d.premises := by rw [← hps_eq]; simp
      have hm2 : p2 ∈ d.premises := by rw [← hps_eq]; simp
      have h1D : Derivable ⟨getCtx p1, .outputDecl α⟩ := by
        have := hprem p1 hm1; rwa [conclusion_eta, h1] at this
      have h2D : Derivable ⟨getCtx p2, .outputDecl β⟩ := by
        have := hprem p2 hm2; rwa [conclusion_eta, h2] at this
      rw [conclusion_eta, hd]
      exact K (getCtx d) (getCtx p1) (getCtx p2) α β hwf h1D h2D⟩
  | _ => throw s!"{rule}: internal error"

def checkOutputSum  (d : Derivation) : CheckM Unit := do
  let _ ← checkOutputBinaryC d "output_sum" Output.sum
    (fun Γ Γ1 Γ2 α β => Derivable.outputSum Γ Γ1 Γ2 α β)
def checkOutputProd (d : Derivation) : CheckM Unit := do
  let _ ← checkOutputBinaryC d "output_prod" Output.prod
    (fun Γ Γ1 Γ2 α β => Derivable.outputProd Γ Γ1 Γ2 α β)
/-- Table 1 declares the arrow *shape* `(α ⇒ β) :: output` without fixing the
    antecedent annotation, so any annotation is accepted here; I→ is what pins
    it to the discharged assumption. -/
def checkOutputArrC (d : Derivation) :
    CheckM (PLift ((∀ p ∈ d.premises, Derivable p.conclusion)
                   → contextWF (getCtx d) = true
                   → Derivable d.conclusion)) := do
  let ⟨ps, hps_eq⟩ ← expectPremises' d 2 "output_arr"
  match ps with
  | [p1, p2] => do
    let ⟨α, h1⟩ ← expectOutputDecl' (getClaim p1) "output_arr: all three claims must be outputDecl"
    let ⟨β, h2⟩ ← expectOutputDecl' (getClaim p2) "output_arr: all three claims must be outputDecl"
    let ⟨δ, hd⟩ ← expectOutputDecl' (getClaim d) "output_arr: all three claims must be outputDecl"
    match δ with
    | .arr α' a β' => do
      let ⟨hab⟩ ← ensure' (α == α' && β == β') "output_arr: conclusion output mismatch"
      pure ⟨fun hprem hwf => by
        rw [Bool.and_eq_true] at hab
        obtain ⟨ha, hb⟩ := hab
        rw [beq_iff_eq] at ha hb; subst ha; subst hb
        have hm1 : p1 ∈ d.premises := by rw [← hps_eq]; simp
        have hm2 : p2 ∈ d.premises := by rw [← hps_eq]; simp
        have h1D : Derivable ⟨getCtx p1, .outputDecl α⟩ := by
          have := hprem p1 hm1; rwa [conclusion_eta, h1] at this
        have h2D : Derivable ⟨getCtx p2, .outputDecl β⟩ := by
          have := hprem p2 hm2; rwa [conclusion_eta, h2] at this
        rw [conclusion_eta, hd]
        exact .outputArr (getCtx d) (getCtx p1) (getCtx p2) α β a hwf h1D h2D⟩
    | _ => throw "output_arr: all three claims must be outputDecl"
  | _ => throw "output_arr: internal error"

def checkOutputArr (d : Derivation) : CheckM Unit := do
  let _ ← checkOutputArrC d

-- ============================================================================
-- Distribution rules
-- ============================================================================

def checkBaseC (d : Derivation) :
    CheckM (PLift ((∀ p ∈ d.premises, Derivable p.conclusion)
                   → contextWF (getCtx d) = true
                   → Derivable d.conclusion)) := do
  let _ ← expectPremises' d 0 "base"
  let ⟨Γ0, hΓ⟩ ← expectDistDecl' (getClaim d) "base: conclusion must be distDecl"
  match Γ0 with
  | [] => pure ⟨fun _ hwf => by rw [conclusion_eta, hΓ]; exact .base (getCtx d) hwf⟩
  | _ :: _ => throw "base: context must be empty"

def checkBase (d : Derivation) : CheckM Unit := do
  let _ ← checkBaseC d

def checkExtendC (d : Derivation) :
    CheckM (PLift ((∀ p ∈ d.premises, Derivable p.conclusion)
                   → contextWF (getCtx d) = true
                   → Derivable d.conclusion)) := do
  let ⟨ps, hps_eq⟩ ← expectPremises' d 1 "extend"
  match ps with
  | [p] => do
    let ⟨Γ, hΓ⟩ ← expectDistDecl' (getClaim p) "extend: premise and conclusion must be distDecl"
    let ⟨Γ', hΓ'⟩ ← expectDistDecl' (getClaim d) "extend: premise and conclusion must be distDecl"
    let ⟨hlen⟩ ← ensure' (Γ'.length == Γ.length + 1)
      "extend: conclusion context must have exactly one more entry"
    let ⟨htake⟩ ← ensure' (Γ'.take Γ.length == Γ)
      "extend: conclusion must be a proper extension of premise"
    let ⟨e, hlast⟩ ← expectSome' Γ'.getLast? "extend: empty conclusion context (impossible)"
    let ⟨a, hexact⟩ ← expectExact' e.constraint "extend: new entry must carry an exact constraint"
    let existingMass := Γ.foldl (fun acc entry =>
      if entry.name == e.name then
        match entry.constraint with
        | .exact p => acc + p.val
        | _        => acc
      else acc) (0 : ℚ)
    let ⟨hmass⟩ ← ensure' (decide (existingMass + a.val ≤ 1))
      "extend: total exact mass for variable exceeds 1"
    pure ⟨fun hprem hwf => by
      have hmem : p ∈ d.premises := by rw [← hps_eq]; exact List.mem_singleton_self p
      have hpD : Derivable ⟨getCtx p, .distDecl Γ⟩ := by
        have := hprem p hmem; rwa [conclusion_eta, hΓ] at this
      rw [beq_iff_eq] at hlen htake
      rw [conclusion_eta, hΓ']
      exact .extend (getCtx d) (getCtx p) Γ Γ' e a hwf hpD hlen htake
        hlast hexact (of_decide_eq_true hmass)⟩
  | _ => throw "extend: internal error"

def checkExtend (d : Derivation) : CheckM Unit := do
  let _ ← checkExtendC d

/-- `extend_det`: deterministic extension `Γ, x : α :: distribution`.

    A deterministic assignment `x : α` is read as the probabilistic
    assumption `x : α_1` and subjected to the ordinary additivity
    discipline.  A variable therefore carries at most one deterministic
    value (1 + 1 > 1), and a deterministic value cannot coexist with any
    other positive mass for that variable.  Deterministic lookups need no
    rule of their own: they are `identity*` on an entry whose constraint is
    `exact 1`. -/
def checkExtendDetC (d : Derivation) :
    CheckM (PLift ((∀ p ∈ d.premises, Derivable p.conclusion)
                   → contextWF (getCtx d) = true
                   → Derivable d.conclusion)) := do
  let ⟨ps, hps_eq⟩ ← expectPremises' d 1 "extend_det"
  match ps with
  | [p] => do
    let ⟨Γ, hΓ⟩ ← expectDistDecl' (getClaim p) "extend_det: premise and conclusion must be distDecl"
    let ⟨Γ', hΓ'⟩ ← expectDistDecl' (getClaim d) "extend_det: premise and conclusion must be distDecl"
    let ⟨hlen⟩ ← ensure' (Γ'.length == Γ.length + 1)
      "extend_det: conclusion context must have exactly one more entry"
    let ⟨htake⟩ ← ensure' (Γ'.take Γ.length == Γ)
      "extend_det: conclusion must be a proper extension of premise"
    let ⟨e, hlast⟩ ← expectSome' Γ'.getLast? "extend_det: empty conclusion context (impossible)"
    let ⟨a, hexact⟩ ← expectExact' e.constraint "extend_det: new entry must carry an exact constraint"
      let ⟨hone⟩ ← ensure' (decide (a.val == 1))
        "extend_det: a deterministic assignment x : α is x : α_1"
    let existingMass := Γ.foldl (fun acc entry =>
      if entry.name == e.name then
        match entry.constraint with
        | .exact p => acc + p.val
        | _        => acc
      else acc) (0 : ℚ)
    let ⟨hmass⟩ ← ensure' (decide (existingMass + a.val ≤ 1))
      "extend_det: total exact mass for variable exceeds 1"
    pure ⟨fun hprem hwf => by
      have hmem : p ∈ d.premises := by rw [← hps_eq]; exact List.mem_singleton_self p
      have hpD : Derivable ⟨getCtx p, .distDecl Γ⟩ := by
        have := hprem p hmem; rwa [conclusion_eta, hΓ] at this
      rw [beq_iff_eq] at hlen htake
      rw [conclusion_eta, hΓ']
      exact .extendDet (getCtx d) (getCtx p) Γ Γ' e a hwf hpD hlen htake
        hlast hexact
        (by exact beq_iff_eq.mp (of_decide_eq_true hone)) (of_decide_eq_true hmass)⟩
  | _ => throw "extend_det: internal error"

def checkExtendDet (d : Derivation) : CheckM Unit := do
  let _ ← checkExtendDetC d

/-- `unknown` (Table 1): `{x : α_[0,1] | α ∈ A}` — an opaque distribution
    over ONE process, for a finite support of interest `A`.

    Two things are part of that shape: it is a single variable `x`, and `A`
    is a SET, so the outputs are pairwise distinct.  This matters because
    `unknown` is exactly what produces the opaque `Δ` that IT/IUT admit as
    their observation premise; an entry set spanning several variables is
    not a distribution over one opaque process at all, and repeating an
    output would declare the same event twice. -/
private def checkUnknownPairsC (pairs : List (Derivation × ContextEntry)) :
    CheckM (PLift (∀ pr ∈ pairs,
      getClaim pr.1 = .outputDecl pr.2.output ∧ pr.2.constraint = .unknown)) :=
  match pairs with
  | [] => pure ⟨fun pr hpr => absurd hpr (List.not_mem_nil)⟩
  | (pi, ei) :: rest => do
    let ⟨α, hα⟩ ← expectOutputDecl' (getClaim pi)
      "unknown: every premise must be outputDecl"
    let ⟨ho⟩ ← ensure' (ei.output == α)
      "unknown: premise output ≠ entry output"
    let ⟨hc⟩ ← ensure' (ei.constraint == .unknown)
      "unknown: entry must have unknown constraint"
    let ⟨ih⟩ ← checkUnknownPairsC rest
    pure ⟨by
      intro pr hpr
      rcases List.mem_cons.mp hpr with h | h
      · subst h
        refine ⟨?_, beq_iff_eq.mp hc⟩
        rw [beq_iff_eq.mp ho]; exact hα
      · exact ih pr h⟩

def checkUnknownC (d : Derivation) :
    CheckM (PLift ((∀ p ∈ d.premises, Derivable p.conclusion)
                   → contextWF (getCtx d) = true
                   → Derivable d.conclusion)) := do
  let ⟨Γ0, hΓ⟩ ← expectDistDecl' (getClaim d) "unknown: conclusion must be distDecl"
  let ⟨hlen⟩ ← ensure' (d.premises.length == Γ0.length)
    "unknown: #premises must equal #entries in conclusion context"
  match Γ0 with
  | [] => throw "unknown: the support of interest A must be non-empty"
  | e :: rest => do
    let ⟨hname⟩ ← ensure' (rest.all (fun r => r.name == e.name))
      "unknown: every entry must be about the same variable x"
    let ⟨hdis⟩ ← ensure' (((e :: rest).map (·.output)).eraseDups.length == (e :: rest).length)
      "unknown: the outputs A must be pairwise distinct"
    let ⟨hpairs⟩ ← checkUnknownPairsC (d.premises.zip (e :: rest))
    pure ⟨fun hprem hwf => by
      rw [beq_iff_eq] at hlen hdis
      -- every entry of the support appears as the second component of a zip pair
      have hpick : ∀ e' ∈ (e :: rest), ∃ pi,
          (pi, e') ∈ d.premises.zip (e :: rest) ∧ pi ∈ d.premises := by
        intro e' he'
        obtain ⟨i, hi, hei⟩ := List.getElem_of_mem he'
        have hip : i < d.premises.length := by rw [hlen]; exact hi
        have hiz : i < (d.premises.zip (e :: rest)).length := by
          rw [List.length_zip, hlen]; exact lt_min hi hi
        refine ⟨d.premises[i], ?_, List.getElem_mem hip⟩
        have hz : (d.premises.zip (e :: rest))[i]'hiz = (d.premises[i], (e :: rest)[i]) :=
          List.getElem_zip
        rw [← hei, ← hz]; exact List.getElem_mem hiz
      have hunk : ∀ e' ∈ (e :: rest), e'.constraint = .unknown := by
        intro e' he'
        obtain ⟨pi, hzmem, _⟩ := hpick e' he'
        exact (hpairs _ hzmem).2
      have houts : ∀ pr ∈ (d.premises.map getCtx).zip (e :: rest),
          Derivable ⟨pr.1, .outputDecl pr.2.output⟩ := by
        intro pr hpr
        rw [List.zip_map_left] at hpr
        obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hpr
        obtain ⟨hclaim, _⟩ := hpairs q hq
        have hqmem : q.1 ∈ d.premises := (List.of_mem_zip hq).1
        have hD := hprem q.1 hqmem
        rw [conclusion_eta, hclaim] at hD
        rw [← hqe]; exact hD
      rw [conclusion_eta, hΓ]
      exact .unknown (getCtx d) e rest (d.premises.map getCtx) hwf hname hdis hunk
        (by rw [List.length_map]; exact hlen) houts⟩

def checkUnknown (d : Derivation) : CheckM Unit := do
  let _ ← checkUnknownC d

end TPTND
