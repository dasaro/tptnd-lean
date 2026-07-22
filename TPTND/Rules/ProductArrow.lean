import TPTND.CheckM
import TPTND.WellFormedness
import TPTND.Arithmetic

namespace TPTND

/-! # Product and Arrow Rules (Table 4)

`I×`, `E×L`, `E×R`, `I→`, `E→`.  Design doc §7.4. -/

-- ============================================================================
-- I×  (product introduction)
-- ============================================================================

def checkIProd (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "I×"
  match ps with
  | [p1, p2] => do
    ensure d.hasIndependenceWitness
      "I×: explicit independence witness required"
    ensure (independentContexts (getCtx p1) (getCtx p2))
      "I×: premise contexts must constrain disjoint variables (Γ #w Δ)"
    let tc1 ← expectTermClaim (getClaim p1) "I×"
    let tc2 ← expectTermClaim (getClaim p2) "I×"
    let conc ← expectTermClaim (getClaim d) "I×"
    ensure (tc1.mode == tc2.mode && tc1.mode == conc.mode)
      "I×: all must share the same mode"
    -- Only THEORETICAL probabilities multiply.  Realised frequencies do not:
    -- independence constrains the expectation of the joint frequency, not its
    -- observed value.  Two dice each showing "one" with observed frequency 1/2
    -- over the paired runs (1,1),(2,2) have joint frequency 1/2, not 1/4.
    ensure (conc.mode == .expected)
      "I×: only expected probabilities multiply — realised frequencies do not"
    ensure (tc1.samples == tc2.samples && tc1.samples == conc.samples)
      "I×: all must share the same sample size"
    ensure (tc1.prov == tc2.prov && tc1.prov == conc.prov)
      "I×: all must share the same provenance"
    ensure (conc.output == Output.prod tc1.output tc2.output)
      "I×: conclusion output must be product of premise outputs"
    ensure (conc.term == Term.pair tc1.term tc2.term)
      "I×: conclusion term must be ⟨t, u⟩"
    let prod := probMul tc1.value tc2.value
    ensure (decide (conc.value.val == prod.val))
      "I×: conclusion value must be p · q"
    -- Contexts merged
    let merged := mergeContexts [getCtx p1, getCtx p2]
    ensure (contextEqSet (getCtx d) merged)
      "I×: conclusion context must be merge of premise contexts"
  | _ => throw "I×: internal error"

-- ============================================================================
-- E×L  (product elimination left)
-- ============================================================================

def checkEProdL (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "E×L"
  match ps with
  | [p1, p2] => do
    let tc1 ← expectTermClaim (getClaim p1) "E×L"   -- (α×β)_r
    let tc2 ← expectTermClaim (getClaim p2) "E×L"   -- snd(v) : β_q
    let conc ← expectTermClaim (getClaim d) "E×L"   -- fst(v) : α_{r/q}
    ensure (tc1.mode == tc2.mode && tc1.mode == conc.mode)
      "E×L: all must share the same mode"
    -- Same objection as I×: r/q recovers a marginal only for THEORETICAL
    -- probabilities.  On realised frequencies r/q is the observed conditional
    -- P̂(α | β), which is not the observed marginal, so division is restricted
    -- to expected mode.  A marginal frequency is obtained by observing it.
    ensure (conc.mode == .expected)
      "E×L: only expected probabilities divide — realised frequencies do not"
    ensure (tc1.samples == tc2.samples && tc1.samples == conc.samples)
      "E×L: all must share the same sample size"
    ensure (tc1.prov == tc2.prov && tc1.prov == conc.prov)
      "E×L: all must share the same provenance"
    -- Term structure: tc1 = v, tc2 = snd(v), conc = fst(v)
    ensure (tc2.term == Term.snd tc1.term && conc.term == Term.fst tc1.term)
      "E×L: terms must be v, snd(v), fst(v)"
    ensure (contextEqSet (getCtx p1) (getCtx d) && contextEqSet (getCtx p2) (getCtx d))
      "E×L: premises and conclusion must share the same context Γ"
    -- r/q is the marginal only under independence (cf. Semantics.prob_prod_of_indep);
    -- without a witness it is the conditional P(α|β).
    ensure d.hasIndependenceWitness
      "E×L: explicit independence witness required to divide"
    -- tc1 output = α × β, tc2 output = β, conc output = α
    ensure (tc1.output == Output.prod conc.output tc2.output)
      "E×L: first premise must be product of conclusion and second outputs"
    -- 0 < q
    ensure (decide (0 < tc2.value.val))
      "E×L: q must be strictly positive"
    match probDiv tc1.value tc2.value with
    | some quot =>
      ensure (decide (conc.value.val == quot.val))
        "E×L: conclusion value must be r / q"
    | none => throw "E×L: division failed (q = 0 or r/q > 1)"
  | _ => throw "E×L: internal error"

-- ============================================================================
-- E×R  (product elimination right)
-- ============================================================================

def checkEProdR (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "E×R"
  match ps with
  | [p1, p2] => do
    let tc1 ← expectTermClaim (getClaim p1) "E×R"   -- (α×β)_r
    let tc2 ← expectTermClaim (getClaim p2) "E×R"   -- fst(v) : α_p
    let conc ← expectTermClaim (getClaim d) "E×R"   -- snd(v) : β_{r/p}
    ensure (tc1.mode == tc2.mode && tc1.mode == conc.mode)
      "E×R: all must share the same mode"
    -- Same objection as I×: r/q recovers a marginal only for THEORETICAL
    -- probabilities.  On realised frequencies r/q is the observed conditional
    -- P̂(α | β), which is not the observed marginal, so division is restricted
    -- to expected mode.  A marginal frequency is obtained by observing it.
    ensure (conc.mode == .expected)
      "E×R: only expected probabilities divide — realised frequencies do not"
    ensure (tc1.samples == tc2.samples && tc1.samples == conc.samples)
      "E×R: all must share the same sample size"
    ensure (tc1.prov == tc2.prov && tc1.prov == conc.prov)
      "E×R: all must share the same provenance"
    -- Term structure: tc1 = v, tc2 = fst(v), conc = snd(v)
    ensure (tc2.term == Term.fst tc1.term && conc.term == Term.snd tc1.term)
      "E×R: terms must be v, fst(v), snd(v)"
    ensure (contextEqSet (getCtx p1) (getCtx d) && contextEqSet (getCtx p2) (getCtx d))
      "E×R: premises and conclusion must share the same context Γ"
    -- r/q is the marginal only under independence (cf. Semantics.prob_prod_of_indep);
    -- without a witness it is the conditional P(α|β).
    ensure d.hasIndependenceWitness
      "E×R: explicit independence witness required to divide"
    ensure (tc1.output == Output.prod tc2.output conc.output)
      "E×R: first premise must be product of second and conclusion outputs"
    ensure (decide (0 < tc2.value.val))
      "E×R: p must be strictly positive"
    match probDiv tc1.value tc2.value with
    | some quot =>
      ensure (decide (conc.value.val == quot.val))
        "E×R: conclusion value must be r / p"
    | none => throw "E×R: division failed (p = 0 or r/p > 1)"
  | _ => throw "E×R: internal error"

-- ============================================================================
-- I→  (arrow introduction)
-- ============================================================================

def checkIArr (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 1 "I→"
  match ps with
  | [p] => do
    let tc ← expectTermClaim (getClaim p) "I→"
    let conc ← expectTermClaim (getClaim d) "I→"
    -- Conclusion term must be [x]t  (lam)
    match conc.term with
    | .lam x body => do
      ensure (body == tc.term)
        "I→: lambda body must match premise term"
      -- Conclusion output must be (α ⇒ β)  where β = premise output
      match conc.output with
      | .arr α a β => do
        ensure (β == tc.output) "I→: arrow target must match premise output"
        ensure (decide (conc.value.val == tc.value.val))
          "I→: arrow probability must equal the premise probability"
        -- Discharged assumption: exactly one entry x : α_a in premise context,
        -- and the arrow's annotation must BE that assumption's value.
        let discharged := (getCtx p).filter (fun e =>
          e.name == x && e.output == α &&
          match e.constraint with | .exact _ => true | _ => false)
        ensure (discharged.length == 1)
          "I→: must discharge exactly one exact entry for x : α"
        match discharged with
        | [de] =>
          ensure (de.constraint == Constraint.exact a)
            "I→: arrow annotation must be the discharged assumption's value"
          -- Conclusion context = premise context minus the discharged entry
          let expectedCtx := (getCtx p).filter (· != de)
          ensure (contextEqSet (getCtx d) expectedCtx)
            "I→: conclusion context must be premise context minus discharged entry"
        | _ => throw "I→: unreachable"
        ensure (conc.samples == tc.samples) "I→: sample size must be preserved"
        ensure (conc.prov == tc.prov) "I→: provenance must be preserved"
        ensure (conc.mode == tc.mode) "I→: mode must be preserved"
      | _ => throw "I→: conclusion output must be an arrow type"
    | _ => throw "I→: conclusion term must be a lambda"
  | _ => throw "I→: internal error"

-- ============================================================================
-- E→  (arrow elimination)
-- ============================================================================

def checkEArr (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "E→"
  match ps with
  | [p1, p2] => do
    let tc1 ← expectTermClaim (getClaim p1) "E→"   -- [x]t : (α ⇒_a β)_q
    let tc2 ← expectTermClaim (getClaim p2) "E→"   -- u : α_r
    let conc ← expectTermClaim (getClaim d) "E→"   -- ([x]t · u) : β_{qr}
    ensure (tc1.mode == tc2.mode && tc1.mode == conc.mode)
      "E→: all must share the same mode"
    ensure (tc1.samples == tc2.samples && tc1.samples == conc.samples)
      "E→: all must share the same sample size"
    ensure (tc1.prov == tc2.prov && tc1.prov == conc.prov)
      "E→: all must share the same provenance"
    -- The major premise must genuinely be an abstraction [x]t, else a
    -- fabricated arrow claim could be eliminated.
    match tc1.term with
    | .lam _ _ => pure ()
    | _ => throw "E→: major premise term must be an abstraction [x]t"
    match tc1.output with
    | .arr α _ β => do
      ensure (α == tc2.output)
        "E→: arrow source must match second premise output"
      ensure (β == conc.output)
        "E→: arrow target must match conclusion output"
      -- Conclusion term = app tc1.term tc2.term
      ensure (conc.term == Term.app tc1.term tc2.term)
        "E→: conclusion term must be application"
      let prod := probMul tc1.value tc2.value
      ensure (decide (conc.value.val == prod.val))
        "E→: conclusion value must be q · r"
      -- Contexts merged
      let merged := mergeContexts [getCtx p1, getCtx p2]
      ensure (contextEqSet (getCtx d) merged)
        "E→: conclusion context must be merge of premise contexts"
    | _ => throw "E→: first premise output must be an arrow type"
  | _ => throw "E→: internal error"

end TPTND
