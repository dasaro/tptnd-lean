import TPTND.CheckM
import TPTND.WellFormedness
import TPTND.Arithmetic

namespace TPTND

/-! # Bayesian Rules (Table 5, first half)

`I-P`, `E-P`.  Design doc §7.5. -/

-- ============================================================================
-- I-P  (prior family introduction)
-- ============================================================================

def checkIPrior (d : Derivation) : CheckM Unit := do
  let ps ← expectAtLeastPremises d 1 "I-P"
  -- Collect the (aᵢ, bᵢ) pairs from the identity premises, in premise order.
  let mut pairs : List (Prob × Prob) := []
  -- The family's indices (x, α, y, β), read off the first premise and then
  -- required of every other premise: a family may vary only in its values.
  let mut idx : Option (String × Output × String × Output) := none
  for pi in ps do
    let ctx := getCtx pi
    ensure (ctx.length == 1) "I-P: each premise must have a singleton context"
    match ctx, getClaim pi with
    | [e], .identity e' => do
      match e.constraint, e'.constraint with
      | .exact a, .exact b => do
        let here := (e.name, e.output, e'.name, e'.output)
        match idx with
        | none => idx := some here
        | some got =>
          ensure (decide (got == here))
            "I-P: every premise must share the family indices (x, α, y, β)"
        pairs := pairs ++ [(a, b)]
      | _, _ => throw "I-P: context and conclusion entries must be exact"
    | _, _ => throw "I-P: premise must be identity claim with singleton context"
  ensure (decide ((pairs.map (·.2.val)).foldl (· + ·) 0 == 1))
    "I-P: prior weights must sum to 1"
  ensure ((pairs.map (·.1.val)).eraseDups.length == pairs.length)
    "I-P: model values aᵢ must be pairwise distinct"
  ensure (getCtx d |>.isEmpty)
    "I-P: conclusion context must be empty"
  -- The conclusion must record exactly this prior family.
  match getClaim d, idx with
  | .priorFamily fam, some (xN, α, yN, β) => do
    ensure (fam.points == pairs)
      "I-P: conclusion prior family must match the premises"
    ensure (fam.xName == xN && fam.alpha == α && fam.yName == yN && fam.beta == β)
      "I-P: conclusion indices (x, α, y, β) must match the premises"
  | .priorFamily _, none => throw "I-P: no premises to read the family indices from"
  | _, _ => throw "I-P: conclusion must be a priorFamily claim"

-- ============================================================================
-- E-P  (posterior computation)
-- ============================================================================

/-- Single-hypothesis weight: aˢ · (1−a)^{n−s} · b -/
private def bayesWeight (a b : ℚ) (s n : Nat) : ℚ :=
  a ^ s * (1 - a) ^ (n - s) * b

/-- Bayesian posterior for hypothesis j:
    aⱼˢ · (1−aⱼ)^{n−s} · bⱼ  /  Σᵢ aᵢˢ · (1−aᵢ)^{n−s} · bᵢ -/
def bayesianPosterior
    (pairs : List (ℚ × ℚ)) (s n : Nat) (j : Nat) : Option ℚ :=
  let weights := pairs.map (fun ⟨a, b⟩ => bayesWeight a b s n)
  let denom := weights.foldl (· + ·) 0
  if denom == 0 then none
  else match weights[j]? with
    | some w => some (w / denom)
    | none   => none

/-- Extract (aᵢ, bᵢ) pairs from the prior-family premise (I-P), reading them
    from its *conclusion* (validated by `checkIPrior`), not its premises. -/
private def extractPriorFamily (priorDeriv : Derivation) :
    CheckM PriorFamily := do
  ensure (priorDeriv.ruleName == "I-P")
    "E-P: the prior premise must be an I-P node"
  match getClaim priorDeriv with
  | .priorFamily fam => pure fam
  | _ => throw "E-P: prior premise must conclude a priorFamily claim"

def checkEPosterior (d : Derivation) : CheckM Unit := do
  let ps ← expectAtLeastPremises d 2 "E-P"
  match ps with
  | priorDeriv :: rest => do
    -- Extract prior family (aᵢ, bᵢ) pairs
    let fam ← extractPriorFamily priorDeriv
    let pairs := fam.points.map (fun p => (p.1.val, p.2.val))
    ensure (!pairs.isEmpty) "E-P: prior family must be non-empty"
    -- Find the observation premise (a term claim with frequency data)
    let obsDeriv ← match rest with
      | [o] => pure o
      | _   => throw "E-P: expected exactly one observation premise after the prior"
    let obs ← expectTermClaim (getClaim obsDeriv) "E-P"
    ensure (obs.mode == .frequency) "E-P: observation must be frequency mode"
    ensure (obs.output == fam.alpha)
      "E-P: the observation must be about the family's hypothesis output α"
    ensure (obs.samples > 0) "E-P: sample size must be positive"
    -- s = n·f must be a natural number
    let s_rat := (obs.samples : ℚ) * obs.value.val
    ensure (s_rat.den == 1 && s_rat.num ≥ 0)
      "E-P: s = n·f must be a non-negative integer"
    let s := s_rat.num.toNat
    -- Table 5: the conclusion is EXACTLY Γ, x : α_{aⱼ} — the observation's
    -- context plus the selected hypothesis, nothing else.  A superset check
    -- would let a certificate smuggle arbitrary extra assumptions into scope.
    ensure ((getCtx d).all (fun e =>
        e ∈ getCtx obsDeriv ||
        (e.name == fam.xName && e.output == fam.alpha &&
         match e.constraint with | .exact _ => true | _ => false)))
      "E-P: conclusion context must be exactly Γ plus the hypothesis x : α"
    ensure ((getCtx obsDeriv).all (· ∈ getCtx d))
      "E-P: conclusion context must preserve the observation premise's context"
    -- The conclusion is an identity claim with exact posterior
    match getClaim d with
    | .identity concEntry => do
      -- Table 5's conclusion is y : β_b, so the entry is pinned to the
      -- family's target indices, not merely to "some exact value".
      ensure (concEntry.name == fam.yName && concEntry.output == fam.beta)
        "E-P: conclusion must be the family's target y : β"
      match concEntry.constraint with
      | .exact posterior => do
        -- Find which hypothesis j is being selected: the one whose
        -- aⱼ matches the supporting assumption in the conclusion context.
        -- Look for an exact entry in the conclusion context for the
        -- observed variable.
        let concCtx := getCtx d
        -- the supporting hypothesis is x : α_{aⱼ}, identified by the family's
        -- own indices rather than by output alone
        -- The supporting hypothesis x : α_{aⱼ} must be UNIQUE: selecting by
        -- list order from competing hypotheses would let one assumption set
        -- certify two different posteriors.
        match concCtx.filter (fun e =>
          e.name == fam.xName && e.output == fam.alpha &&
          match e.constraint with | .exact _ => true | _ => false) with
        | [se] =>
          match se.constraint with
          | .exact aJ => do
            -- Find j such that pairs[j].1 == aJ
            let jOpt := pairs.findIdx? (fun ⟨a, _⟩ => decide (a == aJ.val))
            match jOpt with
            | some j => do
              match bayesianPosterior pairs s obs.samples j with
              | some expectedPost =>
                ensure (decide (posterior.val == expectedPost))
                  "E-P: posterior value does not match Bayesian update formula"
              | none => throw "E-P: Bayesian posterior computation failed (zero denominator)"
            | none => throw "E-P: supporting hypothesis aⱼ not found in prior family"
          | _ => throw "E-P: unreachable"
        | _ => throw "E-P: exactly one exact hypothesis entry x : α is required in the conclusion context"
      | _ => throw "E-P: conclusion must have an exact constraint"
    | _ => throw "E-P: conclusion must be an identity claim"
  | _ => throw "E-P: need at least a prior + observation premise"

end TPTND
