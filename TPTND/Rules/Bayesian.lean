import TPTND.CheckM
import TPTND.Spec
import TPTND.WellFormedness
import TPTND.Arithmetic

namespace TPTND

/-! # Bayesian Rules (Table 5, first half)

`I-P`, `E-P`.  Design doc §7.5. -/

-- ============================================================================
-- I-P  (prior family introduction)
-- ============================================================================

/-- Premises of an I-P family after the first: each must be a singleton
    exact identity sharing the family indices (forward mode).  Returns one
    row `((e, e'), (a, b))` per premise, with the map equations tying the
    rows to the premises positionally. -/
private def checkIPriorRestC (idx : String × Output × String × Output) :
    (ps : List Derivation) →
    CheckM {rows : List ((ContextEntry × ContextEntry) × (Prob × Prob)) //
      ps.map getCtx = rows.map (fun r => [r.1.1]) ∧
      ps.map getClaim = rows.map (fun r => Claim.identity r.1.2) ∧
      ∀ r ∈ rows, r.1.1.constraint = .exact r.2.1 ∧
        r.1.2.constraint = .exact r.2.2 ∧
        (r.1.1.name, r.1.1.output, r.1.2.name, r.1.2.output) = idx}
  | [] => pure ⟨[], rfl, rfl, fun r hr => absurd hr (List.not_mem_nil)⟩
  | pi :: rest => do
    let ⟨_⟩ ← ensure' ((getCtx pi).length == 1)
      "I-P: each premise must have a singleton context"
    match hctx : getCtx pi, hcl : getClaim pi with
    | [e], .identity e' =>
      match hce : e.constraint, hce' : e'.constraint with
      | .exact a, .exact b => do
        let ⟨hidx⟩ ← ensure' (decide (idx == (e.name, e.output, e'.name, e'.output)))
          "I-P: every premise must share the family indices (x, α, y, β)"
        let ⟨rows, hprop⟩ ← checkIPriorRestC idx rest
        pure ⟨((e, e'), (a, b)) :: rows, by
          refine ⟨?_, ?_, ?_⟩
          · rw [List.map_cons, List.map_cons, hctx, hprop.1]
          · rw [List.map_cons, List.map_cons, hcl, hprop.2.1]
          · intro r hr
            rcases List.mem_cons.mp hr with h | h
            · subst h
              exact ⟨hce, hce',
                (beq_iff_eq.mp (of_decide_eq_true hidx)).symm⟩
            · exact hprop.2.2 r h⟩
      | _, _ => throw "I-P: context and conclusion entries must be exact"
    | _, _ => throw "I-P: premise must be identity claim with singleton context"

def checkIPriorC (d : Derivation) :
    CheckM (PLift ((∀ p ∈ d.premises, Derivable p.conclusion)
                   → contextWF (getCtx d) = true
                   → Derivable d.conclusion)) := do
  let ⟨_⟩ ← ensure' (d.premises.length ≥ 1)
    s!"I-P: expected at least 1 premise(s), got {d.premises.length}"
  match hps : d.premises with
  | [] => throw "I-P: no premises to read the family indices from"
  | p0 :: rest => do
    -- The family's indices (x, α, y, β) are read off the first premise and
    -- then required of every other premise: a family may vary only in its
    -- values.
    let ⟨_⟩ ← ensure' ((getCtx p0).length == 1)
      "I-P: each premise must have a singleton context"
    match hctx0 : getCtx p0, hcl0 : getClaim p0 with
    | [e0], .identity e0' =>
      match hce0 : e0.constraint, hce0' : e0'.constraint with
      | .exact a0, .exact b0 => do
        let ⟨rows, hprop⟩ ←
          checkIPriorRestC (e0.name, e0.output, e0'.name, e0'.output) rest
        let ⟨hsum⟩ ← ensure' (decide
            ((((((e0, e0'), (a0, b0)) :: rows).map (·.2)).map (·.2.val)).foldl
              (· + ·) 0 == 1))
          "I-P: prior weights must sum to 1"
        let ⟨hdup⟩ ← ensure'
            ((((((e0, e0'), (a0, b0)) :: rows).map (·.2)).map (·.1.val)).eraseDups.length
              == ((((e0, e0'), (a0, b0)) :: rows).map (·.2)).length)
          "I-P: model values aᵢ must be pairwise distinct"
        let ⟨hemp⟩ ← ensure' (getCtx d |>.isEmpty)
          "I-P: conclusion context must be empty"
        -- The conclusion must record exactly this prior family.
        match hfam : getClaim d with
        | .priorFamily fam => do
          let ⟨hpts⟩ ← ensure' (fam.points == (((e0, e0'), (a0, b0)) :: rows).map (·.2))
            "I-P: conclusion prior family must match the premises"
          let ⟨hix⟩ ← ensure' (fam.xName == e0.name && fam.alpha == e0.output &&
              fam.yName == e0'.name && fam.beta == e0'.output)
            "I-P: conclusion indices (x, α, y, β) must match the premises"
          pure ⟨fun hprem hwf => by
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hix
            obtain ⟨⟨⟨hxN, hα⟩, hyN⟩, hβ⟩ := hix
            rw [beq_iff_eq] at hxN hα hyN hβ hpts
            -- full row list, tied positionally to d.premises
            have hAllCtx : d.premises.map getCtx
                = ((((e0, e0'), (a0, b0)) :: rows).map (fun r => [r.1.1])) := by
              rw [hps, List.map_cons, List.map_cons, hctx0, hprop.1]
            have hAllCl : d.premises.map getClaim
                = ((((e0, e0'), (a0, b0)) :: rows).map
                    (fun r => Claim.identity r.1.2)) := by
              rw [hps, List.map_cons, List.map_cons, hcl0, hprop.2.1]
            have hAllRow : ∀ r ∈ (((e0, e0'), (a0, b0)) :: rows),
                r.1.1.constraint = .exact r.2.1 ∧
                r.1.2.constraint = .exact r.2.2 ∧
                (r.1.1.name, r.1.1.output, r.1.2.name, r.1.2.output)
                  = (e0.name, e0.output, e0'.name, e0'.output) := by
              intro r hr
              rcases List.mem_cons.mp hr with h | h
              · subst h; exact ⟨hce0, hce0', rfl⟩
              · exact hprop.2.2 r h
            have hplen : d.premises.length
                = ((((e0, e0'), (a0, b0)) :: rows)).length := by
              have := congrArg List.length hAllCtx
              simpa using this
            -- positional facts for each row
            have hrowfacts : ∀ i (hi : i < (((e0, e0'), (a0, b0)) :: rows).length),
                getCtx (d.premises[i]'(by rw [hplen]; exact hi))
                    = [((((e0, e0'), (a0, b0)) :: rows)[i]).1.1] ∧
                getClaim (d.premises[i]'(by rw [hplen]; exact hi))
                    = Claim.identity ((((e0, e0'), (a0, b0)) :: rows)[i]).1.2 := by
              intro i hi
              have hip : i < d.premises.length := by rw [hplen]; exact hi
              constructor
              · have h1 : (d.premises.map getCtx)[i]'(by simpa using hip)
                    = (((((e0, e0'), (a0, b0)) :: rows).map (fun r => [r.1.1]))[i]'
                        (by simpa using hi)) := by
                  simp only [hAllCtx]
                simpa only [List.getElem_map] using h1
              · have h2 : (d.premises.map getClaim)[i]'(by simpa using hip)
                    = (((((e0, e0'), (a0, b0)) :: rows).map
                        (fun r => Claim.identity r.1.2))[i]'(by simpa using hi)) := by
                  simp only [hAllCl]
                simpa only [List.getElem_map] using h2
            -- the constructor's zip-shaped hypotheses
            have hzip : ((((e0, e0'), (a0, b0)) :: rows).map (·.1.1)).zip
                ((((e0, e0'), (a0, b0)) :: rows).map (·.1.2))
                = (((e0, e0'), (a0, b0)) :: rows).map (fun r => (r.1.1, r.1.2)) :=
              List.zip_map'
            have hprems : ∀ pr ∈ ((((e0, e0'), (a0, b0)) :: rows).map (·.1.1)).zip
                ((((e0, e0'), (a0, b0)) :: rows).map (·.1.2)),
                Derivable ⟨[pr.1], .identity pr.2⟩ := by
              intro pr hpr
              rw [hzip] at hpr
              obtain ⟨r, hr, hre⟩ := List.mem_map.mp hpr
              obtain ⟨i, hi, hri⟩ := List.getElem_of_mem hr
              have hip : i < d.premises.length := by rw [hplen]; exact hi
              obtain ⟨hc, hl⟩ := hrowfacts i hi
              have hpmem : d.premises[i] ∈ p0 :: rest := by
                rw [← hps]; exact List.getElem_mem hip
              have hD := hprem _ hpmem
              rw [conclusion_eta, hc, hl, hri] at hD
              rw [← hre]; exact hD
            have hidxf : ∀ pr ∈ ((((e0, e0'), (a0, b0)) :: rows).map (·.1.1)).zip
                ((((e0, e0'), (a0, b0)) :: rows).map (·.1.2)),
                pr.1.name = fam.xName ∧ pr.1.output = fam.alpha ∧
                pr.2.name = fam.yName ∧ pr.2.output = fam.beta := by
              intro pr hpr
              rw [hzip] at hpr
              obtain ⟨r, hr, hre⟩ := List.mem_map.mp hpr
              have h4 := (hAllRow r hr).2.2
              rw [Prod.ext_iff, Prod.ext_iff, Prod.ext_iff] at h4
              obtain ⟨h41, h42, h43, h44⟩ := h4
              rw [← hre]
              exact ⟨h41.trans hxN.symm, h42.trans hα.symm,
                     h43.trans hyN.symm, h44.trans hβ.symm⟩
            have hexactf : ∀ q ∈ (((((e0, e0'), (a0, b0)) :: rows).map (·.1.1)).zip
                ((((e0, e0'), (a0, b0)) :: rows).map (·.1.2))).zip
                ((((e0, e0'), (a0, b0)) :: rows).map (·.2)),
                q.1.1.constraint = .exact q.2.1 ∧
                q.1.2.constraint = .exact q.2.2 := by
              intro q hq
              rw [hzip, List.zip_map'] at hq
              obtain ⟨r, hr, hre⟩ := List.mem_map.mp hq
              obtain ⟨h1, h2, _⟩ := hAllRow r hr
              rw [← hre]
              exact ⟨h1, h2⟩
            have hgc : getCtx d = [] := by
              simpa [List.isEmpty_iff] using hemp
            rw [conclusion_eta, hfam, hgc]
            exact .iPrior ((((e0, e0'), (a0, b0)) :: rows).map (·.1.1))
              ((((e0, e0'), (a0, b0)) :: rows).map (·.1.2))
              ((((e0, e0'), (a0, b0)) :: rows).map (·.2)) fam
              (by simp) (by simp) (by simp) hprems hidxf hexactf hpts
              (beq_iff_eq.mp (of_decide_eq_true hsum))
              (beq_iff_eq.mp hdup)⟩
        | _ => throw "I-P: conclusion must be a priorFamily claim"
      | _, _ => throw "I-P: context and conclusion entries must be exact"
    | _, _ => throw "I-P: premise must be identity claim with singleton context"

def checkIPrior (d : Derivation) : CheckM Unit := do
  let _ ← checkIPriorC d

-- ============================================================================
-- E-P  (posterior computation)
-- ============================================================================

def checkEPosteriorC (d : Derivation) :
    CheckM (PLift ((∀ p ∈ d.premises, Derivable p.conclusion)
                   → contextWF (getCtx d) = true
                   → Derivable d.conclusion)) := do
  let ⟨_⟩ ← ensure' (d.premises.length ≥ 2)
    s!"E-P: expected at least 2 premise(s), got {d.premises.length}"
  match hps : d.premises with
  | [] => throw "E-P: need at least a prior + observation premise"
  | priorDeriv :: rest => do
    -- The prior premise must be an I-P node concluding a priorFamily claim.
    -- (Reading the family from its conclusion; validated by `checkIPrior`.)
    ensure (priorDeriv.ruleName == "I-P")
      "E-P: the prior premise must be an I-P node"
    match hfam : getClaim priorDeriv with
    | .priorFamily fam => do
      let ⟨hfne⟩ ← ensure' (!(fam.points.map (fun p => (p.1.val, p.2.val))).isEmpty)
        "E-P: prior family must be non-empty"
      -- Find the observation premise (a term claim with frequency data)
      match hro : rest with
      | [obsDeriv] => do
        match hobs : getClaim obsDeriv with
        | .term obs => do
          let ⟨hmode⟩ ← ensure' (obs.mode == .frequency)
            "E-P: observation must be frequency mode"
          let ⟨hα⟩ ← ensure' (obs.output == fam.alpha)
            "E-P: the observation must be about the family's hypothesis output α"
          let ⟨hn⟩ ← ensure' (obs.samples > 0) "E-P: sample size must be positive"
          -- s = n·f must be a natural number
          let ⟨hnat⟩ ← ensure' (((obs.samples : ℚ) * obs.value.val).den == 1 &&
              ((obs.samples : ℚ) * obs.value.val).num ≥ 0)
            "E-P: s = n·f must be a non-negative integer"
          -- Table 5: the conclusion is EXACTLY Γ, x : α_{aⱼ} — the observation's
          -- context plus the selected hypothesis, nothing else.  A superset check
          -- would let a certificate smuggle arbitrary extra assumptions into scope.
          let ⟨hsub⟩ ← ensure' ((getCtx d).all (fun e =>
              e ∈ getCtx obsDeriv ||
              (e.name == fam.xName && e.output == fam.alpha &&
               match e.constraint with | .exact _ => true | _ => false)))
            "E-P: conclusion context must be exactly Γ plus the hypothesis x : α"
          let ⟨hpres⟩ ← ensure' ((getCtx obsDeriv).all (· ∈ getCtx d))
            "E-P: conclusion context must preserve the observation premise's context"
          -- The conclusion is an identity claim with exact posterior
          match hcid : getClaim d with
          | .identity concEntry => do
            -- Table 5's conclusion is y : β_b, so the entry is pinned to the
            -- family's target indices, not merely to "some exact value".
            let ⟨hcname⟩ ← ensure' (concEntry.name == fam.yName &&
                concEntry.output == fam.beta)
              "E-P: conclusion must be the family's target y : β"
            match hcex : concEntry.constraint with
            | .exact posterior => do
              -- The supporting hypothesis x : α_{aⱼ} must be UNIQUE: selecting by
              -- list order from competing hypotheses would let one assumption set
              -- certify two different posteriors.
              match hse : (getCtx d).filter (fun e =>
                  e.name == fam.xName && e.output == fam.alpha &&
                  match e.constraint with | .exact _ => true | _ => false) with
              | [se] =>
                match hsec : se.constraint with
                | .exact aJ => do
                  -- Find j such that pairs[j].1 == aJ
                  match hfind : (fam.points.map (fun p => (p.1.val, p.2.val))).findIdx?
                      (fun ⟨a, _⟩ => decide (a == aJ.val)) with
                  | some j => do
                    match hbp : bayesianPosterior
                        (fam.points.map (fun p => (p.1.val, p.2.val)))
                        ((obs.samples : ℚ) * obs.value.val).num.toNat
                        obs.samples j with
                    | some expectedPost => do
                      let ⟨hveq⟩ ← ensure' (decide (posterior.val == expectedPost))
                        "E-P: posterior value does not match Bayesian update formula"
                      pure ⟨fun hprem hwf => by
                        have hm1 : priorDeriv ∈ [priorDeriv, obsDeriv] := by simp
                        have hm2 : obsDeriv ∈ [priorDeriv, obsDeriv] := by simp
                        have hpD : Derivable ⟨getCtx priorDeriv,
                            .priorFamily fam⟩ := by
                          have := hprem priorDeriv hm1
                          rwa [conclusion_eta, hfam] at this
                        have hoD : Derivable ⟨getCtx obsDeriv, .term obs⟩ := by
                          have := hprem obsDeriv hm2
                          rwa [conclusion_eta, hobs] at this
                        rw [Bool.and_eq_true] at hnat hcname
                        obtain ⟨hden, hnum⟩ := hnat
                        obtain ⟨hcnm, hcout⟩ := hcname
                        rw [beq_iff_eq] at hmode hα hden hcnm hcout
                        have hfne' : fam.points ≠ [] := by
                          intro hcon
                          rw [hcon] at hfne; simp at hfne
                        have hpost : bayesianPosterior
                            (fam.points.map (fun p => (p.1.val, p.2.val)))
                            ((obs.samples : ℚ) * obs.value.val).num.toNat
                            obs.samples j = some posterior.val := by
                          rw [beq_iff_eq.mp (of_decide_eq_true hveq)]
                          exact hbp
                        rw [conclusion_eta, hcid]
                        exact .ePosterior (getCtx priorDeriv) (getCtx obsDeriv)
                          (getCtx d) fam obs concEntry se aJ posterior j
                          hwf hpD hoD hfne' hmode hα (of_decide_eq_true hn)
                          hden (of_decide_eq_true hnum) hsub hpres
                          hcnm hcout hcex hse hsec hfind hpost⟩
                    | none =>
                      throw "E-P: Bayesian posterior computation failed (zero denominator)"
                  | none =>
                    throw "E-P: supporting hypothesis aⱼ not found in prior family"
                | _ => throw "E-P: unreachable"
              | _ =>
                throw "E-P: exactly one exact hypothesis entry x : α is required in the conclusion context"
            | _ => throw "E-P: conclusion must have an exact constraint"
          | _ => throw "E-P: conclusion must be an identity claim"
        | _ => throw "E-P: expected a term claim"
      | _ => throw "E-P: expected exactly one observation premise after the prior"
    | _ => throw "E-P: prior premise must conclude a priorFamily claim"

def checkEPosterior (d : Derivation) : CheckM Unit := do
  let _ ← checkEPosteriorC d

end TPTND
