import TPTND

open TPTND

/-! # Soundness regression suite

Each derivation below exploits a hole the audit found in the checker.
After the Tier-1 fixes, `checkDerivation` must REJECT every one of them.
A `✗ ACCEPTED` line marks a re-opened soundness hole. -/

private def P (n d : Nat) : Prob := clampProb ((n : ℚ) / d)
private def nd (rule : String) (prems : List Derivation)
    (ctx : Context) (claim : Claim) : Derivation :=
  .node rule prems ⟨ctx, claim⟩ false
private def mkS (s : String) : Finset String := {s}
private def mkS2 (a b : String) : Finset String := {a, b}
private def ndW (rule : String) (prems : List Derivation)
    (ctx : Context) (claim : Claim) : Derivation :=
  .node rule prems ⟨ctx, claim⟩ true

/-- Assert the checker rejects a derivation that exploits a closed hole. -/
private def expectReject (name : String) (d : Derivation) : IO Bool := do
  match checkDerivation d with
  | .error msg => IO.println s!"  ✓ REJECTED  {name}\n      ↳ {msg}"; pure true
  | .ok ()     => IO.println s!"  ✗ ACCEPTED (SOUNDNESS BUG!)  {name}"; pure false

private def α : Output := Output.atom "A"
private def βo : Output := Output.atom "B"

-- 1. Expectation leaf fabricating an expected value ≠ the entry's exact value.
private def attackExpectation : Derivation :=
  let e : ContextEntry := ⟨"r", mkS "S", α, .exact (P 1 100)⟩
  nd "expectation" [] [e] (.term ⟨.expected, Term.atom "r", 50, α, P 99 100, mkS "ρ"⟩)

-- 2. Experiment leaf whose output disagrees with its support entry.
--    Single-run shape kept legal (1 sample, value 1) so the rejection exercises
--    the SUPPORT-ENTRY check, not an earlier gate.
private def attackExperiment : Derivation :=
  let e : ContextEntry := ⟨"r", mkS "S", α, .unknown⟩
  nd "experiment" [] [e] (.term ⟨.frequency, Term.atom "r", 1, βo, P 1 1, mkS "ρ"⟩)

-- 3. A node whose conclusion context violates wf(Γ) (per-variable mass > 1).
private def attackWf : Derivation :=
  let obsE : ContextEntry := ⟨"r", mkS "S", α, .unknown⟩
  -- distinct OUTPUTS for one variable: these are disjoint events, so their
  -- masses genuinely add (0.7 + 0.7 = 1.4 > 1).  Two entries for the SAME
  -- (variable, output) would be competing hypotheses and must NOT be summed.
  let heavy1 : ContextEntry := ⟨"y", mkS "S", α, .exact (P 7 10)⟩
  let heavy2 : ContextEntry := ⟨"y", mkS "S", βo, .exact (P 7 10)⟩
  nd "obs" [] [obsE, heavy1, heavy2]
    (.term ⟨.frequency, Term.atom "r", 10, α, P 3 10, mkS "ρ"⟩)

-- 4. Eliminating a two-sample (𝒬) UTrust certificate via EUT (the keystone).
private def attackTwoSampleElim : Derivation :=
  let tB := Term.atom "b"; let tW := Term.atom "w"
  let fB := P 40 100; let fW := P 20 100
  let ci := twoSampleCI 100 100 fB fW
  let obsB : ContextEntry := ⟨"b", mkS "B", α, .unknown⟩
  let obsW : ContextEntry := ⟨"w", mkS "W", α, .unknown⟩
  let dObsB := nd "obs" [] [obsB] (.term ⟨.frequency, tB, 100, α, fB, mkS "sB"⟩)
  let dObsW := nd "obs" [] [obsW] (.term ⟨.frequency, tW, 100, α, fW, mkS "sW"⟩)
  let utrust : TrustClaim := .untrust .twoSample tB 100 α fB fW ci (mkS "sB" ∪ mkS "sW")
  let dIUT2 := nd "IUT2" [dObsB, dObsW] [obsB, obsW] (.trust utrust)
  let compl := match ci with
    | .interval lo hi => Constraint.outsideInterval lo hi
    | o => o
  let xu : ContextEntry := ⟨"xu", mkS "B", α, compl⟩
  nd "EUT" [dIUT2] [obsB, obsW, xu] (.term ⟨.frequency, tB, 100, α, fB, mkS "sB"⟩)

-- 5. I+ over ¬a and b: no shared atom, but the events overlap (b ⊆ ¬a).
--    All three nodes share one context so the rejection exercises the
--    DISJOINTNESS check, not the context-sharing gate.
private def attackIPlusNeg : Derivation :=
  let a := Output.atom "a"; let notA := Output.neg a; let b := Output.atom "b"
  let t := Term.atom "t"
  let ctx : Context := [⟨"t", mkS "S", notA, .unknown⟩, ⟨"t", mkS "S", b, .unknown⟩]
  let dP1 := nd "obs" [] ctx (.term ⟨.frequency, t, 10, notA, P 3 10, mkS "s"⟩)
  let dP2 := nd "obs" [] ctx (.term ⟨.frequency, t, 10, b, P 2 10, mkS "s"⟩)
  nd "I+" [dP1, dP2] ctx
    (.term ⟨.frequency, t, 10, Output.sum notA b, P 5 10, mkS "s"⟩)

-- 6. E+L whose conclusion is about a different term than the premises.
private def attackEPlusTerm : Derivation :=
  let s := Output.sum α βo
  let t := Term.atom "t"; let u := Term.atom "u"
  let dSum := nd "obs" [] [⟨"t", mkS "S", s, .unknown⟩]
    (.term ⟨.frequency, t, 10, s, P 5 10, mkS "p"⟩)
  let dA := nd "obs" [] [⟨"t", mkS "S", α, .unknown⟩]
    (.term ⟨.frequency, t, 10, α, P 3 10, mkS "p"⟩)
  nd "E+L" [dSum, dA] [⟨"t", mkS "S", s, .unknown⟩]
    (.term ⟨.frequency, u, 10, βo, P 2 10, mkS "p"⟩)

-- 7. INEx with premises ordered smaller-rate-first (would clamp to a false "fair").
private def attackINExOrder : Derivation :=
  let t1 := Term.atom "x"; let t2 := Term.atom "y"
  let f := P 20 100; let g := P 40 100
  let ci := twoSampleCI 100 100 f g
  let tc1 : TermClaim := ⟨.frequency, t1, 100, α, f, mkS "sx"⟩
  let tc2 : TermClaim := ⟨.frequency, t2, 100, α, g, mkS "sy"⟩
  let dO1 := nd "obs" [] [⟨"x", mkS "X", α, .unknown⟩] (.term tc1)
  let dO2 := nd "obs" [] [⟨"y", mkS "Y", α, .unknown⟩] (.term tc2)
  nd "INEx" [dO1, dO2] [⟨"x", mkS "X", α, .unknown⟩, ⟨"y", mkS "Y", α, .unknown⟩]
    (.comparison (.noExcess tc1 tc2 (P 0 1) ci))

-- 8. IT2 whose conclusion context smuggles in a forged assumption entry
--    that appears in neither premise (context must be Γ,Δ exactly).
private def attackForgedCtx : Derivation :=
  let t1 := Term.atom "x"; let t2 := Term.atom "y"
  let f := P 30 100
  let ci := twoSampleCI 100 100 f f
  let e1 : ContextEntry := ⟨"x", mkS "X", α, .unknown⟩
  let e2 : ContextEntry := ⟨"y", mkS "Y", α, .unknown⟩
  let forged : ContextEntry := ⟨"z", mkS "Z", α, .exact (P 9 10)⟩
  let dO1 := nd "obs" [] [e1] (.term ⟨.frequency, t1, 100, α, f, mkS "sx"⟩)
  let dO2 := nd "obs" [] [e2] (.term ⟨.frequency, t2, 100, α, f, mkS "sy"⟩)
  nd "IT2" [dO1, dO2] [e1, e2, forged]
    (.trust (.trust .twoSample t1 100 α f f ci (mkS "sx" ∪ mkS "sy")))


-- 9. I→ whose arrow annotation is NOT the discharged assumption's value.
private def attackArrowAnnotation : Derivation :=
  let A := Output.atom "A"; let B := Output.atom "B"
  let xE : ContextEntry := ⟨"x", mkS "S", A, .exact (P 3 10)⟩
  let bE : ContextEntry := ⟨"t", mkS "S", B, .unknown⟩
  let prem := nd "obs" [] [bE, xE]
    (.term ⟨.frequency, Term.atom "t", 10, B, P 1 2, mkS "ρ"⟩)
  -- discharges x : A_{3/10} but claims the arrow was built at 9/10
  nd "I→" [prem] [bE]
    (.term ⟨.frequency, Term.lam "x" (Term.atom "t"), 10,
            .arr A (P 9 10) B, P 1 2, mkS "ρ"⟩)

-- 10. E→ eliminating a fabricated arrow whose term is not an abstraction.
private def attackArrowNotLambda : Derivation :=
  let A := Output.atom "A"; let B := Output.atom "B"
  let fE : ContextEntry := ⟨"f", mkS "S", .arr A (P 3 10) B, .unknown⟩
  let uE : ContextEntry := ⟨"u", mkS "S", A, .unknown⟩
  let dArr := nd "obs" [] [fE]
    (.term ⟨.frequency, Term.atom "f", 10, .arr A (P 3 10) B, P 1 2, mkS "ρ"⟩)
  let dU := nd "obs" [] [uE]
    (.term ⟨.frequency, Term.atom "u", 10, A, P 3 10, mkS "ρ"⟩)
  nd "E→" [dArr, dU] [fE, uE]
    (.term ⟨.frequency, Term.app (Term.atom "f") (Term.atom "u"), 10, B,
            P 15 100, mkS "ρ"⟩)

-- 11. IT importing its model with IDENTITY*₂, conjuring the benchmark p.
private def attackConjuredModel : Derivation :=
  let A := Output.atom "A"
  let t := Term.atom "u"
  let f := P 50 100
  let p := P 20 100
  let ci := binomialCI 100 f p
  let srcE : ContextEntry := ⟨"z", mkS "S", A, .exact (P 1 2)⟩
  let modelE : ContextEntry := ⟨"w", mkS "S", A, .exact p⟩
  let obsE : ContextEntry := ⟨"u", mkS "O", A, .unknown⟩
  let dModel := nd "identity_model" [] [srcE] (.identity modelE)
  let dObs := nd "obs" [] [obsE] (.term ⟨.frequency, t, 100, A, f, mkS "σ"⟩)
  nd "IUT" [dModel, dObs] [srcE, obsE]
    (.trust (.untrust .oneSample t 100 A f p ci (mkS "σ")))

-- 12. SAMPLING fed a rich obs claim instead of single-run experiments.
private def attackSamplingNotExperiment : Derivation :=
  let A := Output.atom "A"
  let e1 : ContextEntry := ⟨"t", mkS "S", A, .unknown⟩
  let o1 := nd "obs" [] [e1] (.term ⟨.frequency, Term.atom "t", 100, A, P 42 100, mkS "σ1"⟩)
  let o2 := nd "obs" [] [e1] (.term ⟨.frequency, Term.atom "t", 100, A, P 42 100, mkS "σ2"⟩)
  nd "sampling" [o1, o2] [e1]
    (.term ⟨.frequency, Term.atom "t", 2, A, P 1 1, mkS2 "σ1" "σ2"⟩)


-- 13. I× multiplying two OBSERVED FREQUENCIES.  Two dice, 2 runs each, paired
--     run-by-run as the calculus prescribes: d rolls 1 then 2, g rolls 1 then 2.
--     Each shows "one" with observed frequency 1/2, so the rule computes 1/4 —
--     but the joint sample is (1,1),(2,2), whose realised joint frequency is 1/2.
--     Independence constrains the EXPECTATION of the joint frequency, never its
--     observed value, so frequencies must not be multiplied even with a witness.
private def attackProdFrequency : Derivation :=
  let one := Output.atom "one"
  let eD : ContextEntry := ⟨"d", mkS "roll", one, .unknown⟩
  let eG : ContextEntry := ⟨"g", mkS "roll", one, .unknown⟩
  let oD := nd "obs" [] [eD] (.term ⟨.frequency, Term.atom "d", 2, one, P 1 2, mkS "σ"⟩)
  let oG := nd "obs" [] [eG] (.term ⟨.frequency, Term.atom "g", 2, one, P 1 2, mkS "σ"⟩)
  ndW "I×" [oD, oG] [eD, eG]
    (.term ⟨.frequency, Term.pair (Term.atom "d") (Term.atom "g"), 2,
            Output.prod one one, P 1 4, mkS "σ"⟩)

-- 14. I× squaring ONE variable against itself: ⟨x,x⟩ : (α × α)_{a²}.
--     Independence is a property of distinct variables; a vacuous test that
--     accepts Γ ⫫ Γ would certify P(X = α ∧ X = α) = a².  The true value
--     here is 1/2, not 1/4.
private def attackProdSelfSquare : Derivation :=
  let one := Output.atom "one"
  let eX : ContextEntry := ⟨"x", mkS "s", one, .exact (P 1 2)⟩
  let ex := nd "expectation" [] [eX] (.term ⟨.expected, Term.atom "x", 4, one, P 1 2, mkS "σ"⟩)
  ndW "I×" [ex, ex] [eX]
    (.term ⟨.expected, Term.pair (Term.atom "x") (Term.atom "x"), 4,
            Output.prod one one, P 1 4, mkS "σ"⟩)


-- 15. Two deterministic assignments for one variable:
--     {x_A : 0, x_A : 1} :: distribution.  Reading x : α as x : α₁ makes
--     additivity bite: a second deterministic value overflows the variable's
--     mass — otherwise I+ would give x_A : (0 + 1)₂ for a 50/50 process.
private def attackExtendDetTwice : Derivation :=
  let zero := Output.atom "zero"
  let one := Output.atom "one"
  let e0 : ContextEntry := ⟨"xA", mkS "A", zero, .exact (P 1 1)⟩
  let e1 : ContextEntry := ⟨"xA", mkS "A", one, .exact (P 1 1)⟩
  let dBase := nd "base" [] [] (.distDecl [])
  let d1 := nd "extend_det" [dBase] [] (.distDecl [e0])
  nd "extend_det" [d1] [] (.distDecl [e0, e1])

-- 16. A deterministic x : Heads alongside the probabilistic x : Heads_{1/2}:
--     two masses for one (variable, output) pair.  Lookups could then read
--     either 1 or 1/2 for the same pair, and I+ would give (Heads+Tails)_{3/2}.
private def attackDetVsProbabilistic : Derivation :=
  let hd := Output.atom "Heads"
  let tl := Output.atom "Tails"
  let eH : ContextEntry := ⟨"x", mkS "coin", hd, .exact (P 1 2)⟩
  let eT : ContextEntry := ⟨"x", mkS "coin", tl, .exact (P 1 2)⟩
  let eDet : ContextEntry := ⟨"x", mkS "coin", hd, .exact (P 1 1)⟩
  let dBase := nd "base" [] [] (.distDecl [])
  let d1 := nd "extend" [dBase] [] (.distDecl [eH])
  let d2 := nd "extend" [d1] [] (.distDecl [eH, eT])
  nd "extend_det" [d2] [] (.distDecl [eH, eT, eDet])

-- 17. E×L dividing OBSERVED FREQUENCIES: r/q is the observed conditional
--     P̂(α | β), not the observed marginal of α.
private def attackProdElimFrequency : Derivation :=
  let a := Output.atom "a"
  let b := Output.atom "b"
  let v := Term.atom "v"
  let e : ContextEntry := ⟨"v", mkS "s", Output.prod a b, .unknown⟩
  let dJoint := nd "obs" [] [e]
    (.term ⟨.frequency, v, 4, Output.prod a b, P 1 4, mkS "σ"⟩)
  let dSnd := nd "obs" [] [e]
    (.term ⟨.frequency, Term.snd v, 4, b, P 1 2, mkS "σ"⟩)
  ndW "E×L" [dJoint, dSnd] [e]
    (.term ⟨.frequency, Term.fst v, 4, a, P 1 2, mkS "σ"⟩)


-- 18. I-P family whose premises disagree on the indices: two hypotheses about
--     variable x and one smuggled in about a different variable z.  The printed
--     rule is {x : α_{aᵢ} ⊢ y : β_{bᵢ}} — one x and one y throughout.
private def attackPriorMixedIndices : Derivation :=
  let A := Output.atom "A"
  let B := Output.atom "B"
  let mk := fun (xn : String) (a b : Prob) =>
    nd "identity_model" [] [⟨xn, mkS "h", A, .exact a⟩]
      (.identity ⟨"y", mkS "p", B, .exact b⟩)
  let p1 := mk "x" (P 1 4) (P 1 2)
  let p2 := mk "z" (P 3 4) (P 1 2)     -- different hypothesis variable
  nd "I-P" [p1, p2] []
    (.priorFamily { xName := "x", alpha := A, yName := "y", beta := B
                  , points := [(P 1 4, P 1 2), (P 3 4, P 1 2)] })

-- 19. E-P whose conclusion is not the family's target y : β — it reports the
--     posterior against a different output, which the index-free family could
--     not distinguish.
private def attackPosteriorWrongTarget : Derivation :=
  let A := Output.atom "A"
  let B := Output.atom "B"
  let C := Output.atom "C"
  let mk := fun (a b : Prob) =>
    nd "identity_model" [] [⟨"x", mkS "h", A, .exact a⟩]
      (.identity ⟨"y", mkS "p", B, .exact b⟩)
  let fam : PriorFamily :=
    { xName := "x", alpha := A, yName := "y", beta := B
    , points := [(P 1 4, P 1 2), (P 3 4, P 1 2)] }
  let dPrior := nd "I-P" [mk (P 1 4) (P 1 2), mk (P 3 4) (P 1 2)] []
    (.priorFamily fam)
  let obsE : ContextEntry := ⟨"t", mkS "o", A, .unknown⟩
  let dObs := nd "obs" [] [obsE] (.term ⟨.frequency, Term.atom "t", 4, A, P 1 2, mkS "σ"⟩)
  let supp : ContextEntry := ⟨"x", mkS "h", A, .exact (P 1 4)⟩
  -- conclusion names output C, not the family's target β = B
  nd "E-P" [dPrior, dObs] [supp, obsE]
    (.identity ⟨"y", mkS "post", C, .exact (P 1 2)⟩)


-- 18. ET re-entering the audited interval on the MODEL variable instead of the
--     observed one.  Reading A ties x_u to the observed term, so the audited
--     range can no longer be bolted onto whichever assumption is convenient —
--     here it would constrain the benchmark m by the interval derived FROM it.
private def attackETWrongVariable : Derivation :=
  let a := Output.atom "HR"
  let t := Term.atom "u"
  let f := P 1 2
  let pv := P 1 2
  let ci := binomialCI 100 f pv
  let mE : ContextEntry := ⟨"m", mkS "model", a, .exact pv⟩
  let uE : ContextEntry := ⟨"u", mkS "run", a, .unknown⟩
  let dModel := nd "identity" [] [mE] (.identity mE)
  let dObs := nd "obs" [] [uE] (.term ⟨.frequency, t, 100, a, f, mkS "σ"⟩)
  let dIT := nd "IT" [dModel, dObs] [mE, uE]
    (.trust (.trust .oneSample t 100 a f pv ci (mkS "σ")))
  nd "ET" [dIT] [mE, uE, ⟨"m", mkS "model", a, ci⟩]
    (.term ⟨.frequency, t, 100, a, f, mkS "σ"⟩)


-- 19. `unknown` spanning two variables.  The printed conclusion is
--     {x : α_[0,1], …, x : ω_[0,1]} — ONE variable.  An entry set spanning
--     several variables is not a distribution over one opaque process, yet it
--     is exactly the shape IT/IUT accept as their observation premise.
private def attackUnknownTwoVars : Derivation :=
  let a := Output.atom "a"
  let b := Output.atom "b"
  let dA := nd "output_atom" [] [] (.outputDecl a)
  let dB := nd "output_atom" [] [] (.outputDecl b)
  nd "unknown" [dA, dB] []
    (.distDecl [⟨"x", mkS "s", a, .unknown⟩, ⟨"y", mkS "s", b, .unknown⟩])

-- 20. `unknown` repeating an output.  A is the finite SUPPORT of interest, a
--     set, so the same event cannot be declared twice.
private def attackUnknownDupOutput : Derivation :=
  let a := Output.atom "a"
  let dA1 := nd "output_atom" [] [] (.outputDecl a)
  let dA2 := nd "output_atom" [] [] (.outputDecl a)
  nd "unknown" [dA1, dA2] []
    (.distDecl [⟨"x", mkS "s", a, .unknown⟩, ⟨"x", mkS "s", a, .unknown⟩])


-- 22. IT model laundered through WeakeningS: a fabricated IDENTITY*₂ entry
--     forwarded under a new rule name.  The old ruleName guard saw only the
--     immediate premise; the structural check (me ∈ Γm) sees through any
--     claim-preserving wrapper.
private def attackLaunderedModel : Derivation :=
  let xE : ContextEntry := ⟨"x", mkS "S", α, .exact (P 1 2)⟩
  let tE : ContextEntry := ⟨"t", mkS "O", βo, .unknown⟩
  let mFab : ContextEntry := ⟨"m", mkS "F", βo, .exact (P 3 10)⟩
  let dIdModel := nd "identity_model" [] [xE] (.identity mFab)
  let dIdStar := nd "identity_star" [] [tE] (.identity tE)
  let dWeak := ndW "WeakeningS" [dIdModel, dIdStar] [xE, tE] (.identity mFab)
  let dObs := nd "obs" [] [tE] (.term ⟨.frequency, Term.atom "t", 10, βo, P 3 10, mkS "σ"⟩)
  nd "IT" [dWeak, dObs] [xE, tE]
    (.trust (.trust .oneSample (Term.atom "t") 10 βo (P 3 10) (P 3 10)
      (binomialCI 10 (P 3 10) (P 3 10)) (mkS "σ")))

-- 23. wf(Γ) mass overflow laundered by a trivial [0,1] entry: under min-based
--     groupMass the vacuous hypothesis zeroed its group's committed mass.
private def attackMassLaundering : Derivation :=
  let rE : ContextEntry := ⟨"r", mkS "S", α, .unknown⟩
  let h1 : ContextEntry := ⟨"y", mkS "S", α, .exact (P 7 10)⟩
  let hTriv : ContextEntry := ⟨"y", mkS "S", α, .interval (P 0 1) (P 1 1)⟩
  let h2 : ContextEntry := ⟨"y", mkS "S", βo, .exact (P 7 10)⟩
  nd "obs" [] [rE, h1, hTriv, h2]
    (.term ⟨.frequency, Term.atom "r", 10, α, P 3 10, mkS "ρ"⟩)

-- 24. Cherry-picking contradictory hypotheses: {x:HR_0.2, x:HR_0.8} passes wf
--     (competing hypotheses), but citing EITHER as the model let the same data
--     certify both Trust and UTrust.  The unique-hypothesis condition forces a
--     Contraction to a single value before a group can be cited.
private def attackCherryPick : Derivation :=
  let HR := Output.atom "HR"
  let m1 : ContextEntry := ⟨"x", mkS "S", HR, .exact (P 2 10)⟩
  let m2 : ContextEntry := ⟨"x", mkS "S", HR, .exact (P 8 10)⟩
  let uE : ContextEntry := ⟨"u", mkS "O", HR, .unknown⟩
  let ctx : Context := [m1, m2, uE]
  let dId := nd "identity_star" [] ctx (.identity m2)
  let dObs := nd "obs" [] ctx (.term ⟨.frequency, Term.atom "u", 100, HR, P 2 10, mkS "τ"⟩)
  nd "IUT" [dId, dObs] ctx
    (.trust (.untrust .oneSample (Term.atom "u") 100 HR (P 2 10) (P 8 10)
      (binomialCI 100 (P 2 10) (P 8 10)) (mkS "τ")))


-- 26. ET behind a structural wrapper, with a FORGED conclusion provenance.
--     The old checker read provenance from the premise tree (obsProvOf): a
--     claim-preserving WeakeningS hid the observation, obsProvOf found
--     nothing, and the conclusion's σ went entirely unchecked.  Provenance
--     now travels IN the certificate, so the forgery is caught regardless
--     of wrapping.
private def attackForgedProvenance : Derivation :=
  let a := Output.atom "HR"
  let t := Term.atom "u"
  let f := P 1 2
  let ci := binomialCI 100 f f
  let mE : ContextEntry := ⟨"m", mkS "model", a, .exact f⟩
  let uE : ContextEntry := ⟨"u", mkS "run", a, .unknown⟩
  let kE : ContextEntry := ⟨"k", mkS "other", a, .unknown⟩
  let dModel := nd "identity" [] [mE] (.identity mE)
  let dObs := nd "obs" [] [uE] (.term ⟨.frequency, t, 100, a, f, mkS "σ"⟩)
  let dIT := nd "IT" [dModel, dObs] [mE, uE]
    (.trust (.trust .oneSample t 100 a f f ci (mkS "σ")))
  let dK := nd "identity_star" [] [kE] (.identity kE)
  let dWrap := ndW "WeakeningS" [dIT, dK] [mE, uE, kE]
    (.trust (.trust .oneSample t 100 a f f ci (mkS "σ")))
  nd "ET" [dWrap] [mE, uE, kE, ⟨"u", mkS "run", a, ci⟩]
    (.term ⟨.frequency, t, 100, a, f, mkS "FORGED"⟩)

-- 28. ENEx re-emitting the left observation's frequency under a FORGED
--     provenance.  The conclusion provenance was previously unconstrained, so
--     the elimination could relabel a judgement's data lineage to any set —
--     laundering the provenance-disjointness discipline that update/IT2/IEx
--     rely on (one dataset re-minted as two "independent" ones).
private def attackENExForgedProv : Derivation :=
  let tx := Term.atom "x"; let ty := Term.atom "y"
  let f := P 30 100
  let ci := twoSampleCI 100 100 f f
  let tc1 : TermClaim := ⟨.frequency, tx, 100, α, f, mkS "sx"⟩
  let tc2 : TermClaim := ⟨.frequency, ty, 100, α, f, mkS "sy"⟩
  let ex : ContextEntry := ⟨"x", mkS "X", α, .unknown⟩
  let ey : ContextEntry := ⟨"y", mkS "Y", α, .unknown⟩
  let dO1 := nd "obs" [] [ex] (.term tc1)
  let dO2 := nd "obs" [] [ey] (.term tc2)
  let dNE := nd "INEx" [dO1, dO2] [ex, ey]
    (.comparison (.noExcess tc1 tc2 (P 0 1) ci))
  let p := P 1 10
  let mE : ContextEntry := ⟨"m", mkS "bench", α, .exact p⟩
  let dModel := nd "identity" [] [mE] (.identity mE)
  let shifted : Constraint :=
    match ci with
    | .interval lo hi => .interval (clampProb (p.val + lo.val)) (clampProb (p.val + hi.val))
    | c => c
  -- everything valid EXCEPT the conclusion provenance (FORGED ≠ sx)
  nd "ENEx" [dNE, dModel] [ex, ey, mE, ⟨"x", mkS "X", α, shifted⟩]
    (.term ⟨.frequency, tx, 100, α, f, mkS "FORGED"⟩)

-- 27. E-P smuggling an extra assumption into its conclusion context.  The
--     context was previously only superset-checked, so a certificate could
--     carry arbitrary additional assumptions into scope.
private def attackPosteriorSmuggle : Derivation :=
  let FPR := Output.atom "FPR"
  let hypE : ContextEntry := ⟨"h", mkS "hyp", FPR, .exact (P 1 2)⟩
  let wE : ContextEntry := ⟨"w", mkS "prior", FPR, .exact (P 1 1)⟩
  let obsE : ContextEntry := ⟨"q", mkS "pilot", FPR, .unknown⟩
  let smuggled : ContextEntry := ⟨"z", mkS "nowhere", FPR, .exact (P 9 10)⟩
  let dPoint := nd "identity_model" [] [hypE] (.identity wE)
  let dPrior := nd "I-P" [dPoint] []
    (.priorFamily { xName := "h", alpha := FPR, yName := "w", beta := FPR,
                    points := [(P 1 2, P 1 1)] })
  let dObs := nd "obs" [] [obsE] (.term ⟨.frequency, Term.atom "q", 4, FPR, P 1 2, mkS "π"⟩)
  let post := clampProb ((bayesianPosterior [((P 1 2).val, (P 1 1).val)] 2 4 0).getD 0)
  nd "E-P" [dPrior, dObs] [hypE, obsE, smuggled]
    (.identity ⟨"w", mkS "prior", FPR, .exact post⟩)

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println " Soundness regression: every attack must be REJECTED"
  IO.println "═══════════════════════════════════════════════════════════\n"
  let results ← List.mapM (fun (nm, d) => expectReject nm d) [
    ("Expectation fabricates a value ≠ the entry's exact prob", attackExpectation),
    ("Experiment output disagrees with support entry", attackExperiment),
    ("wf(Γ): conclusion context mass exceeds 1", attackWf),
    ("EUT eliminating a two-sample (𝒬) certificate", attackTwoSampleElim),
    ("I+ over ¬a and b (unsound syntactic disjointness)", attackIPlusNeg),
    ("E+L conclusion term ≠ premise term", attackEPlusTerm),
    ("INEx premises ordered smaller-first (f < g)", attackINExOrder),
    ("IT2 conclusion context smuggles a forged assumption", attackForgedCtx),
    ("I→ arrow annotation ≠ the discharged assumption", attackArrowAnnotation),
    ("E→ eliminating a non-abstraction (fabricated arrow)", attackArrowNotLambda),
    ("IT importing its benchmark via IDENTITY*₂ (conjured p)", attackConjuredModel),
    ("sampling fed rich obs claims, not single runs", attackSamplingNotExperiment),
    ("I× multiplying observed frequencies (joint freq is 1/2, not 1/4)", attackProdFrequency),
    ("I× squaring one variable against itself ⟨x,x⟩:(α×α)_{a²}", attackProdSelfSquare),
    ("extend_det twice: {x_A : 0, x_A : 1} (double deterministic)", attackExtendDetTwice),
    ("deterministic x : Heads alongside x : Heads_{1/2}", attackDetVsProbabilistic),
    ("E×L dividing observed frequencies (conditional ≠ marginal)", attackProdElimFrequency),
    ("I-P premises disagreeing on the family indices (x, α, y, β)", attackPriorMixedIndices),
    ("E-P conclusion not the family's target y : β", attackPosteriorWrongTarget),
    ("unknown spanning two variables (not one opaque process)", attackUnknownTwoVars),
    ("unknown declaring the same output twice (A is a set)", attackUnknownDupOutput),
    ("ET re-entering the audited interval on the model variable", attackETWrongVariable),
    ("IT model laundered through WeakeningS (fabricated benchmark)", attackLaunderedModel),
    ("wf mass overflow laundered by a trivial [0,1] entry", attackMassLaundering),
    ("IUT citing one of two contradictory hypotheses (cherry-pick)", attackCherryPick),
    ("ET behind a wrapper with forged conclusion provenance", attackForgedProvenance),
    ("ENEx re-emitting the left frequency under forged provenance", attackENExForgedProv),
    ("E-P smuggling an extra assumption into its conclusion", attackPosteriorSmuggle)]
  let ok := results.filter id |>.length
  IO.println s!"\n═══════════════════════════════════════════════════════════"
  IO.println s!" {ok}/{results.length} attacks correctly rejected"
  IO.println "═══════════════════════════════════════════════════════════"
