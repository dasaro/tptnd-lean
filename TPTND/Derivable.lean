import TPTND

/-! # Faithfulness: `Derivable` spec and `checker_sound`

`Derivable s` is the calculus written directly as a `Prop`: it holds iff
the sequent `s` is the conclusion of a TPTND rule whose premises are
derivable and whose side conditions hold.  The constructors transcribe
the paper's rules (Tables 1–7) for the **certified fragment** — 24 of
the 41 dispatched rules:

  identity, identity_star, identity_model, obs, experiment,
  expectation, update, sampling-adjacent leaves,
  IT, IUT, IT2, IUT2, IEx, INEx, ET, EUT, EEx,
  I+, E+L, E+R, I×, E×L, E×R, WeakeningS, WeakeningD

— the entire statistical spine exercised by the COMPAS and HMDA case
studies plus the connective and weakening rules.  The remaining rules
(sampling, I→/E→, I-P/E-P, ETex, ENEx, Contraction,
output/distribution declarations) are future work; the top-level
theorem `checker_sound` is accordingly guarded by
`Derivation.inFragment` — consult `fragmentRule` below for the
authoritative list.

The soundness (faithfulness) theorems show that whenever the checker
accepts a node of the fragment, its conclusion is `Derivable`: the
checker cannot accept a certificate outside the calculus.  A few
checker strengthenings beyond the printed rules (provenance pinning in
ET/EUT, the unique-hypothesis condition on cited model entries, the
independence-witness node flag) are deliberately not reflected in
`Derivable` — the checker is strictly more restrictive there, which
preserves the theorem's direction. -/

namespace TPTND

/-- Probabilities with equal values are equal (the proof fields are
    propositions). -/
theorem Prob.val_inj {a b : Prob} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

/-- Term claims with equal fields are equal. -/
theorem TermClaim.ext {a b : TermClaim}
    (h1 : a.mode = b.mode) (h2 : a.term = b.term) (h3 : a.samples = b.samples)
    (h4 : a.output = b.output) (h5 : a.value = b.value) (h6 : a.prov = b.prov) :
    a = b := by
  cases a; cases b; simp_all

-- ============================================================================
-- The specification
-- ============================================================================

/-- The TPTND calculus as a specification: one constructor per rule of
    the certified fragment, side conditions transcribed from the paper
    (each rule fires only on a wf conclusion context, per §2.3). -/
inductive Derivable : Sequent → Prop where
  /-- Identity (Table 2, singleton form): a singleton context entry
      concludes itself. -/
  | identity (e : ContextEntry)
      (hwf : contextWF [e] = true) :
      Derivable ⟨[e], .identity e⟩
  /-- Identity (Table 2, lookup form): cite an assumption of Γ. -/
  | identityStar (Γ : Context) (e : ContextEntry)
      (hwf : contextWF Γ = true)
      (hmem : e ∈ Γ) :
      Derivable ⟨Γ, .identity e⟩
  /-- Obs (Table 2): record an observed frequency. -/
  | obs (Γ : Context) (tc : TermClaim)
      (hwf : contextWF Γ = true)
      (hmode : tc.mode = .frequency)
      (hprov : tc.prov.Nonempty)
      (hn : tc.samples > 0)
      (hatom : isAtomicTerm tc.term = true)
      (hden : ((tc.samples : ℚ) * tc.value.val).den = 1)
      (hnum : ((tc.samples : ℚ) * tc.value.val).num ≥ 0)
      (hsupp : (supportEntries Γ tc.term tc.output).length = 1) :
      Derivable ⟨Γ, .term tc⟩
  /-- Update (Table 3): pool two frequency observations from disjoint
      sources into their sample-size-weighted average.  Premises and
      conclusion share the context up to set-equality. -/
  | update (Γ Γ1 Γ2 : Context) (tc1 tc2 : TermClaim) (w : Prob)
      (hwf : contextWF Γ = true)
      (h1 : Derivable ⟨Γ1, .term tc1⟩)
      (h2 : Derivable ⟨Γ2, .term tc2⟩)
      (hc1 : contextEqSet Γ1 Γ = true)
      (hc2 : contextEqSet Γ2 Γ = true)
      (hm1 : tc1.mode = .frequency) (hm2 : tc2.mode = .frequency)
      (hterm : tc1.term = tc2.term)
      (hout : tc1.output = tc2.output)
      (hdisj : Provenance.disjoint tc1.prov tc2.prov = true)
      (hwval : weightedFreq tc1.samples tc1.value tc2.samples tc2.value = some w) :
      Derivable ⟨Γ, .term ⟨.frequency, tc1.term,
        tc1.samples + tc2.samples, tc1.output, w, tc1.prov ∪ tc2.prov⟩⟩
  /-- IT (Table 5): one-sample trust — the model probability lies inside
      the score-test interval. -/
  | it (Γm Γo ctx : Context) (me : ContextEntry) (tc : TermClaim) (p : Prob)
      (hwf : contextWF ctx = true)
      (hm : Derivable ⟨Γm, .identity me⟩)
      (ho : Derivable ⟨Γo, .term tc⟩)
      (hexact : me.constraint = .exact p)
      (hmode : tc.mode = .frequency)
      (hout : me.output = tc.output)
      (hin : inConstraint p (binomialCI tc.samples tc.value p) = true)
      (hctx : contextEqSet ctx (mergeContexts [Γm, Γo]) = true)
      (hmem : me ∈ Γm) :
      Derivable ⟨ctx, .trust (.trust .oneSample tc.term tc.samples tc.output
        tc.value p (binomialCI tc.samples tc.value p) tc.prov)⟩
  /-- IUT (Table 5): one-sample untrust — the model probability lies
      outside the interval. -/
  | iut (Γm Γo ctx : Context) (me : ContextEntry) (tc : TermClaim) (p : Prob)
      (hwf : contextWF ctx = true)
      (hm : Derivable ⟨Γm, .identity me⟩)
      (ho : Derivable ⟨Γo, .term tc⟩)
      (hexact : me.constraint = .exact p)
      (hmode : tc.mode = .frequency)
      (hout : me.output = tc.output)
      (hnotin : notInConstraint p (binomialCI tc.samples tc.value p) = true)
      (hctx : contextEqSet ctx (mergeContexts [Γm, Γo]) = true)
      (hmem : me ∈ Γm) :
      Derivable ⟨ctx, .trust (.untrust .oneSample tc.term tc.samples tc.output
        tc.value p (binomialCI tc.samples tc.value p) tc.prov)⟩
  /-- IT2 (Table 5): two-sample trust — 0 inside the difference interval. -/
  | it2 (Γl Γr ctx : Context) (tcL tcR : TermClaim)
      (hwf : contextWF ctx = true)
      (hl : Derivable ⟨Γl, .term tcL⟩)
      (hr : Derivable ⟨Γr, .term tcR⟩)
      (hml : tcL.mode = .frequency) (hmr : tcR.mode = .frequency)
      (hout : tcL.output = tcR.output)
      (hdisj : Provenance.disjoint tcL.prov tcR.prov = true)
      (hord : tcL.value.val ≥ tcR.value.val)
      (hin : inConstraint Prob.zero
        (twoSampleCI tcL.samples tcR.samples tcL.value tcR.value) = true)
      (hctx : contextEqSet ctx (mergeContexts [Γl, Γr]) = true) :
      Derivable ⟨ctx, .trust (.trust .twoSample tcL.term tcL.samples tcL.output
        tcL.value tcR.value
        (twoSampleCI tcL.samples tcR.samples tcL.value tcR.value)
        (tcL.prov ∪ tcR.prov))⟩
  /-- IUT2 (Table 5): two-sample untrust — 0 outside the interval. -/
  | iut2 (Γl Γr ctx : Context) (tcL tcR : TermClaim)
      (hwf : contextWF ctx = true)
      (hl : Derivable ⟨Γl, .term tcL⟩)
      (hr : Derivable ⟨Γr, .term tcR⟩)
      (hml : tcL.mode = .frequency) (hmr : tcR.mode = .frequency)
      (hout : tcL.output = tcR.output)
      (hdisj : Provenance.disjoint tcL.prov tcR.prov = true)
      (hord : tcL.value.val ≥ tcR.value.val)
      (hnotin : notInConstraint Prob.zero
        (twoSampleCI tcL.samples tcR.samples tcL.value tcR.value) = true)
      (hctx : contextEqSet ctx (mergeContexts [Γl, Γr]) = true) :
      Derivable ⟨ctx, .trust (.untrust .twoSample tcL.term tcL.samples tcL.output
        tcL.value tcR.value
        (twoSampleCI tcL.samples tcR.samples tcL.value tcR.value)
        (tcL.prov ∪ tcR.prov))⟩
  /-- IEx (Table 6): certify a directional excess with its size. -/
  | iEx (Γl Γr ctx : Context) (tcL tcR : TermClaim) (diff : Prob)
      (hwf : contextWF ctx = true)
      (hl : Derivable ⟨Γl, .term tcL⟩)
      (hr : Derivable ⟨Γr, .term tcR⟩)
      (hml : tcL.mode = .frequency) (hmr : tcR.mode = .frequency)
      (hout : tcL.output = tcR.output)
      (hdisj : Provenance.disjoint tcL.prov tcR.prov = true)
      (hnotin : notInConstraint Prob.zero
        (twoSampleCI tcL.samples tcR.samples tcL.value tcR.value) = true)
      (hctx : contextEqSet ctx (mergeContexts [Γl, Γr]) = true)
      (hsub : probSub tcL.value tcR.value = some diff) :
      Derivable ⟨ctx, .comparison (.excess tcL tcR diff
        (twoSampleCI tcL.samples tcR.samples tcL.value tcR.value))⟩
  /-- INEx (Table 6): certify the absence of a significant excess. -/
  | iNEx (Γl Γr ctx : Context) (tcL tcR : TermClaim) (diff : Prob)
      (hwf : contextWF ctx = true)
      (hl : Derivable ⟨Γl, .term tcL⟩)
      (hr : Derivable ⟨Γr, .term tcR⟩)
      (hml : tcL.mode = .frequency) (hmr : tcR.mode = .frequency)
      (hout : tcL.output = tcR.output)
      (hdisj : Provenance.disjoint tcL.prov tcR.prov = true)
      (hord : tcL.value.val ≥ tcR.value.val)
      (hin : inConstraint Prob.zero
        (twoSampleCI tcL.samples tcR.samples tcL.value tcR.value) = true)
      (hctx : contextEqSet ctx (mergeContexts [Γl, Γr]) = true) :
      Derivable ⟨ctx, .comparison (.noExcess tcL tcR diff
        (twoSampleCI tcL.samples tcR.samples tcL.value tcR.value))⟩
  /-- ET (Table 6): re-enter the frequency layer under a one-sample Trust
      certificate; the audited interval is re-entered on the observed
      term's own variable `x_u`, so Contraction can then select a value. -/
  | et (Γp ctx : Context) (t : Term) (n : Nat) (α : Output)
      (f p : Prob) (interval : Constraint) (σ : Provenance)
      (xu : ContextEntry)
      (hwf : contextWF ctx = true)
      (hp : Derivable ⟨Γp, .trust (.trust .oneSample t n α f p interval σ)⟩)
      (hpres : Γp.all (· ∈ ctx) = true)
      (hfilter : ctx.filter (· ∉ Γp) = [xu])
      (hxout : xu.output = α)
      (hxc : xu.constraint = interval)
      (hxdesig : t = Term.atom xu.name) :
      Derivable ⟨ctx, .term ⟨.frequency, t, n, α, f, σ⟩⟩
  /-- EUT (Table 6): as ET but for UTrust; the re-entered assumption on
      `x_u` carries the complement interval. -/
  | eut (Γp ctx : Context) (t : Term) (n : Nat) (α : Output)
      (f p : Prob) (interval : Constraint) (σ : Provenance)
      (xu : ContextEntry)
      (hwf : contextWF ctx = true)
      (hp : Derivable ⟨Γp, .trust (.untrust .oneSample t n α f p interval σ)⟩)
      (hpres : Γp.all (· ∈ ctx) = true)
      (hfilter : ctx.filter (· ∉ Γp) = [xu])
      (hxout : xu.output = α)
      (hxc : xu.constraint = Constraint.complementOf interval)
      (hxdesig : t = Term.atom xu.name) :
      Derivable ⟨ctx, .term ⟨.frequency, t, n, α, f, σ⟩⟩
  /-- EEx (Table 6): under an Excess certificate and an exact benchmark
      for the right group, bound the left observation by the shifted
      interval [p+ℓ, p+h]. -/
  | eEx (Γe Γm ctx : Context) (tcL tcR : TermClaim) (diff : Prob)
      (lo hi : Prob) (me se : ContextEntry) (p : Prob) (σ : Provenance)
      (hwf : contextWF ctx = true)
      (he : Derivable ⟨Γe, .comparison (.excess tcL tcR diff (.interval lo hi))⟩)
      (hm : Derivable ⟨Γm, .identity me⟩)
      (hexact : me.constraint = .exact p)
      (hmout : me.output = tcR.output)
      (hsum : (probAdd p hi).isSome = true)
      (hbase : (mergeContexts [Γe, Γm]).all (· ∈ ctx) = true)
      (hse : se ∈ ctx)
      (hseout : se.output = tcL.output)
      (hsec : se.constraint = .interval (clampProb (p.val + lo.val))
                                        (clampProb (p.val + hi.val)))
      (hmem : me ∈ Γm) :
      Derivable ⟨ctx, .term ⟨.frequency, tcL.term, tcL.samples, tcL.output,
        tcL.value, σ⟩⟩
  /-- EXPERIMENT (Table 2): a single run.  One sample, value 1, one
      provenance token, and a unique supporting assumption in Γ. -/
  | experiment (Γ : Context) (tc : TermClaim)
      (hwf : contextWF Γ = true)
      (hprov : tc.prov.card = 1)
      (hatom : isAtomicTerm tc.term = true)
      (hmode : tc.mode = .frequency)
      (hn : tc.samples = 1)
      (hval : tc.value.val = 1)
      (hsupp : (supportEntries Γ tc.term tc.output).length = 1) :
      Derivable ⟨Γ, .term tc⟩
  /-- IDENTITY*₂ (Table 2): from a singleton exact assumption conclude an
      exact model judgement whose value need not equal it.  This is what
      makes general Bayesian priors `bᵢ ≠ aᵢ` derivable. -/
  | identityModel (e e' : ContextEntry) (p q : Prob)
      (hwf : contextWF [e] = true)
      (he : e.constraint = .exact p)
      (he' : e'.constraint = .exact q) :
      Derivable ⟨[e], .identity e'⟩
  /-- EXPECTATION (Table 2): the expected value carried by the unique exact
      supporting assumption. -/
  | expectation (Γ : Context) (tc : TermClaim) (e : ContextEntry) (a : Prob)
      (hwf : contextWF Γ = true)
      (hmode : tc.mode = .expected)
      (hprov : tc.prov.card = 1)
      (hn : tc.samples > 0)
      (hatom : isAtomicTerm tc.term = true)
      (hsupp : supportEntries Γ tc.term tc.output = [e])
      (hexact : e.constraint = .exact a)
      (hval : tc.value.val = a.val) :
      Derivable ⟨Γ, .term tc⟩
  /-- WeakeningS (Table 7): merge two independent judgements' contexts,
      keeping the first judgement. -/
  | weakeningS (Γ Δ ctx : Context) (J K : Claim)
      (hwf : contextWF ctx = true)
      (hJ : Derivable ⟨Γ, J⟩)
      (hK : Derivable ⟨Δ, K⟩)
      (hindep : independentContexts Γ Δ = true)
      (hctx : contextEqSet ctx (mergeContexts [Γ, Δ]) = true) :
      Derivable ⟨ctx, J⟩
  /-- I+ (Table 3): add the frequencies of two syntactically disjoint outputs
      of the same term. -/
  | iPlus (Γ Γ1 Γ2 : Context) (tc1 tc2 : TermClaim) (s : Prob)
      (hwf : contextWF Γ = true)
      (h1 : Derivable ⟨Γ1, .term tc1⟩) (h2 : Derivable ⟨Γ2, .term tc2⟩)
      (hc1 : contextEqSet Γ1 Γ = true) (hc2 : contextEqSet Γ2 Γ = true)
      (hmode : tc1.mode = tc2.mode) (hsamp : tc1.samples = tc2.samples)
      (hprov : tc1.prov = tc2.prov) (hterm : tc1.term = tc2.term)
      (hdisj : Output.syntacticallyDisjoint tc1.output tc2.output = true)
      (hadd : probAdd tc1.value tc2.value = some s) :
      Derivable ⟨Γ, .term ⟨tc1.mode, tc1.term, tc1.samples,
        Output.sum tc1.output tc2.output, s, tc1.prov⟩⟩
  /-- E+L (Table 3): recover the right summand `γ` by subtraction, the summands
      being syntactically disjoint. -/
  | ePlusL (Γ Γ1 Γ2 : Context) (tc1 tc2 : TermClaim) (γ : Output) (diff : Prob)
      (hwf : contextWF Γ = true)
      (h1 : Derivable ⟨Γ1, .term tc1⟩) (h2 : Derivable ⟨Γ2, .term tc2⟩)
      (hc1 : contextEqSet Γ1 Γ = true) (hc2 : contextEqSet Γ2 Γ = true)
      (hmode : tc1.mode = tc2.mode) (hsamp : tc1.samples = tc2.samples)
      (hprov : tc1.prov = tc2.prov) (hterm : tc1.term = tc2.term)
      (hdisj : Output.syntacticallyDisjoint tc2.output γ = true)
      (hsum : tc1.output = Output.sum tc2.output γ)
      (hsub : probSub tc1.value tc2.value = some diff) :
      Derivable ⟨Γ, .term ⟨tc1.mode, tc1.term, tc1.samples, γ, diff, tc1.prov⟩⟩
  /-- E+R (Table 3): recover the left summand `γ` by subtraction. -/
  | ePlusR (Γ Γ1 Γ2 : Context) (tc1 tc2 : TermClaim) (γ : Output) (diff : Prob)
      (hwf : contextWF Γ = true)
      (h1 : Derivable ⟨Γ1, .term tc1⟩) (h2 : Derivable ⟨Γ2, .term tc2⟩)
      (hc1 : contextEqSet Γ1 Γ = true) (hc2 : contextEqSet Γ2 Γ = true)
      (hmode : tc1.mode = tc2.mode) (hsamp : tc1.samples = tc2.samples)
      (hprov : tc1.prov = tc2.prov) (hterm : tc1.term = tc2.term)
      (hdisj : Output.syntacticallyDisjoint γ tc2.output = true)
      (hsum : tc1.output = Output.sum γ tc2.output)
      (hsub : probSub tc1.value tc2.value = some diff) :
      Derivable ⟨Γ, .term ⟨tc1.mode, tc1.term, tc1.samples, γ, diff, tc1.prov⟩⟩
  /-- I× (Table 4): pair two independent components; the joint probability is
      the product.  Restricted to expected mode — realised frequencies do not
      multiply. -/
  | iProd (Γ Γ1 Γ2 : Context) (tc1 tc2 : TermClaim)
      (hwf : contextWF Γ = true)
      (h1 : Derivable ⟨Γ1, .term tc1⟩) (h2 : Derivable ⟨Γ2, .term tc2⟩)
      (hindep : independentContexts Γ1 Γ2 = true)
      (hmode : tc1.mode = tc2.mode) (hexp : tc1.mode = .expected)
      (hsamp : tc1.samples = tc2.samples) (hprov : tc1.prov = tc2.prov)
      (hctx : contextEqSet Γ (mergeContexts [Γ1, Γ2]) = true) :
      Derivable ⟨Γ, .term ⟨tc1.mode, Term.pair tc1.term tc2.term, tc1.samples,
        Output.prod tc1.output tc2.output, probMul tc1.value tc2.value, tc1.prov⟩⟩
  /-- E×L (Table 4): recover the left marginal `γ` by division (expected mode). -/
  | eProdL (Γ Γ1 Γ2 : Context) (tc1 tc2 : TermClaim) (γ : Output) (quot : Prob)
      (hwf : contextWF Γ = true)
      (h1 : Derivable ⟨Γ1, .term tc1⟩) (h2 : Derivable ⟨Γ2, .term tc2⟩)
      (hc1 : contextEqSet Γ1 Γ = true) (hc2 : contextEqSet Γ2 Γ = true)
      (hmode : tc1.mode = tc2.mode) (hexp : tc1.mode = .expected)
      (hsamp : tc1.samples = tc2.samples) (hprov : tc1.prov = tc2.prov)
      (hterm2 : tc2.term = Term.snd tc1.term)
      (hout : tc1.output = Output.prod γ tc2.output)
      (hdiv : probDiv tc1.value tc2.value = some quot) :
      Derivable ⟨Γ, .term ⟨tc1.mode, Term.fst tc1.term, tc1.samples,
        γ, quot, tc1.prov⟩⟩
  /-- E×R (Table 4): recover the right marginal `γ` by division (expected mode). -/
  | eProdR (Γ Γ1 Γ2 : Context) (tc1 tc2 : TermClaim) (γ : Output) (quot : Prob)
      (hwf : contextWF Γ = true)
      (h1 : Derivable ⟨Γ1, .term tc1⟩) (h2 : Derivable ⟨Γ2, .term tc2⟩)
      (hc1 : contextEqSet Γ1 Γ = true) (hc2 : contextEqSet Γ2 Γ = true)
      (hmode : tc1.mode = tc2.mode) (hexp : tc1.mode = .expected)
      (hsamp : tc1.samples = tc2.samples) (hprov : tc1.prov = tc2.prov)
      (hterm2 : tc2.term = Term.fst tc1.term)
      (hout : tc1.output = Output.prod tc2.output γ)
      (hdiv : probDiv tc1.value tc2.value = some quot) :
      Derivable ⟨Γ, .term ⟨tc1.mode, Term.snd tc1.term, tc1.samples,
        γ, quot, tc1.prov⟩⟩
  /-- WeakeningD (Table 7): extend a judgement's context by a well-formed
      distribution Δ over disjoint variables. -/
  | weakeningD (Γ ctx : Context) (Δ : Context) (J : Claim)
      (hwf : contextWF ctx = true)
      (hJ : Derivable ⟨Γ, J⟩)
      (hindep : independentContexts Γ Δ = true)
      (hΔ : contextWF Δ = true)
      (hctx : contextEqSet ctx (mergeContexts [Γ, Δ]) = true) :
      Derivable ⟨ctx, J⟩

-- ============================================================================
-- Inversion kit for the checking monad
-- ============================================================================

/-- A gate succeeds only when its condition holds. -/
@[simp] theorem ensure_eq_ok (c : Bool) (m : String) :
    (ensure c m = Except.ok ()) ↔ c = true := by
  cases c
  · refine ⟨fun h => ?_, fun h => absurd h (by decide)⟩
    exact absurd (show (Except.error m : CheckM Unit) = Except.ok () from h) (by simp)
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- Bind inversion in `CheckM` (= `ExceptT String Id`). -/
theorem checkM_bind_ok {A B : Type} {x : CheckM A} {f : A → CheckM B} {b : B}
    (h : x >>= f = Except.ok b) :
    ∃ a, x = Except.ok a ∧ f a = Except.ok b := by
  cases x with
  | error e =>
    exact absurd (show (Except.error e : CheckM B) = Except.ok b from h) (by simp)
  | ok a => exact ⟨a, rfl, h⟩

/-- Kept for compatibility with earlier proofs. -/
theorem checkM_bind_eq_ok {A : Type} (x : CheckM A) (f : A → CheckM Unit) :
    (x >>= f = Except.ok ()) ↔ ∃ a, x = Except.ok a ∧ f a = Except.ok () := by
  refine ⟨checkM_bind_ok, ?_⟩
  rintro ⟨a, ha, hfa⟩
  cases x with
  | error e => exact absurd ha (by simp)
  | ok a' =>
    have : a' = a := by injection ha
    subst this; exact hfa

/-- An error is never a success. -/
theorem error_ne_ok {A : Type} {m : String} {a : A}
    (h : (Except.error m : CheckM A) = Except.ok a) : False := by
  simp at h

/-- `pure` succeeds with exactly its argument. -/
theorem pure_ok {A : Type} {a b : A}
    (h : (pure a : CheckM A) = Except.ok b) : a = b := by
  injection h

/-- Inverting `designatedName`: success pins the term to that atom. -/
theorem designatedName_ok {r : String} {t : Term} {u : String}
    (h : designatedName r t = Except.ok u) : t = Term.atom u := by
  cases t <;> simp only [designatedName] at h
  case atom s => rw [pure_ok h]
  all_goals exact (error_ne_ok h).elim

theorem expectPremises_ok {d : Derivation} {n : Nat} {r : String}
    {ps : List Derivation}
    (h : expectPremises d n r = Except.ok ps) : ps = d.premises := by
  unfold expectPremises at h
  obtain ⟨_, _, h⟩ := checkM_bind_ok h
  exact (pure_ok h).symm

theorem expectTermClaim_ok {c : Claim} {r : String} {tc : TermClaim}
    (h : expectTermClaim c r = Except.ok tc) : c = .term tc := by
  cases c <;> simp only [expectTermClaim] at h
  case term tc' => rw [pure_ok h]
  all_goals exact (error_ne_ok h).elim

theorem expectComparisonClaim_ok {c : Claim} {r : String} {cc : ComparisonClaim}
    (h : expectComparisonClaim c r = Except.ok cc) : c = .comparison cc := by
  cases c <;> simp only [expectComparisonClaim] at h
  case comparison cc' => rw [pure_ok h]
  all_goals exact (error_ne_ok h).elim

theorem expectTrustClaim_ok {c : Claim} {r : String} {tc : TrustClaim}
    (h : expectTrustClaim c r = Except.ok tc) : c = .trust tc := by
  cases c <;> simp only [expectTrustClaim] at h
  case trust tc' => rw [pure_ok h]
  all_goals exact (error_ne_ok h).elim

theorem expectIdentity_ok {c : Claim} {msg : String} {e : ContextEntry}
    (h : expectIdentity c msg = Except.ok e) : c = .identity e := by
  cases c <;> simp only [expectIdentity] at h
  case identity e' => rw [pure_ok h]
  all_goals exact (error_ne_ok h).elim

theorem expectExact_ok {c : Constraint} {msg : String} {p : Prob}
    (h : expectExact c msg = Except.ok p) : c = .exact p := by
  cases c <;> simp only [expectExact] at h
  case exact p' => rw [pure_ok h]
  all_goals exact (error_ne_ok h).elim

theorem expectSome_ok {A : Type} {o : Option A} {msg : String} {a : A}
    (h : expectSome o msg = Except.ok a) : o = some a := by
  cases o <;> simp only [expectSome] at h
  case some a' => rw [pure_ok h]
  case none => exact (error_ne_ok h).elim

/-- Checker verdicts have decidable equality (used to instantiate
    `checker_sound` on concrete certificates, e.g. via `native_decide`). -/
instance : DecidableEq (CheckM Unit) := fun a b =>
  match a, b with
  | .ok (), .ok () => .isTrue rfl
  | .error x, .error y =>
    if h : x = y then .isTrue (by rw [h])
    else .isFalse (fun hc => h (by injection hc))
  | .ok _, .error _ => .isFalse (fun hc => by simp at hc)
  | .error _, .ok _ => .isFalse (fun hc => by simp at hc)

/-- Structure eta for conclusions, used to rebuild sequents. -/
theorem conclusion_eta (d : Derivation) :
    d.conclusion = ⟨getCtx d, getClaim d⟩ := rfl

-- ============================================================================
-- Per-rule faithfulness lemmas
-- ============================================================================

theorem checkIdentity_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkIdentity d = Except.ok ())
    (_hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkIdentity at h
  obtain ⟨_, _, h⟩ := checkM_bind_ok h
  obtain ⟨_, _, h⟩ := checkM_bind_ok h
  split at h
  · rename_i e e' heqΓ heqCl
    rw [ensure_eq_ok, beq_iff_eq] at h
    subst h
    rw [heqΓ] at hwf
    rw [conclusion_eta, heqΓ, heqCl]
    exact .identity e hwf
  · exact (error_ne_ok h).elim

theorem checkIdentityStar_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkIdentityStar d = Except.ok ())
    (_hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkIdentityStar at h
  obtain ⟨_, _, h⟩ := checkM_bind_ok h
  split at h
  · rename_i e heq
    rw [ensure_eq_ok] at h
    rw [conclusion_eta, heq]
    exact .identityStar _ e hwf (of_decide_eq_true h)
  · exact (error_ne_ok h).elim

theorem checkObs_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkObs d = Except.ok ())
    (_hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkObs at h
  obtain ⟨_, _, h⟩ := checkM_bind_ok h
  split at h
  · rename_i tc heq
    obtain ⟨_, hmode, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hmode
    obtain ⟨_, hprov, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hprov
    obtain ⟨_, hn, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hn
    obtain ⟨_, hatom, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hatom
    obtain ⟨_, hnf, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hnf
    obtain ⟨hden, hnum⟩ := hnf
    rw [beq_iff_eq] at hden
    rw [ensure_eq_ok, beq_iff_eq] at h
    rw [conclusion_eta, heq]
    exact .obs _ tc hwf hmode (of_decide_eq_true hprov)
      (of_decide_eq_true hn) hatom hden (of_decide_eq_true hnum) h
  · exact (error_ne_ok h).elim

theorem checkUpdate_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkUpdate d = Except.ok ())
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkUpdate at h
  obtain ⟨ps, hexp, h⟩ := checkM_bind_ok h
  have hpseq := expectPremises_ok hexp
  subst hpseq
  rcases hP : d.premises with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, rest⟩⟩⟩
  all_goals try (rw [hP] at h; exact (error_ne_ok h).elim)
  · rw [hP] at h
    obtain ⟨tc1, htc1, h⟩ := checkM_bind_ok h
    have heq1 := expectTermClaim_ok htc1
    obtain ⟨tc2, htc2, h⟩ := checkM_bind_ok h
    have heq2 := expectTermClaim_ok htc2
    obtain ⟨conc, htcc, h⟩ := checkM_bind_ok h
    have heqc := expectTermClaim_ok htcc
    obtain ⟨_, hmodes, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true, Bool.and_eq_true] at hmodes
    have hm1 := beq_iff_eq.mp hmodes.1.1
    have hm2 := beq_iff_eq.mp hmodes.1.2
    have hmc := beq_iff_eq.mp hmodes.2
    -- positive sample sizes: consumed, but not needed by the spec (it only
    -- restricts the checker further, so the semantic rule is unchanged)
    obtain ⟨_, _, h⟩ := checkM_bind_ok h
    obtain ⟨_, hctxs, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hctxs
    have hc1 := hctxs.1
    have hc2 := hctxs.2
    obtain ⟨_, hterms, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hterms
    have ht12 := beq_iff_eq.mp hterms.1
    have htc' := beq_iff_eq.mp hterms.2
    obtain ⟨_, houts, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at houts
    have ho12 := beq_iff_eq.mp houts.1
    have hoc := beq_iff_eq.mp houts.2
    obtain ⟨_, hdisj, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hdisj
    obtain ⟨_, hprov, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hprov
    obtain ⟨_, hsamp, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hsamp
    split at h
    · rename_i w hweq
      rw [ensure_eq_ok] at h
      have hval : conc.value = w := by
        have h' := of_decide_eq_true h
        exact Prob.val_inj (beq_iff_eq.mp h')
      have hdp : d.premises = [p1, p2] := hP
      have h1D : Derivable ⟨getCtx p1, .term tc1⟩ := by
        have := hps p1 (by rw [hdp]; simp)
        rwa [conclusion_eta, heq1] at this
      have h2D : Derivable ⟨getCtx p2, .term tc2⟩ := by
        have := hps p2 (by rw [hdp]; simp)
        rwa [conclusion_eta, heq2] at this
      have hconc : conc = ⟨.frequency, tc1.term, tc1.samples + tc2.samples,
          tc1.output, w, tc1.prov ∪ tc2.prov⟩ :=
        TermClaim.ext hmc htc'.symm hsamp hoc.symm hval hprov
      rw [conclusion_eta, heqc, hconc]
      exact .update (getCtx d) (getCtx p1) (getCtx p2) tc1 tc2 w
        hwf h1D h2D hc1 hc2 hm1 hm2 ht12 ho12 hdisj hweq
    · exact (error_ne_ok h).elim

theorem checkIT_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkIT d = Except.ok ())
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkIT at h
  obtain ⟨ps, hexp, h⟩ := checkM_bind_ok h
  have hpseq := expectPremises_ok hexp
  subst hpseq
  rcases hP : d.premises with _ | ⟨pModel, _ | ⟨pObs, _ | ⟨p3, rest⟩⟩⟩
  all_goals try (rw [hP] at h; exact (error_ne_ok h).elim)
  · rw [hP] at h
    obtain ⟨me, hme, h⟩ := checkM_bind_ok h
    have heqM := expectIdentity_ok hme
    -- structural anti-laundering check, kept in the spec as hmem
    obtain ⟨_, hmem, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hmem
    -- uniqueness of the cited hypothesis: checker-only gate
    obtain ⟨_, _, h⟩ := checkM_bind_ok h
    obtain ⟨mp, hmp, h⟩ := checkM_bind_ok h
    have heqP := expectExact_ok hmp
    obtain ⟨obs, hobs, h⟩ := checkM_bind_ok h
    have heqO := expectTermClaim_ok hobs
    obtain ⟨_, hmode, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hmode
    obtain ⟨_, hout, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hout
    obtain ⟨_, hin, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hin
    obtain ⟨_, hctx, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hctx
    rcases hD : getClaim d with _ | _ | _ | _ | tcl | _ | _
    all_goals try (rw [hD] at h; exact (error_ne_ok h).elim)
    rcases tcl with ⟨kind, t, n, α, f, pv, interval, prv⟩ |
                    ⟨kind, t, n, α, f, pv, interval, prv⟩
    all_goals try (rw [hD] at h; exact (error_ne_ok h).elim)
    · rw [hD] at h
      obtain ⟨_, hkind, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hkind
      rw [hkind] at hD
      obtain ⟨_, ht, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at ht
      rw [ht] at hD
      obtain ⟨_, hn, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hn
      rw [hn] at hD
      obtain ⟨_, hα, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hα
      rw [hα] at hD
      obtain ⟨_, hf, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok] at hf
      have hf' : f = obs.value :=
        Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true hf))
      rw [hf'] at hD
      obtain ⟨_, hpv, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok] at hpv
      have hpv' : pv = mp :=
        Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true hpv))
      rw [hpv'] at hD
      obtain ⟨_, hiv, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hiv
      rw [hiv] at hD
      rw [ensure_eq_ok, beq_iff_eq] at h
      rw [h] at hD
      have hdp : d.premises = [pModel, pObs] := hP
      have hmD : Derivable ⟨getCtx pModel, .identity me⟩ := by
        have := hps pModel (by rw [hdp]; simp)
        rwa [conclusion_eta, heqM] at this
      have hoD : Derivable ⟨getCtx pObs, .term obs⟩ := by
        have := hps pObs (by rw [hdp]; simp)
        rwa [conclusion_eta, heqO] at this
      rw [conclusion_eta, hD]
      exact .it (getCtx pModel) (getCtx pObs) (getCtx d) me obs mp
        hwf hmD hoD heqP hmode hout hin hctx (of_decide_eq_true hmem)

theorem checkIUT_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkIUT d = Except.ok ())
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkIUT at h
  obtain ⟨ps, hexp, h⟩ := checkM_bind_ok h
  have hpseq := expectPremises_ok hexp
  subst hpseq
  rcases hP : d.premises with _ | ⟨pModel, _ | ⟨pObs, _ | ⟨p3, rest⟩⟩⟩
  all_goals try (rw [hP] at h; exact (error_ne_ok h).elim)
  · rw [hP] at h
    obtain ⟨me, hme, h⟩ := checkM_bind_ok h
    have heqM := expectIdentity_ok hme
    -- structural anti-laundering check, kept in the spec as hmem
    obtain ⟨_, hmem, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hmem
    -- uniqueness of the cited hypothesis: checker-only gate
    obtain ⟨_, _, h⟩ := checkM_bind_ok h
    obtain ⟨mp, hmp, h⟩ := checkM_bind_ok h
    have heqP := expectExact_ok hmp
    obtain ⟨obs, hobs, h⟩ := checkM_bind_ok h
    have heqO := expectTermClaim_ok hobs
    obtain ⟨_, hmode, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hmode
    obtain ⟨_, hout, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hout
    obtain ⟨_, hnotin, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hnotin
    obtain ⟨_, hctx, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hctx
    rcases hD : getClaim d with _ | _ | _ | _ | tcl | _ | _
    all_goals try (rw [hD] at h; exact (error_ne_ok h).elim)
    rcases tcl with ⟨kind, t, n, α, f, pv, interval, prv⟩ |
                    ⟨kind, t, n, α, f, pv, interval, prv⟩
    all_goals try (rw [hD] at h; exact (error_ne_ok h).elim)
    · rw [hD] at h
      obtain ⟨_, hkind, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hkind
      rw [hkind] at hD
      obtain ⟨_, ht, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at ht
      rw [ht] at hD
      obtain ⟨_, hn, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hn
      rw [hn] at hD
      obtain ⟨_, hα, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hα
      rw [hα] at hD
      obtain ⟨_, hf, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok] at hf
      have hf' : f = obs.value :=
        Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true hf))
      rw [hf'] at hD
      obtain ⟨_, hpv, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok] at hpv
      have hpv' : pv = mp :=
        Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true hpv))
      rw [hpv'] at hD
      obtain ⟨_, hiv, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hiv
      rw [hiv] at hD
      rw [ensure_eq_ok, beq_iff_eq] at h
      rw [h] at hD
      have hmD : Derivable ⟨getCtx pModel, .identity me⟩ := by
        have := hps pModel (by rw [hP]; simp)
        rwa [conclusion_eta, heqM] at this
      have hoD : Derivable ⟨getCtx pObs, .term obs⟩ := by
        have := hps pObs (by rw [hP]; simp)
        rwa [conclusion_eta, heqO] at this
      rw [conclusion_eta, hD]
      exact .iut (getCtx pModel) (getCtx pObs) (getCtx d) me obs mp
        hwf hmD hoD heqP hmode hout hnotin hctx (of_decide_eq_true hmem)

theorem checkIT2_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkIT2 d = Except.ok ())
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkIT2 at h
  obtain ⟨ps, hexp, h⟩ := checkM_bind_ok h
  have hpseq := expectPremises_ok hexp
  subst hpseq
  rcases hP : d.premises with _ | ⟨pL, _ | ⟨pR, _ | ⟨p3, rest⟩⟩⟩
  all_goals try (rw [hP] at h; exact (error_ne_ok h).elim)
  · rw [hP] at h
    obtain ⟨tcL, htL, h⟩ := checkM_bind_ok h
    have heqL := expectTermClaim_ok htL
    obtain ⟨tcR, htR, h⟩ := checkM_bind_ok h
    have heqR := expectTermClaim_ok htR
    obtain ⟨_, hmodes, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hmodes
    have hml := beq_iff_eq.mp hmodes.1
    have hmr := beq_iff_eq.mp hmodes.2
    obtain ⟨_, hout, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hout
    obtain ⟨_, hdisj, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hdisj
    obtain ⟨_, hin, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hin
    obtain ⟨_, hord, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hord
    obtain ⟨_, hctx, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hctx
    rcases hD : getClaim d with _ | _ | _ | _ | tcl | _ | _
    all_goals try (rw [hD] at h; exact (error_ne_ok h).elim)
    rcases tcl with ⟨kind, t, n, α, f, pv, interval, prv⟩ |
                    ⟨kind, t, n, α, f, pv, interval, prv⟩
    all_goals try (rw [hD] at h; exact (error_ne_ok h).elim)
    · rw [hD] at h
      obtain ⟨_, hkind, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hkind
      rw [hkind] at hD
      obtain ⟨_, ht, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at ht
      rw [ht] at hD
      obtain ⟨_, hn, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hn
      rw [hn] at hD
      obtain ⟨_, hα, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hα
      rw [hα] at hD
      obtain ⟨_, hf, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok] at hf
      have hf' : f = tcL.value :=
        Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true hf))
      rw [hf'] at hD
      obtain ⟨_, hpv, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok] at hpv
      have hpv' : pv = tcR.value :=
        Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true hpv))
      rw [hpv'] at hD
      obtain ⟨_, hiv, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hiv
      rw [hiv] at hD
      rw [ensure_eq_ok, beq_iff_eq] at h
      rw [h] at hD
      have hlD : Derivable ⟨getCtx pL, .term tcL⟩ := by
        have := hps pL (by rw [hP]; simp)
        rwa [conclusion_eta, heqL] at this
      have hrD : Derivable ⟨getCtx pR, .term tcR⟩ := by
        have := hps pR (by rw [hP]; simp)
        rwa [conclusion_eta, heqR] at this
      rw [conclusion_eta, hD]
      exact .it2 (getCtx pL) (getCtx pR) (getCtx d) tcL tcR
        hwf hlD hrD hml hmr hout hdisj (of_decide_eq_true hord) hin hctx

theorem checkIUT2_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkIUT2 d = Except.ok ())
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkIUT2 at h
  obtain ⟨ps, hexp, h⟩ := checkM_bind_ok h
  have hpseq := expectPremises_ok hexp
  subst hpseq
  rcases hP : d.premises with _ | ⟨pL, _ | ⟨pR, _ | ⟨p3, rest⟩⟩⟩
  all_goals try (rw [hP] at h; exact (error_ne_ok h).elim)
  · rw [hP] at h
    obtain ⟨tcL, htL, h⟩ := checkM_bind_ok h
    have heqL := expectTermClaim_ok htL
    obtain ⟨tcR, htR, h⟩ := checkM_bind_ok h
    have heqR := expectTermClaim_ok htR
    obtain ⟨_, hmodes, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hmodes
    have hml := beq_iff_eq.mp hmodes.1
    have hmr := beq_iff_eq.mp hmodes.2
    obtain ⟨_, hout, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hout
    obtain ⟨_, hdisj, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hdisj
    obtain ⟨_, hnotin, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hnotin
    obtain ⟨_, hord, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hord
    obtain ⟨_, hctx, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hctx
    rcases hD : getClaim d with _ | _ | _ | _ | tcl | _ | _
    all_goals try (rw [hD] at h; exact (error_ne_ok h).elim)
    rcases tcl with ⟨kind, t, n, α, f, pv, interval, prv⟩ |
                    ⟨kind, t, n, α, f, pv, interval, prv⟩
    all_goals try (rw [hD] at h; exact (error_ne_ok h).elim)
    · rw [hD] at h
      obtain ⟨_, hkind, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hkind
      rw [hkind] at hD
      obtain ⟨_, ht, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at ht
      rw [ht] at hD
      obtain ⟨_, hn, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hn
      rw [hn] at hD
      obtain ⟨_, hα, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hα
      rw [hα] at hD
      obtain ⟨_, hf, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok] at hf
      have hf' : f = tcL.value :=
        Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true hf))
      rw [hf'] at hD
      obtain ⟨_, hpv, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok] at hpv
      have hpv' : pv = tcR.value :=
        Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true hpv))
      rw [hpv'] at hD
      obtain ⟨_, hiv, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hiv
      rw [hiv] at hD
      rw [ensure_eq_ok, beq_iff_eq] at h
      rw [h] at hD
      have hlD : Derivable ⟨getCtx pL, .term tcL⟩ := by
        have := hps pL (by rw [hP]; simp)
        rwa [conclusion_eta, heqL] at this
      have hrD : Derivable ⟨getCtx pR, .term tcR⟩ := by
        have := hps pR (by rw [hP]; simp)
        rwa [conclusion_eta, heqR] at this
      rw [conclusion_eta, hD]
      exact .iut2 (getCtx pL) (getCtx pR) (getCtx d) tcL tcR
        hwf hlD hrD hml hmr hout hdisj (of_decide_eq_true hord) hnotin hctx

theorem checkIEx_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkIEx d = Except.ok ())
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkIEx at h
  obtain ⟨ps, hexp, h⟩ := checkM_bind_ok h
  have hpseq := expectPremises_ok hexp
  subst hpseq
  rcases hP : d.premises with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, rest⟩⟩⟩
  all_goals try (rw [hP] at h; exact (error_ne_ok h).elim)
  · rw [hP] at h
    obtain ⟨tc1, ht1, h⟩ := checkM_bind_ok h
    have heq1 := expectTermClaim_ok ht1
    obtain ⟨tc2, ht2, h⟩ := checkM_bind_ok h
    have heq2 := expectTermClaim_ok ht2
    obtain ⟨_, hmodes, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hmodes
    have hml := beq_iff_eq.mp hmodes.1
    have hmr := beq_iff_eq.mp hmodes.2
    obtain ⟨_, hout, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hout
    obtain ⟨_, hdisj, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hdisj
    obtain ⟨_, hnotin, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hnotin
    obtain ⟨_, hctx, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hctx
    rcases hD : getClaim d with _ | _ | _ | _ | _ | cc | _
    all_goals try (rw [hD] at h; exact (error_ne_ok h).elim)
    rcases cc with ⟨cl, cr, cd, civ⟩ | ⟨cl, cr, cd, civ⟩
    all_goals try (rw [hD] at h; exact (error_ne_ok h).elim)
    · rw [hD] at h
      obtain ⟨_, hcl, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hcl
      rw [hcl] at hD
      obtain ⟨_, hcr, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hcr
      rw [hcr] at hD
      obtain ⟨dv, hdsub, h⟩ := checkM_bind_ok h
      have hsub := expectSome_ok hdsub
      obtain ⟨_, hdv, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok] at hdv
      have hdv' : cd = dv :=
        Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true hdv))
      rw [hdv'] at hD
      rw [ensure_eq_ok, beq_iff_eq] at h
      rw [h] at hD
      have h1D : Derivable ⟨getCtx p1, .term tc1⟩ := by
        have := hps p1 (by rw [hP]; simp)
        rwa [conclusion_eta, heq1] at this
      have h2D : Derivable ⟨getCtx p2, .term tc2⟩ := by
        have := hps p2 (by rw [hP]; simp)
        rwa [conclusion_eta, heq2] at this
      rw [conclusion_eta, hD]
      exact .iEx (getCtx p1) (getCtx p2) (getCtx d) tc1 tc2 dv
        hwf h1D h2D hml hmr hout hdisj hnotin hctx hsub

theorem checkINEx_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkINEx d = Except.ok ())
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkINEx at h
  obtain ⟨ps, hexp, h⟩ := checkM_bind_ok h
  have hpseq := expectPremises_ok hexp
  subst hpseq
  rcases hP : d.premises with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, rest⟩⟩⟩
  all_goals try (rw [hP] at h; exact (error_ne_ok h).elim)
  · rw [hP] at h
    obtain ⟨tc1, ht1, h⟩ := checkM_bind_ok h
    have heq1 := expectTermClaim_ok ht1
    obtain ⟨tc2, ht2, h⟩ := checkM_bind_ok h
    have heq2 := expectTermClaim_ok ht2
    obtain ⟨_, hmodes, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hmodes
    have hml := beq_iff_eq.mp hmodes.1
    have hmr := beq_iff_eq.mp hmodes.2
    obtain ⟨_, hout, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hout
    obtain ⟨_, hdisj, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hdisj
    obtain ⟨_, hord, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hord
    obtain ⟨_, hin, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hin
    obtain ⟨_, hctx, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hctx
    rcases hD : getClaim d with _ | _ | _ | _ | _ | cc | _
    all_goals try (rw [hD] at h; exact (error_ne_ok h).elim)
    rcases cc with ⟨cl, cr, cd, civ⟩ | ⟨cl, cr, cd, civ⟩
    all_goals try (rw [hD] at h; exact (error_ne_ok h).elim)
    · rw [hD] at h
      obtain ⟨_, hcl, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hcl
      rw [hcl] at hD
      obtain ⟨_, hcr, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hcr
      rw [hcr] at hD
      rw [ensure_eq_ok, beq_iff_eq] at h
      rw [h] at hD
      have h1D : Derivable ⟨getCtx p1, .term tc1⟩ := by
        have := hps p1 (by rw [hP]; simp)
        rwa [conclusion_eta, heq1] at this
      have h2D : Derivable ⟨getCtx p2, .term tc2⟩ := by
        have := hps p2 (by rw [hP]; simp)
        rwa [conclusion_eta, heq2] at this
      rw [conclusion_eta, hD]
      exact .iNEx (getCtx p1) (getCtx p2) (getCtx d) tc1 tc2 cd
        hwf h1D h2D hml hmr hout hdisj (of_decide_eq_true hord) hin hctx

theorem checkET_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkET d = Except.ok ())
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkET at h
  obtain ⟨ps, hexp, h⟩ := checkM_bind_ok h
  have hpseq := expectPremises_ok hexp
  subst hpseq
  rcases hP : d.premises with _ | ⟨p, _ | ⟨p2, rest⟩⟩
  all_goals try (rw [hP] at h; exact (error_ne_ok h).elim)
  · rw [hP] at h
    obtain ⟨tc0, htc0, h⟩ := checkM_bind_ok h
    have hPC := expectTrustClaim_ok htc0
    rcases tc0 with ⟨kind, t, n, α, f, pp, interval, prv⟩ |
                    ⟨kind, t, n, α, f, pp, interval, prv⟩
    all_goals try (exact (error_ne_ok h).elim)
    · obtain ⟨_, hkind, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hkind
      rw [hkind] at hPC
      obtain ⟨conc, hc0, h⟩ := checkM_bind_ok h
      have heqD := expectTermClaim_ok hc0
      obtain ⟨_, hmode, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hmode
      obtain ⟨_, hterm, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hterm
      obtain ⟨_, hsam, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hsam
      obtain ⟨_, hout, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hout
      obtain ⟨_, hval, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok] at hval
      have hval' : conc.value = f :=
        Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true hval))
      obtain ⟨_, hprov, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hprov
      unfold checkElimContext at h
      obtain ⟨_, hpres, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok] at hpres
      rcases hF : (getCtx d).filter (· ∉ getCtx p) with _ | ⟨xu, _ | ⟨y, rest2⟩⟩
      all_goals try (rw [hF] at h; exact (error_ne_ok h).elim)
      · rw [hF] at h
        obtain ⟨_, hxu, h⟩ := checkM_bind_ok h
        rw [ensure_eq_ok, Bool.and_eq_true] at hxu
        have hxout := beq_iff_eq.mp hxu.1
        have hxc := beq_iff_eq.mp hxu.2
        obtain ⟨un, hun, h⟩ := checkM_bind_ok h
        have hdes := designatedName_ok hun
        rw [ensure_eq_ok, beq_iff_eq] at h
        have hxdesig : t = Term.atom xu.name := by rw [hdes, h]
        have hpD : Derivable
            ⟨getCtx p, .trust (.trust .oneSample t n α f pp interval prv)⟩ := by
          have := hps p (by rw [hP]; simp)
          rwa [conclusion_eta, hPC] at this
        have hcrec : conc = ⟨.frequency, t, n, α, f, prv⟩ :=
          TermClaim.ext hmode hterm hsam hout hval' hprov
        rw [conclusion_eta, heqD, hcrec]
        exact .et (getCtx p) (getCtx d) t n α f pp interval prv xu
          hwf hpD hpres hF hxout hxc hxdesig

theorem checkEUT_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkEUT d = Except.ok ())
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkEUT at h
  obtain ⟨ps, hexp, h⟩ := checkM_bind_ok h
  have hpseq := expectPremises_ok hexp
  subst hpseq
  rcases hP : d.premises with _ | ⟨p, _ | ⟨p2, rest⟩⟩
  all_goals try (rw [hP] at h; exact (error_ne_ok h).elim)
  · rw [hP] at h
    obtain ⟨tc0, htc0, h⟩ := checkM_bind_ok h
    have hPC := expectTrustClaim_ok htc0
    rcases tc0 with ⟨kind, t, n, α, f, pp, interval, prv⟩ |
                    ⟨kind, t, n, α, f, pp, interval, prv⟩
    all_goals try (exact (error_ne_ok h).elim)
    · obtain ⟨_, hkind, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hkind
      rw [hkind] at hPC
      obtain ⟨conc, hc0, h⟩ := checkM_bind_ok h
      have heqD := expectTermClaim_ok hc0
      obtain ⟨_, hmode, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hmode
      obtain ⟨_, hterm, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hterm
      obtain ⟨_, hsam, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hsam
      obtain ⟨_, hout, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hout
      obtain ⟨_, hval, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok] at hval
      have hval' : conc.value = f :=
        Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true hval))
      obtain ⟨_, hprov, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hprov
      unfold checkElimContext at h
      obtain ⟨_, hpres, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok] at hpres
      rcases hF : (getCtx d).filter (· ∉ getCtx p) with _ | ⟨xu, _ | ⟨y, rest2⟩⟩
      all_goals try (rw [hF] at h; exact (error_ne_ok h).elim)
      · rw [hF] at h
        obtain ⟨_, hxu, h⟩ := checkM_bind_ok h
        rw [ensure_eq_ok, Bool.and_eq_true] at hxu
        have hxout := beq_iff_eq.mp hxu.1
        have hxc := beq_iff_eq.mp hxu.2
        obtain ⟨un, hun, h⟩ := checkM_bind_ok h
        have hdes := designatedName_ok hun
        rw [ensure_eq_ok, beq_iff_eq] at h
        have hxdesig : t = Term.atom xu.name := by rw [hdes, h]
        have hpD : Derivable
            ⟨getCtx p, .trust (.untrust .oneSample t n α f pp interval prv)⟩ := by
          have := hps p (by rw [hP]; simp)
          rwa [conclusion_eta, hPC] at this
        have hcrec : conc = ⟨.frequency, t, n, α, f, prv⟩ :=
          TermClaim.ext hmode hterm hsam hout hval' hprov
        rw [conclusion_eta, heqD, hcrec]
        exact .eut (getCtx p) (getCtx d) t n α f pp interval prv xu
          hwf hpD hpres hF hxout hxc hxdesig

theorem checkEEx_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkEEx d = Except.ok ())
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkEEx at h
  obtain ⟨ps, hexp, h⟩ := checkM_bind_ok h
  have hpseq := expectPremises_ok hexp
  subst hpseq
  rcases hP : d.premises with _ | ⟨pE, _ | ⟨pM, _ | ⟨p3, rest⟩⟩⟩
  all_goals try (rw [hP] at h; exact (error_ne_ok h).elim)
  · rw [hP] at h
    obtain ⟨exC, hexc, h⟩ := checkM_bind_ok h
    have heqE := expectComparisonClaim_ok hexc
    rcases exC with ⟨tcL, tcR, dv, iv⟩ | ⟨tcL, tcR, dv, iv⟩
    all_goals try (exact (error_ne_ok h).elim)
    · obtain ⟨me, hme, h⟩ := checkM_bind_ok h
      have heqM := expectIdentity_ok hme
      -- structural anti-laundering check, kept in the spec as hmem
      obtain ⟨_, hmem, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok] at hmem
      -- uniqueness of the cited hypothesis: checker-only gate
      obtain ⟨_, _, h⟩ := checkM_bind_ok h
      obtain ⟨_, hmout, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok, beq_iff_eq] at hmout
      obtain ⟨mp, hmp, h⟩ := checkM_bind_ok h
      have heqXP := expectExact_ok hmp
      rcases iv with _ | ⟨lo, hi⟩ | _ | _
      all_goals try (exact (error_ne_ok h).elim)
      · obtain ⟨_, hsum, h⟩ := checkM_bind_ok h
        rw [ensure_eq_ok] at hsum
        obtain ⟨conc, hc0, h⟩ := checkM_bind_ok h
        have heqD := expectTermClaim_ok hc0
        obtain ⟨_, hmode, h⟩ := checkM_bind_ok h
        rw [ensure_eq_ok, beq_iff_eq] at hmode
        obtain ⟨_, hterm, h⟩ := checkM_bind_ok h
        rw [ensure_eq_ok, beq_iff_eq] at hterm
        obtain ⟨_, hsam, h⟩ := checkM_bind_ok h
        rw [ensure_eq_ok, beq_iff_eq] at hsam
        obtain ⟨_, hout, h⟩ := checkM_bind_ok h
        rw [ensure_eq_ok, beq_iff_eq] at hout
        obtain ⟨_, hval, h⟩ := checkM_bind_ok h
        rw [ensure_eq_ok] at hval
        have hval' : conc.value = tcL.value :=
          Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true hval))
        obtain ⟨_, hbase, h⟩ := checkM_bind_ok h
        rw [ensure_eq_ok] at hbase
        rcases hf : (getCtx d).filter (· ∉ mergeContexts [getCtx pE, getCtx pM])
          with _ | ⟨se, _ | ⟨s2, rest⟩⟩
        all_goals try (rw [hf] at h; exact (error_ne_ok h).elim)
        rw [hf] at h
        -- the shifted assumption's output/constraint gate; the name-tie gate
        -- that follows only restricts the checker further, so the spec is
        -- unchanged and its residue is discarded
        obtain ⟨_, hse2, _⟩ := checkM_bind_ok h
        rw [ensure_eq_ok, Bool.and_eq_true] at hse2
        have hseout := beq_iff_eq.mp hse2.1
        have hsec := beq_iff_eq.mp hse2.2
        have hse : se ∈ getCtx d :=
          List.mem_of_mem_filter (a := se) (by rw [hf]; simp)
        have heD : Derivable ⟨getCtx pE,
            .comparison (.excess tcL tcR dv (.interval lo hi))⟩ := by
          have := hps pE (by rw [hP]; simp)
          rwa [conclusion_eta, heqE] at this
        have hmD : Derivable ⟨getCtx pM, .identity me⟩ := by
          have := hps pM (by rw [hP]; simp)
          rwa [conclusion_eta, heqM] at this
        have hcrec : conc =
            ⟨.frequency, tcL.term, tcL.samples, tcL.output, tcL.value, conc.prov⟩ :=
          TermClaim.ext hmode hterm hsam hout hval' rfl
        rw [conclusion_eta, heqD, hcrec]
        exact .eEx (getCtx pE) (getCtx pM) (getCtx d) tcL tcR dv lo hi me se
          mp conc.prov hwf heD hmD heqXP hmout hsum hbase hse hseout hsec (of_decide_eq_true hmem)

-- ============================================================================
-- The top-level theorem
-- ============================================================================

theorem checkExperiment_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkExperiment d = Except.ok ())
    (_hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkExperiment at h
  obtain ⟨_, _, h⟩ := checkM_bind_ok h
  split at h
  · rename_i tc heq
    obtain ⟨_, hprov, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hprov
    obtain ⟨_, hatom, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hatom
    obtain ⟨_, hmode, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hmode
    obtain ⟨_, hn, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hn
    obtain ⟨_, hval, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hval
    rw [ensure_eq_ok, beq_iff_eq] at h
    rw [conclusion_eta, heq]
    exact .experiment _ tc hwf hprov hatom hmode hn
      (beq_iff_eq.mp (of_decide_eq_true hval)) h
  · exact (error_ne_ok h).elim

theorem checkIdentityModel_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkIdentityModel d = Except.ok ())
    (_hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkIdentityModel at h
  obtain ⟨_, _, h⟩ := checkM_bind_ok h
  obtain ⟨_, hlen, h⟩ := checkM_bind_ok h
  rw [ensure_eq_ok, beq_iff_eq] at hlen
  split at h
  · rename_i e e' hctx hclaim
    obtain ⟨_, hex, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hex
    rw [ensure_eq_ok] at h
    -- both constraints are exact; extract the witnesses
    rcases hc : e.constraint with p | _ | _ | _
    all_goals rw [hc] at hex
    all_goals try simp at hex
    rcases hc' : e'.constraint with q | _ | _ | _
    all_goals rw [hc'] at h
    all_goals try simp at h
    rw [conclusion_eta, hctx, hclaim]
    exact .identityModel e e' p q (by rw [← hctx]; exact hwf) hc hc'
  · exact (error_ne_ok h).elim

theorem checkExpectation_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkExpectation d = Except.ok ())
    (_hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkExpectation at h
  obtain ⟨_, _, h⟩ := checkM_bind_ok h
  split at h
  · rename_i tc heq
    obtain ⟨_, hmode, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hmode
    obtain ⟨_, hprov, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hprov
    obtain ⟨_, hn, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hn
    obtain ⟨_, hatom, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hatom
    split at h
    · rename_i e hsupp
      split at h
      · rename_i a hexact
        rw [ensure_eq_ok] at h
        rw [conclusion_eta, heq]
        exact .expectation _ tc e a hwf hmode hprov (of_decide_eq_true hn)
          hatom hsupp hexact (beq_iff_eq.mp (of_decide_eq_true h))
      · exact (error_ne_ok h).elim
    · exact (error_ne_ok h).elim
  · exact (error_ne_ok h).elim

theorem checkWeakeningS_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkWeakeningS d = Except.ok ())
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkWeakeningS at h
  obtain ⟨ps, hexp, h⟩ := checkM_bind_ok h
  have hpseq := expectPremises_ok hexp
  subst hpseq
  rcases hP : d.premises with _ | ⟨pJ, _ | ⟨pK, _ | ⟨p3, rest⟩⟩⟩
  all_goals try (rw [hP] at h; exact (error_ne_ok h).elim)
  · rw [hP] at h
    obtain ⟨_, _, h⟩ := checkM_bind_ok h
    obtain ⟨_, hindep, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hindep
    obtain ⟨_, hctx, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hctx
    rw [ensure_eq_ok, beq_iff_eq] at h
    have hJD : Derivable ⟨getCtx pJ, getClaim pJ⟩ := by
      have := hps pJ (by rw [hP]; simp)
      rwa [conclusion_eta] at this
    have hKD : Derivable ⟨getCtx pK, getClaim pK⟩ := by
      have := hps pK (by rw [hP]; simp)
      rwa [conclusion_eta] at this
    rw [conclusion_eta, h]
    exact .weakeningS (getCtx pJ) (getCtx pK) (getCtx d) (getClaim pJ)
      (getClaim pK) hwf hJD hKD hindep hctx

-- Shared premise-extraction for the two-premise `.term` connective rules.
private theorem twoTermPremises {d : Derivation} {p1 p2 : Derivation}
    (hP : d.premises = [p1, p2])
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable ⟨getCtx p1, getClaim p1⟩ ∧ Derivable ⟨getCtx p2, getClaim p2⟩ := by
  refine ⟨?_, ?_⟩
  · have := hps p1 (by rw [hP]; simp); rwa [conclusion_eta] at this
  · have := hps p2 (by rw [hP]; simp); rwa [conclusion_eta] at this

theorem checkIPlus_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkIPlus d = Except.ok ())
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkIPlus at h
  obtain ⟨ps, hexp, h⟩ := checkM_bind_ok h
  have hpseq := expectPremises_ok hexp; subst hpseq
  rcases hP : d.premises with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, rest⟩⟩⟩
  all_goals try (rw [hP] at h; exact (error_ne_ok h).elim)
  · rw [hP] at h
    obtain ⟨tc1, htc1, h⟩ := checkM_bind_ok h
    have heq1 := expectTermClaim_ok htc1
    obtain ⟨tc2, htc2, h⟩ := checkM_bind_ok h
    have heq2 := expectTermClaim_ok htc2
    obtain ⟨conc, htcc, h⟩ := checkM_bind_ok h
    have heqc := expectTermClaim_ok htcc
    obtain ⟨_, hmodes, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hmodes
    obtain ⟨_, hsamps, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hsamps
    obtain ⟨_, hprovs, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hprovs
    obtain ⟨_, hterms, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hterms
    obtain ⟨_, hctxs, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hctxs
    obtain ⟨_, _, h⟩ := checkM_bind_ok h  -- output-distinct (not needed)
    obtain ⟨_, hdisj, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hdisj
    obtain ⟨_, houtc, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at houtc
    split at h
    · rename_i s hseq
      rw [ensure_eq_ok] at h
      have hval : conc.value = s := Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true h))
      obtain ⟨h1D0, h2D0⟩ := twoTermPremises hP hps
      rw [heq1] at h1D0; rw [heq2] at h2D0
      have hrec : conc = ⟨tc1.mode, tc1.term, tc1.samples,
          Output.sum tc1.output tc2.output, s, tc1.prov⟩ :=
        TermClaim.ext (beq_iff_eq.mp hmodes.2).symm (beq_iff_eq.mp hterms.2).symm
          (beq_iff_eq.mp hsamps.2).symm houtc hval (beq_iff_eq.mp hprovs.2).symm
      rw [conclusion_eta, heqc, hrec]
      exact .iPlus (getCtx d) (getCtx p1) (getCtx p2) tc1 tc2 s hwf h1D0 h2D0
        hctxs.1 hctxs.2 (beq_iff_eq.mp hmodes.1) (beq_iff_eq.mp hsamps.1)
        (beq_iff_eq.mp hprovs.1) (beq_iff_eq.mp hterms.1) hdisj hseq
    · exact (error_ne_ok h).elim

theorem checkEPlusL_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkEPlusL d = Except.ok ())
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkEPlusL at h
  obtain ⟨ps, hexp, h⟩ := checkM_bind_ok h
  have hpseq := expectPremises_ok hexp; subst hpseq
  rcases hP : d.premises with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, rest⟩⟩⟩
  all_goals try (rw [hP] at h; exact (error_ne_ok h).elim)
  · rw [hP] at h
    obtain ⟨tc1, htc1, h⟩ := checkM_bind_ok h
    have heq1 := expectTermClaim_ok htc1
    obtain ⟨tc2, htc2, h⟩ := checkM_bind_ok h
    have heq2 := expectTermClaim_ok htc2
    obtain ⟨conc, htcc, h⟩ := checkM_bind_ok h
    have heqc := expectTermClaim_ok htcc
    obtain ⟨_, hmodes, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hmodes
    obtain ⟨_, hsamps, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hsamps
    obtain ⟨_, hprovs, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hprovs
    obtain ⟨_, hterms, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hterms
    obtain ⟨_, hdisj, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hdisj
    obtain ⟨_, hctxs, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hctxs
    obtain ⟨_, hsum, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hsum
    obtain ⟨_, _, h⟩ := checkM_bind_ok h  -- p ≤ r (not needed by spec)
    split at h
    · rename_i diff hdeq
      rw [ensure_eq_ok] at h
      have hval : conc.value = diff := Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true h))
      obtain ⟨h1D0, h2D0⟩ := twoTermPremises hP hps
      rw [heq1] at h1D0; rw [heq2] at h2D0
      have hrec : conc = ⟨tc1.mode, tc1.term, tc1.samples, conc.output, diff, tc1.prov⟩ :=
        TermClaim.ext (beq_iff_eq.mp hmodes.2).symm (beq_iff_eq.mp hterms.2).symm
          (beq_iff_eq.mp hsamps.2).symm rfl hval (beq_iff_eq.mp hprovs.2).symm
      rw [conclusion_eta, heqc, hrec]
      exact .ePlusL (getCtx d) (getCtx p1) (getCtx p2) tc1 tc2 conc.output diff
        hwf h1D0 h2D0 hctxs.1 hctxs.2 (beq_iff_eq.mp hmodes.1) (beq_iff_eq.mp hsamps.1)
        (beq_iff_eq.mp hprovs.1) (beq_iff_eq.mp hterms.1) hdisj hsum hdeq
    · exact (error_ne_ok h).elim

theorem checkEPlusR_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkEPlusR d = Except.ok ())
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkEPlusR at h
  obtain ⟨ps, hexp, h⟩ := checkM_bind_ok h
  have hpseq := expectPremises_ok hexp; subst hpseq
  rcases hP : d.premises with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, rest⟩⟩⟩
  all_goals try (rw [hP] at h; exact (error_ne_ok h).elim)
  · rw [hP] at h
    obtain ⟨tc1, htc1, h⟩ := checkM_bind_ok h
    have heq1 := expectTermClaim_ok htc1
    obtain ⟨tc2, htc2, h⟩ := checkM_bind_ok h
    have heq2 := expectTermClaim_ok htc2
    obtain ⟨conc, htcc, h⟩ := checkM_bind_ok h
    have heqc := expectTermClaim_ok htcc
    obtain ⟨_, hmodes, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hmodes
    obtain ⟨_, hsamps, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hsamps
    obtain ⟨_, hprovs, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hprovs
    obtain ⟨_, hterms, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hterms
    obtain ⟨_, hdisj, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hdisj
    obtain ⟨_, hctxs, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hctxs
    obtain ⟨_, hsum, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hsum
    obtain ⟨_, _, h⟩ := checkM_bind_ok h
    split at h
    · rename_i diff hdeq
      rw [ensure_eq_ok] at h
      have hval : conc.value = diff := Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true h))
      obtain ⟨h1D0, h2D0⟩ := twoTermPremises hP hps
      rw [heq1] at h1D0; rw [heq2] at h2D0
      have hrec : conc = ⟨tc1.mode, tc1.term, tc1.samples, conc.output, diff, tc1.prov⟩ :=
        TermClaim.ext (beq_iff_eq.mp hmodes.2).symm (beq_iff_eq.mp hterms.2).symm
          (beq_iff_eq.mp hsamps.2).symm rfl hval (beq_iff_eq.mp hprovs.2).symm
      rw [conclusion_eta, heqc, hrec]
      exact .ePlusR (getCtx d) (getCtx p1) (getCtx p2) tc1 tc2 conc.output diff
        hwf h1D0 h2D0 hctxs.1 hctxs.2 (beq_iff_eq.mp hmodes.1) (beq_iff_eq.mp hsamps.1)
        (beq_iff_eq.mp hprovs.1) (beq_iff_eq.mp hterms.1) hdisj hsum hdeq
    · exact (error_ne_ok h).elim

theorem checkIProd_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkIProd d = Except.ok ())
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkIProd at h
  obtain ⟨ps, hexp, h⟩ := checkM_bind_ok h
  have hpseq := expectPremises_ok hexp; subst hpseq
  rcases hP : d.premises with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, rest⟩⟩⟩
  all_goals try (rw [hP] at h; exact (error_ne_ok h).elim)
  · rw [hP] at h
    obtain ⟨_, _, h⟩ := checkM_bind_ok h  -- witness flag
    obtain ⟨_, hindep, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hindep
    obtain ⟨tc1, htc1, h⟩ := checkM_bind_ok h
    have heq1 := expectTermClaim_ok htc1
    obtain ⟨tc2, htc2, h⟩ := checkM_bind_ok h
    have heq2 := expectTermClaim_ok htc2
    obtain ⟨conc, htcc, h⟩ := checkM_bind_ok h
    have heqc := expectTermClaim_ok htcc
    obtain ⟨_, hmodes, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hmodes
    obtain ⟨_, hexpm, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hexpm
    obtain ⟨_, hsamps, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hsamps
    obtain ⟨_, hprovs, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hprovs
    obtain ⟨_, houtc, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at houtc
    obtain ⟨_, htermc, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at htermc
    obtain ⟨_, hvalc, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok] at hvalc
    rw [ensure_eq_ok] at h
    have hval : conc.value = probMul tc1.value tc2.value :=
      Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true hvalc))
    obtain ⟨h1D0, h2D0⟩ := twoTermPremises hP hps
    rw [heq1] at h1D0; rw [heq2] at h2D0
    have hrec : conc = ⟨tc1.mode, Term.pair tc1.term tc2.term, tc1.samples,
        Output.prod tc1.output tc2.output, probMul tc1.value tc2.value, tc1.prov⟩ :=
      TermClaim.ext (beq_iff_eq.mp hmodes.2).symm htermc (beq_iff_eq.mp hsamps.2).symm
        houtc hval (beq_iff_eq.mp hprovs.2).symm
    rw [conclusion_eta, heqc, hrec]
    exact .iProd (getCtx d) (getCtx p1) (getCtx p2) tc1 tc2 hwf h1D0 h2D0 hindep
      (beq_iff_eq.mp hmodes.1) (by rw [beq_iff_eq.mp hmodes.2]; exact hexpm)
      (beq_iff_eq.mp hsamps.1) (beq_iff_eq.mp hprovs.1) h

theorem checkEProdL_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkEProdL d = Except.ok ())
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkEProdL at h
  obtain ⟨ps, hexp, h⟩ := checkM_bind_ok h
  have hpseq := expectPremises_ok hexp; subst hpseq
  rcases hP : d.premises with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, rest⟩⟩⟩
  all_goals try (rw [hP] at h; exact (error_ne_ok h).elim)
  · rw [hP] at h
    obtain ⟨tc1, htc1, h⟩ := checkM_bind_ok h
    have heq1 := expectTermClaim_ok htc1
    obtain ⟨tc2, htc2, h⟩ := checkM_bind_ok h
    have heq2 := expectTermClaim_ok htc2
    obtain ⟨conc, htcc, h⟩ := checkM_bind_ok h
    have heqc := expectTermClaim_ok htcc
    obtain ⟨_, hmodes, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hmodes
    obtain ⟨_, hexpm, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hexpm
    obtain ⟨_, hsamps, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hsamps
    obtain ⟨_, hprovs, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hprovs
    obtain ⟨_, hterms, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hterms
    obtain ⟨_, hctxs, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hctxs
    obtain ⟨_, _, h⟩ := checkM_bind_ok h  -- witness flag
    obtain ⟨_, hout, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hout
    obtain ⟨_, _, h⟩ := checkM_bind_ok h  -- 0 < q
    split at h
    · rename_i quot hqeq
      rw [ensure_eq_ok] at h
      have hval : conc.value = quot := Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true h))
      obtain ⟨h1D0, h2D0⟩ := twoTermPremises hP hps
      rw [heq1] at h1D0; rw [heq2] at h2D0
      have hrec : conc = ⟨tc1.mode, Term.fst tc1.term, tc1.samples,
          conc.output, quot, tc1.prov⟩ :=
        TermClaim.ext (beq_iff_eq.mp hmodes.2).symm (beq_iff_eq.mp hterms.2)
          (beq_iff_eq.mp hsamps.2).symm rfl hval (beq_iff_eq.mp hprovs.2).symm
      rw [conclusion_eta, heqc, hrec]
      exact .eProdL (getCtx d) (getCtx p1) (getCtx p2) tc1 tc2 conc.output quot
        hwf h1D0 h2D0 hctxs.1 hctxs.2 (beq_iff_eq.mp hmodes.1)
        (by rw [beq_iff_eq.mp hmodes.2]; exact hexpm)
        (beq_iff_eq.mp hsamps.1) (beq_iff_eq.mp hprovs.1)
        (beq_iff_eq.mp hterms.1) hout hqeq
    · exact (error_ne_ok h).elim

theorem checkEProdR_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkEProdR d = Except.ok ())
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkEProdR at h
  obtain ⟨ps, hexp, h⟩ := checkM_bind_ok h
  have hpseq := expectPremises_ok hexp; subst hpseq
  rcases hP : d.premises with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, rest⟩⟩⟩
  all_goals try (rw [hP] at h; exact (error_ne_ok h).elim)
  · rw [hP] at h
    obtain ⟨tc1, htc1, h⟩ := checkM_bind_ok h
    have heq1 := expectTermClaim_ok htc1
    obtain ⟨tc2, htc2, h⟩ := checkM_bind_ok h
    have heq2 := expectTermClaim_ok htc2
    obtain ⟨conc, htcc, h⟩ := checkM_bind_ok h
    have heqc := expectTermClaim_ok htcc
    obtain ⟨_, hmodes, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hmodes
    obtain ⟨_, hexpm, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hexpm
    obtain ⟨_, hsamps, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hsamps
    obtain ⟨_, hprovs, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hprovs
    obtain ⟨_, hterms, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hterms
    obtain ⟨_, hctxs, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, Bool.and_eq_true] at hctxs
    obtain ⟨_, _, h⟩ := checkM_bind_ok h  -- witness flag
    obtain ⟨_, hout, h⟩ := checkM_bind_ok h
    rw [ensure_eq_ok, beq_iff_eq] at hout
    obtain ⟨_, _, h⟩ := checkM_bind_ok h  -- 0 < q
    split at h
    · rename_i quot hqeq
      rw [ensure_eq_ok] at h
      have hval : conc.value = quot := Prob.val_inj (beq_iff_eq.mp (of_decide_eq_true h))
      obtain ⟨h1D0, h2D0⟩ := twoTermPremises hP hps
      rw [heq1] at h1D0; rw [heq2] at h2D0
      have hrec : conc = ⟨tc1.mode, Term.snd tc1.term, tc1.samples,
          conc.output, quot, tc1.prov⟩ :=
        TermClaim.ext (beq_iff_eq.mp hmodes.2).symm (beq_iff_eq.mp hterms.2)
          (beq_iff_eq.mp hsamps.2).symm rfl hval (beq_iff_eq.mp hprovs.2).symm
      rw [conclusion_eta, heqc, hrec]
      exact .eProdR (getCtx d) (getCtx p1) (getCtx p2) tc1 tc2 conc.output quot
        hwf h1D0 h2D0 hctxs.1 hctxs.2 (beq_iff_eq.mp hmodes.1)
        (by rw [beq_iff_eq.mp hmodes.2]; exact hexpm)
        (beq_iff_eq.mp hsamps.1) (beq_iff_eq.mp hprovs.1)
        (beq_iff_eq.mp hterms.1) hout hqeq
    · exact (error_ne_ok h).elim

theorem checkWeakeningD_sound (d : Derivation)
    (hwf : contextWF (getCtx d) = true)
    (h : checkWeakeningD d = Except.ok ())
    (hps : ∀ p ∈ d.premises, Derivable p.conclusion) :
    Derivable d.conclusion := by
  unfold checkWeakeningD at h
  obtain ⟨ps, hexp, h⟩ := checkM_bind_ok h
  have hpseq := expectPremises_ok hexp; subst hpseq
  rcases hP : d.premises with _ | ⟨pJ, _ | ⟨pD, _ | ⟨p3, rest⟩⟩⟩
  all_goals try (rw [hP] at h; exact (error_ne_ok h).elim)
  · rw [hP] at h
    obtain ⟨_, _, h⟩ := checkM_bind_ok h  -- witness flag
    rcases hD : getClaim pD with _ | Δ | _ | _ | _ | _ | _
    all_goals try (rw [hD] at h; exact (error_ne_ok h).elim)
    · rw [hD] at h
      obtain ⟨_, hindep, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok] at hindep
      obtain ⟨_, hΔ, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok] at hΔ
      obtain ⟨_, hctx, h⟩ := checkM_bind_ok h
      rw [ensure_eq_ok] at hctx
      rw [ensure_eq_ok, beq_iff_eq] at h
      have hJD : Derivable ⟨getCtx pJ, getClaim pJ⟩ := by
        have := hps pJ (by rw [hP]; simp); rwa [conclusion_eta] at this
      rw [conclusion_eta, h]
      exact .weakeningD (getCtx pJ) (getCtx d) Δ (getClaim pJ) hwf hJD hindep hΔ hctx

/-- The rule names covered by the faithfulness theorem. -/
def fragmentRule (r : String) : Bool :=
  r == "identity" || r == "identity_star" || r == "obs" || r == "update" ||
  r == "IT" || r == "IUT" || r == "IT2" || r == "IUT2" ||
  r == "IEx" || r == "INEx" || r == "ET" || r == "EUT" || r == "EEx" ||
  r == "experiment" || r == "identity_model" ||
  r == "expectation" || r == "WeakeningS" ||
  r == "I+" || r == "E+L" || r == "E+R" ||
  r == "I×" || r == "E×L" || r == "E×R" || r == "WeakeningD"

mutual
/-- Every rule in the derivation lies in the certified fragment. -/
def Derivation.inFragment : Derivation → Bool
  | .node r ps _ _ => fragmentRule r && inFragmentList ps
def inFragmentList : List Derivation → Bool
  | [] => true
  | p :: ps => p.inFragment && inFragmentList ps
end

mutual
/-- **Faithfulness of the checker (certified fragment).**  If every rule
    in the tree belongs to the fragment and `checkDerivation` accepts,
    the conclusion is derivable in the calculus: the checker cannot
    accept a certificate outside the rules. -/
theorem checker_sound :
    ∀ (d : Derivation), d.inFragment = true →
      checkDerivation d = Except.ok () → Derivable d.conclusion
  | .node r ps concl w, hfrag, hok => by
    unfold checkDerivation at hok
    obtain ⟨_, hwf, hok⟩ := checkM_bind_ok hok
    rw [ensure_eq_ok] at hwf
    obtain ⟨_, hnode, hok⟩ := checkM_bind_ok hok
    unfold Derivation.inFragment at hfrag
    rw [Bool.and_eq_true] at hfrag
    have hpsD : ∀ p ∈ (Derivation.node r ps concl w).premises,
        Derivable p.conclusion :=
      premisesSound ps hfrag.2 hok
    have hr := hfrag.1
    simp only [fragmentRule, Bool.or_eq_true, beq_iff_eq] at hr
    rcases hr with (((((((((((((((((((((((hr | hr) | hr) | hr) | hr) | hr) | hr) | hr)
      | hr) | hr) | hr) | hr) | hr) | hr) | hr) | hr) | hr) | hr) | hr) | hr) | hr) | hr) | hr) | hr) <;> subst hr
    · exact checkIdentity_sound _ hwf hnode hpsD
    · exact checkIdentityStar_sound _ hwf hnode hpsD
    · exact checkObs_sound _ hwf hnode hpsD
    · exact checkUpdate_sound _ hwf hnode hpsD
    · exact checkIT_sound _ hwf hnode hpsD
    · exact checkIUT_sound _ hwf hnode hpsD
    · exact checkIT2_sound _ hwf hnode hpsD
    · exact checkIUT2_sound _ hwf hnode hpsD
    · exact checkIEx_sound _ hwf hnode hpsD
    · exact checkINEx_sound _ hwf hnode hpsD
    · exact checkET_sound _ hwf hnode hpsD
    · exact checkEUT_sound _ hwf hnode hpsD
    · exact checkEEx_sound _ hwf hnode hpsD
    · exact checkExperiment_sound _ hwf hnode hpsD
    · exact checkIdentityModel_sound _ hwf hnode hpsD
    · exact checkExpectation_sound _ hwf hnode hpsD
    · exact checkWeakeningS_sound _ hwf hnode hpsD
    · exact checkIPlus_sound _ hwf hnode hpsD
    · exact checkEPlusL_sound _ hwf hnode hpsD
    · exact checkEPlusR_sound _ hwf hnode hpsD
    · exact checkIProd_sound _ hwf hnode hpsD
    · exact checkEProdL_sound _ hwf hnode hpsD
    · exact checkEProdR_sound _ hwf hnode hpsD
    · exact checkWeakeningD_sound _ hwf hnode hpsD

theorem premisesSound :
    ∀ (ps : List Derivation), inFragmentList ps = true →
      checkPremisesList ps = Except.ok () →
      ∀ p ∈ ps, Derivable p.conclusion
  | [], _, _ => by intro p hp; simp at hp
  | q :: qs, hfrag, hok => by
    unfold inFragmentList at hfrag
    rw [Bool.and_eq_true] at hfrag
    unfold checkPremisesList at hok
    obtain ⟨_, hq, hqs⟩ := checkM_bind_ok hok
    intro p hp
    rcases List.mem_cons.mp hp with hpq | hpqs
    · subst hpq; exact checker_sound p hfrag.1 hq
    · exact premisesSound qs hfrag.2 hqs p hpqs
end

end TPTND
