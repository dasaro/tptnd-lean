import TPTND.Syntax
import TPTND.Judgement
import TPTND.WellFormedness
import TPTND.Arithmetic
import Mathlib.Data.Finset.Card

/-! # The `Derivable` specification

`Derivable s` is the calculus written directly as a `Prop`: it holds iff the
sequent `s` is the conclusion of a rule whose premises are derivable and whose
side conditions hold.  It sits BEFORE the rule checkers in the import order so
that checkers can be written in certifying (forward) style, returning the
derivability of their conclusion outright. -/

namespace TPTND

/-- Probabilities with equal values are equal. -/
theorem Prob.val_inj {a b : Prob} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

/-- Term claims with equal fields are equal. -/
theorem TermClaim.ext {a b : TermClaim}
    (h1 : a.mode = b.mode) (h2 : a.term = b.term) (h3 : a.samples = b.samples)
    (h4 : a.output = b.output) (h5 : a.value = b.value) (h6 : a.prov = b.prov) :
    a = b := by
  cases a; cases b; simp_all

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
  /-- output_neg (Table 1): negation of a well-formed output. -/
  | outputNeg (Γ Γp : Context) (α : Output) (hwf : contextWF Γ = true)
      (hp : Derivable ⟨Γp, .outputDecl α⟩) :
      Derivable ⟨Γ, .outputDecl (.neg α)⟩
  /-- output_atom (Table 1): an atomic output is well-formed. -/
  | outputAtom (Γ : Context) (a : String) (hwf : contextWF Γ = true) :
      Derivable ⟨Γ, .outputDecl (.atom a)⟩
  /-- output_sum (Table 1). -/
  | outputSum (Γ Γ1 Γ2 : Context) (α β : Output) (hwf : contextWF Γ = true)
      (h1 : Derivable ⟨Γ1, .outputDecl α⟩) (h2 : Derivable ⟨Γ2, .outputDecl β⟩) :
      Derivable ⟨Γ, .outputDecl (.sum α β)⟩
  /-- output_prod (Table 1). -/
  | outputProd (Γ Γ1 Γ2 : Context) (α β : Output) (hwf : contextWF Γ = true)
      (h1 : Derivable ⟨Γ1, .outputDecl α⟩) (h2 : Derivable ⟨Γ2, .outputDecl β⟩) :
      Derivable ⟨Γ, .outputDecl (.prod α β)⟩
  /-- output_arr (Table 1): the arrow shape; the annotation is pinned later,
      by I→. -/
  | outputArr (Γ Γ1 Γ2 : Context) (α β : Output) (a : Prob)
      (hwf : contextWF Γ = true)
      (h1 : Derivable ⟨Γ1, .outputDecl α⟩) (h2 : Derivable ⟨Γ2, .outputDecl β⟩) :
      Derivable ⟨Γ, .outputDecl (.arr α a β)⟩
  /-- base (Table 1): the empty distribution. -/
  | base (Γ : Context) (hwf : contextWF Γ = true) :
      Derivable ⟨Γ, .distDecl []⟩
  /-- extend (Table 1): extend a distribution by one exact entry, preserving
      per-variable additivity. -/
  | extend (Γc Γp Γ Γ' : Context) (e : ContextEntry) (a : Prob)
      (hwf : contextWF Γc = true)
      (hp : Derivable ⟨Γp, .distDecl Γ⟩)
      (hlen : Γ'.length = Γ.length + 1)
      (htake : Γ'.take Γ.length = Γ)
      (hlast : Γ'.getLast? = some e)
      (hexact : e.constraint = .exact a)
      (hmass : (Γ.foldl (fun acc entry =>
          if entry.name == e.name then
            match entry.constraint with
            | .exact p => acc + p.val
            | _        => acc
          else acc) (0 : ℚ)) + a.val ≤ 1) :
      Derivable ⟨Γc, .distDecl Γ'⟩
  /-- extend_det (Table 1): a deterministic assignment `x : α` read as
      `x : α₁`, under the ordinary additivity discipline. -/
  | extendDet (Γc Γp Γ Γ' : Context) (e : ContextEntry) (a : Prob)
      (hwf : contextWF Γc = true)
      (hp : Derivable ⟨Γp, .distDecl Γ⟩)
      (hlen : Γ'.length = Γ.length + 1)
      (htake : Γ'.take Γ.length = Γ)
      (hlast : Γ'.getLast? = some e)
      (hexact : e.constraint = .exact a)
      (hone : a.val = 1)
      (hmass : (Γ.foldl (fun acc entry =>
          if entry.name == e.name then
            match entry.constraint with
            | .exact p => acc + p.val
            | _        => acc
          else acc) (0 : ℚ)) + a.val ≤ 1) :
      Derivable ⟨Γc, .distDecl Γ'⟩
  /-- unknown (Table 1): an opaque distribution `{x : α_[0,1] | α ∈ A}` over
      one process, with pairwise-distinct outputs, each declared well-formed. -/
  | unknown (Γc : Context) (e0 : ContextEntry) (rest : List ContextEntry)
      (Δs : List Context)
      (hwf : contextWF Γc = true)
      (hname : rest.all (fun r => r.name == e0.name) = true)
      (hdistinct : (((e0 :: rest).map (·.output)).eraseDups).length
                     = (e0 :: rest).length)
      (hunk : ∀ e ∈ (e0 :: rest), e.constraint = .unknown)
      (hlen : Δs.length = (e0 :: rest).length)
      (houts : ∀ pr ∈ Δs.zip (e0 :: rest),
                 Derivable ⟨pr.1, .outputDecl pr.2.output⟩) :
      Derivable ⟨Γc, .distDecl (e0 :: rest)⟩

  /-- I→ (Table 4): discharge the unique exact assumption `x : α_a` and
      internalise its value as the arrow annotation. -/
  | iArr (Γp ctx : Context) (tc : TermClaim) (x : String) (α : Output)
      (a : Prob) (de : ContextEntry)
      (hwf : contextWF ctx = true)
      (hp : Derivable ⟨Γp, .term tc⟩)
      (hfilter : Γp.filter (fun e =>
          e.name == x && e.output == α &&
          match e.constraint with | .exact _ => true | _ => false) = [de])
      (hdec : de.constraint = .exact a)
      (hctx : contextEqSet ctx (Γp.filter (· != de)) = true) :
      Derivable ⟨ctx, .term ⟨tc.mode, .lam x tc.term, tc.samples,
        .arr α a tc.output, tc.value, tc.prov⟩⟩
  /-- E→ (Table 4): apply an abstraction to an argument matching the arrow
      source; values multiply and the premise contexts merge. -/
  | eArr (Γ1 Γ2 ctx : Context) (tc1 tc2 : TermClaim) (α β : Output) (a : Prob)
      (hwf : contextWF ctx = true)
      (h1 : Derivable ⟨Γ1, .term tc1⟩)
      (h2 : Derivable ⟨Γ2, .term tc2⟩)
      (hmode : tc1.mode = tc2.mode)
      (hn : tc1.samples = tc2.samples)
      (hprov : tc1.prov = tc2.prov)
      (hlam : (match tc1.term with | Term.lam _ _ => true | _ => false) = true)
      (hout : tc1.output = .arr α a β)
      (hsrc : α = tc2.output)
      (hctx : contextEqSet ctx (mergeContexts [Γ1, Γ2]) = true) :
      Derivable ⟨ctx, .term ⟨tc1.mode, .app tc1.term tc2.term, tc1.samples, β,
        probMul tc1.value tc2.value, tc1.prov⟩⟩
  /-- ETex (Table 6): under a one-sample Trust certificate, re-enter the
      expected layer at the trusted model value; the observed variable's own
      non-exact assumption is replaced by the trusted exact one, and the
      trusted value must lie in the constraint it replaces. -/
  | eTex (Γp ctx : Context) (t : Term) (n : Nat) (α : Output)
      (f p : Prob) (interval : Constraint) (σ : Provenance)
      (eOld eNew : ContextEntry)
      (hwf : contextWF ctx = true)
      (hp : Derivable ⟨Γp, .trust (.trust .oneSample t n α f p interval σ)⟩)
      (hold : Γp.filter (· ∉ ctx) = [eOld])
      (hnew : ctx.filter (· ∉ Γp) = [eNew])
      (hname : eOld.name = eNew.name)
      (houts : eOld.output = eNew.output)
      (holdα : eOld.output = α)
      (hnewc : eNew.constraint = .exact p)
      (hnonexact : (match eOld.constraint with
                    | Constraint.exact _ => false | _ => true) = true)
      (hcont : eOld.constraint.contains p = true) :
      Derivable ⟨ctx, .term ⟨.expected, t, n, α, p, σ⟩⟩
  /-- ENEx (Table 6): under a No-Excess certificate and an exact benchmark
      for the right group, bound the left observation by the shifted
      interval [p+ℓ, p+h]. -/
  | eNEx (Γe Γm ctx : Context) (tcL tcR : TermClaim) (diff : Prob)
      (lo hi : Prob) (me se : ContextEntry) (p : Prob) (σ : Provenance)
      (hwf : contextWF ctx = true)
      (he : Derivable ⟨Γe, .comparison (.noExcess tcL tcR diff (.interval lo hi))⟩)
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

  /-- sampling (Table 3): collect n single-run experiments of one term into
      the observed frequency of an output.  Premises must be experiment-form
      (one sample, one provenance token each) with pairwise-disjoint runs;
      the conclusion's provenance is their union and its value the observed
      relative frequency. -/
  | sampling (Γc : Context) (Δs : List Context) (tcs : List TermClaim)
      (t : Term) (α : Output) (f : Prob)
      (hwf : contextWF Γc = true)
      (hne : tcs ≠ [])
      (hlen : Δs.length = tcs.length)
      (hprems : ∀ pr ∈ Δs.zip tcs, Derivable ⟨pr.1, .term pr.2⟩)
      (hctxs : Δs.all (fun Δ => contextEqSet Δ Γc) = true)
      (hexp : tcs.all (fun tc =>
          tc.prov.card == 1 && tc.samples == 1 && tc.mode == .frequency) = true)
      (hterm : tcs.all (·.term == t) = true)
      (hdisj : Provenance.pairwiseDisjoint (tcs.map (·.prov)) = true)
      (hval : f.val = (((tcs.filter (·.output == α)).length : ℚ)
                        / (tcs.length : ℚ))) :
      Derivable ⟨Γc, .term ⟨.frequency, t, tcs.length, α, f,
        (tcs.map (·.prov)).foldl (· ∪ ·) ∅⟩⟩

  /-- Contraction (Table 7): the assumptions about one (variable, output)
      pair — and only one — collapse to a single exact value drawn from the
      intersection of their constraints; at least one collapsed constraint
      must be informative, and everything else is carried over unchanged. -/
  | contraction (Γp ctx : Context) (J : Claim)
      (k : String × Output) (repl : ContextEntry) (a : Prob)
      (hwf : contextWF ctx = true)
      (hp : Derivable ⟨Γp, J⟩)
      (hgroup : ((Γp.map (fun e => (e.name, e.output))).eraseDups).filter
          (fun k' => (Γp.filter (fun e => (e.name, e.output) == k')).length ≥ 2 &&
                     (ctx.filter (fun e => (e.name, e.output) == k')).length == 1)
          = [k])
      (hrest : contextEqSet (Γp.filter (fun e => (e.name, e.output) != k))
                            (ctx.filter (fun e => (e.name, e.output) != k)) = true)
      (hrepl : ctx.filter (fun e => (e.name, e.output) == k) = [repl])
      (hexact : repl.constraint = .exact a)
      (hinf : (Γp.filter (fun e => (e.name, e.output) == k)).any
          (fun r => !(match r.constraint with
            | .unknown => true
            | .interval lo hi => decide (lo.val == 0 && hi.val == 1)
            | _ => false)) = true)
      (hin : (Γp.filter (fun e => (e.name, e.output) == k)).all
          (fun r => r.constraint.contains a) = true) :
      Derivable ⟨ctx, J⟩

  /-- I-P (Table 5): form a Bayesian prior family from singleton exact
      identity judgements sharing the family indices (x, α, y, β).  The
      weights must sum to 1 and the hypothesis values must be pairwise
      distinct; the family is concluded in the empty context. -/
  | iPrior (es es' : List ContextEntry) (points : List (Prob × Prob))
      (fam : PriorFamily)
      (hne : es ≠ [])
      (hlen : es.length = es'.length)
      (hplen : points.length = es.length)
      (hprems : ∀ pr ∈ es.zip es', Derivable ⟨[pr.1], .identity pr.2⟩)
      (hidx : ∀ pr ∈ es.zip es',
          pr.1.name = fam.xName ∧ pr.1.output = fam.alpha ∧
          pr.2.name = fam.yName ∧ pr.2.output = fam.beta)
      (hexact : ∀ q ∈ (es.zip es').zip points,
          q.1.1.constraint = .exact q.2.1 ∧ q.1.2.constraint = .exact q.2.2)
      (hpoints : fam.points = points)
      (hsum : (points.map (·.2.val)).foldl (· + ·) 0 = 1)
      (hdistinct : ((points.map (·.1.val)).eraseDups).length = points.length) :
      Derivable ⟨[], .priorFamily fam⟩

  /-- E-P (Table 5): eliminate a prior family against a frequency
      observation of the hypothesis output, concluding the exact Bayesian
      posterior for the hypothesis selected by the unique exact assumption
      `x : α_{aⱼ}` in the conclusion context.  The conclusion context is
      the observation's context plus that hypothesis, nothing else. -/
  | ePosterior (Γp Γo ctx : Context) (fam : PriorFamily) (obs : TermClaim)
      (concEntry se : ContextEntry) (aJ posterior : Prob) (j : Nat)
      (hwf : contextWF ctx = true)
      (hprior : Derivable ⟨Γp, .priorFamily fam⟩)
      (hobs : Derivable ⟨Γo, .term obs⟩)
      (hfne : fam.points ≠ [])
      (hmode : obs.mode = .frequency)
      (hα : obs.output = fam.alpha)
      (hn : obs.samples > 0)
      (hden : ((obs.samples : ℚ) * obs.value.val).den = 1)
      (hnum : ((obs.samples : ℚ) * obs.value.val).num ≥ 0)
      (hsub : ctx.all (fun e => e ∈ Γo ||
          (e.name == fam.xName && e.output == fam.alpha &&
           match e.constraint with | .exact _ => true | _ => false)) = true)
      (hpres : Γo.all (· ∈ ctx) = true)
      (hcname : concEntry.name = fam.yName)
      (hcout : concEntry.output = fam.beta)
      (hcexact : concEntry.constraint = .exact posterior)
      (hse : ctx.filter (fun e =>
          e.name == fam.xName && e.output == fam.alpha &&
          match e.constraint with | .exact _ => true | _ => false) = [se])
      (hsec : se.constraint = .exact aJ)
      (hfind : (fam.points.map (fun p => (p.1.val, p.2.val))).findIdx?
          (fun ⟨a, _⟩ => decide (a == aJ.val)) = some j)
      (hpost : bayesianPosterior (fam.points.map (fun p => (p.1.val, p.2.val)))
          ((obs.samples : ℚ) * obs.value.val).num.toNat obs.samples j
          = some posterior.val) :
      Derivable ⟨ctx, .identity concEntry⟩

end TPTND
