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

end TPTND
