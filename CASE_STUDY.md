# Case study: a kernel-checked TPTND certificate of the ProPublica COMPAS audit

This document walks through a single TPTND-Lean derivation that produces a
machine-checked certificate of the central claim from ProPublica's 2016
COMPAS audit, alongside the Northpointe rebuttal and a calibration check.

The whole point of running the certificate is this: a TPTND derivation
tree is a sequence of inferential moves, each of which the kernel
verifies against a precise side condition. If any move would let an
auditor draw an unjustified conclusion — by miscounting, by pooling
overlapping samples, by using a confidence interval the data doesn't
support — the kernel rejects the tree. So when the kernel says
"accepted", you have a non-handwavy receipt that the public claim is
arithmetically and structurally consistent with the published data.

Source: [`TPTND/PPDiverse.lean`](TPTND/PPDiverse.lean).
Build & run: `lake build pp_diverse && ./.lake/build/bin/pp_diverse`.

---

## 1. The ProPublica claim, verbatim

From *Machine Bias* (Angwin, Larson, Mattu, Kirchner — ProPublica,
May 23 2016):

> "The formula was particularly likely to falsely flag black defendants
> as future criminals, wrongly labeling them this way at almost twice
> the rate as white defendants."

From the accompanying methodology paper *How We Analyzed the COMPAS
Recidivism Algorithm* (Larson, Mattu, Kirchner, Angwin):

> "Black defendants who did not recidivate over a two-year period were
> nearly twice as likely to be misclassified as higher risk compared to
> their white counterparts (45 percent vs. 23 percent)."

This is the **equal-FPR** (false-positive rate) fairness criterion. The
certificate's headline sub-derivation translates exactly this paragraph
into a TPTND derivation, then asks the kernel: *given the published
counts, is this disparity statistically real, or could it be noise?*

Northpointe (the vendor of COMPAS) replied with a different criterion in
their July 2016 response (*COMPAS Risk Scales: Demonstrating Accuracy
Equity and Predictive Parity*, Dieterich, Mendoza, Brennan):

> "COMPAS achieves equal predictive parity across racial groups."

This is the **equal-PPV** (positive predictive value) criterion: among
defendants the model flagged as high-risk, the rate of actual
recidivism is the same in both racial groups. The certificate's second
sub-derivation translates this rebuttal.

The famous mathematical content of the dispute (Chouldechova 2017;
Kleinberg–Mullainathan–Raghavan 2016) is that *both can be true at
once*, and they are, on this data — TPTND-Lean checks each criterion
separately and produces a structured certificate that reports both
verdicts.

## 2. Why having a checkable certificate matters

A fairness audit usually lands as a press release, a methodology PDF, and
a spreadsheet — three artefacts the reader has to manually cross-check
before believing any of them. A *checkable certificate* collapses these
into one machine-verifiable document, with several practical
consequences:

* **Cross-checking is automatic.** Anyone with the kernel binary can
  re-run `pp_diverse` and get the same verdict, without trusting the
  auditor's spreadsheet arithmetic.

* **Disagreements become precise.** If you disagree with the audit, you
  must point to a specific node — a raw count at a leaf, a CI
  procedure, an independence claim — and explain why the kernel's side
  condition was the wrong gate. That's a much narrower argument than
  "I don't believe your numbers".

* **Adversarial moves are blocked structurally.** An attacker cannot
  smuggle in sample-size inflation, double-counting via overlapping
  provenance, wrong chain-rule arithmetic, or fabricated interval
  intersections. Each is the side condition of some rule, and the
  kernel refuses any tree that violates one.

* **Audits compose.** The trust-interval entries that `EUT` and `ET`
  write into the typing context are designed to be picked up by future
  certificates. A follow-up audit can re-use today's verdict by
  composing rather than redoing the math from scratch.

* **Provenance is on the record.** Every leaf cites a cohort by name;
  every `Update` commits to disjoint provenances; every `WeakeningS`
  carries an explicit independence witness. The certificate is an
  *immutable structural record* of which datasets and which assumptions
  the verdict depends on.

In short: a TPTND certificate turns a fairness audit from a *narrative*
into an *artefact* — one that any third party can independently
verify, dissect, attack, or compose with.

## 3. What the certificate is actually checking

In one sentence per sub-derivation:

| Sub-tree | What the kernel is asked to verify |
| --- | --- |
| **subA** ProPublica FPR | "On the published 6,172-row filter, the false-positive flagging rate for Black non-recidivists differs from that for White non-recidivists by *more* than the score-test confidence interval allows under the equal-rate null. Therefore the equal-FPR claim must be Untrusted." |
| **subA′** Calibration on Black PPV | "On the same filter, the empirical positive predictive value for Black defendants (775/1234) is *outside* the confidence interval centred at the model's calibrated rate of 0.50. Therefore the model's calibration claim, restricted to Black defendants, must be Untrusted." |
| **subB** Northpointe PPV | "On the same filter, the difference between Black PPV (775/1234) and White PPV (272/460) lies inside the score-test CI, which contains zero. Therefore the equal-PPV claim is compatible with the data — Trusted." |
| **subC** Joint audit | "Treating classification (Flagged) and outcome (Recidivated) as independent attributes of the same defendant, the joint frequency equals the product. The kernel checks the multiplication and the syntactic separation of the two output types." |
| **subD** Calibration as a conditional | "The conditional probability P(Recidivated \| Flagged) is *packaged* as a typed conditional that can be applied to other Flagged frequencies via the chain rule, without recomputing." |
| **subE** Prior consolidation | "Two earlier audits (a 2014 estimate of [40 %, 45 %] and a 2016 estimate of [42 %, 50 %] for the Black FPR) are reconciled into the single point estimate 0.43 — and the kernel checks that 0.43 actually lies in the intersection." |

The top-level `WeakeningS` chain bundles these six sub-certificates into
one auditable document. The bundle's *headline conclusion* is subA's
claim — the disparity verdict — but the document also carries the other
sub-trees' conclusions, and any future audit can pick up where this one
left off by composing with one of the trust-interval entries.

## 4. ASCII derivation trees

These are drawn in standard natural-deduction style — **premises on top,
conclusion below the rule's horizontal bar**. The rule name labels the
bar on the right. Each `Obs` / `Identity` line at the very top of a
tree is a leaf with no premises (the "─── obs" / "─── id" mark above it
just stands for "no premise"). Read each sub-tree top-down; read each
horizontal bar as *"from these premises, by this rule, conclude this"*.

### subA — ProPublica FPR pipeline

```text
─── obs       ─── obs        ─── obs       ─── obs        ─── obs       ─── obs        ─── obs       ─── obs
BM:Med_{198/  BM:High_{312/  BF:Med_{56/   BF:High_{75/   WM:Med_{130/  WM:High_{62/   WF:Med_{70/   WF:High_{20/
       1168}        1168}          346}          346}            969}         969}            312}         312}
──────────────────── I+      ──────────────────── I+      ──────────────────── I+      ──────────────────── I+
   BM:Flagged_{510/1168}        BF:Flagged_{131/346}         WM:Flagged_{192/969}         WF:Flagged_{90/312}
   ──────────────────────────────────── Update             ──────────────────────────────────── Update
            B:Flagged_{641/1514}                                     W:Flagged_{282/1281}
            ─────────────────────────────────────────────────────────────────────────────────── IUT2
                                            UTrust(equal-FPR : 0 ∉ [16.8 %, 23.8 %])
                                            ─────────────────────────────────────────── EUT
                                              B:Flagged_{641/1514}, ⟨ x_FPR : ¬[16.8 %, 23.8 %] in ctx ⟩
```

### subA' — calibration on Black PPV (one-sample)

```text
─── identity                    ─── obs
x_model : Recidivated_{0.5}     v_B : Recidivated_{775/1234}
──────────────────────────────────────────────────────────── IUT
              UTrust(model 0.5 ∉ binomialCI for 775/1234)
              ─────────────────────────────────────────── EUT
              v_B : Recidivated_{775/1234},
                ⟨ x_model exact ⟩ ⟨ x_PPV_gap ¬[ℓ, h] in ctx ⟩
              ─────────────────────────────────────────── I→  (discharges x_model)
              [x_model] v_B : (Recidivated ⇒ Recidivated)_{775/1234}      ─── obs
                                                                          u_apply : Recidivated_{925/1234}
              ──────────────────────────────────────────────────────────────────────────────────────────── E→
                                ([x_model] v_B · u_apply) : Recidivated_{(775·925)/1234²}
```

### subB — Northpointe PPV defence

```text
─── obs                          ─── obs
v_B : Recidivated_{775/1234}     v_W : Recidivated_{272/460}
──────────────────────────────────────────────────────────── IT2
              Trust(equal-PPV : 0 ∈ [0.0 %, 8.9 %])
              ─────────────────────────────────────── ET
                v_B : Recidivated_{775/1234},
                ⟨ x_PPV : [0.0 %, 8.9 %] in ctx ⟩
```

### subC — joint independence audit

```text
─── obs                          ─── obs
u_audit : Flagged_{1/2}          u_audit : Recidivated_{3/10}
─────────────────────────────────────────────────────────── I×  (witness asserted)
            (u_audit, u_audit) : (Flagged × Recidivated)_{3/20}            ─── obs
                                                                           u_audit : Recidivated_{3/10}
            ─────────────────────────────────────────────────────────────────────────────────────── E×L
                                                u_audit : Flagged_{1/2}
```

### subD — calibration packaged as a typed conditional

```text
─── obs  ⟨ with x_flag : Flagged_{716/1694} exact in ctx ⟩
u_calib : Recidivated_{1047/1694}
──────────────────────────────────────────────────── I→  (discharges x_flag)
[x_flag] u_calib : (Flagged ⇒ Recidivated)_{1047/1694}     ─── obs
                                                           v_flag : Flagged_{716/1694}
──────────────────────────────────────────────────────────────────────────────────────── E→
                ([x_flag] u_calib · v_flag) : Recidivated_{(1047·716)/1694²}
```

### subE — consolidating two prior audits

```text
─── obs ⟨ with x_FPR :Flagged_{[40 %, 45 %]} (Audit 2014) and x_FPR :Flagged_{[42 %, 50 %]} (Audit 2016) in ctx ⟩
u_post : Flagged_{0.43}
──────────────────────────────────────────── Contraction  (collapse intervals → x_FPR : Flagged_{0.43})
u_post : Flagged_{0.43}
```

### Top-level — `WeakeningS` chain bundling the six sub-trees

The five `WeakeningS` applications form a left-leaning chain that
bundles each sub-certificate, in order, into the running audit
document. Reading top-down (premises on top, document at the bottom):

```text
{subA conclusion}           {subA' conclusion}
                                 │
─────────────────────────────────┴───────────────── WeakeningS  (witness asserted)
                ws₀                                                       {subB conclusion}
                                                                                 │
                ─────────────────────────────────────────────────────────────────┴────────── WeakeningS
                                          ws₁                                                                {subC conclusion}
                                                                                                                  │
                                          ───────────────────────────────────────────────────────────────────────┴──────────── WeakeningS
                                                                ws₂                                                                              {subD conclusion}
                                                                ─────────────────────────────────────────────────────────────────────────────────────────────── WeakeningS
                                                                                       ws₃                                                                                          {subE conclusion}
                                                                                       ──────────────────────────────────────────────────────────────────────────────────────────── WeakeningS
                                                                                                                                              audit document  (root, with subA's claim)
```

The audit document at the root retains the deepest sub-tree's claim
(subA's FPR-disparity verdict) and merges every premise context. Each
WeakeningS commitment carries an explicit *independence witness* —
the auditor's assertion, on the record, that the two combined
sub-certificates rest on independent provenance.

## 5. ProPublica narrative → derivation node mapping

This is the core of the case study: each sentence the audit makes
in plain English maps to one rule application, and the kernel check on
that rule application is what makes the sentence formally meaningful.

### subA — ProPublica's headline FPR-disparity finding

The audit narrative for this sub-derivation reads, sentence by
sentence:

> *"We start from the published 6,172-row Broward County filter,
> restricted to defendants who did not recidivate within two years."*

The eight `Obs` leaves of subA encode exactly this: each leaf is a raw
empirical claim like *"of 1168 Black-male non-recidivists, 198 were
rated Medium-risk"*. The kernel's check on `Obs` is that the
provenance is non-empty (the leaf cites a real cohort), the sample
size is positive, and the cohort's support entry exists in the typing
context. There is no oracle for the count itself — the leaf is
trusted for the data; the rest of the tree is what the kernel
actually verifies.

> *"The Medium and High risk categories together constitute the
> 'flagged' classification."*

Each `I+` step formalises this binarisation. Its kernel check is
the syntactic disjointness `Medium ⊥_syn High` (the two risk types
share no atomic component, so adding their frequencies cannot
double-count) and that the conclusion's frequency is exactly the sum
of the premise frequencies.

> *"Within each race we pool male and female non-recidivists into a
> single audit cohort."*

Each `Update` step formalises this pooling. Its kernel check is that
the male and female provenances are disjoint (no defendant counted
twice) and that the pooled frequency is the weighted average,
*exactly* in rationals — the kernel rejects any arithmetic
shortcut.

> *"Black non-recidivists were flagged at 42.3 %; White at 22.0 %.
> Could this gap be sampling noise? The score-test 95 % CI for the
> difference is [16.8 %, 23.8 %], which excludes zero."*

This is the `IUT2` step — the formal rendering of ProPublica's
*"nearly twice as likely to be misclassified as higher risk"*
sentence. The kernel computes the score-test CI in exact rationals
and checks that 0 lies outside it. If the CI included zero, the
kernel would reject `IUT2` and demand an `IT2` instead — i.e., the
rule itself enforces the *direction* of the verdict.

> *"From here on, any downstream certificate may assume the gap
> interval as a typing-context fact."*

The final `EUT` step writes the gap interval `¬[16.8 %, 23.8 %]` into
the typing context as a transferable assumption. The kernel checks
that the conclusion's context contains this entry and that no
unrelated entries are smuggled in.

### subA′ — calibration on Black PPV (one-sample IUT)

This sub-derivation makes a *different* claim using a *different* family
of rules, and is included to show how a fixed-rate hypothesis is
checked. The narrative:

> *"The model is calibrated to 0.50 — that's its declared average
> recidivism rate among flagged defendants."*

The `Identity` leaf encodes the model's claim as an exact-typed
context entry `x_model : Recidivated_{0.5}`. The kernel checks
that this leaf's context is a singleton — i.e., the model's claim is
declared standalone, not buried in a larger hypothesis.

> *"Empirically, on the Black flagged sub-cohort, 775 of 1234 actually
> recidivated — that's 62.8 %."*

The `Obs` leaf records the empirical rate.

> *"0.50 lies outside the binomial CI for 775/1234 — therefore the
> calibration claim, restricted to this cohort, is Untrusted."*

This is the `IUT` step: the kernel computes `binomialCI(1234, 0.628,
0.5)` in exact rationals and checks that 0.50 lies *outside* it.

> *"Promote the calibration-gap interval into the typing context, but
> keep the original model-rate entry around for downstream
> reasoning."*

The `EUT` step does both at once.

> *"There is, then, a function from 'model says rate = p' to
> 'recidivism rate = 0.628'. We package this as a typed conditional."*

The `I→` step discharges the `x_model` entry from the context and
returns a derivation whose conclusion type is the arrow
`Recidivated ⇒ Recidivated` — a typed conditional certificate. The
kernel checks that the discharged entry was exact, that the lambda
binder name matches the discharged entry's name, and that the
arrow type is well-formed.

> *"Apply this conditional to a fresh empirical rate, via the chain
> rule."*

The `E→` step applies the conditional to another `Obs` leaf. The
kernel checks that the two premises share term-shape, sample size,
and provenance, and that the conclusion frequency is exactly the
product (chain rule).

### subB — Northpointe's PPV-equality defence

The narrative is shorter:

> *"Among defendants the model flagged, 775 of 1234 Black and 272 of
> 460 White actually recidivated."*

Two `Obs` leaves.

> *"The two-sample 95 % CI for the difference of these two rates is
> [0.0 %, 8.9 %]. It contains zero. Therefore the equal-PPV claim is
> Trusted on this data."*

The `IT2` step is the *symmetric counterpart* of `IUT2`: the kernel
computes the same score-test CI but checks that 0 lies *inside* it.
Same rule family, opposite verdict.

> *"Carry the trusted PPV-equality interval forward."*

The `ET` step adds the interval to the typing context.

### subC — joint attribute audit

The narrative of *"two attributes of the same defendant, treated as
independent"* maps to:

- two `Obs` leaves recording the marginals (one for Flagged, one for
  Recidivated) on a small audit cohort;
- one `I×` step that combines them into a single product-typed
  judgment, with an explicit *independence witness* asserted by the
  auditor (the kernel does not check independence — it only checks
  that the witness is present, putting the assumption on the record);
- one `E×L` step that projects the joint judgment back onto the
  Flagged factor by dividing the joint by the conditioning factor.

### subD — calibration packaged as a conditional

Same shape as subA′'s `I→ / E→` tail, applied to the overall flagged
cohort (Black + White) rather than just the Black sub-cohort. The
narrative is:

> *"P(Recidivated | Flagged) = 1047/1694 ≈ 61.8 %. Package this as a
> conditional certificate that we can apply later."*

The `I→` step packages it; the `E→` step applies it to a fresh
Flagged frequency, checking the chain rule.

### subE — consolidating prior audits

This sub-tree shows how multiple historical audits collapse into a
single point estimate. The narrative:

> *"A 2014 audit placed the Black FPR in [40 %, 45 %]; a 2016 audit
> placed it in [42 %, 50 %]. We are willing to commit to the point
> estimate 0.43 — but only because 0.43 is in the intersection of
> the two prior intervals."*

The `Contraction` step does exactly this collapse, and the kernel
checks the intersection-membership condition (`0.43 ∈ [0.40, 0.45] ∩
[0.42, 0.50]`). If we'd written `0.10` instead, the kernel would
reject — a key adversarial-attack defence.

### Top-level — `WeakeningS` chain

Each of the five `WeakeningS` applications combines one sub-certificate
with the running audit document, retaining the deepest sub-tree's
claim and merging the contexts. The kernel check is the explicit
*independence witness* (the auditor asserts that the two
sub-certificates rest on independent provenance) and the structural
constraint that the merged context contains both premise contexts.

The headline conclusion at the root is therefore subA's frequency
claim about Black non-recidivists, with the FPR-gap interval carried
in the typing context — exactly the formal content of *"the
equal-FPR hypothesis fails on the published data"*. But the
document also carries Northpointe's PPV-equality certificate, the
calibration certificates, the joint-attribute claim, and the
consolidated prior — all in one bundle, all kernel-checked.

## 6. The fairness landscape, in plain English

There is no single "fair" — there are several orthogonal definitions
that data scientists disagree about. This certificate puts three of them
side by side:

* **Equal FPR** (ProPublica) — *"are non-recidivists flagged at the
  same rate across races?"* On this data: **no**, with a kernel-checked
  Untrusted verdict.
* **Equal PPV** (Northpointe) — *"are the model's flagged defendants
  equally likely to actually recidivate, across races?"* On this data:
  **yes**, with a kernel-checked Trusted verdict.
* **Calibration** — *"does the model's quoted risk score equal the
  empirical recidivism rate of those it gives that score?"* On this
  data: **no**, restricted to the Black sub-cohort.

These three verdicts can hold *simultaneously* on the published
COMPAS data because of the impossibility result: when the underlying
group base rates differ, no single algorithm can satisfy more than one
of the three at once. TPTND-Lean does not resolve the dispute. It
makes each side's claim a *separately* checkable certificate, with
the side conditions of the calculus standing in for the auditor's
informal "I checked the arithmetic". Each verdict's certificate can
be inspected, composed, or attacked independently.

## 7. What the kernel is NOT checking

A few things it would be honest to flag:

* **Raw counts at the leaves.** `Obs` trusts the leaf's claim about
  the data. If you write *"1500 Black non-recidivists were flagged"*
  when the CSV says 510, the kernel won't notice — the leaf is the
  ingestion boundary. Defence: use a separate ingest auditor (e.g.
  `compas_audit` against the published CSV).

* **Choice of CI procedure.** The kernel computes one specific kind of
  CI — the score-test (Wilson) interval in exact rationals. If a
  different methodology (Wald, Clopper-Pearson, Bayesian credible
  interval) would have given the opposite verdict on a borderline
  case, the certificate doesn't tell you that. The procedure is
  fixed by the kernel implementation, not by the certificate.

* **Choice of cohort.** Dropping or relabelling whole sub-cohorts
  produces a different but kernel-valid certificate of a different
  audit. The *kernel* never knows what audit you intended; the
  *certificate* is what a reader can hold you to.

These boundaries are honest gaps; each could be closed by a separate
auditor module. The kernel's job is to ensure that, *given* the leaves
and *given* the procedure, every inferential move is sound.

## 8. Reproducing the verdict

```sh
lake build pp_diverse
./.lake/build/bin/pp_diverse
```

The binary prints the kernel verdict and a per-rule justification
table. Every rule application is paired with the audit-report sentence
it formalises and the kernel-checked side condition that gates it.

If any side condition were violated, the kernel would reject. As a
quick sanity check that the kernel really is doing the work, edit
`PPDiverse.lean` to change the IUT2 step's `untrust` to `trust`
(claiming equal-FPR is *Trusted*) and rebuild — the kernel will refuse
the certificate with `IT2: 0 must lie within two-sample CI`, because
the data does not support that verdict.
