# Case study: a kernel-checked TPTND certificate of the ProPublica COMPAS audit

A single TPTND-Lean derivation certifies the central claim from
ProPublica's 2016 COMPAS audit, the Northpointe rebuttal, and a
calibration check, side by side. The kernel verifies every inferential
step against a precise side condition; if any step lets the auditor
draw a conclusion the data doesn't support — a miscount, a pool of
overlapping samples, a confidence interval the procedure doesn't allow
— the kernel refuses the tree. Acceptance is therefore a receipt, not
an assurance.

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

That's the equal-FPR (false-positive rate) criterion. The certificate's
headline sub-derivation puts this paragraph through the kernel and asks:
given the published counts, is the disparity real, or could it be
sampling noise?

Northpointe (the vendor of COMPAS) replied with a different criterion in
its July 2016 response (*COMPAS Risk Scales: Demonstrating Accuracy
Equity and Predictive Parity*, Dieterich, Mendoza, Brennan):

> "COMPAS achieves equal predictive parity across racial groups."

That's the equal-PPV (positive predictive value) criterion: among
defendants the model flagged as high-risk, the rate of actual
recidivism is the same in both racial groups. The certificate's second
sub-derivation handles the rebuttal.

Both can be true at once on the same data — the result familiar from
Chouldechova (2017) and Kleinberg–Mullainathan–Raghavan (2016) — and on
this data they are. TPTND-Lean checks each criterion separately and
reports both verdicts in one structured certificate.

## 2. Why having a checkable certificate matters

A fairness audit usually arrives as a press release, a methodology PDF,
and a spreadsheet. The reader has to cross-check three artefacts before
believing any of them. A single machine-checkable certificate folds
those into one document, with five practical consequences.

Anyone with the kernel binary can re-run `pp_diverse` and reach the
same verdict, without trusting the auditor's spreadsheet arithmetic.

If you disagree with the audit, you have to point at a specific node.
That might be a raw count at a leaf, the choice of CI procedure, or an
independence claim — but you have to say which one, and explain why
the kernel's side condition was the wrong gate. That's a much narrower
argument than "I don't believe your numbers".

The kernel blocks adversarial moves structurally. Sample-size
inflation, double-counting via overlapping provenance, wrong
chain-rule arithmetic, fabricated interval intersections — each is the
side condition of some rule. Any tree that violates one is rejected.

Audits compose. The trust-interval entries that `EUT` and `ET` write
into the typing context can be picked up by future certificates: a
follow-up audit re-uses today's verdict by composing rather than
redoing the math from scratch.

Provenance is on the record. Every leaf cites a cohort by name; every
`Update` commits to disjoint provenances; every `WeakeningS` carries
an explicit independence witness. The certificate is an immutable
structural record of the datasets and assumptions the verdict depends
on.

A TPTND certificate, in other words, is the difference between a
fairness audit as a story and a fairness audit as an artefact. A third
party can verify, dissect, attack, or compose with the artefact. The
story they can only argue with.

## 3. What the certificate is actually checking

| Sub-tree | What the kernel is asked to verify |
| --- | --- |
| **subA** ProPublica FPR | On the published 6,172-row filter, the false-positive flagging rate for Black non-recidivists differs from the rate for White non-recidivists by more than the score-test confidence interval allows under the equal-rate null. The equal-FPR claim is therefore Untrusted. |
| **subA′** Calibration on Black PPV | The empirical positive predictive value for Black defendants (775/1234) lies outside the confidence interval centred at the model's calibrated rate of 0.50. The model's calibration claim, restricted to Black defendants, is Untrusted. |
| **subB** Northpointe PPV | The difference between Black PPV (775/1234) and White PPV (272/460) lies inside the score-test CI, which contains zero. The equal-PPV claim is compatible with the data — Trusted. |
| **subC** Joint audit | Treating classification (Flagged) and outcome (Recidivated) as independent attributes of the same defendant, the joint frequency equals the product. The kernel checks the multiplication and the syntactic separation of the two outputs. |
| **subD** Calibration as a conditional | P(Recidivated \| Flagged) is packaged as a typed conditional, so other Flagged frequencies can be applied to it via the chain rule without recomputing. |
| **subE** Prior consolidation | A 2014 estimate of [40 %, 45 %] and a 2016 estimate of [42 %, 50 %] for the Black FPR are reconciled into the single point estimate 0.43, after the kernel checks that 0.43 actually lies in the intersection. |

The top-level `WeakeningS` chain bundles the six sub-certificates into
one auditable document. The bundle's headline conclusion is subA's —
the disparity verdict — but the document also carries the others, and
any future audit can pick up where this one left off by composing with
one of the trust-interval entries.

## 4. ASCII derivation trees

The trees are drawn in standard natural-deduction style: premises on
top, conclusion below the rule's horizontal bar, rule name on the
right. An `Obs` or `Identity` line at the top of a tree is a leaf with
no premises (the `─── obs` or `─── id` mark above it just stands for
"no premise"). Read each tree top-down; each horizontal bar reads
"from these premises, by this rule, conclude this".

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

### Top-level `WeakeningS` chain bundling the six sub-trees

The five `WeakeningS` applications form a left-leaning chain. Each
adds one sub-certificate to the running audit document:

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

The root retains subA's claim and merges every premise context. Each
`WeakeningS` step carries an explicit independence witness — the
auditor's on-the-record assertion that the two combined sub-certificates
rest on independent provenance.

## 5. ProPublica narrative → derivation node mapping

Each sentence the audit makes in plain English maps to one rule
application. The kernel check on the rule application is what makes the
sentence formally meaningful.

### subA — ProPublica's FPR-disparity finding

> *"We start from the published 6,172-row Broward County filter,
> restricted to defendants who did not recidivate within two years."*

Eight `Obs` leaves carry the raw empirical claims, one per
(race, sex, risk-bucket) cell — for example, *"of 1168 Black-male
non-recidivists, 198 were rated Medium-risk"*. The kernel requires
that the cohort's provenance is non-empty, the sample size is
positive, and the support entry exists in the typing context. It does
not check the count itself: leaves are the ingestion boundary, trusted
for the data.

> *"The Medium and High risk categories together constitute the
> 'flagged' classification."*

`I+` does the binarisation. The kernel checks syntactic disjointness
`Medium ⊥_syn High` — adding their frequencies cannot double-count —
and that the conclusion's frequency is the sum of the premise
frequencies.

> *"Within each race we pool male and female non-recidivists into a
> single audit cohort."*

`Update` does the pooling. The kernel checks that the male and female
provenances are disjoint (no defendant counted twice) and that the
pooled frequency is the weighted average, in exact rationals — no
arithmetic shortcut.

> *"Black non-recidivists were flagged at 42.3 %; White at 22.0 %.
> Could this gap be sampling noise? The score-test 95 % CI for the
> difference is [16.8 %, 23.8 %], which excludes zero."*

This is `IUT2`, the formal counterpart of ProPublica's "nearly twice as
likely to be misclassified" sentence. The kernel computes the
score-test CI in exact rationals and checks that 0 falls outside it.
Had the CI included zero, the kernel would refuse `IUT2` and demand
`IT2` instead. The rule itself encodes the direction of the verdict.

> *"From here on, any downstream certificate may assume the gap
> interval as a typing-context fact."*

`EUT` writes the interval `¬[16.8 %, 23.8 %]` into the typing context
as a transferable assumption. The kernel checks that the conclusion's
context contains the new entry and inherits the rest from the IUT2
premise.

### subA′ — calibration on Black PPV (one-sample IUT)

A different claim, a different rule family, included to show how a
fixed-rate hypothesis is checked.

> *"The model is calibrated to 0.50 — that's its declared average
> recidivism rate among flagged defendants."*

`Identity` declares the model's claim as the singleton context entry
`x_model : Recidivated_{0.5}`. The kernel checks the singleton
condition — the model's claim has to be on its own, not buried in a
larger hypothesis.

> *"Empirically, on the Black flagged sub-cohort, 775 of 1234 actually
> recidivated — that's 62.8 %."*

An `Obs` leaf records the empirical rate.

> *"0.50 lies outside the binomial CI for 775/1234 — therefore the
> calibration claim, restricted to this cohort, is Untrusted."*

`IUT` computes `binomialCI(1234, 0.628, 0.5)` in exact rationals and
checks that 0.50 lies outside it.

> *"Promote the calibration-gap interval into the typing context, but
> keep the original model-rate entry around for downstream
> reasoning."*

`EUT` does both at once.

> *"There is, then, a function from 'model says rate = p' to
> 'recidivism rate = 0.628'. Package it as a typed conditional."*

`I→` discharges the `x_model` entry from the context and produces a
conclusion typed as the arrow `Recidivated ⇒ Recidivated`. The kernel
checks that the discharged entry was exact, that the lambda binder
matches the discharged entry's name, and that the arrow type is
well-formed.

> *"Apply the conditional to a fresh empirical rate, via the chain
> rule."*

`E→` applies the conditional to another `Obs` leaf. The kernel checks
that the two premises share term-shape, sample size, and provenance,
and that the conclusion frequency is the product.

### subB — Northpointe's PPV-equality defence

A shorter narrative.

> *"Among defendants the model flagged, 775 of 1234 Black and 272 of
> 460 White actually recidivated."*

Two `Obs` leaves.

> *"The two-sample 95 % CI for the difference of these two rates is
> [0.0 %, 8.9 %]. It contains zero. Therefore the equal-PPV claim is
> Trusted on this data."*

`IT2` is the symmetric counterpart of `IUT2`: same score-test CI,
opposite gate. The kernel checks that 0 lies inside the CI.

> *"Carry the trusted PPV-equality interval forward."*

`ET` adds the interval to the typing context.

### subC — joint attribute audit

The narrative *"two attributes of the same defendant, treated as
independent"* maps to two `Obs` leaves recording the marginals on a
small audit cohort, an `I×` step combining them into a single
product-typed judgment with an explicit independence witness asserted
by the auditor (the kernel does not check independence — it only
checks that the witness is present, putting the assumption on the
record), and an `E×L` step that recovers the Flagged factor by
dividing the joint by the conditioning factor.

### subD — calibration packaged as a conditional

The same `I→` / `E→` pattern as subA′'s tail, but on the overall
flagged cohort instead of just the Black sub-cohort.

> *"P(Recidivated | Flagged) = 1047/1694 ≈ 61.8 %. Package it as a
> conditional certificate that we can apply later."*

`I→` packages, `E→` applies, the kernel checks the chain rule.

### subE — consolidating prior audits

> *"A 2014 audit placed the Black FPR in [40 %, 45 %]; a 2016 audit
> placed it in [42 %, 50 %]. We are willing to commit to the point
> estimate 0.43 — but only because 0.43 is in the intersection of
> the two prior intervals."*

`Contraction` does the collapse, and the kernel checks the
intersection-membership condition `0.43 ∈ [0.40, 0.45] ∩ [0.42, 0.50]`.
Writing `0.10` instead would be rejected — one of the
adversarial-attack defences worth pointing at.

### Top-level `WeakeningS` chain

Each of the five `WeakeningS` applications adds one sub-certificate to
the running audit document, retaining the deepest sub-tree's claim and
merging the contexts. The kernel check is the explicit independence
witness — the auditor's assertion that the two combined sub-certificates
rest on independent provenance — and the structural constraint that
the merged context contains both premise contexts.

The headline conclusion at the root is subA's frequency claim about
Black non-recidivists, with the FPR-gap interval carried in the typing
context — the formal content of "the equal-FPR hypothesis fails on the
published data". The document also carries Northpointe's PPV-equality
certificate, the calibration certificates, the joint-attribute claim,
and the consolidated prior. All in one bundle, all kernel-checked.

## 6. The fairness landscape, in plain English

There is no single "fair". There are several orthogonal definitions
that data scientists disagree about, and this certificate puts three of
them side by side.

* **Equal FPR** (ProPublica) — *"are non-recidivists flagged at the
  same rate across races?"* On this data: no, with a kernel-checked
  Untrusted verdict.
* **Equal PPV** (Northpointe) — *"are the model's flagged defendants
  equally likely to actually recidivate, across races?"* On this data:
  yes, with a kernel-checked Trusted verdict.
* **Calibration** — *"does the model's quoted risk score equal the
  empirical recidivism rate of those it gives that score?"* On this
  data: no, restricted to the Black sub-cohort.

All three verdicts can hold at once on the published COMPAS data
because of the impossibility result: when the underlying group base
rates differ, no single algorithm can satisfy more than one of the
three at once. TPTND-Lean does not resolve the dispute. It makes each
side's claim a separately checkable certificate, with the side
conditions of the calculus standing in for the auditor's informal
"I checked the arithmetic". Each verdict's certificate can be
inspected, composed, or attacked on its own.

## 7. What the kernel is NOT checking

A few things worth flagging.

**Raw counts at the leaves.** `Obs` trusts the leaf's claim about the
data. If you write *"1500 Black non-recidivists were flagged"* when
the CSV says 510, the kernel won't notice — the leaf is the ingestion
boundary. Defence: use a separate ingest auditor (e.g. `compas_audit`
against the published CSV).

**Choice of CI procedure.** The kernel computes one specific kind of
CI — the score-test (Wilson) interval in exact rationals. If a
different methodology (Wald, Clopper-Pearson, Bayesian credible
interval) would have given the opposite verdict on a borderline case,
the certificate doesn't tell you that. The procedure is fixed by the
kernel implementation, not by the certificate.

**Choice of cohort.** Dropping or relabelling whole sub-cohorts
produces a different but kernel-valid certificate of a different
audit. The kernel never knows what audit you intended; the certificate
is what a reader can hold you to.

These are honest gaps. Each could be closed by a separate auditor
module. The kernel's job is to ensure that, given the leaves and given
the procedure, every inferential move is sound.

## 8. Reproducing the verdict

```sh
lake build pp_diverse
./.lake/build/bin/pp_diverse
```

The binary prints the kernel verdict and a per-rule justification
table. Every rule application is paired with the audit-report sentence
it formalises and the kernel-checked side condition that gates it.

For a sanity check that the kernel really is doing the work, edit
`PPDiverse.lean` to change the IUT2 step's `untrust` to `trust` —
claiming equal-FPR is Trusted — and rebuild. The kernel refuses the
certificate with `IT2: 0 must lie within two-sample CI`, because the
data does not support that verdict.
