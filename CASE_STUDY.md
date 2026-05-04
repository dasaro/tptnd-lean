# Case study: rule-diverse COMPAS fairness certificate

A single TPTND-Lean derivation tree that exercises **14 distinct rules** of
the calculus and produces machine-checked certificates of three orthogonal
fairness criteria over the published 6,172-row ProPublica COMPAS data set.

| metric | value |
| --- | --- |
| tree depth | **10** |
| total nodes | **43** |
| distinct rules used | 14 |
| min rule types per internal depth | **2** |
| sub-trees combined | 6 |
| kernel verdict | ✓ accepted |

Source: [`TPTND/PPDiverse.lean`](TPTND/PPDiverse.lean).
Build & run: `lake build pp_diverse && ./.lake/build/bin/pp_diverse`.

---

## 1. Why this certificate

Real fairness audits do not look like a single neat pyramid. They are
*multi-pronged*:

* a headline disparity claim (ProPublica: equal-FPR Untrusted),
* a defendant's-side rebuttal (Northpointe: equal-PPV Trusted),
* a calibration check,
* a joint-attribute audit,
* the consolidation of prior estimates.

This case study assembles all five threads as separate sub-derivations and
glues them into one document with `WeakeningS`. The resulting tree has the
property that **every internal depth hosts more than one rule family** — the
opposite of a calculus where rules are stratified by level. This means the
certificate is *braided*: at any given horizontal slice you see several
different inferential moves running in parallel.

## 2. ASCII derivation tree

```text
                                                                                     WeakeningS                                ← depth 10 (root)
                                                                  ┌──────────────────────┴──────────────────────┐
                                                                  │                                              │
                                                              WeakeningS                                     Contraction      ← depth 9
                                                       ┌──────────┴──────────┐                                  │
                                                       │                     │                                  │
                                                  WeakeningS                E→                                 Obs            ← depth 8
                                              ┌────────┴────────┐         ┌──┴──┐
                                              │                 │         │     │
                                         WeakeningS            E×L       I→    Obs                                            ← depth 7
                                       ┌──────┴──────┐        ┌─┴──┐    ┌─┴┐
                                       │             │        │    │    │  │
                                  WeakeningS        ET        I×  Obs  Obs (with x_flag exact)                                 ← depth 6
                                  ┌────┴────┐       │      ┌──┴──┐
                                  │         │      IT2     │     │
                                EUT        E→    ┌──┴──┐  Obs   Obs                                                            ← depth 5
                                  │      ┌──┴──┐ Obs  Obs   ↑     ↑
                                IUT2    I→  Obs                 (subC: I×/E×L joint audit)
                              ┌──┴──┐    │                                                                                    ← depth 4
                              │     │   EUT                       (subB: IT2/ET — Northpointe PPV)
                           Update Update  │
                            ┌┴┐    ┌┴┐  IUT                                                                                   ← depth 3
                            │ │    │ │  ┌┴┐
                            I+ I+  I+ I+ Identity Obs                                                                          ← depth 2
                           ┌┴┐┌┴┐ ┌┴┐┌┴┐  │   │
                          OOOO OOOO    Identity (x_model: Rec_{0.5})                                                          ← depth 1
                          (subA: ProPublica FPR pipeline,         (subA': one-sample IUT calibration on Black PPV)
                           BM·BF·WM·WF × Med·High Obs leaves)
```

Two depth-5 sub-trees co-occupy the deep side of the WeakeningS chain
(`subA` and `subA'`), so the leaf layer hosts both `Obs` and `Identity`,
the depth-2 layer hosts `I+` and `IUT`, and so on upward. Four shallower
sub-trees join progressively higher up the chain (`subB` at depth 5
join, `subC` at 6, `subD` at 7, `subE` at 8), populating each absolute
depth with a different rule family from the corresponding sub-tree's
internal level.

## 3. Per-depth rule profile

Output of `./.lake/build/bin/pp_diverse`:

```text
depth 1 (2 rule types) : obs · identity
depth 2 (2 rule types) : I+ · IUT
depth 3 (2 rule types) : update · EUT
depth 4 (3 rule types) : IUT2 · I→ · obs
depth 5 (4 rule types) : EUT · E→ · IT2 · obs
depth 6 (4 rule types) : WeakeningS · ET · I× · obs
depth 7 (4 rule types) : WeakeningS · E×L · I→ · obs
depth 8 (3 rule types) : WeakeningS · E→ · obs
depth 9 (2 rule types) : WeakeningS · Contraction
depth 10 (1 rule type) : WeakeningS                       (the root)
```

Every internal depth (1–9) hosts at least 2 distinct rule families; five
of them host 3 or more. The single-rule depth 10 is unavoidable — there
is only one root.

## 4. The COMPAS narrative, sub-tree by sub-tree

Each sub-derivation is a self-contained mini-audit. The kernel checks a
specific arithmetic or structural side condition for every rule
application; the natural-language sentence below each rule is the
audit-report sentence that step formalises.

### Sub-tree A — ProPublica FPR pipeline (5 levels deep)

`Obs ×8 → I+ ×4 → Update ×2 → IUT2 → EUT`. Headline ProPublica finding.

| rule | × | natural-language move | kernel side condition |
| --- | --- | --- | --- |
| Obs | 8 | "Of 1168 Black-male non-recidivists, 198 were rated Medium-risk and 312 were rated High-risk; likewise for BF, WM, WF on the published filter." | σ ≠ ∅; n > 0; the support entry for the term name lives in Γ |
| I+ | 4 | "ProPublica's binarisation: collapse Medium and High into a single 'flagged' classification — Flagged := Medium + High." | α ⊥_syn β; same n, σ, term across both premises |
| Update | 2 | "Within each race, pool male and female non-recidivists to form the audit cohort." | σ₁ ∩ σ₂ = ∅; n_conc = n₁ + n₂; weighted-average frequency |
| IUT2 | 1 | "Black FPR = 42.3 %; White FPR = 22.0 %; the score-test CI for the difference is [16.8 %, 23.8 %], excluding zero — therefore the equal-FPR hypothesis is *Untrusted*." | 0 ∉ Q(n_B, n_W, f_B, f_W); disjoint provenance |
| EUT | 1 | "Promote the gap interval ¬[16.8 %, 23.8 %] into the typing context so any downstream certificate inherits the disparity claim." | conclusion ctx contains x : α_{¬[ℓ,h]}; preserves the rest |

### Sub-tree A' — one-sample IUT calibration on Black PPV (5 levels deep)

`Obs · Identity → IUT → EUT → I→ → E→`. Adds Identity-typed leaves at the
deepest layer, alongside subA's Obs, so depth 1 hosts two leaf rules.

| rule | × | natural-language move | kernel side condition |
| --- | --- | --- | --- |
| Obs | 1 | "Among 1234 Black defendants the model flagged, 775 (62.8 %) actually recidivated." | n·f ∈ ℕ; nonempty σ |
| Identity | 1 | "The model's calibrated rate is fixed at 0.50 — declared as an exact-typed entry x_model : Rec_{0.5}." | context is a singleton {x_model : Rec_{0.5}} |
| IUT | 1 | "0.50 lies outside the binomial CI for 775/1234 (≈ [0.60, 0.65]) — the calibration claim is *Untrusted*." | p ∉ binomialCI(n, f, p); identity entry exact |
| EUT | 1 | "Promote the calibration-gap interval into the typing context, while the Identity exact entry survives for I→." | outsideInterval entry added; existing entries preserved |
| I→ | 1 | "Discharge the model-rate hypothesis: there is a function from calibration-rate to recidivism-rate. Result: typed conditional [x_model]u : (Rec ⇒ Rec)_{0.628}." | exactly one exact entry x:α_a discharged; arrow output α⇒β with β = premise output; lambda body = premise term |
| E→ | 1 | "Apply the conditional to the empirical Recidivated rate 925/1234 — chain rule gives the joint rate 0.628 · 0.749 ≈ 0.471." | matching n, σ, mode; conclusion frequency = q · r |

### Sub-tree B — Northpointe PPV defence (3 levels deep)

`Obs ×2 → IT2 → ET`. The Trust verdict that runs alongside ProPublica's UTrust.

| rule | × | natural-language move | kernel side condition |
| --- | --- | --- | --- |
| Obs | 2 | "Among 1234 flagged Black defendants, 775 recidivated (62.8 %); among 460 flagged White defendants, 272 recidivated (59.1 %)." | n·f ∈ ℕ on each leaf |
| IT2 | 1 | "The two-sample CI for the PPV difference is [0.0 %, 8.9 %] — it CONTAINS zero — therefore equal-PPV is *Trusted*." | 0 ∈ Q(n_B, n_W, f_B, f_W); both n > 0 |
| ET | 1 | "Carry the Trusted PPV interval into the typing context as an assumption available to compositional certificates." | ci-interval entry added; conclusion is a frequency claim |

### Sub-tree C — Joint independence audit (3 levels deep)

`Obs ×2 → I× → E×L`. Demonstrates the product fragment of the calculus.

| rule | × | natural-language move | kernel side condition |
| --- | --- | --- | --- |
| Obs | 2 | "Per defendant in the audit cohort: the model's classification (Flagged) and the eventual outcome (Recidivated)." | matching σ, term, n |
| I× | 1 | "Treating Flagged and Recidivated as independent (witness asserted), form the joint judgment." | explicit independence witness; matching σ, n; conclusion = p · q |
| E×L | 1 | "Project the joint judgment back onto the classification component." | tc1.output = sum conc.output tc2.output; conclusion value = r / q |

### Sub-tree D — Calibration as a typed conditional (3 levels deep)

`Obs ×2 → I→ → E→`. Mirrors subA' but on the overall flagged cohort.

| rule | × | natural-language move | kernel side condition |
| --- | --- | --- | --- |
| Obs | 2 | "Among 1694 flagged defendants overall, 1047 (61.8 %) recidivated. The calibration rate is the empirical 716/1694 ≈ 0.423." | exact-typed Flagged entry pre-loaded for I→ to discharge |
| I→ | 1 | "Discharge the Flagged hypothesis — package P(Recidivated \| Flagged) as a first-class conditional certificate." | exactly one exact entry x:Flagged_a; arrow output α⇒β |
| E→ | 1 | "Apply the conditional to a fresh Flagged frequency: chain rule." | matching frame; conclusion frequency = q · r |

### Sub-tree E — Prior consolidation (2 levels deep)

`Obs → Contraction`. Shows how multiple historical audits collapse.

| rule | × | natural-language move | kernel side condition |
| --- | --- | --- | --- |
| Obs | 1 | "Two prior FPR audits — 2014 [40 %, 45 %] and 2016 [42 %, 50 %] — are loaded as interval-typed context entries on the variable x_FPR." | context contains both interval entries |
| Contraction | 1 | "Collapse the two prior intervals into a single exact entry x_FPR : Flagged_{0.43}, since 0.43 ∈ [0.40, 0.45] ∩ [0.42, 0.50]." | exact value lies in ⋂ᵢ cᵢ; contracted entries share name + output |

### Top-level WeakeningS chain

`WeakeningS ×5`. Threads all six sub-certificates into a single auditable
document that retains the deepest sub-tree's claim and merges contexts.

| rule | × | natural-language move | kernel side condition |
| --- | --- | --- | --- |
| WeakeningS | 5 | "Combine each sub-certificate with the running audit document. The five WeakeningS layers thread (subA' calibration UTrust), (subB PPV Trust), (subC joint), (subD conditional) and (subE contraction) onto subA's FPR-disparity backbone." | explicit independence witness; merged context; conclusion = first-premise claim |

## 5. The fairness-criterion landscape

Three orthogonal definitions of "fair" — known to be *jointly* unsatisfiable
when group base rates differ (Chouldechova 2017; Kleinberg–Mullainathan–
Raghavan 2016) — are all kernel-checked side by side in this single tree:

| criterion | sub-tree | TPTND verdict |
| --- | --- | --- |
| equal **FPR** across races (ProPublica) | subA | UTrust (rejected by data) |
| equal **PPV** across races (Northpointe) | subB | Trust (compatible with data) |
| **calibration**: P(Recidivated \| Flagged) = q | subA' + subD | conditional, kernel-composable |

The empirical face of the impossibility result: TPTND-Lean cannot make the
three criteria simultaneously hold *as a single Trust verdict over the
combined claim*, but each sub-tree's individual verdict is independently
checkable, and the structural rules (`WeakeningS`, `Contraction`) bundle
them into one auditable certificate carrying every side condition.

## 6. Reproducing the verdict

```sh
lake build pp_diverse
./.lake/build/bin/pp_diverse
```

The binary prints (in order):

1. tree statistics (depth, node count, root rule)
2. the per-depth rule-diversity profile
3. the kernel verdict (`✓ Kernel ACCEPTED the entire diverse audit`)
4. the natural-language justification table reproduced above

Build time on a clean machine is ~10 s for the kernel + ~5 s for the
binary; the binary itself runs in well under one second.
