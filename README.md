# TPTND-Lean

Lean 4 implementation of a core fragment of **Trustworthy Probabilistic
Typed Natural Deduction (TPTND)**, used to produce machine-checked
fairness certificates from group-level statistics.

This is the supporting implementation for the OVERLAY 2026
submission *"Fairness Certificates via a Lean-Backed
Probabilistic Typed Deduction"* by F. A. D'Asaro and G. Primiero.

## Quick start

Requires Lean 4 via [`elan`](https://leanprover-community.github.io/install/)
and `lake`. The pinned toolchain is in `lean-toolchain`.

```bash
lake build                                    # builds the library + 4 binaries
./.lake/build/bin/tptnd_tests                 # 13 acceptance + 7 negative tests
./.lake/build/bin/compas_audit                # numerical comparison vs ProPublica
./.lake/build/bin/compas_from_data            # 12 COMPAS case-study derivations
./.lake/build/bin/hmda_showcase               # 6 HMDA case-study derivations
```

Each binary exits `0` when every derivation passes the kernel and nonzero
otherwise; the runners are CI-friendly.

## Mapping paper sections to derivations

| Paper section                          | Executable          | Rules used in the derivation             |
|----------------------------------------|---------------------|------------------------------------------|
| §4.1 ProPublica headline (UTrust)      | `compas_from_data`  | `Update` → `IUT` → `EUT` (depth 3)       |
| §4.1 Bayesian belief update            | `compas_from_data`  | `I-P` + `E-P` (depth 2)                  |
| §4.1 Genuine non-finding (Trust)       | `compas_from_data`  | `IT` + `ETex` (depth 2)                  |
| §4.2 HMDA Tree A (reference-rate)      | `hmda_showcase`     | `IT` (depth 2)                           |
| §4.2 HMDA Tree B (temporal pool)       | `hmda_showcase`     | `Update`×2 + `IUT2` (depth 3)            |
| §4.2 HMDA Trees C.1/C.2 (intersect.)   | `hmda_showcase`     | `IUT2` (depth 2)                         |
| §4.2 HMDA Trees D.1/D.2 (year-over-yr) | `hmda_showcase`     | `IUT2` (depth 2)                         |

## User-facing entry point

The kernel exposes one dispatcher:

```lean
def checkDerivation (d : Derivation) : CheckM Unit
```

`CheckM` is `Except String Id`, so `checkDerivation d` returns either
`.ok ()` (the derivation `d` is the certificate) or `.error msg` where
`msg` identifies the failing premise.

A `Derivation` tree is built with
`Derivation.node ruleName premises sequent independenceWitness` where
`ruleName : RuleName` is one of the closed enumeration of rule
constructors (e.g. `.iT`, `.iUT2`, `.update`, `.ePosterior`,
`.contraction`). Rule-name typos are compile-time errors.

### A minimal end-to-end example

```lean
import TPTND
open TPTND

example : Except String Unit := Id.run do
  let α    := Output.atom "Denied"
  let t    := Term.atom "applicants"
  let σ    := ({"src_A"} : Finset String)
  let supp := ({"groupA"} : Finset String)
  let n    : Nat := 100
  let f    := clampProb (35 / 100)
  let p    := clampProb (20 / 100)

  -- Observation leaf: 100 applicants, 35 denied
  let obsCtx : Context := [⟨"applicants", supp, α, .unknown⟩]
  let obsClaim : TermClaim := ⟨.frequency, t, n, α, f, σ⟩
  let dObs := Derivation.node .obs [] ⟨obsCtx, .term obsClaim⟩ false

  -- Identity leaf: model says 20%
  let mE  : ContextEntry := ⟨"x", supp, α, .exact p⟩
  let dM  := Derivation.node .identity [] ⟨[mE], .identity mE⟩ false

  -- IUT: 20% is outside the binomial CI for f=35%, n=100
  let ci          := binomialCI n f p
  let untrust     : TrustClaim := .untrust t n α f p ci
  let dIUT        := Derivation.node .iUT [dM, dObs]
                       ⟨[mE] ++ obsCtx, .trust untrust⟩ false

  checkDerivation dIUT
```

The kernel verifies, in order: that the observation leaf's provenance is
non-empty, that the identity leaf's constraint is exact, that the
declared CI matches `binomialCI`, that the model probability lies
outside the CI (otherwise `IT` would be the right rule), that the
conclusion's term, sample size, output and frequency match the
observation premise, and that the conclusion context inherits properly
from the premises.

### Rule constructors

The complete list of `RuleName` constructors:

```
Output / distribution: .outputAtom .outputNeg .outputSum .outputProd
                       .outputArr .base .extend .unknown
Atomic leaves:         .identity .identityStar .obs .experiment .expectation
Sampling / sum:        .sampling .update .iPlus .ePlusL .ePlusR
Product / arrow:       .iProd .eProdL .eProdR .iArr .eArr
Bayesian:              .iPrior .ePosterior
Trust:                 .iT .iUT .iT2 .iUT2 .eT .eUT .eTex
Comparison:            .iEx .iNEx .eEx .eNEx
Structural:            .weakeningD .weakeningS .contraction
```

The dispatcher in `TPTND.lean` is exhaustive over `RuleName`, so adding
a new rule requires extending the inductive and writing a new
`checkXXX` function in `TPTND/Rules/`.

## Project layout

```
TPTND.lean                # top-level dispatcher: checkDerivation
TPTND/
  Syntax.lean             # Output, Term, Prob, Constraint, Context
  Judgement.lean          # Claim, Sequent, Derivation, RuleName
  CheckM.lean             # ExceptT String Id monad and helpers
  Arithmetic.lean         # exact-rational ops, sqrt, binomialCI/twoSampleCI
  WellFormedness.lean     # context wf-ness, provenance, contextExtendsBy
  Rules/                  # one file per rule family
    OutputDist.lean
    AtomicLeaves.lean
    SamplingSum.lean
    ProductArrow.lean
    Bayesian.lean
    Trust.lean
    Comparison.lean
    Structural.lean
  Tests.lean              # acceptance tests (8 positive + 7 negative)
  COMPASAudit.lean        # numerical comparison vs ProPublica
  COMPASFromData.lean     # 12 COMPAS derivations
  HMDAShowcase.lean       # 6 HMDA derivations

paper/
  overlay2026.tex         # OVERLAY 2026 submission
  overlay2026.pdf         # built PDF
```

## Data sources

- `compas-scores-two-years.csv` from
  <https://github.com/propublica/compas-analysis>
- `hmda_de_2022.csv`, `hmda_de_2023.csv` from the CFPB HMDA Data Browser
  (<https://ffiec.cfpb.gov/data-browser/>), filtered to Delaware

## Reproducibility

A clean `lake build` followed by running the four binaries reproduces
every numerical claim in the paper. The Lean toolchain version is
pinned in `lean-toolchain`; the dependency on Mathlib is pinned in
`lake-manifest.json`.
