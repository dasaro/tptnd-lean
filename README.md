# TPTND-Lean

A Lean 4 implementation of a checker for **TPTND**, a typed probabilistic
natural-deduction calculus for trustworthiness certificates over
probabilistic processes.

The checker is a small, total, `sorry`-free kernel that type-checks
derivation trees. Alongside it the development provides:

- a machine-checked **faithfulness theorem** (`checker_sound`): on the
  certified rule fragment, checker acceptance implies derivability in the
  calculus;
- a **measure-theoretic semantics** — a run space of repeated sampling,
  almost-sure convergence of observed frequencies, and a Chebyshev
  coverage guarantee for trust certificates;
- an **adversarial regression suite** of rejected attack certificates;
- worked **case studies** on the COMPAS and HMDA datasets.

## Build

Requires [Lean 4](https://leanprover.github.io) via `elan` and
[Mathlib](https://github.com/leanprover-community/mathlib4).

```bash
lake exe cache get   # fetch prebuilt Mathlib (optional but recommended)
lake build           # builds the library and checks every proof
```

Run a case study or the regression suite:

```bash
lake exe compas_from_data
lake exe hmda_showcase
lake exe soundness_regression
```

## Layout

```
TPTND/            core: syntax, checker rules, well-formedness
TPTND.lean        top-level checker (rule dispatch + recursion)
TPTND/Derivable.lean     Derivable spec + checker_sound
TPTND/Semantics.lean     measure-theoretic semantics
TPTND/Operational/       run space, convergence, trust guarantee
TPTNDLean.lean    aggregator: `lake build` checks the whole development
```

## License

© Fabio Aurelio D'Asaro.
