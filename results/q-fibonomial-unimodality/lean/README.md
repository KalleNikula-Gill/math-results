# Lean verification

`QFib.qFibonomial_midpoint` proves the midpoint formulation for the integer-polynomial factorial quotient. `QFib.qFibonomial_unimodal` proves the existential-peak formulation, including all nonnegative indices. Both theorems are defined in [QFibAudit.lean](QFibAudit.lean).

This project pins Lean and Mathlib v4.24.0. Use Elan, Git, and Python 3. From this directory, run:

```sh
lake exe cache get
../verify.sh
```

The script builds the project, checks the axiom report, and runs the independent Python supplement. It writes its generated logs to `lean/logs/`. You can also run `lake build` and `lake env lean QFibAudit.lean` directly from this directory. Keep the supplied `lake-manifest.json` to retain exact dependency revisions.

The final theorems depend on `propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`, and `Lean.trustCompiler`. The last two are used by `native_decide` for the finite computations. The analytic proof and coefficient bridge do not rely on native evaluation.
