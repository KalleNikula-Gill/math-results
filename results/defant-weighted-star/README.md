# A Narayana sum with nonreal zeros on a weighted star

A 107-vertex weighted star gives a counterexample to the real-rootedness part of [Defant's Question 9.4](https://arxiv.org/html/2611.13479v1#S9.SS2). The center translation is 1. Ten leaves have translation 1 and incident edge mass 23; the other 96 have translation 30 and incident edge mass 1. At `x = -1/258`, an exact integer calculation proves a strict violation of the Laguerre inequality. This does not resolve log-concavity.

- [Manuscript PDF](paper/paper.pdf) and [LaTeX source](paper/paper.tex)
- [Independent Python check](supplement/verify.py) and [integer certificate](supplement/certificate.txt)
- [Lean project](lean/) and [axiom report](lean/axioms.txt)

The manuscript lists Kalle Nikula-Gill and separately credits OpenAI's GPT 6.2 Astra for substantive research and writing assistance.

## Exact arithmetic

From this directory, run `python3 -B supplement/verify.py` with Python 3.9 or newer. It checks each of the three stored certificate integers and verifies

```text
12,223,800 A² < AC − B² < 12,223,801 A².
```

## Lean verification

Run `bash verify.sh` from this directory to replay both checks.
Use Lean 4.24.0 and Lake, for example through Elan. The toolchain and dependency revisions are pinned in `lean/`. An initial build needs the Mathlib dependencies and build cache.

```sh
cd lean
lake exe cache get Mathlib.Tactic Mathlib.Analysis.Convex.Segment \
  Mathlib.Combinatorics.SimpleGraph.Acyclic Mathlib.Algebra.Group.Pointwise.Set.BigOperators \
  Mathlib.Analysis.Complex.Polynomial.Basic Mathlib.Algebra.Polynomial.Splits \
  Mathlib.Data.List.GetD Mathlib.Algebra.Polynomial.Derivative
lake build
lake env lean WeightedStar.lean
```

The entry point checks the geometric construction, its lattice-point bijection, the relation between the geometric sum and the circuit polynomial, and the nonreal root. The final statement is `WeightedStar.exists_nonreal_zero`. Its axiom report includes `Lean.ofReduceBool` and `Lean.trustCompiler` because the exact arithmetic check uses `native_decide`.

To rebuild the manuscript, run `pdflatex -interaction=nonstopmode -halt-on-error paper.tex` twice from `paper/`.
