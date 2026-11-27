#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 -B supplement/verify.py
(
  cd lean
  lake exe cache get Mathlib.Tactic Mathlib.Analysis.Convex.Segment \
    Mathlib.Combinatorics.SimpleGraph.Acyclic Mathlib.Algebra.Group.Pointwise.Set.BigOperators \
    Mathlib.Analysis.Complex.Polynomial.Basic Mathlib.Algebra.Polynomial.Splits \
    Mathlib.Data.List.GetD Mathlib.Algebra.Polynomial.Derivative
  lake build
  lake env lean WeightedStar.lean
)
