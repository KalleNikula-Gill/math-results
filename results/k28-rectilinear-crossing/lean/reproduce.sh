#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
out="$PWD/build/replay"
mkdir -p "$out"
export MATHLIB_NO_CACHE_ON_UPDATE=1
{
  lean --version
  lake --version
  c++ --version
  python3 --version
  latexmk --version
} > "$out/versions.txt"
# Lake materializes the dependencies from the committed manifest. A user
# with the imported Mathlib modules already cached can skip their download.
if [[ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic/Linarith.olean ||
      ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic/FieldSimp.olean ||
      ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic/Ring.olean ||
      ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Real/Basic.olean ||
      ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/List/FinRange.olean ||
      ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Finset/Powerset.olean ||
      ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Finset/Max.olean ||
      ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Algebra/Order/BigOperators/Group/Finset.olean ]]; then
  lake exe cache get Mathlib.Data.Real.Basic Mathlib.Data.List.FinRange \
    Mathlib.Tactic.Linarith Mathlib.Tactic.FieldSimp Mathlib.Tactic.Ring \
    Mathlib.Data.Finset.Powerset Mathlib.Data.Finset.Max Mathlib.Data.Fintype.Fin \
    Mathlib.Algebra.BigOperators.Group.Finset.Piecewise Mathlib.Algebra.Order.BigOperators.Group.Finset
fi
lake build 2>&1 | tee "$out/lean-build.txt"
lake env lean Axioms.lean 2>&1 | tee "$out/axioms.txt"
lean K28Arithmetic.lean > "$out/K28Arithmetic.txt"
python3 -E scripts/check_witness.py | tee "$out/witness.txt"
c++ -O3 -std=c++17 verify_k28.cpp -o "$out/verify_k28"
"$out/verify_k28" | tee "$out/path-replay.txt"
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir="$out" ../paper/paper.tex \
  > "$out/typeset.txt" 2>&1
test -s "$out/paper.pdf"
printf '%s\n' "Checks complete. Outputs are in $out."
