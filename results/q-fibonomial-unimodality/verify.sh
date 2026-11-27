#!/usr/bin/env bash
set -euo pipefail
base_dir="$(cd "$(dirname "$0")" && pwd)"
cd "$base_dir/lean"
mkdir -p logs

lean --version | tee logs/toolchain.log
lean QFibFinite.lean 2>&1 | tee logs/finite-original.log
lake build 2>&1 | tee logs/build.log
lake env lean QFibAudit.lean 2>&1 | tee logs/axioms.log
python3 -E "$base_dir/supplement/original_verifier.py" | tee logs/python-reference.log

python3 -E - <<'PY'
import re
from pathlib import Path

report = Path("logs/axioms.log").read_text()
expected = {"propext", "Classical.choice", "Quot.sound",
            "Lean.ofReduceBool", "Lean.trustCompiler"}
for theorem in ("QFib.all_unimodal", "QFib.qFibonomial_unimodal"):
    match = re.search(r"'" + re.escape(theorem) + r"' depends on axioms: \[([^\]]*)\]", report)
    if match is None:
        raise SystemExit(f"Missing axiom report for {theorem}")
    actual = {name.strip() for name in match.group(1).split(",")}
    if actual != expected:
        raise SystemExit(f"Unexpected axiom report for {theorem}: {sorted(actual)}")
print("Both final axiom reports match the documented trust assumptions.")
PY
