# Computational supplement

The [28 integer coordinates](../lean/K28/Coordinates.lean) are shared by the Lean proof and the [Python witness checker](../lean/scripts/check_witness.py). The [standalone C++ verifier](../lean/verify_k28.cpp) checks the finite sweep exclusion. The [certificate generator](../lean/scripts/make_certificates.py) regenerates the [sweep graphs and states](../lean/SweepCore/Certificates/) and [case split data](../lean/SweepCore/CaseTree.lean) consumed by Lean.

From the result directory:

```sh
cd lean
python3 -E scripts/check_witness.py
c++ -O3 -std=c++17 verify_k28.cpp -o /tmp/verify_k28
/tmp/verify_k28
```

The witness has 7,234 crossings. The finite sweep check should find no survivors among the 2,048 assignments.
