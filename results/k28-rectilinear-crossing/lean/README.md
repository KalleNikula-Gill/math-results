# Crossing pairs for 28 points

The mathematical argument, complete integer witness, and computational certificate are in [paper.pdf](../paper/paper.pdf). The manuscript gives the geometric argument and the integer computations. This file documents the Lean proof, its build and its axiom reports.

**Formal theorem.** `K28.minimum_28 : K28.MinimumIs 7234` proves the minimum for arbitrary real general-position drawings and gives an integer drawing attaining it. The cumulative edge bound of Aichholzer, García, Orden, and Ramos is proved for all twelve required orders in `K28.Low.cumulative_bound_28`. The endpoint theorem takes no mathematical hypotheses.

## Reproduce

Use Lean 4.24.0 and the matching Lake (for example, through elan), Git, a C and C++17 toolchain, Python 3, and a working pdfLaTeX installation with latexmk and Latin Modern. The manuscript uses the standard AMS, mathtools, hyperref, booktabs, geometry, microtype and enumitem packages. The committed Lake manifest pins Mathlib to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` and all transitive Git dependencies. The first build needs access to these public dependencies and their compiled cache.

From the directory containing this file run

```sh
bash reproduce.sh
```

The script runs the default Lake target, prints the axiom reports, tests the original standalone arithmetic entry point, checks the integer coordinates in Python, compiles and runs the original C++ search, and rebuilds the manuscript from its LaTeX source. Results are written under `build/replay/`. The five generated certificate files were regenerated in a separate directory and matched byte for byte on the recorded toolchain. The source archive ships the exact certificate data consumed by Lean. To regenerate those data in a separate copy of the project, run `python3 scripts/make_certificates.py` followed by `bash reproduce.sh`. The C++ graph export and branch choices are revalidated by Lean.

## Formal statement and model

- `K28/Geometry.lean` uses a map from 28 labels to pairs of reals. General position requires injectivity and a nonzero determinant on each triple of distinct labels. A crossing consists of two relative interiors meeting, expressed by two parameters strictly between zero and one. The increasing index quadruples and their three pairings count every pair once, including when other edges cross at the same point.
- `K28/Coordinates.lean` contains the sole coordinate input to both witness checkers. `K28/CertificateBase.lean`, `K28/GeneralPosition.lean`, `K28/Rows/` and `K28/Witness.lean` give kernel-checked determinant and counting proofs. The real-plane theorem is `K28.drawing_with_7234`.
- `K28/Quartet.lean` and `K28/Incidence.lean` connect real open-segment intersections, separation of pairs on opposite sides, and the weighted cumulative-edge count. `K28Arithmetic.lean` gives the original conditional arithmetic. `K28/Peeling.lean` proves the shared-apex collinearity obstruction and the strict affine-height bound in a triangle. `K28/Gates.lean` proves a fixed-interval swap incompatibility from adjacent rightward moves.
- `K28/Deletions.lean`, `K28/Hull.lean` and `K28/Triangles.lean` count supporting edges over deletions, prove a lower bound of three for each hull, recover each triangular hull and bound the number of exceptional ninth deletions. `K28/Groups.lean` constructs the three peeling chains and proves their sizes, disjointness, coverage and affine separation. `K28/Transversals.lean` proves that they have a common orientation and can be named counterclockwise. The combined theorem is `K28.Edges.oriented_groups_of_7233`.
- `K28/Realization.lean` proves acceptance of the actual geometric sweeps by the ordinary list checker and excludes the equality profile. `K28/CentralBound.lean` proves the central inequality and derives the minimum from cumulative edge bounds. `K28/PhysicalMove.lean` checks each case of a physical event against the exact state-update code.
- `K28/Schedule.lean` constructs the adjacent swaps from exact real event slopes. `K28/InternalProfile.lean` proves the internal edge counts. `K28/Saturation.lean` proves the minimizing cut rules. `K28/RecordConflict.lean` compares real events in independently chosen group frames. `K28/CandidateTraces.lean` constructs the three compatible tagged lists and proves their combined score.
- `K28/Projection.lean` parameterizes the rotating projection by a real slope and proves the order of events for each point of an exposed group and the one-sidedness of the third group at a between-group event. `K28/Frames.lean` constructs the real starting frames and proves that one plus the number of projected points below an event is its gate. `K28/Bands.lean` proves gate and band flux identities for rightward adjacent-swap sequences. Equal prefix counts in a single trace imply incompatibility of a two-occupied event and a two-vacant event at the same gate.
- `SweepCore/SweepPaths.lean` defines packed states, transitions, and accepting traces for the two group sizes. The compressed graph can contract a silent step. A live tagged move must have an arc with the same record. The coverage check expands every reachable state with all its permitted transitions and fails if its recursion budget is exhausted.
- `SweepCore/Plain.lean` independently specifies moves using ordinary permutations and lists of counts. The verifier checks that every available ordinary move lifts to a packed transition with the same decoded state and record. `K28/PlainExclusion.lean` derives `K28.Finite.plain_paths_below_fifty` from this simulation and the packed-state theorem.
- `SweepCore/PathBounds.lean` proves the path bounds from integer potentials, including for exclusions that use dead states. `SweepCore/CaseAudit.lean` proves the case-split and central mask argument. `K28/Exclusion.lean` checks the data and yields `K28.Finite.projected_paths_below_fifty`. `SweepCore/Certificates/` contains data, and the extra splits are in `SweepCore/CaseTree.lean`.

## Proof of the cumulative estimates

The proof operates on subsets of the original 28 labels. `K28/LowPlane.lean` defines directed edges by strict signed area. `K28/LowRay.lean` constructs an outward median direction at an exposed point and establishes its half-plane property. `K28/LowDirections.lean` chooses three such directions around the origin. `K28/LowStar.lean` counts their incident edges and `K28/LowDelete.lean` bounds the change of the side count after deleting the three points. `K28/LowArc.lean` constructs the events of a positive-time angular sweep. `K28/LowSector.lean` injects each departing label into a distinct oriented edge and proves the sector count. `K28/LowRecurrence.lean` combines the disjoint counts and proves the recurrence by induction. `K28/Minimum.lean` checks its twelve values in the kernel, maps the oriented counts to the original unordered edge profile, and proves the unconditional minimum.

## Trust and theorem reports

The witness theorem uses Lean's standard `propext`, `Classical.choice` and `Quot.sound`. It uses kernel evaluation for every coordinate check. The finite-path proof uses `native_decide` for its large closed computations, introducing `Lean.ofReduceBool` and `Lean.trustCompiler`. The same native trust applies to large fixed-index enumerations in the global incidence identity. See `logs/axioms.txt` for the per-theorem reports. The standalone C++ output is an independent replay of the prior algorithm.

`Axioms.lean` prints the minimum theorem, its axiom dependencies, the geometric edge bound, and the reports for each major component. This directory includes the resulting `logs/axioms.txt`. To inspect the public declaration directly after building, run `lake env lean Axioms.lean`. The manuscript gives the mathematical reduction and the standalone certificate procedure. This README and the logs document the formal proof and its compiler assumptions.
