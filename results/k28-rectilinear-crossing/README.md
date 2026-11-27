# The rectilinear crossing number of K₂₈

**Kalle Nikula-Gill**, with proof development, computation, and drafting assisted by **GPT 6.2 Astra**.

The minimum is **7,234** crossing pairs. A drawing with 7,233 would force three groups of sizes 10, 9, and 9 and a prescribed set of projection sweeps. An exact finite check rules those sweeps out, and explicit integer coordinates attain 7,234.

- [Manuscript (PDF)](paper/paper.pdf) and [LaTeX source](paper/paper.tex)
- [Exact computational supplement](supplement/README.md)
- [Lean formalization and axiom report](lean/README.md)

Run `bash lean/reproduce.sh` to check the result and rebuild the paper. The formal theorem is `K28.minimum_28 : K28.MinimumIs 7234`. It has no remaining mathematical hypotheses. Large finite checks use Lean's native evaluation; the coordinate witness and the cumulative edge estimates are kernel-checked.
