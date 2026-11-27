# Math results

Manuscripts, exact computational supplements, and Lean formalizations from Kalle Nikula-Gill’s work with GPT 6.2 Astra. Each result has its own directory so the paper and the verification project can be read and built independently.

| Result | Claim | Manuscript | Formalization |
| --- | --- | --- | --- |
| Defant’s weighted-tree Narayana question | A 107-vertex weighted star gives a Narayana sum with a nonreal zero. | [Paper](results/defant-weighted-star/paper/paper.pdf) | [Lean project](results/defant-weighted-star/lean/) |
| q-Fibonomial unimodality | The factorial quotient has weakly unimodal coefficients for every pair of positive indices. | [Paper](results/q-fibonomial-unimodality/paper/paper.pdf) | [Lean project](results/q-fibonomial-unimodality/lean/) |

## Reproduce a result

Start with the README in the result directory. The paper gives the mathematical argument, the supplement contains exact computations used by that argument, and the Lean project records its pinned toolchain and proof dependencies. Machine verification and journal peer review are separate; these manuscripts have not been peer reviewed.

## In progress

The rectilinear crossing number of (K_{28}) and Alexandersson’s long-cycle excedance interlacing are undergoing formal verification. Their entries will be added as the verification and manuscripts are ready.
