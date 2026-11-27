# Unimodality of the q-Fibonomial coefficients

**Kalle Nikula-Gill**, with proof development, computation, and drafting assisted by **GPT 6.2 Astra**.

Every q-Fibonomial polynomial is unimodal, with a peak at the floor of half its degree. The proof controls coefficient differences near the midpoint via partial fractions and root-of-unity bounds, then reduces the remaining cases to two finite exact checks.

- [Manuscript (PDF)](paper/paper.pdf) and [LaTeX source](paper/paper.tex)
- [Independent Python supplement](supplement/original_verifier.py)
- [Lean formalization](lean/README.md)

Run the numerical supplement with Python 3 and assertions enabled:

```sh
python3 -E supplement/original_verifier.py
```

The expected output is `1424 divisor inequalities and 28 coefficient cases passed.` To rebuild the manuscript, change to `paper/` and run `latexmk -pdf paper.tex` with TeX Live.
