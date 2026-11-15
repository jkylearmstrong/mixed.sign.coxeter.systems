# Mixed-Sign Coxeter Systems


Python package, Lean 4 formalization, Manim presentation, and Quarto
writeup supporting:

> Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter
> Systems*, Ph.D. Dissertation, Florida State University, 2012 ([FSU
> Digital Library
> PDF](https://repository.lib.fsu.edu/islandora/object/fsu:182755/datastream/PDF/view)
> ·
> [Download](https://repository.lib.fsu.edu/islandora/object/fsu:182755/datastream/PDF/download)).

For the full theorem-by-theorem index, mathematical exposition, and
Lean/Python cross-references, see the writeup
([HTML](docs/mixed_sign_coxeter.html) ·
[PDF](docs/mixed_sign_coxeter.pdf) ·
[source](docs/mixed_sign_coxeter.qmd)) and [computational verifications
note](docs/verifications.md).

## Repository Layout

| Directory | Contents |
|:---|:---|
| `src/mixed_sign_coxeter/` | Python package: `ReflectionSystem`, `MixedSignCoxeterGraph`, group/root utilities, Appendix A–D catalogs, and exhaustive searches (`isomorphisms.py`, `finite_search.py`, `principal_search.py`) |
| `lean/MixedSignCoxeter/` | `sorry`-free Lean 4 (`v4.35.0` + Mathlib) formalization across 16 modules covering Chapters 1–3 (Howlett’s formula, bipartite & tree conjugacy, Deletion/Exchange, parabolic transfer, spectral classification & interlacing, and counterexamples) |
| `slides/` | 10-scene Manim presentation (`dissertation_deck.py`) backed by exact package computations (`deck_content.py`) |
| `docs/` | Quarto writeup (`mixed_sign_coxeter.qmd` → HTML/PDF/DOCX) and `verifications.md` |

## Python Package & Tests

``` bash
pip install -e ".[dev]"
pytest -v
```

``` python
import sys
sys.path.insert(0, "src")

from mixed_sign_coxeter import MixedSignCoxeterGraph

g = MixedSignCoxeterGraph.example_3_33()
print("Bipartite:", g.is_bipartite())
print("Linear principal spectral radius:   ", round(g.spectral_radius([0, 1, 2, 3, 4, 5]), 5))
print("Bipartite principal spectral radius:", round(g.spectral_radius([0, 3, 5, 1, 2, 4]), 5))
```

    Bipartite: True
    Linear principal spectral radius:    3.05129
    Bipartite principal spectral radius: 5.55193

## Lean 4 Formalization

``` bash
cd lean
lake exe cache get
lake build
```

## Slides & Writeup

``` bash
# Manim slides (requires LaTeX for MathTex)
pip install -e ".[manim]"
manim -pql slides/dissertation_deck.py TitleOverviewScene

# Re-render Quarto writeup or README.md
quarto render docs/mixed_sign_coxeter.qmd
quarto render README.qmd
```
