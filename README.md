# Mixed-Sign Coxeter Systems


Python package, Lean 4 formalizations, and Quarto writeup supporting:

> Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter
> Systems*, Ph.D. Dissertation, Florida State University, 2012 ([FSU
> Digital Library
> PDF](https://repository.lib.fsu.edu/islandora/object/fsu:182755/datastream/PDF/view)
> ·
> [Download](https://repository.lib.fsu.edu/islandora/object/fsu:182755/datastream/PDF/download)).

## Python Package (`mixed_sign_coxeter`)

Located in `src/mixed_sign_coxeter/`:

- `reflection_system.py`: `ReflectionSystem` and `Signature` — symmetric
  bilinear forms $B$, generating reflections $S(B)$, form preservation,
  connected components, bipartite detection/conjugation (Theorem 1.4),
  Howlett’s $U$ matrix and generalized theorem
  $s_0 \cdots s_{n-1} = -U^{-1} U^T$ (Theorem 1.1), principal
  polynomials $\chi(w_\sigma, x)$ (Lemma 2.63), spectral radii
  $\lambda(w)$, minimal spectral radius $\Lambda(\Gamma)$, and signature
  classification.
- `mixed_sign.py`: `MixedSignCoxeterGraph` — mixed-sign Coxeter graphs
  $\Gamma$ with `+`/`-` node signs and edge weights
  $m(i, j) \in \{2, 3, \dots, \infty\}$, standard families ($A_n$,
  $\widetilde{A_n}$, $\widetilde{A_{-n}}$, $B_n$, $D_n$, $E_n$, $F_4$,
  $H_3$, $H_4$, $I_2[m]$), and `example_3_33`.
- `group.py`: Word evaluation, element orders, finite group enumeration,
  two-deletion testing for the Deletion Property (Proposition 3.7 /
  Lemma 3.21), and root orbits $\Phi = W \Pi^+$.

### Quick Example (Theorem 1.7 / Example 3.33)

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

### Running Tests

``` bash
pip install -e ".[dev]"
pytest -v
```

## Lean 4 Formalization (`lean/`)

Located in `lean/MixedSignCoxeter/` (targeting **Lean `v4.35.0`** +
Mathlib `v4.35.0`):

- `Basic.lean`: `ReflectionSystem`, `reflectionMatrix`, involutions
  (`reflectionMatrix_mul_self`), form preservation (Proposition 2.17),
  odd-word non-identity (`odd_word_ne_one`, Proposition 2.21),
  orthogonal commutativity (Proposition 2.22), and $W(B) = W(-B)$ (Lemma
  2.31).
- `Conjugacy.lean`: `SignedPerm` ($\mathcal{O}$, Definition 2.8),
  $\mathcal{O}$-conjugacy of reflections
  (`conjugate_reflections_of_neg_form`, Lemma 2.32), and graph
  isomorphism conjugacy (`graphIso_conjugates_forms`, Lemma 2.37).
- `Bipartite.lean`: `BipartiteReflectionSystem`, `bipartiteConjugator`,
  Theorem 1.4 (`bipartite_conjugation_theorem`), and reflection
  conjugation (`bipartite_conjugates_reflections`).
- `ComponentsAndTrees.lean`: Component word decomposition and pointwise
  action (`wordProd_split_components`, `component_fixes_other`,
  Proposition 2.45) and leaf-insertion conjugacy for trees
  (`leaf_insert_conj`, Theorem 2.58).
- `Howlett.lean`: `howlettU`, `principalElement`, Theorem 1.1
  (`howlett_U_mul_principalElement`: $U (s_0 \cdots s_{n-1}) = -U^T$),
  and Lemma 2.63 (`principal_charpoly_eq`).
- `MixedSign.lean`: `MixedSignCoxeterGraph`, Corollary 1.5
  (`bipartite_mixed_sign_conjugation`), and $\widetilde{A_{-2}}$ matrix
  relations (`tildeAminus2_principal_order_four`,
  `tildeAminus2_eq_3_21_3`).
- `RankTwo.lean`: Rank-2 mixed-sign systems, Lemma 3.17
  (`det_rank2_pm`), Lemma 3.14 (`rank2_pm_order_two_of_zero`,
  `rank2_pm_infinite_order`), and Example 3.16 Fibonacci matrix powers
  (`a2_pm_3_fibonacci_powers`).
- `CyclesAndDeletion.lean`: Failure of the Deletion Property in
  $W(\widetilde{A_{-2}})$ (`tildeAminus2_fails_deletion`, Lemma 3.21 /
  Theorem 1.2) and odd-cycle definiteness (`cyclePosForm_posSemidef`,
  `oddCycleNegForm_negDef`, Theorem 1.6).
- `SpectralRadius.lean`: Hyperbolic system with spectral radius $1$
  (`det_B_A3_ppm`, `w_A3_ppm_add_one_cube`, Example 3.29) and Example
  3.33 / Theorem 1.7 spectral radius comparison
  (`wLinEx333Z_annihilated`, `pLinEx333_no_root_ge_four`,
  `pBpEx333_has_root_gt_four`).

### Building Lean

``` bash
cd lean
lake exe cache get
lake build
```

## Quarto Writeup (`docs/` & `README.qmd`)

- Source: [`docs/mixed_sign_coxeter.qmd`](docs/mixed_sign_coxeter.qmd)
- Rendered HTML:
  [`docs/mixed_sign_coxeter.html`](docs/mixed_sign_coxeter.html)
- Rendered PDF:
  [`docs/mixed_sign_coxeter.pdf`](docs/mixed_sign_coxeter.pdf)

To re-render the writeup or this `README.md`:

``` bash
quarto render docs/mixed_sign_coxeter.qmd
quarto render docs/mixed_sign_coxeter.qmd --to pdf
quarto render README.qmd
```
