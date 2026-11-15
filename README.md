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
- `catalog.py`: Mahler measure `mahler_measure`, signature
  classification `classify_signature`, Appendix A finite catalogs
  `table_a1` / `table_a2`, Appendix B $A_n$ sign tables
  `A_n_sign_table`, and Remark 3.26 cycle determinant checks
  `finite_even_odd_cycle_determinants`.

- `isomorphisms.py`: explicit isomorphism $W(\widetilde{A_{-n}}) \cong W(D_{n+1})$
  for every even $n$, and a Python port of Appendix D (the thesis's GAP session).
- `finite_search.py`: exhaustive search for finite mixed-sign groups (Remark A.3).
- `principal_search.py`: exhaustive search over principal elements for Question 3.35.

See [`docs/verifications.md`](docs/verifications.md) for the results of these searches.

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
  orthogonal commutativity (`reflectionMatrix_comm_of_orthogonal`,
  Proposition 2.22; `reflectionMatrix_comm_of_not_adjacent`, Proposition
  2.28), $W(B) = W(-B)$ (Lemma 2.31), and quadratic-form signature
  definitions (`IsPosDef`, `IsPosSemidefDegenerate`, `IsNegDef`,
  `IsIndefinite`, Definitions 2.47–2.51 & Example 2.52).
- `Conjugacy.lean`: `SignedPerm` ($\mathcal{O}$, Definition 2.8),
  $\mathcal{O}$-conjugacy of reflections
  (`conjugate_reflections_of_neg_form`, Lemma 2.32), graph isomorphism
  conjugacy (`graphIso_conjugates_forms`, Lemma 2.37;
  `graphIso_iff_perm_conjugate`, `O_conjugate_preserves_diag_and_abs`,
  Corollary 2.38), and signature invariance (`O_conjugate_isPosDef_iff`,
  Corollary 2.46).
- `Bipartite.lean`: `BipartiteReflectionSystem`, `bipartiteConjugator`,
  Theorem 1.4 (`bipartite_conjugation_theorem`,
  `bipartite_conjugates_reflections`, `bipartite_conjugates_wordProd`,
  `bipartite_conjugates_charpoly`), and bipartite principal-element
  conjugacy (`bipartite_same_part_comm`,
  `bipartite_principalElements_conjugate`, Proposition 2.41 /
  Proposition 3.32).
- `ComponentsAndTrees.lean`: Component word decomposition and pointwise
  action (`wordProd_split_components`, `component_fixes_other`,
  Proposition 2.45) and leaf-insertion conjugacy for trees
  (`leaf_insert_conj`, Theorem 2.58).
- `Howlett.lean`: `howlettU`, `principalElement`, Theorem 1.1
  (`howlett_U_mul_principalElement`,
  `howlett_principalElement_eq_neg_inv_mul_transpose`:
  $w = -U^{-1} U^T$), and Lemma 2.63 (`principal_charpoly_eq`).
- `MixedSign.lean`: `MixedSignCoxeterGraph`, Corollary 1.5
  (`bipartite_mixed_sign_conjugation`), and $\widetilde{A_{-2}}$ matrix
  relations (`tildeAminus2_principal_order_four`,
  `tildeAminus2_eq_3_21_3`).
- `RankTwo.lean`: Rank-2 mixed-sign systems, Lemma 3.17
  (`det_rank2_pm`), Lemma 3.14 (`rank2_pm_order_two_of_zero`,
  `rank2_pm_infinite_order`), Corollary 3.18
  (`adjacent_pm_infinite_order`), and Example 3.16 Fibonacci matrix
  powers (`a2_pm_3_fibonacci_powers`).
- `CyclesAndDeletion.lean`: Failure of the Deletion Property in
  $W(\widetilde{A_{-2}})$ (`tildeAminus2_fails_deletion`, Lemma 3.21),
  the infinite family of Theorem 1.2 (`theorem_1_2_infinite_family`),
  infinite order of $W(\widetilde{A_2})$ (`tildeA2_infinite_order`,
  Lemma 3.25), and odd-cycle definiteness and
  non-$\mathcal{O}$-conjugacy (`cyclePosForm_posSemidef`,
  `oddCycleNegForm_negDef`, `oddCycle_not_O_conjugate`, Theorem 1.6).
- `SpectralRadius.lean`: Hyperbolic system with spectral radius $1$
  (`det_B_A3_ppm`, `w_A3_ppm_add_one_cube`, Example 3.29) and Example
  3.33 / Theorem 1.7 / Theorem 3.34 spectral radius comparison
  (`wLinEx333Z_annihilated`, `pLinEx333_no_root_ge_four`,
  `pBpEx333_has_root_gt_four`, `theorem_3_34_bipartite_exceeds_linear`).
- `ClassicalDeletion.lean`: Universal Coxeter quotient
  (`freeCoxeterQuotient`, Proposition 3.19), Deletion $\leftrightarrow$
  Exchange equivalence (`SatisfiesDeletionProperty`,
  `SatisfiesExchangeProperty`, `deletion_iff_exchange`, Proposition 3.8
  / Theorem 3.9), $\mathcal{O}$-conjugacy invariance
  (`deletion_invariant_of_O_conjugate`), and Corollary 1.3
  (`corollary_1_3_not_conjugate_to_deletion`).
- `TreeConjugacy.lean`: Full **Theorem 2.58** for arbitrary forests and
  trees (`theorem_2_58_principal_conj_of_isAcyclic`,
  `theorem_2_58_principal_conj_of_isTree`,
  `principal_moves_of_isAcyclic`, `exists_leaf_of_isAcyclic`) — all
  principal elements of a tree or forest lie in a single conjugacy class
  of $W(\Gamma)$.
- `OddCycles.lean`: Full **Proposition 2.41**
  (`isBipartite_iff_no_odd_cycle`,
  `exists_bipartition_iff_no_odd_cycle`,
  `nonempty_bipartite_of_no_odd_cycle`) — a reflection diagram is
  bipartite if and only if it contains no odd cycle.
- `ParabolicTransfer.lean`: Parabolic subgroup transfer and **Theorem
  1.2** in full generality: any reflection system containing an induced
  copy of $\widetilde{A_{-2}}$ fails the Deletion Property
  (`not_deletion_of_contains_tildeAminus2`), covering both the
  dissertation’s tail family $\Gamma_{3+k}$ (`tildeAminus2Tail`,
  `theorem_1_2_tail_family`) and orthogonal extensions
  (`theorem_1_2_extended_family`).
- `RankTwoRoots.lean`: Full **Proposition 3.11** for any infinite
  dihedral pair $(s_i, s_j)$ in arbitrary rank (`prop_3_11_general`,
  `prop_3_11_infinite_order`, `alternating_word_root`), proving via
  Chebyshev polynomials that $(s_i s_j)^k e_i \in \Phi^+$ and $s_i s_j$
  has infinite order whenever $B_{ii} = B_{jj}$ and
  $-2 B_{ij}/B_{ii} \ge 2$.
- `SpectralClassification.lean`: Full **Theorem 3.27** (A’Campo’s
  spherical / affine / hyperbolic spectral classification of bipartite
  Coxeter elements, `theorem_3_27_classification`) and **Theorem 3.28**
  (eigenvalue interlacing and strict monotonicity on induced subgraphs /
  node deletion, `theorem_3_28_interlacing`, `theorem_3_28_strict`).
- `RemarksAndClassical.lean`: **Remark 3.23**
  ($W(\widetilde{A_{-2}}) \cong S_4$ of order $24$,
  `remark_3_23_tildeAminus2_iso_S4`, `remark_3_23_card`), **Remark
  3.26** ($\det(-B(\widetilde{A_{-n}})) = 4$ for every even $n \ge 2$,
  `remark_3_26_det_neg_odd_cycle`), and **Remark 3.30** (annihilating
  polynomials `wA2Z_annihilated`–`wA5Z_annihilated` and spectral-radius
  oscillation bounds `remark_3_30_A2_root_gt`, `remark_3_30_A4_root_gt`,
  `remark_3_30_A5_roots_lt`).

### Building Lean

``` bash
cd lean
lake exe cache get
lake build
```

## Manim Presentation (`slides/`)

Ten presentation scenes built on top of `mixed_sign_coxeter` live in
[`slides/dissertation_deck.py`](slides/dissertation_deck.py). Every
number on a slide is computed from the package by
[`slides/deck_content.py`](slides/deck_content.py), and
`tests/test_slides.py` checks those numbers against the dissertation.

| Scene | Results |
|:---|:---|
| `TitleOverviewScene` | Overview |
| `HowlettFormulaScene` | Theorem 1.1, Lemma 2.63 |
| `BipartiteConjugacyScene` | Theorem 1.4, Corollary 1.5 |
| `RankTwoHyperbolicScene` | Example 3.16, Lemma 3.14, Proposition 3.12 |
| `DeletionFailureScene` | Lemma 3.21, Theorem 1.2, Corollary 1.3, Remark 3.23 |
| `OddCycleSignatureScene` | Theorem 1.6, Remark 3.26 |
| `HyperbolicRadiusOneScene` | Example 3.29 against Theorems 3.27 and 3.28 |
| `SpectralRadiusSeparationScene` | Example 3.33, Table 3.1, Theorem 1.7 |
| `AppendixBScene` | Table B.1, Remark 3.30 |
| `FormalizationScene` | What is checked in Lean 4 and Python |

To render (`MathTex` also needs a LaTeX installation):

``` bash
pip install -e ".[manim]"
manim -pql slides/dissertation_deck.py TitleOverviewScene   # one scene
manim -ql slides/dissertation_deck.py -a                    # whole deck
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
