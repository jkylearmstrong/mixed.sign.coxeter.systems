# Presentation Order, Render Settings, and Speaker Script

## Render Quality Flags

`-ql` (480p at 15 fps) is only for fast draft previews. For final presentation video, use `-qh` (1080p60) or `-qk` (4K60):

```powershell
# 1080p at 60 fps (recommended for presentations)
& "$env:APPDATA\Python\Python310\Scripts\manim.exe" -qh slides/dissertation_deck.py -a

# 4K at 60 fps
& "$env:APPDATA\Python\Python310\Scripts\manim.exe" -qk slides/dissertation_deck.py -a
```

---

## Scene Order & Coverage

The 10 scenes in `SCENE_ORDER` (`slides/dissertation_deck.py`) cover all headline Chapter 1 results (**Theorems 1.1, 1.2, 1.4, 1.6, 1.7** and **Corollaries 1.3, 1.5**) plus the key Chapter 3 counterexamples and appendices:

1. `TitleOverviewScene` — Overview of the dissertation and main theorems
2. `HowlettFormulaScene` — Theorem 1.1 ($w = -U^{-1} U^T$) and Lemma 2.63 on $\widetilde{A_{-2}}$
3. `BipartiteConjugacyScene` — Theorem 1.4 and Corollary 1.5 (bipartite sign-negation conjugacy)
4. `RankTwoHyperbolicScene` — Example 3.16, Proposition 3.12, and Lemma 3.14 (Fibonacci roots & infinite order)
5. `DeletionFailureScene` — Lemma 3.21, Theorem 1.2, Corollary 1.3, and Remark 3.23 ($\widetilde{A_{-2}}$ and $\Gamma_n$)
6. `OddCycleSignatureScene` — Theorem 1.6 and Remark 3.26 ($\widetilde{A_n}$ vs. $\widetilde{A_{-n}}$)
7. `HyperbolicRadiusOneScene` — Example 3.29 vs. Theorems 3.27 and 3.28 ($A_3(+,+,-)$)
8. `SpectralRadiusSeparationScene` — Example 3.33, Table 3.1, and Theorem 1.7 / 3.34
9. `AppendixBScene` — Table B.1 and Remark 3.30 (non-monotonicity of $\Lambda$)
10. `FormalizationScene` — Summary of Lean 4 (`v4.35.0`) and Python verifications

*(Note: **Theorem 2.58** — conjugacy of all principal elements of a tree/forest — and **Proposition 2.41** — bipartite iff no odd cycle — are summarized on Slide 10 rather than having standalone visual slides.)*

---

## Speaker Script

### 1. `TitleOverviewScene`

> This talk presents the main results of *Principal Elements of Mixed-Sign Coxeter Systems*, together with an executable Python package and a `sorry`-free Lean 4 formalization. Mixed-sign Coxeter systems generalize classical Coxeter reflection representations by allowing both positive and negative diagonal entries in the defining symmetric bilinear form $B$. Today we'll trace five main themes: Howlett's factorization for principal elements, when sign flips preserve the system, how rank-2 mixed-sign pairs behave, how odd negative cycles break the Deletion Property, and how spectral-radius minimality fails outside the classical setting.

### 2. `HowlettFormulaScene`

> **Theorem 1.1** extends Howlett's upper-triangular factorization to arbitrary mixed-sign reflection systems. Given an ordering of the nodes, we form the upper-triangular matrix $U$ from $B$—specifically $U_{ii} = \tfrac{1}{2} B_{ii}$ and $U_{ij} = B_{ij}$ for $i < j$. Then the principal element $w = s_1 s_2 \cdots s_n$ satisfies $U w = -U^T$, or equivalently $w = -U^{-1} U^T$. On $\widetilde{A_{-2}}$, where all three diagonal entries are $-2$, this immediately gives the integer matrix $w$ and its principal polynomial $\chi(w, x) = x^3 + x^2 + x + 1$, showing $w^4 = I$ (Lemma 2.63).

### 3. `BipartiteConjugacyScene`

> When is a mixed-sign system secretly equivalent to a classical one? **Theorem 1.4** shows that if the reflection graph $\Gamma$ is bipartite, negating the bilinear form on one part of the bipartition conjugates every reflection by a diagonal sign matrix $D$ without changing the group's reflection representation up to $\mathcal{O}$-conjugacy. By **Corollary 1.5**, this means any bipartite mixed-sign Coxeter graph has the same principal polynomials and spectral radii as its classical all-positive counterpart.

### 4. `RankTwoHyperbolicScene`

> In rank 2, **Example 3.16** illustrates what happens when one node is positive and one is negative, $A_2(+,-)$ with edge weight $3$. Even though the reflections individually have order 2, the product $s_1 s_2$ has powers governed by the Fibonacci numbers: $(s_1 s_2)^k = (-1)^k \begin{pmatrix} F_{2k+1} & F_{2k} \\ F_{2k} & F_{2k-1} \end{pmatrix}$. As $k$ grows, $(s_1 s_2)^k e_1$ repeatedly leaves the positive root cone $\Phi^+$ (Proposition 3.12), proving $s_1 s_2$ has infinite order (Lemma 3.14). More generally, by Corollary 3.18, any mixed-sign edge with opposite signs forces an infinite group.

### 5. `DeletionFailureScene`

> Once we leave bipartite graphs, odd negative cycles break classical Coxeter combinatorics. In $W(\widetilde{A_{-2}})$ (**Lemma 3.21**), the group is finite of order $24$—isomorphic to $S_4$ (**Remark 3.23**)—and the length-5 word $w = s_1 s_2 s_1 s_3 s_1$ equals the length-3 word $s_3 s_1 s_2$. Yet none of the 10 two-letter deletions from $w$ reproduces $w$: the Deletion Property fails. By parabolic transfer (**Theorem 1.2**), any graph containing $\widetilde{A_{-2}}$—such as the tail family $\Gamma_n$—fails the Deletion Property in the same way, and by **Corollary 1.3** none of these systems is $\mathcal{O}$-conjugate to a classical Coxeter system.

### 6. `OddCycleSignatureScene`

> **Theorem 1.6** separates odd cycles by quadratic-form signature. Classical $\widetilde{A_n}$ (for even $n$) is positive semidefinite and degenerate on $(1,\dots,1)^T$, giving an infinite affine group. By contrast, $\widetilde{A_{-n}}$ with $n$ even has $v^T B v = -\sum_i (v_i + v_{i+1})^2 < 0$ for all $v \neq 0$—strictly negative definite, with $\det(-B) = 4$ (**Remark 3.26**). Since $\mathcal{O}$-conjugacy preserves definiteness, $\widetilde{A_{-n}}$ and $\widetilde{A_n}$ are never conjugate; in fact $W(\widetilde{A_{-n}}) \cong W(D_{n+1})$ for every even $n$.

### 7. `HyperbolicRadiusOneScene`

> In classical Coxeter theory, **Theorem 3.27** classifies a system as spherical, affine, or hyperbolic by whether its Coxeter element has eigenvalues on the unit circle or outside it, and **Theorem 3.28** gives eigenvalue interlacing under node deletion. **Example 3.29** shows both fail in the mixed-sign setting: $A_3(+,+,-)$ is hyperbolic ($\det B = -8 < 0$, signature $(2,1,0)$), yet its principal polynomial is $(x+1)^3$, so $\lambda(w) = 1$. Moreover, deleting a node raises the minimal spectral radius from $\Lambda(A_3(+,+,-)) = 1$ to $\Lambda(A_2(+,-)) \approx 2.618$.

### 8. `SpectralRadiusSeparationScene`

> In classical Coxeter groups, the bipartite Coxeter element always minimizes the spectral radius among all principal elements. **Example 3.33** (**Theorem 1.7 / 3.34**) constructs a 6-node bipartite mixed-sign graph where the linear principal element has $\lambda \approx 3.051$, while the bipartite principal element $s_1 s_4 s_6 s_2 s_3 s_5$ has $\lambda \approx 5.552$—strictly larger. This leaves **Question 3.35** open: what general principle characterizes the minimal spectral-radius ordering?

### 9. `AppendixBScene`

> **Appendix B** catalogs sign patterns on $A_n$, and **Remark 3.30** highlights the non-monotonicity of $\Lambda$ along the chain $A_2(+,-) \subset A_3(-,+,+) \subset A_4(-,+,+,+) \subset A_5(-,+,+,+,+)$. Adding a single positive node makes the minimal spectral radius drop from $\approx 2.618$ to $1.000$, jump up to $\approx 2.154$, and drop again to $\approx 1.883$.

### 10. `FormalizationScene`

> Finally, every number shown in this deck is computed live by the `mixed_sign_coxeter` Python package, and all numbered results from Chapters 1–3 of the dissertation are formally verified—`sorry`-free—in Lean 4 (`v4.35.0`) across 16 modules, alongside Python verifications for Appendices A, B, and D, the general even-$n$ isomorphism $W(\widetilde{A_{-n}}) \cong W(D_{n+1})$, and exhaustive searches for Remark A.3 and Question 3.35.
