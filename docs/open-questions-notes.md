# Investigation Notes: Open Questions 2.59 & 3.35

Summary of exact computational findings from [`src/mixed_sign_coxeter/principal_search.py`](../src/mixed_sign_coxeter/principal_search.py) on connected simply-laced mixed-sign graphs with cycles.

## Question 3.35 — Minimizing Spectral Radius of Principal Elements

Exhaustive exact characteristic-polynomial search (`search_question_3_35(n)`):

| Rank $n$ | Nonconstant cyclic graphs | Mixed graphs | Sign-sorted attains min | Bipartite mixed | Bipartite not min | Bipartite is max |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 0 | 0 | — | 0 | 0 | 0 |
| 4 | 12 | 11 | 9 | 4 | 1 | 1 |
| 5 | 194 | 180 | 153 | 32 | 8 | 8 |
| 6 | 3123 | 2992 | 2457 | 277 | 87 | 63 |

Key observations:
1. **Bipartite failure at $n = 4, 5, 6$**: For every $n \in \{4, 5\}$ bipartite mixed graph where a bipartite principal element fails to minimize $\rho(w_\sigma)$ ($1/4$ at $n=4$, $8/32$ at $n=5$), the bipartite element actually **maximizes** $\rho(w_\sigma)$. At $n = 6$, this pattern breaks: out of $87$ bipartite failures ($87/277$), $63$ maximize $\rho$ while $24$ (including $C_6(+,-,+,-,+,-)$) are strictly intermediate.
2. **Sign-sorted orientations are not universally minimal**: Sign-sorted orientations attain the minimum on $9/11$ mixed graphs at $n=4$ and $153/180$ at $n=5$, but fail already at $n = 4$:
   - $C_4$ with signs $(+, -, -, +)$: $\min \rho \approx 3.54646$ vs. sign-sorted $\min \approx 5.82843$.
   - $K_4 - e$ with signs $(+, +, -, -)$: $\min \rho \approx 3.73205$ vs. sign-sorted $\min \approx 6.85410$.
3. **Intermediate circulation can minimize on $C_6$**: On the alternating 6-cycle $(+, -, +, -, +, -)$, `cycle_radius_by_circulation` gives:
   - $|c| = 0$ (bipartite): $\rho \approx 5.82843$
   - $|c| = 2$: $\rho \approx 4.91314$ (minimum)
   - $|c| = 4$: $\rho \approx 8.18570$ (maximum)

## Question 2.59 — Conjugacy of Principal Elements Beyond Trees

By Theorem 2.58, all principal elements of an acyclic graph (tree/forest) are conjugate. On graphs with cycles, acyclic orientations are classified up to source/sink-reversal equivalence by cycle circulations $c$:
- On any single cycle $C_k$, distinct $|c| \in \{k \bmod 2, \dots, k-2\}$ already separate characteristic polynomials and spectral radii on mixed-sign cycles (e.g. $C_4(+, -, +, -)$ separates $|c|=0$ with $\rho = 3 + 2\sqrt{2} \approx 5.82843$ from $|c|=2$ with $\rho \approx 3.54646$), proving non-conjugacy.
- For single-defect odd cycles $C_{2m+1}(+, -, \dots, -)$ ($m \ge 1$), the principal element $w = s_{2m}\cdots s_1 s_0$ satisfies $(w - I)^{2m}(w + I) = 0$ and $w + I \neq 0$, hence $\rho(w) = 1$, formally verified in [`lean/MixedSignCoxeter/OddCycleSingleDefect.lean`](../lean/MixedSignCoxeter/OddCycleSingleDefect.lean) (`oddCycleSinglePlus_minimal_poly`, `oddCycleSinglePlus_ne_neg_one_poly`).
- For single-defect even cycles $C_{2m}(+, -, \dots, -)$ ($m \ge 2$), the principal element $w = s_{2m-1}\cdots s_1 s_0$ always has a real eigenvalue $\lambda < -1$ (specifically $\det(-I - w) = (-1)^m \cdot 4 \neq 0$ and $\det(-5I - w) < 0$), hence $\rho(w) > 1$, formally verified in [`lean/MixedSignCoxeter/EvenCycleSingleDefect.lean`](../lean/MixedSignCoxeter/EvenCycleSingleDefect.lean) (`evenCycleSinglePlus_has_eigenvalue_lt_neg_one`), establishing the odd/even parity dichotomy on single-defect cycles.
- Conversely, for classical positive-sign cycles $C_k(+, \dots, +)$, all acyclic orientations yield $\rho = 1.0$.
