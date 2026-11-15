"""Numbers and labels shown in the Manim deck, computed from ``mixed_sign_coxeter``.

Everything on a slide that comes from mathematics is produced here, without importing
Manim, so ``tests/test_slides.py`` can check the deck against the package and against
the dissertation (Armstrong 2012) even where Manim is not installed.
"""

from __future__ import annotations

from dataclasses import dataclass

import sympy as sp

from mixed_sign_coxeter import (
    A_n_sign_table,
    MixedSignCoxeterGraph,
    evaluate_word,
    fast_integer_group_order,
    find_two_deletions,
    mahler_measure,
)

X = sp.Symbol("x")


def sign_string(signs: tuple[int, ...] | str) -> str:
    """Render node signs as a compact string such as ``+-++``."""
    if isinstance(signs, str):
        return signs
    return "".join("+" if s > 0 else "-" for s in signs)


# ---------------------------------------------------------------------------
# Theorem 1.1 / Lemma 2.63: Howlett's formula on ~A_{-2}
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class HowlettData:
    B: sp.Matrix
    U: sp.Matrix
    w: sp.Matrix
    product: sp.Matrix
    principal_polynomial: sp.Expr
    mahler: float
    det_B: sp.Expr


def howlett_data() -> HowlettData:
    g = MixedSignCoxeterGraph.A_tilde(2, negative=True)
    U = g.howlett_U()
    w = sp.simplify(-U.inv() * U.T)
    chi = g.principal_polynomial(var=X)
    return HowlettData(
        B=g.B,
        U=U,
        w=w,
        product=evaluate_word(g, [0, 1, 2]),
        principal_polynomial=sp.factor(chi.as_expr()),
        mahler=mahler_measure(chi, var=X),
        det_B=g.B.det(),
    )


# ---------------------------------------------------------------------------
# Theorem 1.4 / Corollary 1.5: bipartite sign flip
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class BipartiteData:
    graph: MixedSignCoxeterGraph
    flipped: MixedSignCoxeterGraph
    parts: tuple[list[int], list[int]]
    conjugates: bool
    polynomial: sp.Expr
    flipped_polynomial: sp.Expr


def bipartite_data() -> BipartiteData:
    g = MixedSignCoxeterGraph.A_n(["+", "-", "+", "+"])
    g_neg = g.negate_signs()
    P = g.bipartite_conjugator()
    return BipartiteData(
        graph=g,
        flipped=g_neg,
        parts=g.bipartition(),
        conjugates=sp.simplify(P.T * g.B * P + g_neg.B) == sp.zeros(g.n, g.n),
        polynomial=sp.factor(g.principal_polynomial(var=X).as_expr()),
        flipped_polynomial=sp.factor(g_neg.principal_polynomial(var=X).as_expr()),
    )


# ---------------------------------------------------------------------------
# Example 3.16 / Lemma 3.14 / Proposition 3.12: rank-2 hyperbolic system
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class FibonacciRow:
    k: int
    power: sp.Matrix
    first_coordinate: int


def rank_two_fibonacci_rows(max_k: int = 4) -> list[FibonacciRow]:
    """Rows of (s1 s2)^k in A_2(+, -)[3], whose entries are signed Fibonacci numbers."""
    g = MixedSignCoxeterGraph.I_2(3, signs=("+", "-"))
    s1, s2 = g.generators()
    rows = []
    for k in range(1, max_k + 1):
        power = sp.simplify((s1 * s2) ** k)
        rows.append(FibonacciRow(k=k, power=power, first_coordinate=int(power[0, 0])))
    return rows


def rank_two_signature() -> tuple[int, int, int]:
    return MixedSignCoxeterGraph.I_2(3, signs=("+", "-")).signature().as_tuple()


# ---------------------------------------------------------------------------
# Lemma 3.21 / Theorem 1.2 / Remark 3.23: Deletion Property failure in ~A_{-2}
# ---------------------------------------------------------------------------

DELETION_WORD = (0, 1, 0, 2, 0)
DELETION_SHORT_WORD = (2, 0, 1)


@dataclass(frozen=True)
class DeletionData:
    word_equals_short_word: bool
    successful_deletions: list[tuple[int, int]]
    group_order: int


def deletion_data() -> DeletionData:
    g = MixedSignCoxeterGraph.A_tilde(2, negative=True)
    w = evaluate_word(g, DELETION_WORD)
    return DeletionData(
        word_equals_short_word=w == evaluate_word(g, DELETION_SHORT_WORD),
        successful_deletions=find_two_deletions(g, list(DELETION_WORD), w),
        group_order=fast_integer_group_order(g),
    )


def theorem_1_2_graph(n: int, sign: str = "+") -> MixedSignCoxeterGraph:
    """Gamma_n from the proof of Theorem 1.2: Gamma_3 = ~A_{-2}, Gamma_n = Gamma_{n-1} *_{r_{n-1}} {r_n}.

    Each new node hangs off the previous one, so Gamma_n is ~A_{-2} with a path of
    n - 3 extra nodes attached at r_3.
    """
    if n < 3:
        raise ValueError("Gamma_n is defined for n >= 3.")
    g = MixedSignCoxeterGraph.A_tilde(2, negative=True)
    for k in range(4, n + 1):
        g = g.join_node(k - 2, sign=sign)
    return g


def theorem_1_2_family(ns: tuple[int, ...] = (3, 4, 5, 6)) -> list[tuple[int, bool, int]]:
    """For each Gamma_n: (n, the length-5 word equals the length-3 word, # working deletions)."""
    out = []
    for n in ns:
        g = theorem_1_2_graph(n)
        w = evaluate_word(g, DELETION_WORD)
        out.append((n, w == evaluate_word(g, DELETION_SHORT_WORD), len(find_two_deletions(g, list(DELETION_WORD), w))))
    return out


def word_latex(word: tuple[int, ...]) -> str:
    """LaTeX for a word, using the dissertation's 1-based generator names."""
    return " ".join(f"s_{{{i + 1}}}" for i in word)


# ---------------------------------------------------------------------------
# Theorem 1.6 / Remark 3.26: odd cycles ~A_n versus ~A_{-n}
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class OddCycleRow:
    n: int
    positive_signature: tuple[int, int, int]
    negative_signature: tuple[int, int, int]
    negative_group_order: int | None
    d_group_order: int | None


def odd_cycle_rows(ns: tuple[int, ...] = (2, 4)) -> list[OddCycleRow]:
    """Signatures of ~A_n and ~A_{-n}, and |W(~A_{-n})| = |W(D_{n+1})| (Remark 3.26).

    D_3 is A_3, so ``MixedSignCoxeterGraph.A_n(3)`` stands in for D_3.
    """
    rows = []
    for n in ns:
        pos = MixedSignCoxeterGraph.A_tilde(n)
        neg = MixedSignCoxeterGraph.A_tilde(n, negative=True)
        d = MixedSignCoxeterGraph.A_n(3) if n + 1 == 3 else MixedSignCoxeterGraph.D_n(n + 1)
        rows.append(
            OddCycleRow(
                n=n,
                positive_signature=pos.signature().as_tuple(),
                negative_signature=neg.signature().as_tuple(),
                negative_group_order=fast_integer_group_order(neg),
                d_group_order=fast_integer_group_order(d),
            )
        )
    return rows


# ---------------------------------------------------------------------------
# Example 3.29: hyperbolic, yet spectral radius 1
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class HyperbolicRadiusOneData:
    signature: tuple[int, int, int]
    classification: str
    polynomial: sp.Expr
    spectral_radius: float


def hyperbolic_radius_one_data() -> HyperbolicRadiusOneData:
    g = MixedSignCoxeterGraph.A_n(["+", "+", "-"])
    return HyperbolicRadiusOneData(
        signature=g.signature().as_tuple(),
        classification=g.classify(),
        polynomial=g.factor_principal_polynomial(),
        spectral_radius=g.spectral_radius(),
    )


# ---------------------------------------------------------------------------
# Example 3.33 / Table 3.1 / Theorem 1.7: the bipartite element is not minimal
# ---------------------------------------------------------------------------

#: Orderings from Table 3.1 (0-based) and how the dissertation labels them.
TABLE_3_1_ORDERS: tuple[tuple[tuple[int, ...], str], ...] = (
    ((0, 1, 2, 3, 4, 5), "linear"),
    ((1, 0, 2, 3, 4, 5), "boundary circuit from s2"),
    ((0, 3, 5, 1, 2, 4), "bipartite"),
    ((4, 1, 0, 2, 3, 5), "(positive nodes)(negative nodes)"),
)


@dataclass(frozen=True)
class SpectralRow:
    order: tuple[int, ...]
    label: str
    spectral_radius: float


def example_3_33_rows() -> list[SpectralRow]:
    g = MixedSignCoxeterGraph.example_3_33()
    return [SpectralRow(order, label, g.spectral_radius(order)) for order, label in TABLE_3_1_ORDERS]


def example_3_33_graph() -> MixedSignCoxeterGraph:
    return MixedSignCoxeterGraph.example_3_33()


# ---------------------------------------------------------------------------
# Appendix B (Table B.1) and Remark 3.30
# ---------------------------------------------------------------------------


def appendix_b_rows(n: int = 4, limit: int = 6):
    """First rows of the A_n sign table (Table B.1 for n = 4)."""
    return A_n_sign_table(n)[:limit]


def interlacing_failure() -> tuple[float, float]:
    """Example 3.29: Lambda(A_2(+,-)) > Lambda(A_3(+,+,-)) although A_2(+,-) is a subgraph.

    Theorem 3.28 (interlacing) says the opposite holds for classical Coxeter graphs.
    """
    small, _ = MixedSignCoxeterGraph.A_n(["+", "-"]).minimal_spectral_radius()
    big, _ = MixedSignCoxeterGraph.A_n(["+", "+", "-"]).minimal_spectral_radius()
    return small, big


def remark_3_30_lambdas() -> list[tuple[str, float]]:
    """Lambda along A_2(+,-) < A_3(-,+,+) < A_4(-,+,+,+) < A_5(-,+,+,+,+): not monotone."""
    chain = [["+", "-"], ["-", "+", "+"], ["-", "+", "+", "+"], ["-", "+", "+", "+", "+"]]
    out = []
    for signs in chain:
        lam, _ = MixedSignCoxeterGraph.A_n(signs).minimal_spectral_radius()
        out.append(("".join(signs), lam))
    return out
