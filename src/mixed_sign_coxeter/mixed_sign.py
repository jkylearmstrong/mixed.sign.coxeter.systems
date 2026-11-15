"""Mixed-sign Coxeter graphs and standard families.

Implements Chapter 3, Appendix A, and Appendix B of Armstrong (2012).
"""

from __future__ import annotations

import math
from fractions import Fraction
from typing import Iterable, Mapping, Sequence

import sympy as sp

from .reflection_system import ReflectionSystem

SignLike = int | str
WeightLike = int | float | Fraction | sp.Expr | str


def _parse_sign(s: SignLike) -> int:
    if isinstance(s, str):
        s_clean = s.strip()
        if s_clean in ("+", "+1", "1"):
            return 1
        if s_clean in ("-", "-1"):
            return -1
        raise ValueError(f"Invalid sign string: {s!r}")
    if s in (1, -1):
        return int(s)
    raise ValueError(f"Sign must be +1/-1 or '+'/'-', got {s!r}")


def _parse_weight(m: WeightLike) -> int | sp.Expr:
    if m == sp.oo or m == math.inf or (isinstance(m, str) and m.strip().lower() in ("inf", "oo", "∞")):
        return sp.oo
    if isinstance(m, (int, sp.Integer)):
        val = int(m)
        if val < 2:
            raise ValueError(f"Edge weight m(i, j) must be >= 2 or inf, got {val}")
        return val
    if isinstance(m, Fraction):
        r = sp.Rational(m.numerator, m.denominator)
        if r < 2:
            raise ValueError(f"Edge weight m(i, j) must be >= 2 or inf, got {m!r}")
        return int(r) if r.is_Integer else r
    if isinstance(m, (float, sp.Float)):
        fval = float(m)
        if math.isnan(fval) or fval < 2.0:
            raise ValueError(f"Edge weight m(i, j) must be >= 2 or inf, got {m!r}")
        if math.isinf(fval):
            return sp.oo
        return sp.Float(fval)
    if isinstance(m, str):
        s = m.strip()
        try:
            r = sp.Rational(s)
            if r < 2:
                raise ValueError(f"Edge weight m(i, j) must be >= 2 or inf, got {m!r}")
            return int(r) if r.is_Integer else r
        except (TypeError, ValueError):
            pass
    if isinstance(m, sp.Expr) and m.is_real is not False:
        try:
            if float(m.evalf()) >= 2.0:
                return m
        except TypeError:
            pass
    raise ValueError(f"Unsupported edge weight: {m!r}")


def _edge_entry(m: int | sp.Expr) -> sp.Expr:
    """Compute B(e_i, e_j) = -2 cos(pi / m), or -2 for m = oo (Def. 3.1)."""
    if m == sp.oo:
        return sp.Integer(-2)
    if m == 2:
        return sp.Integer(0)
    if m == 3:
        return sp.Integer(-1)
    if m == 4:
        return -sp.sqrt(2)
    if m == 6:
        return -sp.sqrt(3)
    return -2 * sp.cos(sp.pi / sp.sympify(m))


class MixedSignCoxeterGraph(ReflectionSystem):
    """A mixed-sign Coxeter graph Gamma and its reflection system (W, S, B(Gamma)).

    Nodes are indexed 0, ..., n-1 with signs in {+1, -1} and edge weights m(i, j) >= 2
    (default 2 = no edge, oo = parallel/infinite label).
    """

    def __init__(
        self,
        signs: Sequence[SignLike],
        edges: Mapping[tuple[int, int], WeightLike] | Iterable[tuple[int, int, WeightLike]] = (),
    ):
        self._signs: tuple[int, ...] = tuple(_parse_sign(s) for s in signs)
        n = len(self._signs)
        if n == 0:
            raise ValueError("Graph must have at least one node.")

        edge_map: dict[tuple[int, int], int | sp.Expr] = {}
        if isinstance(edges, Mapping):
            items = [(u, v, w) for (u, v), w in edges.items()]
        else:
            items = list(edges)

        for u, v, w in items:
            if not (0 <= u < n and 0 <= v < n):
                raise IndexError(f"Edge ({u}, {v}) out of range for {n} nodes.")
            if u == v:
                raise ValueError(f"Self-loop ({u}, {u}) not allowed in mixed-sign Coxeter graph.")
            a, b = (u, v) if u < v else (v, u)
            parsed = _parse_weight(w)
            if parsed != 2:
                edge_map[(a, b)] = parsed

        self._edges: dict[tuple[int, int], int | sp.Expr] = edge_map

        B = sp.zeros(n, n)
        for i in range(n):
            B[i, i] = sp.Integer(2 * self._signs[i])
        for (a, b), m in edge_map.items():
            val = _edge_entry(m)
            B[a, b] = val
            B[b, a] = val

        super().__init__(B)

    @property
    def signs(self) -> tuple[int, ...]:
        return self._signs

    @property
    def edges(self) -> dict[tuple[int, int], int | sp.Expr]:
        return dict(self._edges)

    def is_classical(self) -> bool:
        """True iff all nodes are positive (Proposition 3.5)."""
        return all(s == 1 for s in self._signs)

    def negate_signs(self) -> MixedSignCoxeterGraph:
        """Return Gamma_-, the graph with all node signs negated (Def. 2.43)."""
        return MixedSignCoxeterGraph([-s for s in self._signs], self._edges)

    def join_node(self, target: int, sign: SignLike = "+", weight: WeightLike = 3) -> MixedSignCoxeterGraph:
        """Return Gamma *_{target}^m {r_n} (Definition 2.55)."""
        if not (0 <= target < self._n):
            raise IndexError(f"Target node {target} out of range.")
        new_signs = list(self._signs) + [_parse_sign(sign)]
        new_edges = dict(self._edges)
        new_edges[(target, self._n)] = _parse_weight(weight)
        return MixedSignCoxeterGraph(new_signs, new_edges)

    def delete_node(self, node: int) -> MixedSignCoxeterGraph:
        """Return Gamma / (r_node) (Definition 2.56)."""
        if self._n <= 1:
            raise ValueError("Cannot delete the only node.")
        if not (0 <= node < self._n):
            raise IndexError(f"Node {node} out of range.")
        new_signs = [s for idx, s in enumerate(self._signs) if idx != node]
        remap = {}
        cur = 0
        for idx in range(self._n):
            if idx != node:
                remap[idx] = cur
                cur += 1
        new_edges = {
            (remap[u], remap[v]): w
            for (u, v), w in self._edges.items()
            if u != node and v != node
        }
        return MixedSignCoxeterGraph(new_signs, new_edges)

    def bipartite_principal_order(self) -> tuple[int, ...]:
        """Return an ordering (N1..., N2...) for a bipartite principal element (Def. 3.31)."""
        bp = self.bipartition()
        if bp is None:
            raise ValueError("Graph is not bipartite.")
        n1, n2 = bp
        return tuple(n1 + n2)

    def bipartite_principal_element(self) -> sp.Matrix:
        """Return a bipartite principal element r*g (Def. 3.31)."""
        return self.principal_element(self.bipartite_principal_order())

    def factor_principal_polynomial(
        self, order: Sequence[int] | None = None
    ) -> sp.Expr:
        """Factor the principal polynomial over Z[x] / Q[x] (Tables B.1, B.2)."""
        poly = self.principal_polynomial(order)
        return sp.factor(poly.as_expr())

    # ------------------------------------------------------------------
    # Standard graph families (Chapter 3, Appendix A, Appendix B)
    # ------------------------------------------------------------------

    @classmethod
    def A_n(cls, signs_or_n: int | Sequence[SignLike]) -> MixedSignCoxeterGraph:
        """Path graph A_n with optional node signs (default all '+')."""
        if isinstance(signs_or_n, int):
            signs: Sequence[SignLike] = ["+"] * signs_or_n
        else:
            signs = signs_or_n
        n = len(signs)
        edges = [(i, i + 1, 3) for i in range(n - 1)]
        return cls(signs, edges)

    @classmethod
    def A_tilde(cls, n: int, negative: bool = False) -> MixedSignCoxeterGraph:
        """Cycle graph ~A_n (or ~A_{-n}) with n + 1 nodes (Definition 3.24)."""
        if n < 2:
            raise ValueError(f"~A_n requires n >= 2 (at least 3 nodes), got n={n}.")
        num_nodes = n + 1
        sign = "-" if negative else "+"
        signs = [sign] * num_nodes
        edges = [(i, (i + 1) % num_nodes, 3) for i in range(num_nodes)]
        return cls(signs, edges)

    @classmethod
    def I_2(cls, m: WeightLike, signs: Sequence[SignLike] = ("+", "+")) -> MixedSignCoxeterGraph:
        """Rank-2 graph A_2[m] / I_2[m] with specified node signs."""
        if len(signs) != 2:
            raise ValueError("I_2 requires exactly 2 signs.")
        return cls(signs, [(0, 1, m)])

    @classmethod
    def B_n(cls, n: int, signs: Sequence[SignLike] | None = None) -> MixedSignCoxeterGraph:
        """B_n = C_n (n >= 2): path with edge (0, 1) weighted 4."""
        if n < 2:
            raise ValueError("B_n requires n >= 2.")
        s = ["+"] * n if signs is None else signs
        edges = [(0, 1, 4)] + [(i, i + 1, 3) for i in range(1, n - 1)]
        return cls(s, edges)

    @classmethod
    def D_n(cls, n: int, signs: Sequence[SignLike] | None = None) -> MixedSignCoxeterGraph:
        """D_n (n >= 4): node 0 and 1 connected to node 2, then path 2..n-1."""
        if n < 4:
            raise ValueError("D_n requires n >= 4.")
        s = ["+"] * n if signs is None else signs
        edges = [(0, 2, 3), (1, 2, 3)] + [(i, i + 1, 3) for i in range(2, n - 1)]
        return cls(s, edges)

    @classmethod
    def F_4(cls, signs: Sequence[SignLike] | None = None) -> MixedSignCoxeterGraph:
        s = ["+"] * 4 if signs is None else signs
        return cls(s, [(0, 1, 3), (1, 2, 4), (2, 3, 3)])

    @classmethod
    def H_3(cls, signs: Sequence[SignLike] | None = None) -> MixedSignCoxeterGraph:
        s = ["+"] * 3 if signs is None else signs
        return cls(s, [(0, 1, 5), (1, 2, 3)])

    @classmethod
    def H_4(cls, signs: Sequence[SignLike] | None = None) -> MixedSignCoxeterGraph:
        s = ["+"] * 4 if signs is None else signs
        return cls(s, [(0, 1, 5), (1, 2, 3), (2, 3, 3)])

    @classmethod
    def E_n(cls, n: int, signs: Sequence[SignLike] | None = None) -> MixedSignCoxeterGraph:
        """E_6, E_7, E_8 (or general E_n for n >= 6)."""
        if n < 6:
            raise ValueError("E_n requires n >= 6.")
        s = ["+"] * n if signs is None else signs
        # Main chain 0-1-2-..-(n-2), branch node (n-1) attached to node 2
        edges = [(i, i + 1, 3) for i in range(n - 2)] + [(2, n - 1, 3)]
        return cls(s, edges)

    @classmethod
    def example_3_33(cls) -> MixedSignCoxeterGraph:
        """The 6-node bipartite mixed-sign Coxeter graph from Figure 3.15 / Table 3.1.

        Nodes 1..6 in the paper correspond to 0..5 here:
        0(+): r1, 1(+): r2, 2(+): r3, 3(-): r4, 4(+): r5, 5(-): r6.
        Edges: (1,2), (1,3), (3,4), (2,4), (2,6), (4,5), (5,6) in 1-based indexing.
        """
        signs = ["+", "+", "+", "-", "+", "-"]
        edges = [
            (0, 1, 3),
            (0, 2, 3),
            (2, 3, 3),
            (1, 3, 3),
            (1, 5, 3),
            (3, 4, 3),
            (4, 5, 3),
        ]
        return cls(signs, edges)

