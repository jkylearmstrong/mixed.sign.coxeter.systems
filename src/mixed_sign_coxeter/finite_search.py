"""Search for finite mixed-sign Coxeter groups (Remark A.3 of Armstrong 2012).

Remark A.3 asks whether there are finite W(Gamma) beyond Table A.2 and Figure A.1.
This module answers it exhaustively for connected graphs of rank <= 4 (any edge
weights) and for simply-laced graphs of rank <= 6.

The search rests on the following reduction (proved in docs/verifications.md and
exercised in the tests):

    If Gamma is connected and W(Gamma) is finite, then B(Gamma) is definite.

Sketch. A finite W preserves a positive definite form Q, so V = R^n is completely
reducible. Each s_i has a one-dimensional (-1)-eigenspace spanned by e_i, so in any
W-stable splitting V = U1 + U2 each e_i lies in one summand and s_i is the identity
on the other. If e_i is in U1, e_j is in U2 and B(e_i, e_j) != 0, then
s_i e_j = e_j - c e_i with c != 0 is not in U2, a contradiction. Connectedness then
puts every e_i in one summand, and the e_i span V, so V is irreducible. By Schur's
lemma the W-invariant symmetric forms on an irreducible real representation are the
multiples of Q, so B = cQ with c != 0 (the diagonal of B is +-2). Hence B is definite.

Consequences.
* A connected graph with both a positive and a negative node has W(Gamma) infinite
  (Corollary 3.18 of the thesis), because its diagonal has entries +2 and -2.
* All-positive graphs are classical: finite exactly for Table A.1.
* All-negative graphs: W(B) = W(-B), so W is finite iff the reflection group of
  -B is. Bipartite ones are conjugate to Table A.1 graphs (Theorem 1.4), which is
  Table A.2. Non-bipartite ones are where new examples can appear.

Finite irreducible reflection groups of rank 3 have order <= 120 and of rank 4 order
<= 14400, and every product of two of their reflections has order <= 5. So for rank
3 and 4 it suffices to try weights m in {2, 3, 4, 5} (6 is included as a check), and
a breadth-first enumeration that passes the bound proves W infinite.
"""

from __future__ import annotations

import itertools
import math
from collections import defaultdict
from dataclasses import dataclass, field

import numpy as np

#: (rank, |W|, number of reflections) -> Coxeter type of a finite irreducible group.
FINITE_IRREDUCIBLE_TYPES: dict[tuple[int, int, int], str] = {
    (1, 2, 1): "A1",
    (3, 24, 6): "A3",
    (3, 48, 9): "B3",
    (3, 120, 15): "H3",
    (4, 120, 10): "A4",
    (4, 192, 12): "D4",
    (4, 384, 16): "B4",
    (4, 1152, 24): "F4",
    (4, 14400, 60): "H4",
}

#: Largest order of a finite irreducible reflection group of the given rank (rank >= 3).
MAX_IRREDUCIBLE_ORDER = {3: 120, 4: 14400}

#: |Phi| (number of roots) -> simply-laced type, for ranks 5 and 6.
SIMPLY_LACED_ROOT_COUNTS: dict[tuple[int, int], str] = {
    (5, 30): "A5",
    (5, 40): "D5",
    (6, 42): "A6",
    (6, 60): "D6",
    (6, 72): "E6",
}


def gram_matrix(signs: tuple[int, ...], weights: dict[tuple[int, int], int]) -> np.ndarray:
    """B(Gamma) as floats: diagonal 2*sign, off-diagonal -2 cos(pi / m)."""
    n = len(signs)
    B = np.diag([2.0 * s for s in signs])
    for (i, j), m in weights.items():
        B[i, j] = B[j, i] = -2.0 * math.cos(math.pi / m)
    return B


def reflections(B: np.ndarray) -> list[np.ndarray]:
    """Generating reflections s_i(v) = v - (2 B(v, e_i) / B_ii) e_i as matrices."""
    n = len(B)
    out = []
    for i in range(n):
        s = np.eye(n)
        s[i, :] -= (2.0 / B[i, i]) * B[i, :]
        out.append(s)
    return out


def is_definite(B: np.ndarray, tol: float = 1e-9) -> bool:
    ev = np.linalg.eigvalsh(B)
    return bool(ev.min() > tol or ev.max() < -tol)


def _key(M: np.ndarray) -> bytes:
    # "+ 0.0" folds -0.0 into 0.0 so equal matrices hash equally.
    return (np.round(M, 6) + 0.0).tobytes()


def bounded_group_order(B: np.ndarray, cap: int) -> tuple[int, int] | None:
    """(|W(B)|, #reflections in W) by breadth-first search, or None if |W| > cap.

    Floating point with entries rounded to 1e-6; adequate because every entry of a
    finite group element here lies in Z[2 cos(pi/m)] with small coefficients.
    """
    gens = reflections(B)
    n = len(B)
    ident = np.eye(n)
    seen = {_key(ident): ident}
    frontier = [ident]
    while frontier:
        nxt = []
        for M in frontier:
            for s in gens:
                N = M @ s
                k = _key(N)
                if k not in seen:
                    seen[k] = N
                    if len(seen) > cap:
                        return None
                    nxt.append(N)
        frontier = nxt
    refl = 0
    for M in seen.values():
        if abs(np.linalg.det(M) + 1) < 1e-6 and np.linalg.matrix_rank(M - ident, tol=1e-6) == 1:
            refl += 1
    return len(seen), refl


def _connected(n: int, edges) -> bool:
    adj = defaultdict(set)
    for i, j in edges:
        adj[i].add(j)
        adj[j].add(i)
    seen, stack = {0}, [0]
    while stack:
        u = stack.pop()
        for v in adj[u]:
            if v not in seen:
                seen.add(v)
                stack.append(v)
    return len(seen) == n


def _is_bipartite(n: int, edges) -> bool:
    adj = defaultdict(set)
    for i, j in edges:
        adj[i].add(j)
        adj[j].add(i)
    col = {0: 0}
    stack = [0]
    while stack:
        u = stack.pop()
        for v in adj[u]:
            if v not in col:
                col[v] = 1 - col[u]
                stack.append(v)
            elif col[v] == col[u]:
                return False
    return True


def canonical_form(signs, weights) -> tuple:
    """Lexicographically least relabelling of a signed, weighted graph."""
    n = len(signs)
    best = None
    for p in itertools.permutations(range(n)):
        s = [0] * n
        for i in range(n):
            s[p[i]] = signs[i]
        ew = tuple(sorted(((min(p[i], p[j]), max(p[i], p[j])), m) for (i, j), m in weights.items()))
        c = (tuple(s), ew)
        if best is None or c < best:
            best = c
    return best


@dataclass(frozen=True)
class FiniteGraph:
    signs: tuple[int, ...]
    weights: tuple[tuple[tuple[int, int], int], ...]
    order: int
    n_reflections: int
    coxeter_type: str
    bipartite: bool

    @property
    def rank(self) -> int:
        return len(self.signs)

    @property
    def sign_class(self) -> str:
        if all(s == 1 for s in self.signs):
            return "positive"
        if all(s == -1 for s in self.signs):
            return "negative"
        return "mixed"

    @property
    def catalog_source(self) -> str:
        """Where the thesis lists this graph, or 'new'."""
        if self.sign_class == "positive":
            return "Table A.1"
        if self.sign_class == "negative" and self.bipartite:
            return "Table A.2"
        if self.sign_class == "negative" and self.weights == ((( 0, 1), 3), ((0, 2), 3), ((1, 2), 3)):
            return "Figure A.1 (~A_{-2})"
        return "new"


@dataclass
class FiniteSearchResult:
    rank: int
    weights: tuple[int, ...]
    graphs_examined: int = 0
    definite: int = 0
    finite: list[FiniteGraph] = field(default_factory=list)
    indefinite_but_finite: int = 0  # must stay 0 (the reduction above)


def search_finite_graphs(rank: int, weights=(3, 4, 5, 6), check_indefinite: bool = False) -> FiniteSearchResult:
    """All connected mixed-sign graphs of the given rank (3 or 4) with W finite.

    Graphs are taken up to relabelling. Edge weights range over `weights` (2 means
    no edge and is always allowed). With check_indefinite=True the group order of
    every indefinite graph is also bounded, confirming none is finite (slow at rank 4).
    """
    if rank not in MAX_IRREDUCIBLE_ORDER:
        raise ValueError("rank must be 3 or 4")
    cap = MAX_IRREDUCIBLE_ORDER[rank]
    pairs = list(itertools.combinations(range(rank), 2))
    res = FiniteSearchResult(rank=rank, weights=tuple(weights))
    seen = set()
    for ms in itertools.product((2,) + tuple(weights), repeat=len(pairs)):
        w = {p: m for p, m in zip(pairs, ms) if m != 2}
        if not _connected(rank, w):
            continue
        for signs in itertools.product((1, -1), repeat=rank):
            c = canonical_form(signs, w)
            if c in seen:
                continue
            seen.add(c)
            res.graphs_examined += 1
            cs, cw = c
            B = gram_matrix(cs, dict(cw))
            definite = is_definite(B)
            if not definite and not check_indefinite:
                continue
            out = bounded_group_order(B, cap)
            if out is None:
                if definite:
                    res.definite += 1
                continue
            if not definite:
                res.indefinite_but_finite += 1
                continue
            res.definite += 1
            order, nref = out
            res.finite.append(
                FiniteGraph(
                    signs=cs,
                    weights=cw,
                    order=order,
                    n_reflections=nref,
                    coxeter_type=FINITE_IRREDUCIBLE_TYPES.get((rank, order, nref), "?"),
                    bipartite=_is_bipartite(rank, [e for e, _ in cw]),
                )
            )
    return res


def _simple_graphs(n: int):
    pairs = list(itertools.combinations(range(n), 2))
    seen = set()
    for mask in range(1 << len(pairs)):
        e = [pairs[k] for k in range(len(pairs)) if mask >> k & 1]
        if len(e) < n - 1 or not _connected(n, e):
            continue
        best = None
        for p in itertools.permutations(range(n)):
            c = tuple(sorted((min(p[a], p[b]), max(p[a], p[b])) for a, b in e))
            if best is None or c < best:
                best = c
        if best not in seen:
            seen.add(best)
            yield list(best)


def root_count(Q: np.ndarray) -> int:
    """|W . {e_i}| for an integral positive definite Gram matrix Q with Q_ii = 2."""
    n = len(Q)
    Qi = Q.astype(np.int64)
    frontier = [tuple(int(i == j) for j in range(n)) for i in range(n)]
    orbit = set(frontier)
    while frontier:
        nxt = []
        for v in frontier:
            vv = np.array(v, dtype=np.int64)
            for i in range(n):
                c = int((Qi[i] @ vv))
                if c:
                    w = list(v)
                    w[i] -= c
                    w = tuple(w)
                    if w not in orbit:
                        orbit.add(w)
                        nxt.append(w)
        frontier = nxt
    return len(orbit)


def simply_laced_negative_finite(n: int) -> list[tuple[tuple[tuple[int, int], ...], str, bool]]:
    """Connected all-negative simply-laced graphs of rank n with W finite.

    For m in {2, 3}, -B is an integral Gram matrix with 2 on the diagonal, so W
    preserves the lattice Z^n. If -B is positive definite W is finite (a discrete
    subgroup of a compact group); otherwise it is infinite by the reduction. The
    type is read off from the number of roots. Returns (edges, type, bipartite).
    """
    out = []
    for e in _simple_graphs(n):
        Q = 2 * np.eye(n)
        for a, b in e:
            Q[a, b] = Q[b, a] = 1.0  # -B for negative nodes, m = 3
        if np.linalg.eigvalsh(Q).min() <= 1e-9:
            continue
        t = SIMPLY_LACED_ROOT_COUNTS.get((n, root_count(Q)), "?")
        out.append((tuple(e), t, _is_bipartite(n, e)))
    return out
