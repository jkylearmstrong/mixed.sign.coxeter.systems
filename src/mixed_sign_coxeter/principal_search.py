"""Exhaustive search for Question 3.35: which principal elements minimize spectral radius?

For every connected simply-laced mixed-sign graph on n nodes (up to relabelling and
graph automorphisms), every principal element w_sigma = s_sigma(1) ... s_sigma(n) is
computed. Principal elements with the same acyclic orientation of Gamma (edge i -> j
when s_i comes before s_j) are equal, since non-adjacent generators commute, so one
element per orientation suffices. Trees are skipped: all their principal elements
are conjugate (Theorem 2.58), so only graphs with a cycle can show any variation.

All matrices have integer entries (m = 3), so characteristic polynomials are computed
exactly (Faddeev-LeVerrier over Z). Spectral radii are then taken from the roots of
the square-free factors, which avoids the error that repeated eigenvalues on the unit
circle cause in floating-point eigenvalue routines.

Candidate "types" tested against the minimum:
* bipartite principal elements (Definition 3.31), when Gamma is bipartite;
* sign-sorted elements: every edge joining a positive node to a negative node is
  oriented the same way (all positive-to-negative, or all negative-to-positive), as
  in the last row of Table 3.1.
"""

from __future__ import annotations

import itertools
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from functools import lru_cache

import numpy as np
import sympy as sp

_X = sp.Symbol("x")
TOL = 1e-9


def integer_generators(signs: tuple[int, ...], edges: list[tuple[int, int]]) -> list[np.ndarray]:
    """Reflections of a simply-laced mixed-sign graph (all edge weights 3).

    s_i e_j = e_j - (2 B_ij / B_ii) e_i with B_ij = -1 and B_ii = 2 sign_i, so row i of
    s_i has -1 on the diagonal and sign_i in each neighbouring column.
    """
    n = len(signs)
    out = []
    for i in range(n):
        s = np.eye(n, dtype=np.int64)
        s[i, i] = -1
        for a, b in edges:
            if i in (a, b):
                s[i, b if a == i else a] = signs[i]
        out.append(s)
    return out


def integer_charpoly(M: np.ndarray) -> tuple[int, ...]:
    """Coefficients of det(xI - M), highest degree first, by Faddeev-LeVerrier."""
    n = len(M)
    Mi = [[int(v) for v in row] for row in M.tolist()]
    coeffs = [1]
    A = [[0] * n for _ in range(n)]
    for k in range(1, n + 1):
        T = [[A[i][j] + (coeffs[-1] if i == j else 0) for j in range(n)] for i in range(n)]
        A = [[sum(Mi[i][l] * T[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        tr = sum(A[i][i] for i in range(n))
        if tr % k:
            raise ArithmeticError("non-integral Faddeev-LeVerrier step")
        coeffs.append(-tr // k)
    return tuple(coeffs)


@lru_cache(maxsize=None)
def radius_of_polynomial(coeffs: tuple[int, ...]) -> float:
    """Largest modulus of a root, computed factor by factor over Q."""
    best = 0.0
    for fac, _ in sp.factor_list(sp.Poly(list(coeffs), _X).as_expr())[1]:
        p = sp.Poly(fac, _X)
        if p.degree() > 0:
            best = max(best, max(abs(complex(z)) for z in p.nroots(n=30)))
    return best


def _connected(n, edges) -> bool:
    adj = defaultdict(set)
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    seen, stack = {0}, [0]
    while stack:
        u = stack.pop()
        for v in adj[u]:
            if v not in seen:
                seen.add(v)
                stack.append(v)
    return len(seen) == n


def _two_colouring(n, edges) -> dict[int, int] | None:
    adj = defaultdict(set)
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    col, stack = {0: 0}, [0]
    while stack:
        u = stack.pop()
        for v in adj[u]:
            if v not in col:
                col[v] = 1 - col[u]
                stack.append(v)
            elif col[v] == col[u]:
                return None
    return col


def cyclic_graphs(n: int):
    """Connected simple graphs on n nodes with at least one cycle, up to isomorphism."""
    pairs = list(itertools.combinations(range(n), 2))
    seen = set()
    for mask in range(1 << len(pairs)):
        e = [pairs[k] for k in range(len(pairs)) if mask >> k & 1]
        if len(e) < n or not _connected(n, e):
            continue
        canon = min(
            tuple(sorted((min(p[a], p[b]), max(p[a], p[b])) for a, b in e))
            for p in itertools.permutations(range(n))
        )
        if canon not in seen:
            seen.add(canon)
            yield list(canon)


def orientation_radii(signs, edges) -> dict[tuple[bool, ...], tuple[float, tuple[int, ...]]]:
    """Map each acyclic orientation (realised by some order) to (radius, an order)."""
    n = len(signs)
    gens = integer_generators(tuple(signs), edges)
    out: dict[tuple[bool, ...], tuple[float, tuple[int, ...]]] = {}
    for p in itertools.permutations(range(n)):
        pos = {v: k for k, v in enumerate(p)}
        o = tuple(pos[a] < pos[b] for a, b in edges)
        if o in out:
            continue
        w = np.eye(n, dtype=np.int64)
        for i in p:
            w = w @ gens[i]
        out[o] = (radius_of_polynomial(integer_charpoly(w)), p)
    return out


@dataclass(frozen=True)
class GraphRecord:
    signs: tuple[int, ...]
    edges: tuple[tuple[int, int], ...]
    minimum: float
    maximum: float
    argmin: tuple[int, ...]
    bipartite_radius: float | None
    sign_sorted_minimum: float | None

    @property
    def mixed(self) -> bool:
        return len(set(self.signs)) > 1

    @property
    def bipartite_fails(self) -> bool:
        return self.bipartite_radius is not None and self.bipartite_radius > self.minimum + TOL


@dataclass
class SearchSummary:
    n: int
    graphs: int = 0
    constant: int = 0
    records: list[GraphRecord] = field(default_factory=list)

    def counts(self) -> Counter:
        c: Counter = Counter()
        for r in self.records:
            c["nonconstant"] += 1
            if r.bipartite_radius is not None:
                c["bipartite"] += 1
                if r.mixed:
                    c["bipartite_mixed"] += 1
                if r.bipartite_fails:
                    c["bipartite_not_min"] += 1
                    if abs(r.bipartite_radius - r.maximum) < TOL:
                        c["bipartite_is_max"] += 1
            if r.mixed:
                c["mixed"] += 1
                if r.sign_sorted_minimum is not None and r.sign_sorted_minimum < r.minimum + TOL:
                    c["sign_sorted_attains_min"] += 1
        return c


def search_question_3_35(n: int) -> SearchSummary:
    """Run the search on all cyclic simply-laced graphs with n nodes (n <= 6 is quick)."""
    summary = SearchSummary(n=n)
    for edges in cyclic_graphs(n):
        es = set(edges)
        auts = [
            p
            for p in itertools.permutations(range(n))
            if {(min(p[a], p[b]), max(p[a], p[b])) for a, b in edges} == es
        ]
        seen = set()
        for signs in itertools.product((1, -1), repeat=n):
            key = min(tuple(signs[p.index(i)] for i in range(n)) for p in auts)
            if key in seen:
                continue
            seen.add(key)
            summary.graphs += 1
            radii = orientation_radii(signs, edges)
            vals = [r for r, _ in radii.values()]
            lo, hi = min(vals), max(vals)
            if hi - lo < TOL:
                summary.constant += 1
                continue
            argmin = min(radii.values())[1]
            col = _two_colouring(n, edges)
            rb = None
            if col is not None:
                rb = radii[tuple(col[a] == 0 for a, b in edges)][0]

            def sorted_ok(o):
                firsts = {signs[a] if f else signs[b] for (a, b), f in zip(edges, o) if signs[a] != signs[b]}
                return len(firsts) <= 1

            ss = [r for o, (r, _) in radii.items() if sorted_ok(o)]
            summary.records.append(
                GraphRecord(
                    signs=tuple(signs),
                    edges=tuple(edges),
                    minimum=lo,
                    maximum=hi,
                    argmin=argmin,
                    bipartite_radius=rb,
                    sign_sorted_minimum=min(ss) if ss else None,
                )
            )
    return summary


def alternating_square() -> tuple[tuple[int, ...], list[tuple[int, int]]]:
    """The 4-cycle r0 - r1 - r2 - r3 - r0 with signs (+, -, +, -).

    The smallest graph on which a bipartite principal element fails to minimize the
    spectral radius (four nodes, against six in Example 3.33): the bipartite element
    s0 s2 s1 s3 has radius 3 + 2 sqrt 2 ~ 5.82843, the maximum, while the circuit
    s0 s1 s2 s3 has radius ~ 3.54646.
    """
    return (1, -1, 1, -1), [(0, 1), (1, 2), (2, 3), (0, 3)]


def cycle_radius_by_circulation(signs: tuple[int, ...]) -> dict[int, float]:
    """For the cycle with the given node signs: |circulation| -> spectral radius.

    On a cycle of length k, conjugacy classes of principal elements are labelled by the
    circulation (#edges oriented forwards - #backwards), which lies in
    {-(k-2), ..., k-2}. Reversal (c -> -c) gives an element with the same radius
    whenever B is nondegenerate, so only |c| is reported.
    """
    k = len(signs)
    edges = [(i, (i + 1) % k) for i in range(k)]
    out: dict[int, float] = {}
    for o, (r, p) in orientation_radii(signs, edges).items():
        c = abs(sum(1 if f else -1 for f in o))
        out.setdefault(c, r)
    return dict(sorted(out.items()))
