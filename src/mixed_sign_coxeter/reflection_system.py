"""Core reflection systems, reflection diagrams, and principal elements.

Implements Definitions, Lemmas, and Theorems from Chapter 2 of Armstrong (2012),
"Principal Elements of Mixed-Sign Coxeter Systems".
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from itertools import permutations
from typing import Iterable, Sequence

import numpy as np
import sympy as sp


@dataclass(frozen=True)
class Signature:
    """Signature (p, q, l) of a symmetric bilinear form."""

    positive: int
    negative: int
    zero: int

    def as_tuple(self) -> tuple[int, int, int]:
        return (self.positive, self.negative, self.zero)

    def classify(self) -> str:
        """Classify an irreducible reflection system by signature (Def. 2.51)."""
        n = self.positive + self.negative + self.zero
        p, q, l = self.positive, self.negative, self.zero
        if (p, q, l) in ((n, 0, 0), (0, n, 0)):
            return "spherical"
        if (p, q, l) in ((n - 1, 0, 1), (0, n - 1, 1)):
            return "affine"
        if (p, q, l) in ((n - 1, 1, 0), (1, n - 1, 0)):
            return "hyperbolic"
        return "higher-rank"


class ReflectionSystem:
    """A reflection system (W, S, B) on R^n (Definition 2.18).

    B is represented as an exact SymPy Matrix (n x n, symmetric, with B[i, i] != 0).
    """

    def __init__(self, B: sp.Matrix | Sequence[Sequence[object]] | np.ndarray):
        if isinstance(B, np.ndarray):
            mat = sp.Matrix(B.tolist())
        elif isinstance(B, sp.MatrixBase):
            mat = sp.Matrix(B)
        else:
            mat = sp.Matrix(B)

        if mat.rows != mat.cols:
            raise ValueError(f"Bilinear form matrix must be square, got {mat.rows}x{mat.cols}.")
        if mat.rows == 0:
            raise ValueError("Bilinear form matrix must have at least 1 row.")
        if not mat.is_symmetric():
            raise ValueError("Bilinear form matrix B must be symmetric.")
        for i in range(mat.rows):
            if sp.simplify(mat[i, i]) == 0:
                raise ValueError(f"Diagonal entry B[{i}, {i}] must be nonzero.")

        self._B: sp.Matrix = mat
        self._n: int = mat.rows

    @property
    def n(self) -> int:
        return self._n

    @property
    def B(self) -> sp.Matrix:
        return self._B.copy()

    def B_numpy(self) -> np.ndarray:
        """Return B as a float64 NumPy array."""
        return np.array(self._B.evalf(), dtype=np.float64)

    def quadratic_form(self, v: Sequence[object] | sp.Matrix) -> sp.Expr:
        """Compute Q(v) = B(v, v) = v^T B v (Definition 2.48)."""
        vec = sp.Matrix(v)
        if vec.rows != self._n or vec.cols != 1:
            vec = vec.reshape(self._n, 1)
        return sp.simplify((vec.T * self._B * vec)[0, 0])

    def bilinear(self, u: Sequence[object] | sp.Matrix, v: Sequence[object] | sp.Matrix) -> sp.Expr:
        """Compute B(u, v) = u^T B v."""
        u_vec = sp.Matrix(u).reshape(self._n, 1)
        v_vec = sp.Matrix(v).reshape(self._n, 1)
        return sp.simplify((u_vec.T * self._B * v_vec)[0, 0])

    def reflection_matrix(self, i: int) -> sp.Matrix:
        """Return the generating reflection matrix s_i (Remark 2.7).

        s_i(e_j) = e_j - (2 B(e_i, e_j) / B(e_i, e_i)) e_i.
        """
        if not (0 <= i < self._n):
            raise IndexError(f"Generator index {i} out of range [0, {self._n}).")
        M = sp.eye(self._n)
        bii = self._B[i, i]
        for j in range(self._n):
            if j == i:
                M[i, i] = sp.Integer(-1)
            else:
                M[i, j] = sp.simplify(-2 * self._B[i, j] / bii)
        return M

    def generators(self) -> list[sp.Matrix]:
        """Return the list of generating reflection matrices S = [s_0, ..., s_{n-1}]."""
        return [self.reflection_matrix(i) for i in range(self._n)]

    def generators_numpy(self) -> list[np.ndarray]:
        """Return generating reflections as float64 NumPy arrays."""
        return [np.array(s.evalf(), dtype=np.float64) for s in self.generators()]

    def preserves_form(self, M: sp.Matrix) -> bool:
        """Check whether M^T B M == B (Definition 2.14 / Proposition 2.17)."""
        diff = sp.simplify(M.T * self._B * M - self._B)
        return diff == sp.zeros(self._n, self._n)

    def adjacency_list(self) -> list[list[int]]:
        """Adjacency list of the underlying reflection diagram Gamma (Def. 2.25)."""
        adj: list[list[int]] = [[] for _ in range(self._n)]
        for i in range(self._n):
            for j in range(i + 1, self._n):
                if sp.simplify(self._B[i, j]) != 0:
                    adj[i].append(j)
                    adj[j].append(i)
        return adj

    def connected_components(self) -> list[list[int]]:
        """Return connected components of the reflection diagram."""
        adj = self.adjacency_list()
        visited = [False] * self._n
        comps: list[list[int]] = []
        for start in range(self._n):
            if not visited[start]:
                comp: list[int] = []
                q = deque([start])
                visited[start] = True
                while q:
                    u = q.popleft()
                    comp.append(u)
                    for v in adj[u]:
                        if not visited[v]:
                            visited[v] = True
                            q.append(v)
                comps.append(sorted(comp))
        return comps

    def is_irreducible(self) -> bool:
        """True if the reflection diagram is connected (Definition 2.44)."""
        return len(self.connected_components()) == 1

    def is_tree(self) -> bool:
        """True if the reflection diagram is connected and acyclic."""
        if not self.is_irreducible():
            return False
        adj = self.adjacency_list()
        edges = sum(len(nbrs) for nbrs in adj) // 2
        return edges == self._n - 1

    def bipartition(self) -> tuple[list[int], list[int]] | None:
        """Return (N1, N2) bipartition if the reflection diagram is bipartite, else None."""
        adj = self.adjacency_list()
        color: dict[int, int] = {}
        for start in range(self._n):
            if start in color:
                continue
            color[start] = 0
            q = deque([start])
            while q:
                u = q.popleft()
                for v in adj[u]:
                    if v not in color:
                        color[v] = 1 - color[u]
                        q.append(v)
                    elif color[v] == color[u]:
                        return None
        n1 = sorted(i for i, c in color.items() if c == 0)
        n2 = sorted(i for i, c in color.items() if c == 1)
        return (n1, n2)

    def is_bipartite(self) -> bool:
        """True if the reflection diagram is bipartite (Definition 2.40)."""
        return self.bipartition() is not None

    def bipartite_conjugator(self) -> sp.Matrix:
        """Return P in O such that P^T B(Gamma) P = -B(Gamma_-) (Theorem 1.4).

        Raises ValueError if the reflection diagram is not bipartite.
        """
        bp = self.bipartition()
        if bp is None:
            raise ValueError("Reflection diagram is not bipartite.")
        n1, _ = bp
        n1_set = set(n1)
        P = sp.eye(self._n)
        for i in range(self._n):
            if i in n1_set:
                P[i, i] = sp.Integer(-1)
        return P

    def negate_node_weights(self) -> ReflectionSystem:
        """Return the reflection system for Gamma_- (negated diagonal entries, Def. 2.43)."""
        B_neg = self._B.copy()
        for i in range(self._n):
            B_neg[i, i] = -B_neg[i, i]
        return ReflectionSystem(B_neg)

    def howlett_U(self, order: Sequence[int] | None = None) -> sp.Matrix:
        """Construct the upper-triangular matrix U from Theorem 1.1.

        If `order` is provided (a permutation of 0..n-1), computes U for the
        permuted basis (e_{order[0]}, ..., e_{order[n-1]}).
        """
        if order is None:
            perm = list(range(self._n))
        else:
            perm = list(order)
            if sorted(perm) != list(range(self._n)):
                raise ValueError("order must be a permutation of 0..n-1.")

        U = sp.zeros(self._n, self._n)
        for i in range(self._n):
            pi = perm[i]
            U[i, i] = self._B[pi, pi] / sp.Integer(2)
            for j in range(i + 1, self._n):
                pj = perm[j]
                U[i, j] = self._B[pi, pj]
        return U

    def principal_element(self, order: Sequence[int] | None = None) -> sp.Matrix:
        """Compute the principal element w_sigma = s_{sigma(0)} ... s_{sigma(n-1)}.

        Uses Theorem 1.1 (-U^{-1} U^T) when order is identity, or direct product.
        """
        if order is None:
            U = self.howlett_U()
            return sp.simplify(-U.inv() * U.T)
        perm = list(order)
        if sorted(perm) != list(range(self._n)):
            raise ValueError("order must be a permutation of 0..n-1.")
        gens = self.generators()
        w = sp.eye(self._n)
        for idx in perm:
            w = w * gens[idx]
        return sp.simplify(w)

    def principal_polynomial(
        self,
        order: Sequence[int] | None = None,
        var: sp.Symbol | None = None,
        monic: bool = True,
    ) -> sp.Poly:
        """Compute the principal polynomial chi(w_sigma, x) = det(xI - w_sigma) (Def. 2.60).

        By Lemma 2.63, det(xI - w_sigma) = det(U_sigma)^{-1} det(U_sigma * x + U_sigma^T).
        """
        x = var if var is not None else sp.Symbol("x")
        U = self.howlett_U(order)
        expr = sp.det(U * x + U.T)
        if monic:
            expr = expr / sp.det(U)
        return sp.Poly(sp.expand(sp.simplify(expr)), x)

    def signature(self, tol: float = 1e-9) -> Signature:
        """Compute the signature (p, q, l) of B (Definition 2.47)."""
        eigvals = np.linalg.eigvalsh(self.B_numpy())
        p = int(np.sum(eigvals > tol))
        q = int(np.sum(eigvals < -tol))
        l = self._n - p - q
        return Signature(positive=p, negative=q, zero=l)

    def classify(self, tol: float = 1e-9) -> str:
        """Classify an irreducible reflection system (Definition 2.51)."""
        if not self.is_irreducible():
            raise ValueError("Classification by signature in Def. 2.51 requires irreducible system.")
        return self.signature(tol=tol).classify()

    def _eigenvalues_high_prec(self, order: Sequence[int] | None = None) -> list[complex]:
        """Compute eigenvalues of w_sigma via high-precision roots of principal_polynomial."""
        poly = self.principal_polynomial(order)
        try:
            _, factors = sp.sqf_list(poly)
            eigvals: list[complex] = []
            for fac, mult in factors:
                roots = sp.nroots(fac, n=30, maxsteps=200)
                for r in roots:
                    z = complex(r.evalf())
                    eigvals.extend([z] * mult)
            return eigvals
        except Exception:
            w = self.principal_element(order)
            w_np = np.array(w.evalf(), dtype=np.complex128)
            return [complex(z) for z in np.linalg.eigvals(w_np)]

    def spectral_radius(self, order: Sequence[int] | None = None) -> float:
        """Compute the spectral radius lambda(w_sigma) = max |lambda_i| (Def. 2.61)."""
        eigvals = self._eigenvalues_high_prec(order)
        return float(max(abs(z) for z in eigvals))

    def roots_outside_unit_disk(
        self, order: Sequence[int] | None = None, tol: float = 1e-9
    ) -> int:
        """Number of eigenvalues of w_sigma with |lambda| > 1 (N(Gamma) in Appendix B)."""
        eigvals = self._eigenvalues_high_prec(order)
        return int(sum(1 for z in eigvals if abs(z) > 1.0 + tol))

    def minimal_spectral_radius(self) -> tuple[float, tuple[int, ...]]:
        """Compute Lambda(Gamma) = min{lambda(w)} over principal elements (Def. 2.62).

        If Gamma is a tree, all principal elements are conjugate (Theorem 2.58),
        so only one ordering needs to be checked.
        Returns (min_lambda, argmin_order).
        """
        if self.is_tree():
            order = tuple(range(self._n))
            return self.spectral_radius(order), order

        # Fix first generator up to cyclic shift to reduce n! to (n-1)!
        # Cyclic shifts of a principal element are conjugate, so they share eigenvalues.
        best_val = float("inf")
        best_order: tuple[int, ...] = tuple(range(self._n))
        for rest in permutations(range(1, self._n)):
            order = (0,) + rest
            val = self.spectral_radius(order)
            if val < best_val:
                best_val = val
                best_order = order
        return best_val, best_order

    def is_conjugate_by_O(self, other: ReflectionSystem) -> sp.Matrix | None:
        """Check if two reflection systems are conjugate by P in O (Def. 2.29).

        Searches over signed permutation matrices P in O such that
        P^T B1 P == B2 or P^T B1 P == -B2.
        Intended for small ranks (n <= 6).
        """
        if self._n != other._n:
            return None
        n = self._n
        from itertools import product

        for perm in permutations(range(n)):
            for signs in product((-1, 1), repeat=n):
                P = sp.zeros(n, n)
                for j in range(n):
                    P[perm[j], j] = signs[j]
                cand = sp.simplify(P.T * self._B * P)
                if cand == other._B or cand == -other._B:
                    return P
        return None
