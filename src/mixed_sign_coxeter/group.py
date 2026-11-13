"""Group-theoretic utilities for reflection groups W(B).

Supports word evaluation, element orders, finite group enumeration,
Deletion Property verification (Proposition 3.7 / Lemma 3.21), and root orbits.
"""

from __future__ import annotations

from collections import deque
from typing import Sequence

import sympy as sp

from .reflection_system import ReflectionSystem


def _matrix_key(M: sp.Matrix) -> tuple[sp.Expr, ...]:
    """Canonical hashable key for a SymPy matrix."""
    return tuple(sp.simplify(entry) for entry in M)


def evaluate_word(system: ReflectionSystem, word: Sequence[int]) -> sp.Matrix:
    """Evaluate a word [i_0, i_1, ..., i_{k-1}] as s_{i_0} ... s_{i_{k-1}}."""
    gens = system.generators()
    res = sp.eye(system.n)
    for idx in word:
        if not (0 <= idx < system.n):
            raise IndexError(f"Generator index {idx} out of range [0, {system.n}).")
        res = res * gens[idx]
    return sp.simplify(res)


def element_order(M: sp.Matrix, max_order: int = 1000) -> int | None:
    """Compute the multiplicative order of matrix M, or None if > max_order."""
    n = M.rows
    I = sp.eye(n)
    cur = M.copy()
    for k in range(1, max_order + 1):
        if sp.simplify(cur - I) == sp.zeros(n, n):
            return k
        cur = sp.simplify(cur * M)
    return None


def enumerate_group(
    system: ReflectionSystem, max_elements: int = 5000
) -> tuple[list[sp.Matrix], bool]:
    """Enumerate elements of W(B) via BFS on generating reflections.

    Returns (elements, is_complete). If len(elements) reaches max_elements,
    is_complete is False.
    """
    gens = system.generators()
    I = sp.eye(system.n)
    seen: dict[tuple[sp.Expr, ...], sp.Matrix] = {_matrix_key(I): I}
    queue: deque[sp.Matrix] = deque([I])

    while queue:
        cur = queue.popleft()
        for g in gens:
            nxt = sp.simplify(cur * g)
            key = _matrix_key(nxt)
            if key not in seen:
                seen[key] = nxt
                if len(seen) >= max_elements:
                    return list(seen.values()), False
                queue.append(nxt)

    return list(seen.values()), True


def find_two_deletions(
    system: ReflectionSystem, word: Sequence[int], target: sp.Matrix | None = None
) -> list[tuple[int, int]]:
    """Find all pairs (i, j) with i < j such that deleting word[i] and word[j]
    evaluates to `target` (defaults to evaluate_word(system, word)).

    Used to test the Deletion Property (Proposition 3.7 / Lemma 3.21).
    """
    if target is None:
        target = evaluate_word(system, word)
    matches: list[tuple[int, int]] = []
    k = len(word)
    for i in range(k):
        for j in range(i + 1, k):
            subword = [word[idx] for idx in range(k) if idx != i and idx != j]
            if sp.simplify(evaluate_word(system, subword) - target) == sp.zeros(
                system.n, system.n
            ):
                matches.append((i, j))
    return matches


def is_positive_vector(v: sp.Matrix) -> bool:
    """True if v != 0 and all entries v_i >= 0 (Definition 2.13)."""
    entries = [sp.simplify(x) for x in v]
    if all(x == 0 for x in entries):
        return False
    return all(bool(x >= 0) for x in entries)


def generate_roots(
    system: ReflectionSystem, max_word_length: int = 6
) -> tuple[list[sp.Matrix], list[sp.Matrix]]:
    """Generate roots Phi = W Pi^+ up to `max_word_length`.

    Returns (all_roots, positive_roots).
    """
    gens = system.generators()
    n = system.n
    seen: dict[tuple[sp.Expr, ...], sp.Matrix] = {}
    queue: deque[tuple[sp.Matrix, int]] = deque()

    for i in range(n):
        e_i = sp.zeros(n, 1)
        e_i[i, 0] = sp.Integer(1)
        key = tuple(e_i)
        seen[key] = e_i
        queue.append((e_i, 0))

    while queue:
        vec, depth = queue.popleft()
        if depth >= max_word_length:
            continue
        for g in gens:
            nxt = sp.simplify(g * vec)
            key = tuple(nxt)
            if key not in seen:
                seen[key] = nxt
                queue.append((nxt, depth + 1))

    all_roots = list(seen.values())
    pos_roots = [r for r in all_roots if is_positive_vector(r)]
    return all_roots, pos_roots

