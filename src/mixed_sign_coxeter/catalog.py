"""Catalog, signature classification, Mahler measure, and Appendix A–D computations."""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Iterable

import numpy as np
import sympy as sp

from .mixed_sign import MixedSignCoxeterGraph
from .reflection_system import ReflectionSystem


def mahler_measure(poly: sp.Poly | sp.Expr, var: sp.Symbol | None = None) -> float:
    """Compute the Mahler measure M(P) = |a_d| * prod_{|alpha_i| > 1} |alpha_i|."""
    x = var or (poly.gen if isinstance(poly, sp.Poly) else sp.Symbol("x"))
    if not isinstance(poly, sp.Poly):
        poly = sp.Poly(poly, x)
    const, factors = sp.factor_list(poly.as_expr(), x)
    prod = abs(complex(const))
    for fac_expr, mult in factors:
        fac = sp.Poly(fac_expr, x)
        if fac.degree() == 0:
            continue
        if fac.degree() == 1:
            a, b = fac.all_coeffs()
            roots = [-complex(b) / complex(a)]
        else:
            try:
                roots = [complex(r) for r in sp.nroots(fac, n=20, maxsteps=200)]
            except Exception:
                roots = list(np.roots([complex(c) for c in fac.all_coeffs()]))
        fac_lc = abs(complex(fac.LC()))
        fac_prod = fac_lc
        for r in roots:
            val = abs(r)
            if val > 1.0 + 1e-12:
                fac_prod *= val
        prod *= fac_prod ** mult
    return float(prod)


def classify_signature(system: ReflectionSystem) -> str:
    """Classify a ReflectionSystem by its bilinear-form signature (Defs. 2.47–2.51)."""
    sig = system.signature()
    n = system.n
    if sig.positive == n:
        return "positive_definite"
    if sig.negative == n:
        return "negative_definite"
    if sig.negative == 0 and sig.zero > 0:
        return "positive_semidefinite_degenerate"
    if sig.positive > 0 and sig.negative == 1 and sig.zero == 0:
        return "hyperbolic"
    return "indefinite"


@dataclass(frozen=True)
class AnTableEntry:
    """One row of the Appendix B A_n-type mixed-sign table."""

    signs: str
    signature: tuple[int, int, int]
    classification: str
    principal_polynomial: sp.Expr
    spectral_radius: float
    mahler_measure: float


def A_n_sign_table(n: int, unique_up_to_negation: bool = True) -> list[AnTableEntry]:
    """Generate the Appendix B table of A_n mixed-sign Coxeter systems."""
    x = sp.Symbol("x")
    entries: list[AnTableEntry] = []
    seen: set[str] = set()
    for bits in product(["+", "-"], repeat=n):
        s_str = "".join(bits)
        neg_str = "".join("-" if b == "+" else "+" for b in bits)
        if unique_up_to_negation and neg_str in seen:
            continue
        seen.add(s_str)
        g = MixedSignCoxeterGraph.A_n(list(bits))
        sig = g.signature()
        chi = sp.factor(g.principal_polynomial(var=x).as_expr())
        rho = float(g.spectral_radius())
        mm = mahler_measure(chi, var=x)
        entries.append(
            AnTableEntry(
                signs=s_str,
                signature=(sig.positive, sig.negative, sig.zero),
                classification=classify_signature(g),
                principal_polynomial=chi,
                spectral_radius=rho,
                mahler_measure=mm,
            )
        )
    return entries


def finite_even_odd_cycle_determinants(even_ns: Iterable[int] = (2, 4, 6)) -> dict[int, int]:
    """Verify Remark 3.26: det(-B(~A_{-n})) = 4 for even n (strictly negative definite)."""
    out: dict[int, int] = {}
    for n in even_ns:
        if n % 2 != 0:
            raise ValueError(f"Expected even n, got {n}")
        g = MixedSignCoxeterGraph.A_tilde(n, negative=True)
        out[n] = int(sp.det(-g.B))
    return out


def table_a1(max_rank: int = 8) -> dict[str, MixedSignCoxeterGraph]:
    """Return the Appendix A Table A.1 catalog of finite all-positive Coxeter graphs.

    Includes A_n (n=1..max_rank), B_n (n=2..max_rank), D_n (n=4..max_rank),
    E_6, E_7, E_8 (when max_rank >= 6/7/8), F_4, H_3, H_4, and I_2[m] (m=3..8).
    """
    catalog: dict[str, MixedSignCoxeterGraph] = {}
    for n in range(1, max_rank + 1):
        catalog[f"A_{n}"] = MixedSignCoxeterGraph.A_n(n)
    for n in range(2, max_rank + 1):
        catalog[f"B_{n}"] = MixedSignCoxeterGraph.B_n(n)
    for n in range(4, max_rank + 1):
        catalog[f"D_{n}"] = MixedSignCoxeterGraph.D_n(n)
    for n in (6, 7, 8):
        if n <= max_rank:
            catalog[f"E_{n}"] = MixedSignCoxeterGraph.E_n(n)
    if max_rank >= 4:
        catalog["F_4"] = MixedSignCoxeterGraph.F_4()
        catalog["H_4"] = MixedSignCoxeterGraph.H_4()
    if max_rank >= 3:
        catalog["H_3"] = MixedSignCoxeterGraph.H_3()
    for m in range(3, 9):
        catalog[f"I_2[{m}]"] = MixedSignCoxeterGraph.I_2(m)
    return catalog


def table_a2(max_rank: int = 8) -> dict[str, MixedSignCoxeterGraph]:
    """Return the Appendix A Table A.2 catalog of finite all-negative Coxeter graphs.

    Obtained by negating every node sign in Table A.1 (Theorem 1.4, since every
    spherical Coxeter graph is a tree and hence bipartite).
    """
    return {f"{name}_neg": g.negate_signs() for name, g in table_a1(max_rank=max_rank).items()}
