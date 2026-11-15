"""Computational verifications beyond the thesis text (see docs/verifications.md)."""

from collections import Counter

import pytest

from mixed_sign_coxeter import MixedSignCoxeterGraph
from mixed_sign_coxeter.finite_search import (
    bounded_group_order,
    gram_matrix,
    is_definite,
    search_finite_graphs,
    simply_laced_negative_finite,
)
from mixed_sign_coxeter.isomorphisms import (
    a_tilde_minus_is_finite,
    appendix_d_matches_package,
    appendix_d_presentation_is_faithful,
    appendix_d_relators_hold,
    appendix_d_subgroup_index,
    verify_a_tilde_minus_isomorphism,
)
from mixed_sign_coxeter.principal_search import (
    alternating_square,
    cycle_radius_by_circulation,
    orientation_radii,
    search_question_3_35,
)


# ---------------------------------------------------------------------------
# Theorem 1.6 remark: W(~A_{-n}) = W(D_{n+1})
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("n", [2, 4, 6, 8, 10])
def test_a_tilde_minus_is_isomorphic_to_D(n):
    cert = verify_a_tilde_minus_isomorphism(n)
    assert cert.gram_matches
    assert abs(cert.det_T) == 2
    assert cert.conjugates_generators
    assert cert.root_orbit_is_D
    assert cert.contains_D_simple_reflections
    assert cert.is_isomorphism


def test_a_tilde_minus_finiteness_parity():
    assert [n for n in range(2, 12) if a_tilde_minus_is_finite(n)] == [2, 4, 6, 8, 10]
    # Odd n: even cycle, bipartite, so conjugate to the affine (infinite) ~A_n.
    g = MixedSignCoxeterGraph.A_tilde(3, negative=True)
    assert g.is_bipartite()
    assert bounded_group_order(gram_matrix(g.signs, {e: 3 for e in g.edges}), 14400) is None


# ---------------------------------------------------------------------------
# Appendix D, in Python
# ---------------------------------------------------------------------------


def test_appendix_d_in_python():
    assert appendix_d_matches_package()
    assert appendix_d_relators_hold()
    assert appendix_d_subgroup_index() == 16
    assert appendix_d_presentation_is_faithful()


# ---------------------------------------------------------------------------
# Remark A.3: finite mixed-sign groups of rank <= 4
# ---------------------------------------------------------------------------


def test_connected_finite_implies_definite_rank_3():
    # Every connected rank-3 graph (weights 2..6), indefinite ones included.
    res = search_finite_graphs(3, check_indefinite=True)
    assert res.indefinite_but_finite == 0
    assert all(f.sign_class != "mixed" for f in res.finite)


def test_mixed_rank_2_is_infinite():
    for m in (3, 4, 5, 6):
        B = gram_matrix((1, -1), {(0, 1): m})
        assert not is_definite(B)
        assert bounded_group_order(B, 10_000) is None


def test_rank_3_finite_classification():
    res = search_finite_graphs(3)
    c = Counter((f.catalog_source, f.coxeter_type) for f in res.finite)
    assert c == Counter(
        {
            ("Table A.1", "A3"): 1, ("Table A.1", "B3"): 1, ("Table A.1", "H3"): 1,
            ("Table A.2", "A3"): 1, ("Table A.2", "B3"): 1, ("Table A.2", "H3"): 1,
            ("Figure A.1 (~A_{-2})", "A3"): 1,
            ("new", "B3"): 1, ("new", "H3"): 3,
        }
    )
    # The new ones are all-negative triangles.
    new = {f.weights for f in res.finite if f.catalog_source == "new"}
    assert new == {
        (((0, 1), 3), ((0, 2), 4), ((1, 2), 4)),
        (((0, 1), 3), ((0, 2), 3), ((1, 2), 5)),
        (((0, 1), 3), ((0, 2), 5), ((1, 2), 5)),
        (((0, 1), 5), ((0, 2), 5), ((1, 2), 5)),
    }


def test_rank_4_finite_classification():
    res = search_finite_graphs(4)
    assert all(f.coxeter_type != "?" for f in res.finite)
    assert all(f.sign_class != "mixed" for f in res.finite)
    c = Counter((f.catalog_source, f.coxeter_type) for f in res.finite)
    for t in ("A4", "B4", "D4", "F4", "H4"):
        assert c[("Table A.1", t)] == 1
        assert c[("Table A.2", t)] == 1
    new = Counter(f.coxeter_type for f in res.finite if f.catalog_source == "new")
    assert new == Counter({"A4": 2, "D4": 1, "B4": 3, "F4": 3, "H4": 15})
    # No new graph uses weight 6, and every new graph is non-bipartite.
    assert all(m != 6 for f in res.finite for _, m in f.weights)
    assert all(not f.bipartite for f in res.finite if f.catalog_source == "new")


def test_K4_negative_is_A4():
    # Complete graph on four negative nodes: -B = I + J, det 5, Weyl group of A4.
    edges = {(i, j): 3 for i in range(4) for j in range(i + 1, 4)}
    B = gram_matrix((-1, -1, -1, -1), edges)
    assert bounded_group_order(B, 14400) == (120, 10)


def test_rank_5_simply_laced_negative():
    found = simply_laced_negative_finite(5)
    c = Counter((t, b) for _, t, b in found)
    assert c == Counter({("A5", True): 1, ("D5", True): 1, ("A5", False): 5, ("D5", False): 7})
    # Figure A.1's ~A_{-4} (the 5-cycle) is among the D5 ones.
    assert any(t == "D5" and len(e) == 5 and not b for e, t, b in found)


# ---------------------------------------------------------------------------
# Question 3.35: which principal elements minimize spectral radius?
# ---------------------------------------------------------------------------


def test_alternating_square_smaller_than_example_3_33():
    signs, edges = alternating_square()
    radii = orientation_radii(signs, edges)
    vals = sorted({round(r, 5) for r, _ in radii.values()})
    assert vals == [3.54646, 5.82843]
    # Bipartite order N1 = {0, 2}, N2 = {1, 3} gives the maximum; the circuit the minimum.
    g = MixedSignCoxeterGraph(list(signs), [(a, b, 3) for a, b in edges])
    assert g.spectral_radius([0, 2, 1, 3]) == pytest.approx(3 + 2 * 2**0.5, abs=1e-6)
    assert g.spectral_radius([0, 1, 2, 3]) == pytest.approx(3.54646, abs=1e-5)


def test_search_counts_n4_n5():
    s4 = search_question_3_35(4).counts()
    assert s4["bipartite_not_min"] == 1 and s4["bipartite_is_max"] == 1
    s5 = search_question_3_35(5)
    c5 = s5.counts()
    assert c5["bipartite_not_min"] == 8 == c5["bipartite_is_max"]
    assert c5["mixed"] == 180 and c5["sign_sorted_attains_min"] == 153
    # McMullen's theorem: unmixed bipartite graphs never fail.
    assert not any(r.bipartite_fails and not r.mixed for r in s5.records)


def test_cycle_circulation_table():
    assert cycle_radius_by_circulation((1, -1, 1, -1)) == pytest.approx({0: 5.82843, 2: 3.54646}, abs=1e-5)
    assert cycle_radius_by_circulation((1, 1, 1, 1)) == pytest.approx({0: 1.0, 2: 1.0}, abs=1e-6)


@pytest.mark.parametrize("m", [1, 2, 3, 4, 5])
def test_odd_cycle_single_defect_spectral_radius(m):
    n = 2 * m + 1
    signs = [1] + [-1] * (n - 1)
    edges = [(i, (i + 1) % n, 3) for i in range(n)]
    g = MixedSignCoxeterGraph(signs, edges)
    assert g.spectral_radius(list(range(n))) == pytest.approx(1.0, abs=1e-6)


@pytest.mark.parametrize("m", [2, 3, 4, 5])
def test_even_cycle_single_defect_spectral_radius(m):
    n = 2 * m
    signs = [1] + [-1] * (n - 1)
    edges = [(i, (i + 1) % n, 3) for i in range(n)]
    g = MixedSignCoxeterGraph(signs, edges)
    assert g.spectral_radius(list(range(n))) > 1.0

