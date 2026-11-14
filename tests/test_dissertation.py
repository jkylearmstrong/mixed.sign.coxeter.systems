"""Verification tests against theorems, examples, and tables in Armstrong (2012)."""

import math
import sympy as sp

from mixed_sign_coxeter import (
    MixedSignCoxeterGraph,
    ReflectionSystem,
    element_order,
    enumerate_group,
    evaluate_word,
    find_two_deletions,
    generate_roots,
)


def test_reflection_properties_and_howlett():
    """Verify Prop. 2.17, 2.22, Theorem 1.1, and Lemma 2.63 on a general graph."""
    g = MixedSignCoxeterGraph(["+", "-", "+", "+"], [(0, 1, 3), (1, 2, 4), (2, 3, 6)])
    gens = g.generators()
    n = g.n
    I = sp.eye(n)

    for i, s in enumerate(gens):
        # Involution
        assert sp.simplify(s * s - I) == sp.zeros(n, n)
        # Preserves B (Prop. 2.17)
        assert g.preserves_form(s)

    # Non-adjacent generators commute (Prop. 2.22 / 2.28)
    assert sp.simplify(gens[0] * gens[2] - gens[2] * gens[0]) == sp.zeros(n, n)
    assert sp.simplify(gens[0] * gens[3] - gens[3] * gens[0]) == sp.zeros(n, n)
    assert sp.simplify(gens[1] * gens[3] - gens[3] * gens[1]) == sp.zeros(n, n)

    # Theorem 1.1: s_0 s_1 ... s_{n-1} == -U^{-1} U^T
    prod = evaluate_word(g, list(range(n)))
    w_howlett = g.principal_element()
    assert sp.simplify(prod - w_howlett) == sp.zeros(n, n)

    # Lemma 2.63: principal polynomial matches charpoly of prod
    x = sp.Symbol("x")
    chi_howlett = g.principal_polynomial(var=x)
    chi_direct = sp.Poly(sp.expand((x * I - prod).det()), x)
    assert chi_howlett == chi_direct


def test_bipartite_conjugation_theorem_1_4():
    """Verify Theorem 1.4 / Corollary 1.5 for bipartite graphs."""
    g = MixedSignCoxeterGraph.A_n(["+", "-", "+", "+"])
    g_neg = g.negate_signs()
    assert g.is_bipartite()
    P = g.bipartite_conjugator()

    # P in O: P^T = P = P^{-1}
    assert P * P == sp.eye(g.n)
    assert P.T == P

    # P^T B(Gamma) P == -B(Gamma_-)
    assert sp.simplify(P.T * g.B * P + g_neg.B) == sp.zeros(g.n, g.n)

    # Principal polynomials are equal
    x = sp.Symbol("x")
    assert g.principal_polynomial(var=x) == g_neg.principal_polynomial(var=x)


def test_rank2_fibonacci_example_3_16():
    """Verify Example 3.16: A_2(+, -)[3] has Fibonacci matrix powers."""
    g = MixedSignCoxeterGraph.I_2(3, signs=("+", "-"))
    assert g.signature().as_tuple() == (1, 1, 0)
    assert g.classify() == "hyperbolic"

    s1, s2 = g.generators()
    assert s1 == sp.Matrix([[-1, 1], [0, 1]])
    assert s2 == sp.Matrix([[1, 0], [-1, -1]])

    for k in range(1, 6):
        mat = sp.simplify((s1 * s2) ** k)
        expected = ((-1) ** k) * sp.Matrix(
            [[sp.fibonacci(2 * k + 1), sp.fibonacci(2 * k)],
             [sp.fibonacci(2 * k), sp.fibonacci(2 * k - 1)]]
        )
        assert mat == expected

    roots, pos_roots = generate_roots(g, max_word_length=4)
    assert len(roots) > len(pos_roots)


def test_a_tilde_minus_2_deletion_failure_lemma_3_21():
    """Verify Lemma 3.21: W(~A_{-2}) has order 24 and fails Deletion Property."""
    g = MixedSignCoxeterGraph.A_tilde(2, negative=True)
    assert not g.is_bipartite()
    assert g.signature().as_tuple() == (0, 3, 0)
    assert g.classify() == "spherical"

    # (s1 s2 s3)^4 = 1
    w = evaluate_word(g, [0, 1, 2])
    assert element_order(w) == 4

    # |W(~A_{-2})| == 24 (isomorphic to S_4)
    elements, complete = enumerate_group(g, max_elements=100)
    assert complete is True
    assert len(elements) == 24

    # Equation (3.21.3): (s1 s2 s3)^2 s1 == (s3 s2 s1) s3 s2
    lhs_word = [0, 1, 2, 0, 1, 2, 0]  # length 7
    rhs_word = [2, 1, 0, 2, 1]        # length 5
    lhs_mat = evaluate_word(g, lhs_word)
    rhs_mat = evaluate_word(g, rhs_word)
    assert lhs_mat == rhs_mat

    # Shortest word failing the Deletion Property in W(~A_{-2}): s1 s2 s1 s3 s1 (length 5, l(w) = 3)
    bad_word = [0, 1, 0, 2, 0]
    bad_mat = evaluate_word(g, bad_word)
    # Verify reduced length <= 3 (e.g. s2 s3 s2 or similar; actually check no 2-deletion works)
    assert find_two_deletions(g, bad_word, bad_mat) == []


def test_odd_cycles_theorem_1_6():
    """Verify Theorem 1.6: ~A_{-n} is negative definite, ~A_n is positive semi-definite."""
    for n in (2, 4, 6):
        g_neg = MixedSignCoxeterGraph.A_tilde(n, negative=True)
        g_pos = MixedSignCoxeterGraph.A_tilde(n, negative=False)
        assert not g_neg.is_bipartite()
        assert g_neg.signature().as_tuple() == (0, n + 1, 0)
        assert g_pos.signature().as_tuple() == (n, 0, 1)


def test_example_3_29():
    """Verify Example 3.29: A_3(+, +, -) is hyperbolic yet has spectral radius 1."""
    g = MixedSignCoxeterGraph.A_n(["+", "+", "-"])
    assert g.signature().as_tuple() == (2, 1, 0)
    assert g.classify() == "hyperbolic"
    x = sp.Symbol("x")
    assert g.factor_principal_polynomial() == (x + 1) ** 3
    assert math.isclose(g.spectral_radius(), 1.0, rel_tol=1e-9)


def test_table_b1():
    """Verify all rows of Table B.1 (A_n for n = 2, 3, 4)."""
    x = sp.Symbol("x")
    # (signs, expected_sig, expected_poly_expr, expected_lambda, expected_N)
    rows = [
        (["+", "+"], (2, 0, 0), x**2 + x + 1, 1.0, 0),
        (["+", "-"], (1, 1, 0), x**2 + 3 * x + 1, 2.6180339887, 1),
        (["+", "+", "+"], (3, 0, 0), (x + 1) * (x**2 + 1), 1.0, 0),
        (["-", "+", "+"], (2, 1, 0), (x + 1) ** 3, 1.0, 0),
        (["+", "-", "+"], (2, 1, 0), (x + 1) * (x**2 + 4 * x + 1), 3.7320508, 1),
        (["+", "+", "+", "+"], (4, 0, 0), x**4 + x**3 + x**2 + x + 1, 1.0, 0),
        (["-", "+", "+", "+"], (3, 1, 0), x**4 + 3 * x**3 + 3 * x**2 + 3 * x + 1, 2.15372, 1),
        (["+", "-", "+", "+"], (3, 1, 0), x**4 + 5 * x**3 + 7 * x**2 + 5 * x + 1, 3.31651, 1),
        (["-", "-", "+", "+"], (2, 2, 0), x**4 + 3 * x**3 + 5 * x**2 + 3 * x + 1, 1.72208, 2),
        (["-", "+", "-", "+"], (2, 2, 0), x**4 + 7 * x**3 + 13 * x**2 + 7 * x + 1, 4.39025, 2),
        (["-", "+", "+", "-"], (2, 2, 0), x**4 + 5 * x**3 + 9 * x**2 + 5 * x + 1, 2.36920, 2),
    ]
    for signs, sig, poly_expr, lam, n_out in rows:
        g = MixedSignCoxeterGraph.A_n(signs)
        assert g.signature().as_tuple() == sig
        assert sp.expand(g.principal_polynomial(var=x).as_expr() - poly_expr) == 0
        assert math.isclose(g.spectral_radius(), lam, abs_tol=1e-4)
        assert g.roots_outside_unit_disk() == n_out


def test_table_b2():
    """Verify all rows of Table B.2 (A_5)."""
    x = sp.Symbol("x")
    rows = [
        (["+", "+", "+", "+", "+"], (5, 0, 0), (x + 1) * (x**2 + x + 1) * (x**2 - x + 1), 1.0, 0),
        (["-", "+", "+", "+", "+"], (4, 1, 0), (x + 1) * (x**4 + 2 * x**3 + x**2 + 2 * x + 1), 1.88320, 1),
        (["+", "-", "+", "+", "+"], (4, 1, 0), (x + 1) * (x**4 + 4 * x**3 + 3 * x**2 + 4 * x + 1), 3.44148, 1),
        (["+", "+", "-", "+", "+"], (4, 1, 0), (x + 1) * (x**2 + 3 * x + 1) * (x**2 + x + 1), 2.61803, 1),
        (["-", "-", "+", "+", "+"], (3, 2, 0), (x + 1) * (x**2 + x + 1) ** 2, 1.0, 0),
        (["-", "+", "-", "+", "+"], (3, 2, 0), (x + 1) * (x**4 + 6 * x**3 + 9 * x**2 + 6 * x + 1), 4.17467, 1),
        (["-", "+", "+", "-", "+"], (3, 2, 0), (x + 1) * (x**2 + 3 * x + 1) ** 2, 2.61803, 2),
        (["-", "+", "+", "+", "-"], (3, 2, 0), (x + 1) * (x**2 + 3 * x + 1) * (x**2 + x + 1), 2.61803, 1),
        (["+", "-", "-", "+", "+"], (3, 2, 0), (x + 1) * (x**4 + 4 * x**3 + 7 * x**2 + 4 * x + 1), 2.08102, 2),
        (["+", "-", "+", "-", "+"], (3, 2, 0), (x + 1) * (x**2 + 5 * x + 1) * (x**2 + 3 * x + 1), 4.79129, 2),
        (["+", "-", "+", "+", "-"], (3, 2, 0), (x + 1) * (x**2 + 3 * x + 1) ** 2, 2.61803, 2),
        (["+", "+", "-", "-", "+"], (3, 2, 0), (x + 1) * (x**4 + 4 * x**3 + 7 * x**2 + 4 * x + 1), 2.08102, 2),
        (["+", "+", "-", "+", "-"], (3, 2, 0), (x + 1) * (x**4 + 6 * x**3 + 9 * x**2 + 6 * x + 1), 4.17467, 1),
    ]
    for signs, sig, poly_expr, lam, n_out in rows:
        g = MixedSignCoxeterGraph.A_n(signs)
        assert g.signature().as_tuple() == sig
        assert sp.expand(g.principal_polynomial(var=x).as_expr() - poly_expr) == 0
        assert math.isclose(g.spectral_radius(), lam, abs_tol=1e-4)
        assert g.roots_outside_unit_disk() == n_out


def test_example_3_33_bipartite_not_minimal():
    """Verify Example 3.33 / Table 3.1 / Theorem 1.7."""
    g = MixedSignCoxeterGraph.example_3_33()
    assert g.is_bipartite()

    # 1-based indices in Table 3.1 -> 0-based here
    orders_and_expected = [
        ([0, 1, 2, 3, 4, 5], 3.05128),  # s1 s2 s3 s4 s5 s6
        ([1, 0, 2, 3, 4, 5], 4.09781),  # s2 s1 s3 s4 s5 s6
        ([0, 3, 5, 1, 2, 4], 5.55193),  # bipartite: s1 s4 s6 s2 s3 s5
        ([4, 1, 0, 2, 3, 5], 7.14809),  # (s5 s2 s1 s3)(s4 s6)
    ]
    for order, expected_lam in orders_and_expected:
        assert math.isclose(g.spectral_radius(order), expected_lam, abs_tol=1e-4)

    # Confirm bipartite principal element has spectral radius 5.55193 > 3.05128
    bp_order = g.bipartite_principal_order()
    assert math.isclose(g.spectral_radius(bp_order), 5.55193, abs_tol=1e-4)
    assert g.spectral_radius([0, 1, 2, 3, 4, 5]) < g.spectral_radius(bp_order)


def test_catalog_mahler_signature_and_an_table():
    from mixed_sign_coxeter import (
        A_n_sign_table,
        classify_signature,
        finite_even_odd_cycle_determinants,
        mahler_measure,
    )

    assert classify_signature(MixedSignCoxeterGraph.A_n(["+", "+"])) == "positive_definite"
    assert classify_signature(MixedSignCoxeterGraph.A_n(["+", "-"])) == "hyperbolic"
    assert classify_signature(MixedSignCoxeterGraph.A_tilde(2, negative=False)) == "positive_semidefinite_degenerate"
    assert classify_signature(MixedSignCoxeterGraph.A_tilde(2, negative=True)) == "negative_definite"

    # Example 3.29: A3(+, +, -) has (x+1)^3 -> Mahler measure 1.0
    g329 = MixedSignCoxeterGraph.A_n(["+", "+", "-"])
    assert math.isclose(mahler_measure(g329.principal_polynomial()), 1.0, abs_tol=1e-6)

    # Appendix B table for n=3: 2^3 / 2 = 4 entries up to sign negation
    table3 = A_n_sign_table(3, unique_up_to_negation=True)
    assert len(table3) == 4

    # Remark 3.26: det(-B(~A_{-n})) = 4 for n = 2, 4, 6
    assert finite_even_odd_cycle_determinants((2, 4, 6)) == {2: 4, 4: 4, 6: 4}


def test_appendix_a_tables_and_remark_3_26():
    from mixed_sign_coxeter import classify_signature, table_a1, table_a2

    a1 = table_a1(max_rank=6)
    a2 = table_a2(max_rank=6)
    assert set(a2.keys()) == {f"{k}_neg" for k in a1.keys()}
    for name in ("A_3", "B_3", "D_4", "E_6", "F_4", "H_3", "I_2[5]"):
        assert classify_signature(a1[name]) == "positive_definite"
        assert classify_signature(a2[f"{name}_neg"]) == "negative_definite"

    # Remark 3.26: |W(~A_{-4})| = 1920 = |W(D_5)|
    elems_a, ok_a = enumerate_group(MixedSignCoxeterGraph.A_tilde(4, negative=True), max_elements=2500)
    elems_d, ok_d = enumerate_group(MixedSignCoxeterGraph.D_n(5), max_elements=2500)
    assert ok_a and len(elems_a) == 1920
    assert ok_d and len(elems_d) == 1920


