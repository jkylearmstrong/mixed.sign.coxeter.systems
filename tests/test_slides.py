"""Keep the Manim deck in step with the package and with the dissertation.

The content checks run everywhere. The scene checks run only when Manim is installed,
and the dry-run render only when LaTeX is available as well.
"""

import inspect
import math
import shutil
import sys
from pathlib import Path

import pytest
import sympy as sp

SLIDES = Path(__file__).resolve().parent.parent / "slides"
sys.path.insert(0, str(SLIDES))

import deck_content as dc  # noqa: E402

x = dc.X


def test_howlett_slide_matches_theorem_1_1():
    d = dc.howlett_data()
    assert d.w == d.product
    assert sp.expand(d.principal_polynomial - (x + 1) * (x**2 + 1)) == 0
    assert math.isclose(d.mahler, 1.0, abs_tol=1e-9)
    assert d.det_B == -4


def test_bipartite_slide_matches_theorem_1_4():
    d = dc.bipartite_data()
    assert d.conjugates
    assert sp.expand(d.polynomial - d.flipped_polynomial) == 0
    assert d.parts == ([0, 2], [1, 3])


def test_rank_two_slide_matches_example_3_16():
    assert dc.rank_two_signature() == (1, 1, 0)
    for r in dc.rank_two_fibonacci_rows(4):
        assert r.first_coordinate == (-1) ** r.k * sp.fibonacci(2 * r.k + 1)


def test_deletion_slide_matches_lemma_3_21():
    d = dc.deletion_data()
    assert d.word_equals_short_word
    assert d.successful_deletions == []
    assert d.group_order == 24


def test_deletion_slide_matches_theorem_1_2_family():
    # Gamma_n from the proof of Theorem 1.2: ~A_{-2} with a path of n - 3 nodes at r_3.
    assert dc.theorem_1_2_graph(5).edges == {(0, 1): 3, (1, 2): 3, (0, 2): 3, (2, 3): 3, (3, 4): 3}
    assert dc.theorem_1_2_family((3, 4, 5, 6)) == [(3, True, 0), (4, True, 0), (5, True, 0), (6, True, 0)]


def test_odd_cycle_slide_matches_theorem_1_6_and_remark_3_26():
    rows = dc.odd_cycle_rows((2, 4))
    assert [(r.positive_signature, r.negative_signature) for r in rows] == [
        ((2, 0, 1), (0, 3, 0)),
        ((4, 0, 1), (0, 5, 0)),
    ]
    assert [(r.negative_group_order, r.d_group_order) for r in rows] == [(24, 24), (1920, 1920)]


def test_hyperbolic_radius_one_slide_matches_example_3_29():
    d = dc.hyperbolic_radius_one_data()
    assert d.signature == (2, 1, 0)
    assert d.classification == "hyperbolic"
    assert d.polynomial == (x + 1) ** 3
    assert math.isclose(d.spectral_radius, 1.0, abs_tol=1e-9)
    small, big = dc.interlacing_failure()
    assert math.isclose(small, (3 + math.sqrt(5)) / 2, abs_tol=1e-6)
    assert small > big


def test_spectral_slide_matches_table_3_1():
    rows = dc.example_3_33_rows()
    expected = [3.05128, 4.09781, 5.55193, 7.14809]
    for r, lam in zip(rows, expected):
        assert math.isclose(r.spectral_radius, lam, abs_tol=1e-4)
    g = dc.example_3_33_graph()
    bipartite = next(r for r in rows if r.label == "bipartite")
    n1, n2 = g.bipartition()
    assert set(bipartite.order[: len(n1)]) in (set(n1), set(n2))
    assert min(r.spectral_radius for r in rows) < bipartite.spectral_radius


def test_appendix_b_slide_matches_table_b1_and_remark_3_30():
    rows = dc.appendix_b_rows(4, 6)
    assert len(rows) == 6
    assert rows[0].signs == "++++" and rows[0].signature == (4, 0, 0)
    lams = [lam for _, lam in dc.remark_3_30_lambdas()]
    # Dissertation: 2.618 > 1 < 2.153 > 1.883
    assert lams[0] > lams[1] < lams[2] > lams[3]
    assert math.isclose(lams[1], 1.0, abs_tol=1e-9)
    assert math.isclose(lams[3], 1.88320, abs_tol=1e-4)


def test_word_latex_uses_one_based_names():
    assert dc.word_latex((0, 1, 2)) == "s_{1} s_{2} s_{3}"


# ---------------------------------------------------------------------------
# Scene checks (need Manim)
# ---------------------------------------------------------------------------


@pytest.fixture(scope="module")
def deck():
    pytest.importorskip("manim")
    import dissertation_deck

    return dissertation_deck


def test_every_scene_is_in_presentation_order(deck):
    from manim import Scene

    defined = {
        obj
        for _, obj in inspect.getmembers(deck, inspect.isclass)
        if issubclass(obj, Scene) and obj is not Scene and obj.__module__ == deck.__name__
    }
    assert set(deck.SCENE_ORDER) == defined
    assert len(deck.SCENE_ORDER) == len(defined)


@pytest.mark.skipif(shutil.which("latex") is None, reason="MathTex needs LaTeX")
@pytest.mark.parametrize(
    "name",
    [
        "TitleOverviewScene",
        "HowlettFormulaScene",
        "BipartiteConjugacyScene",
        "RankTwoHyperbolicScene",
        "DeletionFailureScene",
        "OddCycleSignatureScene",
        "HyperbolicRadiusOneScene",
        "SpectralRadiusSeparationScene",
        "AppendixBScene",
        "FormalizationScene",
    ],
)
def test_scene_builds(deck, name, tmp_path):
    from manim import tempconfig

    with tempconfig({"dry_run": True, "media_dir": str(tmp_path), "quality": "low_quality"}):
        getattr(deck, name)().render()
