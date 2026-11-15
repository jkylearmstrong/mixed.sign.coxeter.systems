"""Manim presentation scenes for *Principal Elements of Mixed-Sign Coxeter Systems*.

Every number on a slide is computed live from ``mixed_sign_coxeter`` through
``slides/deck_content.py`` (checked by ``tests/test_slides.py``).

Render one scene after installing the optional Manim extra (``MathTex`` also needs LaTeX):
    pip install -e ".[manim]"
    manim -pql slides/dissertation_deck.py TitleOverviewScene

Render the whole deck in order:
    manim -ql slides/dissertation_deck.py -a

Scenes, in presentation order (``SCENE_ORDER``):
    TitleOverviewScene              Overview of the main results
    HowlettFormulaScene             Theorem 1.1 and Lemma 2.63 on ~A_{-2}
    BipartiteConjugacyScene         Theorem 1.4 and Corollary 1.5
    RankTwoHyperbolicScene          Example 3.16, Lemma 3.14 and Proposition 3.12
    DeletionFailureScene            Lemma 3.21, Theorem 1.2, Corollary 1.3, Remark 3.23
    OddCycleSignatureScene          Theorem 1.6 and Remark 3.26
    HyperbolicRadiusOneScene        Example 3.29 against Theorems 3.27 and 3.28
    SpectralRadiusSeparationScene   Example 3.33, Table 3.1, Theorem 1.7 / 3.34
    AppendixBScene                  Table B.1 and Remark 3.30
    FormalizationScene              What is checked in Lean 4 and Python
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import sympy as sp
from manim import (
    BLUE,
    DOWN,
    GREEN,
    GREY_B,
    LEFT,
    ORANGE,
    RED,
    RIGHT,
    UP,
    WHITE,
    YELLOW,
    Circle,
    Create,
    FadeIn,
    Line,
    MathTex,
    Scene,
    Text,
    VGroup,
    Write,
)

sys.path.insert(0, str(Path(__file__).resolve().parent))

import deck_content as dc  # noqa: E402
from mixed_sign_coxeter import MixedSignCoxeterGraph  # noqa: E402

Point = tuple[float, float, float]


def graph_mobject(graph: MixedSignCoxeterGraph, positions: list[Point], radius: float = 0.26) -> VGroup:
    """Draw a mixed-sign Coxeter graph: + nodes blue, - nodes red, weights m > 3 labelled."""
    if len(positions) != graph.n:
        raise ValueError(f"Need {graph.n} positions, got {len(positions)}.")
    edges = VGroup()
    for (i, j), m in sorted(graph.edges.items()):
        line = Line(positions[i], positions[j], color=GREY_B, stroke_width=3)
        edges.add(line)
        if m != 3:
            label = MathTex(r"\infty" if m == sp.oo else str(m), font_size=26, color=GREY_B)
            edges.add(label.move_to(line.get_center() + 0.25 * UP))
    nodes = VGroup()
    for i, pos in enumerate(positions):
        sign = graph.signs[i]
        dot = Circle(radius=radius, color=BLUE if sign > 0 else RED, fill_opacity=0.85).move_to(pos)
        label = MathTex(f"{i + 1}^{{{'+' if sign > 0 else '-'}}}", font_size=24, color=WHITE).move_to(pos)
        nodes.add(VGroup(dot, label))
    return VGroup(edges, nodes)


def circle_positions(n: int, radius: float, center: Point = (0.0, 0.0, 0.0), start: float = math.pi / 2) -> list[Point]:
    return [
        (center[0] + radius * math.cos(start + 2 * math.pi * k / n), center[1] + radius * math.sin(start + 2 * math.pi * k / n), 0.0)
        for k in range(n)
    ]


def line_positions(n: int, spacing: float, center: Point = (0.0, 0.0, 0.0)) -> list[Point]:
    left = center[0] - spacing * (n - 1) / 2
    return [(left + spacing * k, center[1], 0.0) for k in range(n)]


def header(text: str, color=BLUE) -> Text:
    return Text(text, font_size=32, color=color).to_edge(UP, buff=0.4)


def sig_tex(sig: tuple[int, int, int]) -> str:
    return f"({sig[0]}, {sig[1]}, {sig[2]})"


class TitleOverviewScene(Scene):
    """Opening slide: the dissertation and its main results."""

    def construct(self) -> None:
        title = Text("Principal Elements of Mixed-Sign Coxeter Systems", font_size=38, color=BLUE).to_edge(UP, buff=0.7)
        author = Text("J. Kyle Armstrong  ·  Florida State University, 2012", font_size=22, color=GREY_B).next_to(title, DOWN, buff=0.3)
        pillars = VGroup(
            Text("Theorem 1.1   Howlett's formula  w = -U⁻¹Uᵀ", font_size=22, color=YELLOW),
            Text("Theorem 1.2, Corollary 1.3   the Deletion Property fails", font_size=22, color=RED),
            Text("Theorem 1.4, Corollary 1.5   bipartite sign flips are conjugate", font_size=22, color=GREEN),
            Text("Theorem 1.6   odd cycles Ã₋ₙ and Ãₙ are not conjugate", font_size=22, color=ORANGE),
            Text("Theorem 1.7   the bipartite element need not minimize λ", font_size=22, color=BLUE),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.3).next_to(author, DOWN, buff=0.7)
        footer = Text("Checked in Python and formalized in Lean 4", font_size=20, color=GREY_B).to_edge(DOWN, buff=0.5)

        self.play(Write(title), FadeIn(author, shift=UP * 0.2))
        self.play(FadeIn(pillars, lag_ratio=0.2))
        self.play(FadeIn(footer))
        self.wait(2)


class HowlettFormulaScene(Scene):
    """Theorem 1.1 and Lemma 2.63, computed on ~A_{-2}."""

    def construct(self) -> None:
        d = dc.howlett_data()
        title = header("Theorem 1.1: Howlett's formula", YELLOW)
        formula = MathTex(r"s_1 s_2 \cdots s_n \;=\; -U^{-1} U^{T}", font_size=40, color=YELLOW).next_to(title, DOWN, buff=0.4)

        mats = VGroup(
            MathTex(r"B(\widetilde{A}_{-2}) = " + sp.latex(d.B), font_size=30),
            MathTex(r"U = " + sp.latex(d.U), font_size=30),
            MathTex(r"s_1 s_2 s_3 = " + sp.latex(d.product), font_size=30),
        ).arrange(RIGHT, buff=0.6).next_to(formula, DOWN, buff=0.5)

        check = "=" if d.product == d.w else r"\neq"
        result = MathTex(r"-U^{-1}U^{T} " + check + r" s_1 s_2 s_3", font_size=32, color=GREEN).next_to(mats, DOWN, buff=0.45)
        lemma = MathTex(
            r"\text{Lemma 2.63: } \chi(w, x) \propto \det(Ux + U^T) = " + sp.latex(d.principal_polynomial),
            font_size=30,
        ).next_to(result, DOWN, buff=0.35)
        mahler = Text(f"Mahler measure M(χ) = {d.mahler:.3f},   det B = {d.det_B}", font_size=22, color=GREY_B).next_to(lemma, DOWN, buff=0.35)

        self.play(Write(title))
        self.play(Write(formula))
        self.play(FadeIn(mats, lag_ratio=0.2))
        self.play(Write(result))
        self.play(FadeIn(lemma), FadeIn(mahler))
        self.wait(2)


class BipartiteConjugacyScene(Scene):
    """Theorem 1.4 / Corollary 1.5: flipping every sign of a bipartite graph is O-conjugate."""

    def construct(self) -> None:
        d = dc.bipartite_data()
        title = header("Theorem 1.4: bipartite sign flip", GREEN)
        left = graph_mobject(d.graph, line_positions(d.graph.n, 1.2, (-3.4, 0.8, 0.0)))
        right = graph_mobject(d.flipped, line_positions(d.flipped.n, 1.2, (3.4, 0.8, 0.0)))
        names = VGroup(
            MathTex(r"\Gamma = A_4(" + ",".join(dc.sign_string(d.graph.signs)) + ")", font_size=30).next_to(left, DOWN, buff=0.4),
            MathTex(r"\Gamma^- = A_4(" + ",".join(dc.sign_string(d.flipped.signs)) + ")", font_size=30).next_to(right, DOWN, buff=0.4),
        )
        arrow = MathTex(r"\sim_{\mathcal{O}}", font_size=44, color=YELLOW).move_to((0.0, 0.8, 0.0))

        n1, n2 = d.parts
        conj = MathTex(
            r"B(\Gamma^-) = -P\,B(\Gamma)\,P,\qquad P = \mathrm{diag}(\pm 1)\ \text{negating } N_2 = \{"
            + ",".join(str(i + 1) for i in n2)
            + r"\}",
            font_size=30,
            color=GREEN if d.conjugates else RED,
        ).shift(DOWN * 1.2)
        polys = MathTex(
            r"\chi_\Gamma(x) = " + sp.latex(d.polynomial) + r" = \chi_{\Gamma^-}(x)",
            font_size=30,
        ).next_to(conj, DOWN, buff=0.4)
        caption = Text("Corollary 1.5: same group, conjugate principal elements", font_size=22, color=GREY_B).to_edge(DOWN, buff=0.4)

        self.play(Write(title))
        self.play(Create(left), Create(right), Write(arrow))
        self.play(FadeIn(names))
        self.play(Write(conj))
        self.play(FadeIn(polys), FadeIn(caption))
        self.wait(2)


class RankTwoHyperbolicScene(Scene):
    """Example 3.16 / Lemma 3.14 / Proposition 3.12: A_2(+,-)[3] and Fibonacci powers."""

    def construct(self) -> None:
        rows = dc.rank_two_fibonacci_rows(4)
        sig = dc.rank_two_signature()
        title = header("Example 3.16: a rank-2 hyperbolic system", ORANGE)
        graph = graph_mobject(MixedSignCoxeterGraph.I_2(3, signs=("+", "-")), line_positions(2, 1.6, (-4.2, 1.2, 0.0)))
        sig_line = MathTex(r"\mathrm{sig}\,B = " + sig_tex(sig) + r"\ \text{(hyperbolic)}", font_size=28).next_to(graph, DOWN, buff=0.4)

        powers = VGroup(
            *[MathTex(f"(s_1 s_2)^{{{r.k}}} = " + sp.latex(r.power), font_size=28) for r in rows]
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.25).shift(RIGHT * 2.2 + UP * 0.1)
        fib = MathTex(
            r"(s_1 s_2)^k = (-1)^k \begin{pmatrix} F_{2k+1} & F_{2k} \\ F_{2k} & F_{2k-1} \end{pmatrix}",
            font_size=30,
            color=YELLOW,
        ).next_to(sig_line, DOWN, buff=0.5).align_to(sig_line, LEFT)
        signs = ", ".join(str(r.first_coordinate) for r in rows)
        note = Text(
            f"First coordinate of (s₁s₂)ᵏe₁: {signs}, ...\n"
            "so (s₁s₂)ᵏe₁ keeps leaving Φ⁺ as length grows (Prop. 3.12),\n"
            "and s₁s₂ has infinite order (Lemma 3.14).",
            font_size=20,
            color=GREY_B,
            line_spacing=1.2,
        ).to_edge(DOWN, buff=0.4)

        self.play(Write(title))
        self.play(Create(graph), FadeIn(sig_line))
        self.play(FadeIn(powers, lag_ratio=0.2))
        self.play(Write(fib))
        self.play(FadeIn(note))
        self.wait(2)


class DeletionFailureScene(Scene):
    """Lemma 3.21, Theorem 1.2, Corollary 1.3 and Remark 3.23 on ~A_{-2}."""

    def construct(self) -> None:
        d = dc.deletion_data()
        title = header("Lemma 3.21: the Deletion Property fails", RED)
        tri = graph_mobject(MixedSignCoxeterGraph.A_tilde(2, negative=True), circle_positions(3, 1.0, (-4.0, 0.9, 0.0)))
        tri_name = MathTex(r"\widetilde{A}_{-2}", font_size=34).next_to(tri, DOWN, buff=0.3)

        relation = MathTex(
            dc.word_latex(dc.DELETION_WORD) + (" = " if d.word_equals_short_word else r" \neq ") + dc.word_latex(dc.DELETION_SHORT_WORD),
            font_size=36,
            color=YELLOW,
        ).move_to(RIGHT * 2.0 + UP * 1.6)
        failure = Text(
            f"A length-5 word equal to a length-3 word,\nyet {len(d.successful_deletions)} of the 10 two-letter deletions give w.",
            font_size=22,
            line_spacing=1.2,
        ).next_to(relation, DOWN, buff=0.4)
        order = Text(f"|W(Ã₋₂)| = {d.group_order} = |S₄|   (Remark 3.23)", font_size=22, color=GREY_B).next_to(failure, DOWN, buff=0.4)
        family_rows = dc.theorem_1_2_family((3, 4, 5, 6))
        held = [n for n, same, deletions in family_rows if same and deletions == 0]
        small_tri = circle_positions(3, 0.55, (-5.2, -2.3, 0.0))
        r3 = small_tri[2]
        tail_positions = small_tri + [(r3[0] + 0.85 * k, r3[1], 0.0) for k in (1, 2, 3)]
        tail = graph_mobject(dc.theorem_1_2_graph(6), tail_positions, radius=0.2)
        family = Text(
            "Theorem 1.2: Γₙ, Ã₋₂ plus a tail of n − 3 nodes,\n"
            f"fails the same way (checked for n = {', '.join(map(str, held))}).\n"
            "Corollary 1.3: none is conjugate to a classical system.",
            font_size=19,
            line_spacing=1.2,
        ).next_to(tail, RIGHT, buff=0.5)
        self.play(Write(title))
        self.play(Create(tri), FadeIn(tri_name))
        self.play(Write(relation), FadeIn(failure))
        self.play(FadeIn(order))
        self.play(Create(tail), FadeIn(family))
        self.wait(2)


class OddCycleSignatureScene(Scene):
    """Theorem 1.6 and Remark 3.26: ~A_n is positive semidefinite, ~A_{-n} is negative definite."""

    def construct(self) -> None:
        rows = dc.odd_cycle_rows((2, 4))
        title = header("Theorem 1.6: odd cycles are not conjugate", ORANGE)
        pos = graph_mobject(MixedSignCoxeterGraph.A_tilde(2), circle_positions(3, 0.9, (-3.6, 1.2, 0.0)))
        neg = graph_mobject(MixedSignCoxeterGraph.A_tilde(2, negative=True), circle_positions(3, 0.9, (3.6, 1.2, 0.0)))
        labels = VGroup(
            MathTex(r"\widetilde{A}_2:\ \text{positive semidefinite}", font_size=28, color=BLUE).next_to(pos, DOWN, buff=0.3),
            MathTex(r"\widetilde{A}_{-2}:\ \text{negative definite}", font_size=28, color=RED).next_to(neg, DOWN, buff=0.3),
        )

        table = VGroup(
            MathTex(r"n", r"\quad \mathrm{sig}\,B(\widetilde{A}_n)", r"\quad \mathrm{sig}\,B(\widetilde{A}_{-n})", r"\quad |W(\widetilde{A}_{-n})|", r"\quad |W(D_{n+1})|", font_size=28),
            *[
                MathTex(
                    str(r.n),
                    r"\quad " + sig_tex(r.positive_signature),
                    r"\quad " + sig_tex(r.negative_signature),
                    r"\quad " + str(r.negative_group_order),
                    r"\quad " + str(r.d_group_order),
                    font_size=28,
                )
                for r in rows
            ],
        ).arrange(DOWN, buff=0.25).shift(DOWN * 1.2)
        note = Text(
            "Conjugation by O preserves the signature up to sign, so the two systems differ.",
            font_size=20,
            color=YELLOW,
        ).to_edge(DOWN, buff=0.4)

        self.play(Write(title))
        self.play(Create(pos), Create(neg))
        self.play(FadeIn(labels))
        self.play(FadeIn(table, lag_ratio=0.2))
        self.play(FadeIn(note))
        self.wait(2)


class HyperbolicRadiusOneScene(Scene):
    """Example 3.29: classical eigenvalue tests (Theorems 3.27, 3.28) do not extend."""

    def construct(self) -> None:
        d = dc.hyperbolic_radius_one_data()
        small, big = dc.interlacing_failure()
        title = header("Example 3.29: hyperbolic, yet λ = 1", ORANGE)
        graph = graph_mobject(MixedSignCoxeterGraph.A_n(["+", "+", "-"]), line_positions(3, 1.5, (0.0, 1.6, 0.0)))
        facts = VGroup(
            MathTex(r"\mathrm{sig}\,B(A_3(+,+,-)) = " + sig_tex(d.signature) + r"\ \Rightarrow\ \text{" + d.classification + "}", font_size=30),
            MathTex(r"\chi(w, x) = " + sp.latex(d.polynomial) + r",\qquad \lambda(w) = " + f"{d.spectral_radius:.3f}", font_size=30),
        ).arrange(DOWN, buff=0.3).next_to(graph, DOWN, buff=0.5)
        contrast = VGroup(
            Text("Theorem 3.27 (classical): all |eigenvalues| = 1 means spherical or affine.", font_size=21, color=GREY_B),
            Text("Here every eigenvalue is -1, but the system is hyperbolic.", font_size=21, color=YELLOW),
            Text(
                f"Theorem 3.28 (interlacing) also fails: Λ(A₂(+,-)) = {small:.3f} > Λ(A₃(+,+,-)) = {big:.3f}.",
                font_size=21,
                color=YELLOW,
            ),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.25).next_to(facts, DOWN, buff=0.5)

        self.play(Write(title))
        self.play(Create(graph))
        self.play(FadeIn(facts, lag_ratio=0.2))
        self.play(FadeIn(contrast, lag_ratio=0.3))
        self.wait(2)


class SpectralRadiusSeparationScene(Scene):
    """Example 3.33 / Table 3.1 / Theorem 1.7: the bipartite element does not minimize λ."""

    # Layout of Figure 3.15 (0-based nodes): top row 1, 2, 6; bottom row 3, 4, 5.
    POSITIONS: list[Point] = [
        (-5.2, 1.4, 0.0),
        (-3.8, 1.4, 0.0),
        (-5.2, 0.0, 0.0),
        (-3.8, 0.0, 0.0),
        (-2.4, -0.7, 0.0),
        (-2.4, 0.7, 0.0),
    ]

    def construct(self) -> None:
        rows = dc.example_3_33_rows()
        title = header("Theorem 1.7: the bipartite element is not minimal", YELLOW)
        graph = graph_mobject(dc.example_3_33_graph(), self.POSITIONS)

        table = VGroup(
            *[
                VGroup(
                    MathTex(dc.word_latex(r.order), font_size=28),
                    MathTex(f"{r.spectral_radius:.5f}", font_size=28),
                    Text(r.label, font_size=18, color=GREY_B),
                ).arrange(RIGHT, buff=0.4)
                for r in rows
            ]
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.3).shift(RIGHT * 2.0 + UP * 0.4)
        bipartite = next(r for r in rows if r.label == "bipartite")
        smallest = min(rows, key=lambda r: r.spectral_radius)
        for row, r in zip(table, rows):
            if r is bipartite:
                row.set_color(GREEN)
            if r is smallest:
                row[1].set_color(YELLOW)
        conclusion = Text(
            f"λ(bipartite) = {bipartite.spectral_radius:.3f} > λ({smallest.label}) = {smallest.spectral_radius:.3f}.\n"
            "In classical Coxeter groups the bipartite eigenvalue is a lower bound (McMullen).\n"
            "Question 3.35: which principal elements minimize λ?",
            font_size=20,
            line_spacing=1.2,
        ).to_edge(DOWN, buff=0.5)

        self.play(Write(title))
        self.play(Create(graph))
        self.play(FadeIn(table, lag_ratio=0.2))
        self.play(FadeIn(conclusion))
        self.wait(2)


class AppendixBScene(Scene):
    """Table B.1 (A_4 sign patterns) and Remark 3.30 (Λ is not monotone)."""

    def construct(self) -> None:
        entries = dc.appendix_b_rows(4, 6)
        lambdas = dc.remark_3_30_lambdas()
        title = header("Appendix B: A₄ sign patterns", BLUE)
        table = VGroup(
            *[
                MathTex(
                    r"A_4(" + ",".join(e.signs) + r")\quad",
                    r"\mathrm{sig} = " + sig_tex(e.signature) + r"\quad",
                    r"\lambda = " + f"{e.spectral_radius:.3f}" + r"\quad",
                    r"M = " + f"{e.mahler_measure:.3f}",
                    font_size=28,
                )
                for e in entries
            ]
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.22).next_to(title, DOWN, buff=0.4)
        chain_tex = r"\Lambda:\ " + f"{lambdas[0][1]:.3f}"
        for (_, prev), (_, cur) in zip(lambdas, lambdas[1:]):
            chain_tex += (r" > " if prev > cur else r" < ") + f"{cur:.3f}"
        chain = MathTex(chain_tex, font_size=30, color=YELLOW).next_to(table, DOWN, buff=0.45)
        chain_note = Text(
            "Remark 3.30: along A₂(+,-) ⊂ A₃(-,+,+) ⊂ A₄(-,+,+,+) ⊂ A₅(-,+,+,+,+),\n"
            "adding a positive node makes Λ go down, up, then down again.",
            font_size=20,
            color=GREY_B,
            line_spacing=1.2,
        ).next_to(chain, DOWN, buff=0.3)

        self.play(Write(title))
        self.play(FadeIn(table, lag_ratio=0.15))
        self.play(Write(chain))
        self.play(FadeIn(chain_note))
        self.wait(2)


class FormalizationScene(Scene):
    """Closing slide: where each result is checked."""

    def construct(self) -> None:
        title = header("How the results are checked", GREEN)
        lean = VGroup(
            Text("Lean 4 + Mathlib (16 modules, sorry-free)", font_size=26, color=BLUE),
            Text("Theorems 1.1, 1.2, 1.4, 1.6, 1.7, 2.58, 3.9, 3.27, 3.28, 3.34", font_size=20),
            Text("Corollaries 1.3, 1.5, 3.18; Props 2.41, 3.11; Remarks 3.23, 3.26, 3.30", font_size=20),
            Text("All numbered Ch. 1–3 results, decide, and IVT root bounds", font_size=20, color=GREY_B),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.2)
        python = VGroup(
            Text("Python (mixed_sign_coxeter)", font_size=26, color=ORANGE),
            Text("Tables 3.1, A.1, A.2, B.1, B.2 & Appendix D (16 relators)", font_size=20),
            Text("W(Ã₋ₙ) ≅ W(Dₙ₊₁) for all even n; Remark A.3 & Question 3.35 searches", font_size=20),
            Text("Every number in this deck is computed live", font_size=20, color=GREY_B),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.2)
        cols = VGroup(lean, python).arrange(DOWN, buff=0.6, aligned_edge=LEFT).next_to(title, DOWN, buff=0.6)
        footer = Text("github.com/jkylearmstrong/mixed.sign.coxeter.systems", font_size=20, color=GREY_B).to_edge(DOWN, buff=0.5)

        self.play(Write(title))
        self.play(FadeIn(lean, shift=RIGHT * 0.2), FadeIn(python, shift=LEFT * 0.2))
        self.play(FadeIn(footer))
        self.wait(2)


#: Presentation order; ``tests/test_slides.py`` checks every Scene here is listed.
SCENE_ORDER: tuple[type[Scene], ...] = (
    TitleOverviewScene,
    HowlettFormulaScene,
    BipartiteConjugacyScene,
    RankTwoHyperbolicScene,
    DeletionFailureScene,
    OddCycleSignatureScene,
    HyperbolicRadiusOneScene,
    SpectralRadiusSeparationScene,
    AppendixBScene,
    FormalizationScene,
)
