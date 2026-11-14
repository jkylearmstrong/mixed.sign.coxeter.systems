"""Manim presentation scenes for *Mixed-Sign Coxeter Systems*.

Render any scene after installing the optional Manim extra:
    pip install -e ".[manim]"
    manim -pql slides/dissertation_deck.py TitleOverviewScene
    manim -pql slides/dissertation_deck.py HowlettFormulaScene
    manim -pql slides/dissertation_deck.py BipartiteConjugacyScene
    manim -pql slides/dissertation_deck.py TildeAMinusTwoDeletionScene
    manim -pql slides/dissertation_deck.py OddCycleSignatureScene
    manim -pql slides/dissertation_deck.py SpectralRadiusSeparationScene
"""

from __future__ import annotations

import numpy as np
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
    FadeOut,
    Line,
    MathTex,
    Scene,
    Text,
    VGroup,
    Write,
)

from mixed_sign_coxeter import (
    A_n_sign_table,
    ReflectionSystem,
    SignedGraph,
    a_tilde_minus_2,
    cycle_graph,
    mahler_measure,
)


def _graph_mobject(
    graph: SignedGraph,
    positions: list[tuple[float, float, float]],
    radius: float = 0.24,
) -> VGroup:
    """Build a Manim VGroup for a SignedGraph (+ nodes blue, - nodes red)."""
    nodes = VGroup()
    edges = VGroup()
    for i, pos in enumerate(positions):
        color = BLUE if graph.signs[i] > 0 else RED
        dot = Circle(radius=radius, color=color, fill_opacity=0.85).move_to(pos)
        label = Text(f"{i}: {'+' if graph.signs[i] > 0 else '-'}", font_size=18, color=WHITE).move_to(pos)
        nodes.add(VGroup(dot, label))
    for i in range(graph.n):
        for j in range(i + 1, graph.n):
            weight = graph.edges.get((i, j), graph.edges.get((j, i), 0.0))
            if weight != 0.0:
                edges.add(Line(positions[i], positions[j], color=GREY_B, stroke_width=2.5))
    return VGroup(edges, nodes)


class TitleOverviewScene(Scene):
    """Opening slide: Mixed-Sign Coxeter Systems & Lean 4 + Python verification."""

    def construct(self) -> None:
        title = Text("Mixed-Sign Coxeter Systems", font_size=44, color=BLUE)
        subtitle = Text(
            "Dissertation Results, Python Library & Lean 4 Formalization",
            font_size=24,
            color=GREY_B,
        ).next_to(title, DOWN, buff=0.35)
        author = Text("J Kyle Armstrong, PhD", font_size=22, color=WHITE).next_to(subtitle, DOWN, buff=0.5)

        pillars = VGroup(
            Text("1. Theorem 1.1: Howlett's Formula  w = -U^{-1} U^T", font_size=22, color=YELLOW),
            Text("2. Theorem 1.2 & Cor 1.3: Deletion Failure & Non-Classicality", font_size=22, color=RED),
            Text("3. Theorem 1.4: Bipartite Sign-Flip Conjugacy", font_size=22, color=GREEN),
            Text("4. Theorem 1.6 & 1.7: Odd-Cycle Signatures & Spectral Separation", font_size=22, color=ORANGE),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.25).next_to(author, DOWN, buff=0.6)

        self.play(Write(title), FadeIn(subtitle, shift=UP * 0.2))
        self.play(FadeIn(author))
        self.play(FadeIn(pillars, lag_ratio=0.15))
        self.wait(2)


class HowlettFormulaScene(Scene):
    """Theorem 1.1: Principal Coxeter element via Howlett's upper-triangular U."""

    def construct(self) -> None:
        header = Text("Theorem 1.1: Howlett's Formula", font_size=36, color=BLUE).to_edge(UP)
        formula = MathTex(
            r"U w = -U^T \quad \Longrightarrow \quad w = -U^{-1} U^T",
            font_size=38,
            color=YELLOW,
        ).next_to(header, DOWN, buff=0.5)

        rs = ReflectionSystem(a_tilde_minus_2())
        w_exact = rs.principal_element()
        char_poly = rs.principal_char_poly()
        m_val = mahler_measure(char_poly)

        note = Text(
            f"Rank-3 example A~_-2: det(B) = {float(rs.bilinear_form().det()):.3f}, "
            f"Mahler measure M(P_w) = {m_val:.4f}",
            font_size=22,
            color=WHITE,
        ).next_to(formula, DOWN, buff=0.5)
        eigen_note = Text(
            "All reflections s_i satisfy s_i^2 = I and B(e_i, e_i) in {+2, -2}.",
            font_size=22,
            color=GREY_B,
        ).next_to(note, DOWN, buff=0.35)

        self.play(Write(header))
        self.play(Write(formula))
        self.play(FadeIn(note), FadeIn(eigen_note))
        self.wait(2)


class BipartiteConjugacyScene(Scene):
    """Theorem 1.4: All sign assignments on a bipartite graph are O-conjugate."""

    def construct(self) -> None:
        header = Text("Theorem 1.4: Bipartite Sign-Flip Conjugacy", font_size=34, color=GREEN).to_edge(UP)
        positions = [(-3.0, 0.5, 0.0), (-1.5, 0.5, 0.0), (-3.0, -1.0, 0.0), (-1.5, -1.0, 0.0)]
        pos_right = [(1.5, 0.5, 0.0), (3.0, 0.5, 0.0), (1.5, -1.0, 0.0), (3.0, -1.0, 0.0)]

        g_plus = cycle_graph(4, signs=[1, 1, 1, 1])
        g_mixed = cycle_graph(4, signs=[1, -1, 1, -1])

        m_left = _graph_mobject(g_plus, positions)
        m_right = _graph_mobject(g_mixed, pos_right)
        arrow = MathTex(r"\sim_O", font_size=42, color=YELLOW).move_to((0.0, -0.25, 0.0))

        caption = Text(
            "Negating one part of a bipartite graph conjugates every reflection sign.",
            font_size=22,
            color=WHITE,
        ).to_edge(DOWN, buff=0.6)

        self.play(Write(header))
        self.play(Create(m_left), Create(m_right), Write(arrow))
        self.play(FadeIn(caption))
        self.wait(2)


class TildeAMinusTwoDeletionScene(Scene):
    """Lemma 3.21 & Theorem 1.2 / Corollary 1.3: Deletion property counterexample."""

    def construct(self) -> None:
        header = Text("Lemma 3.21 & Theorem 1.2: Deletion Property Failure", font_size=32, color=RED).to_edge(UP)
        g = a_tilde_minus_2()
        positions = [(0.0, 1.0, 0.0), (-1.3, -0.8, 0.0), (1.3, -0.8, 0.0)]
        tri = _graph_mobject(g, positions).shift(LEFT * 3.0)

        relation = MathTex(
            r"s_0 s_1 s_0 s_2 s_0 = s_2 s_0 s_1",
            font_size=34,
            color=YELLOW,
        ).move_to(RIGHT * 2.0 + UP * 0.6)
        failure = Text(
            "Deleting any two letters from [0, 1, 0, 2, 0]\nnever equals [0, 1, 0, 2, 0]!",
            font_size=22,
            color=WHITE,
        ).next_to(relation, DOWN, buff=0.4)
        cor = Text(
            "Corollary 1.3: Adjoining nodes yields an infinite family\nnot O-conjugate to any classical Coxeter system.",
            font_size=20,
            color=GREY_B,
        ).to_edge(DOWN, buff=0.5)

        self.play(Write(header))
        self.play(Create(tri))
        self.play(Write(relation), FadeIn(failure))
        self.play(FadeIn(cor))
        self.wait(2)


class OddCycleSignatureScene(Scene):
    """Theorem 1.6: All-positive vs all-negative odd cycles have distinct signatures."""

    def construct(self) -> None:
        header = Text("Theorem 1.6: Odd-Cycle Signature Obstruction", font_size=34, color=ORANGE).to_edge(UP)

        g_pos = ReflectionSystem(cycle_graph(3, signs=[1, 1, 1]))
        g_neg = ReflectionSystem(cycle_graph(3, signs=[-1, -1, -1]))

        sig_pos = g_pos.signature()
        sig_neg = g_neg.signature()

        left_txt = Text(
            f"All-Positive C_3\nsignature = ({sig_pos.positive}, {sig_pos.negative}, {sig_pos.zero})\n{sig_pos.classify()}",
            font_size=24,
            color=BLUE,
        ).move_to(LEFT * 3.2)
        right_txt = Text(
            f"All-Negative C_3\nsignature = ({sig_neg.positive}, {sig_neg.negative}, {sig_neg.zero})\n{sig_neg.classify()}",
            font_size=24,
            color=RED,
        ).move_to(RIGHT * 3.2)
        conclusion = Text(
            "O-conjugate systems preserve bilinear-form signature -> non-conjugate!",
            font_size=22,
            color=YELLOW,
        ).to_edge(DOWN, buff=0.7)

        self.play(Write(header))
        self.play(FadeIn(left_txt), FadeIn(right_txt))
        self.play(Write(conclusion))
        self.wait(2)


class SpectralRadiusSeparationScene(Scene):
    """Theorem 1.7 / 3.34 & Appendix B: Spectral radius separation on A_n."""

    def construct(self) -> None:
        header = Text("Theorem 1.7 & Appendix B: Spectral Radius Separation", font_size=32, color=YELLOW).to_edge(UP)
        entries = A_n_sign_table(4)
        rows = VGroup()
        for entry in entries[:6]:
            sign_str = "".join("+" if s > 0 else "-" for s in entry.signs)
            rows.add(
                Text(
                    f"signs={sign_str}  rho={entry.spectral_radius:.3f}  M={entry.mahler_measure:.3f}  ({entry.signature_class})",
                    font_size=20,
                    color=WHITE,
                )
            )
        rows.arrange(DOWN, aligned_edge=LEFT, buff=0.22).next_to(header, DOWN, buff=0.5)
        footer = Text(
            "Bipartite Coxeter elements strictly exceed the classical linear-graph spectral radius.",
            font_size=21,
            color=GREEN,
        ).to_edge(DOWN, buff=0.6)

        self.play(Write(header))
        self.play(FadeIn(rows, lag_ratio=0.1))
        self.play(FadeIn(footer))
        self.wait(2)
