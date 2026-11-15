"""Interactive Mixed-Sign Coxeter System Explorer (Shiny for Python)."""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import Any
from urllib.parse import parse_qs, urlencode

import matplotlib.pyplot as plt
import networkx as nx
import numpy as np
import sympy as sp
import yaml
from shiny import App, reactive, render, ui

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT / "src") not in sys.path:
    sys.path.insert(0, str(ROOT / "src"))

from mixed_sign_coxeter import (  # noqa: E402
    MixedSignCoxeterGraph,
    mahler_measure,
)
from mixed_sign_coxeter.isomorphisms import (  # noqa: E402
    verify_a_tilde_minus_isomorphism,
)

THEOREMS_PATH = ROOT / "data" / "theorems.yml"
GARNET = "#782F40"
LEAN_BLUE = "#1E6BD6"


def load_theorems() -> list[dict[str, Any]]:
    if not THEOREMS_PATH.exists():
        return []
    data = yaml.safe_load(THEOREMS_PATH.read_text(encoding="utf-8")) or {}
    return list(data.get("theorems", []))


PRESETS: dict[str, tuple[str, MixedSignCoxeterGraph]] = {
    "example_3_33": (
        "Example 3.33 (6-vertex bipartite, Fig. 3.15)",
        MixedSignCoxeterGraph.example_3_33(),
    ),
    "a_tilde_minus_2": (
        "~A_{-2} (Negative 3-cycle, Lemma 3.21)",
        MixedSignCoxeterGraph.A_tilde(2, negative=True),
    ),
    "a_tilde_minus_4": (
        "~A_{-4} (Negative 5-cycle, Theorem 1.6)",
        MixedSignCoxeterGraph.A_tilde(4, negative=True),
    ),
    "a3_ppm": (
        "A_3(+, +, -) (Hyperbolic, Example 3.29)",
        MixedSignCoxeterGraph.A_n(["+", "+", "-"]),
    ),
    "a_n_alt_4": (
        "A_4(+, -, +, -) (Alternating path)",
        MixedSignCoxeterGraph.A_n(["+", "-", "+", "-"]),
    ),
    "d_4_mixed": (
        "D_4(+, +, +, -) (Mixed-sign D_4)",
        MixedSignCoxeterGraph.D_n(4, ["+", "+", "+", "-"]),
    ),
    "e_6_plus": (
        "E_6(+, +, +, +, +, +) (Classical E_6)",
        MixedSignCoxeterGraph.E_n(6),
    ),
}


def default_positions(n: int, edges: list[tuple[int, int, Any]]) -> dict[int, tuple[float, float]]:
    if n == 0:
        return {}
    G = nx.Graph()
    G.add_nodes_from(range(n))
    for u, v, _ in edges:
        G.add_edge(u, v)
    pos = nx.spring_layout(G, seed=42)
    return {int(k): (float(v[0]), float(v[1])) for k, v in pos.items()}


def parse_edges_param(raw: str, n: int) -> list[tuple[int, int, Any]]:
    edges: list[tuple[int, int, Any]] = []
    for item in raw.split(","):
        item = item.strip()
        if not item:
            continue
        if ":" in item:
            pair_s, w_s = item.split(":", 1)
            w: Any = sp.oo if w_s.strip().lower() in ("oo", "inf") else int(w_s.strip())
        else:
            pair_s, w = item, 3
        u_s, v_s = pair_s.split("-", 1)
        u, v = int(u_s), int(v_s)
        if 0 <= u < n and 0 <= v < n and u != v:
            edges.append((min(u, v), max(u, v), w))
    return edges


app_ui = ui.page_navbar(
    ui.nav_panel(
        "Explorer",
        ui.layout_sidebar(
            ui.sidebar(
                ui.input_select(
                    "preset",
                    "Preset Graph",
                    choices={k: v[0] for k, v in PRESETS.items()},
                    selected="example_3_33",
                ),
                ui.input_radio_buttons(
                    "edit_mode",
                    "Click Graph To:",
                    choices={
                        "sign": "Toggle Vertex Sign (+ / −)",
                        "edge": "Draw / Remove Edge",
                        "add_v": "Add Vertex (click canvas)",
                        "del_v": "Delete Vertex",
                    },
                    selected="sign",
                ),
                ui.input_select(
                    "edge_weight",
                    "New Edge Weight m(i, j)",
                    choices={"3": "3 (standard)", "4": "4", "5": "5", "6": "6", "oo": "∞"},
                    selected="3",
                ),
                ui.layout_columns(
                    ui.input_action_button("add_vertex_btn", "+ Add Vertex", class_="btn-sm btn-outline-primary"),
                    ui.input_action_button("negate_btn", "Flip All Signs", class_="btn-sm btn-outline-secondary"),
                    col_widths=(6, 6),
                ),
                ui.hr(),
                ui.input_radio_buttons(
                    "ordering_mode",
                    "Principal Ordering",
                    choices={"linear": "Linear (0..n-1)", "bipartite": "Bipartite", "custom": "Custom"},
                    selected="linear",
                ),
                ui.input_text("custom_order", "Custom Order", value="0, 1, 2, 3, 4, 5"),
                ui.hr(),
                ui.output_ui("share_ui"),
                width=310,
            ),
            ui.card(
                ui.card_header("Interactive Signed Coxeter Graph (click directly on vertices or canvas)"),
                ui.output_plot("graph_plot", click=True, height="430px"),
                ui.output_ui("mode_hint_ui"),
            ),
            ui.layout_columns(
                ui.card(
                    ui.card_header("Structure, Principal Ordering & Applicable Theorems"),
                    ui.output_ui("summary_ui"),
                    ui.hr(),
                    ui.output_ui("theorem_hints_ui"),
                ),
                ui.card(
                    ui.card_header("Eigenvalue Spectrum & Unit Circle"),
                    ui.output_plot("spectrum_plot", height="360px"),
                ),
                col_widths=(6, 6),
            ),
            ui.HTML("<details class='mt-3'><summary><strong>▶ Advanced Spectral Data &amp; Adjacency / Bilinear Matrices</strong></summary>"),
            ui.card(ui.output_code("matrices_out")),
            ui.HTML("</details>"),
        ),
    ),
    ui.nav_panel(
        "Export",
        ui.card(
            ui.card_header("Reproducible Python, JSON, CSV, GraphML & LaTeX/TikZ"),
            ui.output_code("export_out"),
        ),
    ),
    title="Mixed-Sign Coxeter Explorer",
)


def server(input, output, session):
    init_g = PRESETS["example_3_33"][1]
    init_edges = [(u, v, w) for (u, v), w in sorted(init_g.edges.items())]

    signs_rv = reactive.value(list(init_g.signs))
    edges_rv = reactive.value(init_edges)
    pos_rv = reactive.value(default_positions(init_g.n, init_edges))
    edge_start_rv = reactive.value(None)
    url_loaded_rv = reactive.value(False)

    @reactive.effect
    def _load_from_url_once():
        if url_loaded_rv():
            return
        url_loaded_rv.set(True)
        qs = parse_qs(session.clientdata.url_search().lstrip("?"))
        if "signs" in qs and qs["signs"]:
            s_raw = qs["signs"][0]
            s_list = [1 if ch == "+" else -1 for ch in s_raw if ch in ("+", "-")]
            if s_list:
                e_list = parse_edges_param(qs.get("edges", [""])[0], len(s_list))
                signs_rv.set(s_list)
                edges_rv.set(e_list)
                pos_rv.set(default_positions(len(s_list), e_list))
                edge_start_rv.set(None)

    @reactive.effect
    @reactive.event(input.preset)
    def _on_preset():
        key = input.preset()
        if key in PRESETS:
            g = PRESETS[key][1]
            e_list = [(u, v, w) for (u, v), w in sorted(g.edges.items())]
            signs_rv.set(list(g.signs))
            edges_rv.set(e_list)
            pos_rv.set(default_positions(g.n, e_list))
            edge_start_rv.set(None)
            ui.update_text("custom_order", value=", ".join(str(i) for i in range(g.n)))

    @reactive.effect
    @reactive.event(input.negate_btn)
    def _on_negate():
        signs_rv.set([-s for s in signs_rv()])

    @reactive.effect
    @reactive.event(input.add_vertex_btn)
    def _on_add_vertex_btn():
        s = list(signs_rv())
        p = dict(pos_rv())
        idx = len(s)
        angle = (idx * 2.39996) % (2 * math.pi)
        p[idx] = (0.75 * math.cos(angle), 0.75 * math.sin(angle))
        s.append(1)
        signs_rv.set(s)
        pos_rv.set(p)

    @reactive.effect
    @reactive.event(input.graph_plot_click)
    def _on_graph_click():
        clk = input.graph_plot_click()
        if not clk or "x" not in clk or "y" not in clk:
            return
        cx, cy = float(clk["x"]), float(clk["y"])
        pos = pos_rv()
        mode = input.edit_mode()

        nearest = None
        min_d = 1e9
        for i, (px, py) in pos.items():
            d = math.hypot(px - cx, py - cy)
            if d < min_d:
                min_d = d
                nearest = i

        hit_thresh = 0.22
        if mode == "add_v":
            s = list(signs_rv())
            p = dict(pos)
            p[len(s)] = (cx, cy)
            s.append(1)
            signs_rv.set(s)
            pos_rv.set(p)
            return

        if nearest is None or min_d > hit_thresh:
            edge_start_rv.set(None)
            return

        if mode == "sign":
            s = list(signs_rv())
            s[nearest] = -s[nearest]
            signs_rv.set(s)
        elif mode == "del_v":
            s = list(signs_rv())
            if len(s) <= 2:
                return
            del s[nearest]
            new_edges = []
            for u, v, w in edges_rv():
                if u == nearest or v == nearest:
                    continue
                nu = u - 1 if u > nearest else u
                nv = v - 1 if v > nearest else v
                new_edges.append((min(nu, nv), max(nu, nv), w))
            new_pos = {}
            for k, xy in pos.items():
                if k == nearest:
                    continue
                nk = k - 1 if k > nearest else k
                new_pos[nk] = xy
            signs_rv.set(s)
            edges_rv.set(new_edges)
            pos_rv.set(new_pos)
            edge_start_rv.set(None)
        elif mode == "edge":
            start = edge_start_rv()
            if start is None:
                edge_start_rv.set(nearest)
            elif start == nearest:
                edge_start_rv.set(None)
            else:
                u, v = min(start, nearest), max(start, nearest)
                e_list = list(edges_rv())
                existing = [item for item in e_list if (item[0], item[1]) == (u, v)]
                if existing:
                    e_list = [item for item in e_list if (item[0], item[1]) != (u, v)]
                else:
                    w_raw = input.edge_weight()
                    w: Any = sp.oo if w_raw == "oo" else int(w_raw)
                    e_list.append((u, v, w))
                edges_rv.set(e_list)
                edge_start_rv.set(None)

    @reactive.calc
    def current_graph() -> MixedSignCoxeterGraph:
        return MixedSignCoxeterGraph(signs_rv(), edges_rv())

    @reactive.calc
    def active_order() -> tuple[tuple[int, ...], str | None]:
        g = current_graph()
        mode = input.ordering_mode()
        if mode == "linear":
            return tuple(range(g.n)), None
        if mode == "bipartite":
            if not g.is_bipartite():
                return tuple(range(g.n)), "Graph is not bipartite; using linear ordering."
            return g.bipartite_principal_order(), None
        try:
            vals = [int(x.strip()) for x in input.custom_order().split(",") if x.strip()]
            if sorted(vals) != list(range(g.n)):
                return tuple(range(g.n)), f"Custom order must be a permutation of 0..{g.n - 1}."
            return tuple(vals), None
        except Exception as exc:
            return tuple(range(g.n)), str(exc)

    @render.ui
    def mode_hint_ui():
        mode = input.edit_mode()
        start = edge_start_rv()
        if mode == "sign":
            msg = "Click any vertex to toggle its sign (+ Garnet ↔ − Lean Blue)."
        elif mode == "edge":
            msg = (
                f"Selected vertex {start}. Click a second vertex to toggle the edge."
                if start is not None
                else "Click a first vertex, then a second vertex to add or remove an edge."
            )
        elif mode == "add_v":
            msg = "Click anywhere on the canvas to place a new (+) vertex."
        else:
            msg = "Click any vertex to delete it (minimum 2 vertices)."
        return ui.p(msg, class_="text-muted small mb-0 mt-1")

    @render.plot
    def graph_plot():
        g = current_graph()
        pos = pos_rv()
        start = edge_start_rv()
        fig, ax = plt.subplots(figsize=(8.0, 4.4))
        for (u, v), w in g.edges.items():
            x0, y0 = pos[u]
            x1, y1 = pos[v]
            ax.plot([x0, x1], [y0, y1], color="#333333", lw=2.4, zorder=1)
            if w != 3:
                ax.text(
                    (x0 + x1) / 2,
                    (y0 + y1) / 2,
                    "∞" if w == sp.oo else str(w),
                    fontsize=10,
                    ha="center",
                    va="center",
                    bbox=dict(fc="white", ec="#cbd5e1", pad=1.5),
                    zorder=2,
                )
        for i in range(g.n):
            x, y = pos[i]
            color = GARNET if g.signs[i] > 0 else LEAN_BLUE
            edge_c = "#f59e0b" if start == i else "#ffffff"
            lw = 3.5 if start == i else 2.0
            ax.scatter([x], [y], s=780, color=color, edgecolors=edge_c, linewidths=lw, zorder=3)
            ax.text(
                x,
                y,
                f"{i}\n({'+' if g.signs[i] > 0 else '−'})",
                color="white",
                ha="center",
                va="center",
                fontsize=9,
                fontweight="bold",
                zorder=4,
            )
        xs = [p[0] for p in pos.values()]
        ys = [p[1] for p in pos.values()]
        pad = 0.35
        ax.set_xlim(min(xs) - pad, max(xs) + pad)
        ax.set_ylim(min(ys) - pad, max(ys) + pad)
        ax.set_aspect("equal")
        ax.axis("off")
        ax.set_title("Garnet (#782F40) = (+) vertex   |   Lean Blue (#1E6BD6) = (−) vertex", fontsize=10)
        return fig

    @render.plot
    def spectrum_plot():
        g = current_graph()
        order, _ = active_order()
        w = g.principal_element(order)
        eigs = np.linalg.eigvals(np.array(w.tolist(), dtype=float))
        fig, ax = plt.subplots(figsize=(5.5, 3.8))
        theta = np.linspace(0, 2 * np.pi, 256)
        ax.plot(np.cos(theta), np.sin(theta), "--", color="#94a3b8", lw=1.2, label="|λ| = 1")
        ax.axhline(0, color="#cbd5e1", lw=0.8)
        ax.axvline(0, color="#cbd5e1", lw=0.8)
        ax.scatter(eigs.real, eigs.imag, s=80, color=GARNET, zorder=3, label="Eigenvalues")
        lim = max(1.3, float(np.max(np.abs(eigs))) * 1.15)
        ax.set_xlim(-lim, lim)
        ax.set_ylim(-lim, lim)
        ax.set_aspect("equal")
        ax.set_xlabel("Re(λ)")
        ax.set_ylabel("Im(λ)")
        ax.set_title(f"Principal Spectrum (ρ = {float(np.max(np.abs(eigs))):.4f})")
        ax.legend(loc="upper right", fontsize=8)
        return fig

    @render.ui
    def summary_ui():
        g = current_graph()
        order, note = active_order()
        comps = len(g.connected_components())
        rho_lin = g.spectral_radius(tuple(range(g.n)))
        sig = g.signature()
        if g.is_bipartite():
            rho_bip = g.spectral_radius(g.bipartite_principal_order())
            pct = ((rho_bip / rho_lin) - 1.0) * 100.0 if rho_lin > 0 else 0.0
            bip_line = (
                f"<div class='mb-2'><strong>✓ Bipartite</strong> &nbsp;|&nbsp; "
                f"<code>ρ_linear = {rho_lin:.4f}</code> &nbsp;|&nbsp; "
                f"<code>ρ_bipartite = {rho_bip:.4f}</code> "
                f"(<span class='text-primary'>{pct:+.1f}%</span>)</div>"
            )
        else:
            bip_line = f"<div class='mb-2'><strong>✗ Not bipartite</strong> &nbsp;|&nbsp; <code>ρ_linear = {rho_lin:.4f}</code></div>"
        note_html = f"<p class='text-warning small'>{note}</p>" if note else ""
        return ui.HTML(
            note_html
            + bip_line
            + f"""
            <div class="small text-muted">
              Vertices: <strong>{g.n}</strong> &nbsp;·&nbsp;
              Edges: <strong>{len(g.edges)}</strong> &nbsp;·&nbsp;
              Connected: <strong>{'Yes' if g.is_irreducible() else f'No ({comps})'}</strong> &nbsp;·&nbsp;
              Tree: <strong>{'Yes' if g.is_tree() else 'No'}</strong> &nbsp;·&nbsp;
              Signature: <strong>{sig.as_tuple()} ({sig.classify()})</strong>
            </div>
            """
        )

    @render.ui
    def theorem_hints_ui():
        g = current_graph()
        hints = []
        hints.append(
            "<li>✅ <strong>Theorem 1.1 (Howlett's Formula)</strong>: "
            "<code>w = -U⁻¹ Uᵀ</code> holds on this graph. "
            "<a href='https://jkylearmstrong.github.io/mixed.sign.coxeter.systems/lean-verification.html' target='_blank'>Learn More →</a></li>"
        )
        if g.is_bipartite():
            hints.append(
                "<li>✅ <strong>Theorem 1.4 / 3.14 (Bipartite Principal Element)</strong>: "
                "Graph is bipartite — sign negation is O(B)-conjugate and bipartite ordering is defined. "
                "<a href='https://jkylearmstrong.github.io/mixed.sign.coxeter.systems/lean-verification.html' target='_blank'>Learn More →</a></li>"
            )
        if g.signature().classify() == "hyperbolic":
            hints.append(
                "<li>✅ <strong>Hyperbolic Signature</strong>: "
                "Indefinite form with signature (n−1, 1, 0) — compare with Example 3.29. "
                "<a href='https://jkylearmstrong.github.io/mixed.sign.coxeter.systems/dissertation.html' target='_blank'>Learn More →</a></li>"
            )
        if input.preset() in ("a_tilde_minus_2", "a_tilde_minus_4"):
            n_val = 2 if input.preset() == "a_tilde_minus_2" else 4
            cert = verify_a_tilde_minus_isomorphism(n_val)
            hints.append(
                f"<li>✅ <strong>Theorem 1.6 Remark</strong>: "
                f"<code>W(~A_-{n_val}) ≅ W(D_{n_val + 1})</code> (order {cert.order_W_D}).</li>"
            )
        return ui.HTML(f"<h6 class='mb-1'>Applicable Results</h6><ul class='mb-0 ps-3 small'>{''.join(hints)}</ul>")

    @render.ui
    def share_ui():
        g = current_graph()
        signs_param = "".join("+" if s > 0 else "-" for s in g.signs)
        edges_param = ",".join(f"{u}-{v}:{'oo' if w == sp.oo else w}" for (u, v), w in sorted(g.edges.items()))
        query = urlencode({"signs": signs_param, "edges": edges_param})
        return ui.HTML(
            f"<div class='small'><strong>Share Graph URL:</strong><br/>"
            f"<code style='word-break:break-all'>?{query}</code></div>"
        )

    @render.text
    def matrices_out():
        g = current_graph()
        order, _ = active_order()
        U = g.howlett_U(order)
        w = g.principal_element(order)
        poly = g.principal_polynomial(order)
        mm = mahler_measure(poly)
        eigs = sorted(np.linalg.eigvals(np.array(w.tolist(), dtype=float)), key=lambda z: -abs(z))
        eig_lines = "\n".join(f"  {z.real:+.6f} {z.imag:+.6f}j  (|λ| = {abs(z):.6f})" for z in eigs)
        return (
            f"Active order: {list(order)}\n"
            f"Principal polynomial: {sp.sstr(poly.as_expr())}\n"
            f"Factored:             {sp.sstr(g.factor_principal_polynomial(order))}\n"
            f"Mahler measure:       {mm:.6f}\n"
            f"Howlett identity w == -U^(-1) U^T: {w == -(U.inv() * U.T)}\n\n"
            f"Eigenvalues:\n{eig_lines}\n\n"
            f"Bilinear Form B:\n{sp.pretty(g.B)}\n\n"
            f"Principal Element w:\n{sp.pretty(w)}"
        )

    @render.text
    def export_out():
        g = current_graph()
        signs_py = ["+" if s > 0 else "-" for s in g.signs]
        edges_py = [(u, v, int(w) if w != sp.oo else "oo") for (u, v), w in sorted(g.edges.items())]
        py_code = (
            "from mixed_sign_coxeter import MixedSignCoxeterGraph\n\n"
            f"g = MixedSignCoxeterGraph(\n    signs={signs_py!r},\n    edges={edges_py!r},\n)\n"
            "print('Spectral radius:', g.spectral_radius())\n"
            "print('Principal polynomial:', g.principal_polynomial())\n"
        )
        json_data = json.dumps({"signs": signs_py, "edges": edges_py, "signature": g.signature().as_tuple()}, indent=2)
        csv_lines = "source,target,weight\n" + "\n".join(f"{u},{v},{w}" for (u, v), w in sorted(g.edges.items()))
        G = nx.Graph()
        for i, s in enumerate(g.signs):
            G.add_node(i, sign="+" if s > 0 else "-")
        for (u, v), w in g.edges.items():
            G.add_edge(u, v, weight=str(w))
        graphml = "\n".join(nx.generate_graphml(G))
        return f"--- Python ---\n{py_code}\n--- JSON ---\n{json_data}\n\n--- CSV ---\n{csv_lines}\n\n--- GraphML ---\n{graphml}"


app = App(app_ui, server)
