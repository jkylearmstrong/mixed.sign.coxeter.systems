"""Interactive Mixed-Sign Coxeter System Explorer (Shiny for Python)."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

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
    classify_signature,
    mahler_measure,
)
from mixed_sign_coxeter.isomorphisms import (  # noqa: E402
    verify_a_tilde_minus_isomorphism,
)

THEOREMS_PATH = ROOT / "data" / "theorems.yml"


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


def format_edges(g: MixedSignCoxeterGraph) -> str:
    return ", ".join(f"{u}-{v}:{w}" for (u, v), w in sorted(g.edges.items()))


def format_signs(g: MixedSignCoxeterGraph) -> str:
    return ", ".join("+" if s > 0 else "-" for s in g.signs)


def parse_signs(text: str) -> list[str]:
    tokens = [t.strip() for t in text.replace(";", ",").split(",") if t.strip()]
    out = []
    for t in tokens:
        if t in ("+", "+1", "1"):
            out.append("+")
        elif t in ("-", "-1"):
            out.append("-")
        else:
            raise ValueError(f"Invalid sign token: {t!r} (use + or -)")
    if not out:
        raise ValueError("Provide at least one vertex sign.")
    return out


def parse_edges(text: str, n: int) -> list[tuple[int, int, Any]]:
    edges: list[tuple[int, int, Any]] = []
    for raw in text.replace("\n", ",").split(","):
        item = raw.strip()
        if not item:
            continue
        if ":" in item:
            pair_str, w_str = item.split(":", 1)
            w_str = w_str.strip()
            w: Any = sp.oo if w_str.lower() in ("oo", "inf") else int(w_str)
        else:
            pair_str, w = item, 3
        if "-" not in pair_str:
            raise ValueError(f"Edge {item!r} must look like u-v:weight (e.g. 0-1:3)")
        u_s, v_s = pair_str.split("-", 1)
        u, v = int(u_s.strip()), int(v_s.strip())
        if not (0 <= u < n and 0 <= v < n) or u == v:
            raise ValueError(f"Edge ({u}, {v}) out of range for {n} vertices.")
        edges.append((u, v, w))
    return edges


app_ui = ui.page_navbar(
    ui.nav_panel(
        "Explorer",
        ui.layout_sidebar(
            ui.sidebar(
                ui.input_select(
                    "preset",
                    "Preset Graph",
                    choices={k: v[0] for k, v in PRESETS.items()} | {"custom": "Custom Graph"},
                    selected="example_3_33",
                ),
                ui.input_text(
                    "signs_input",
                    "Vertex Signs (+ / -)",
                    value=format_signs(PRESETS["example_3_33"][1]),
                ),
                ui.input_action_button("negate_btn", "Negate All Signs", class_="btn-sm btn-outline-secondary"),
                ui.input_text_area(
                    "edges_input",
                    "Edges (u-v:weight)",
                    value=format_edges(PRESETS["example_3_33"][1]),
                    rows=3,
                ),
                ui.input_radio_buttons(
                    "ordering_mode",
                    "Principal Ordering",
                    choices={"linear": "Linear (0, 1, ..., n-1)", "bipartite": "Bipartite", "custom": "Custom"},
                    selected="linear",
                ),
                ui.input_text(
                    "custom_order",
                    "Custom Order (comma-separated)",
                    value="0, 1, 2, 3, 4, 5",
                ),
                ui.hr(),
                ui.markdown(
                    "Part of the [Mixed-Sign Coxeter Systems](https://jkylearmstrong.github.io/mixed.sign.coxeter.systems/) portal."
                ),
                width=330,
            ),
            ui.layout_columns(
                ui.card(
                    ui.card_header("Signed Coxeter Graph"),
                    ui.output_plot("graph_plot", height="340px"),
                ),
                ui.card(
                    ui.card_header("Structural & Signature Data"),
                    ui.output_ui("structural_ui"),
                ),
                col_widths=(6, 6),
            ),
            ui.layout_columns(
                ui.card(
                    ui.card_header("Principal Element & Spectral Radius"),
                    ui.output_ui("spectral_ui"),
                ),
                ui.card(
                    ui.card_header("Eigenvalues & Howlett Matrices"),
                    ui.output_text_verbatim("matrices_out"),
                ),
                col_widths=(6, 6),
            ),
            ui.card(
                ui.card_header("Verified Theorem Checker (from data/theorems.yml)"),
                ui.output_ui("theorem_checker_ui"),
            ),
        ),
    ),
    ui.nav_panel(
        "Export",
        ui.card(
            ui.card_header("Reproducible Python, JSON & LaTeX/TikZ"),
            ui.output_text_verbatim("export_out"),
        ),
    ),
    title="Mixed-Sign Coxeter Explorer",
)


def server(input, output, session):
    theorems = load_theorems()

    @reactive.effect
    @reactive.event(input.preset)
    def _sync_preset():
        key = input.preset()
        if key in PRESETS:
            g = PRESETS[key][1]
            ui.update_text("signs_input", value=format_signs(g))
            ui.update_text_area("edges_input", value=format_edges(g))
            ui.update_text("custom_order", value=", ".join(str(i) for i in range(g.n)))

    @reactive.effect
    @reactive.event(input.negate_btn)
    def _negate_signs():
        try:
            signs = parse_signs(input.signs_input())
            flipped = ["-" if s == "+" else "+" for s in signs]
            ui.update_text("signs_input", value=", ".join(flipped))
        except Exception:
            pass

    @reactive.calc
    def current_graph() -> tuple[MixedSignCoxeterGraph | None, str | None]:
        try:
            signs = parse_signs(input.signs_input())
            edges = parse_edges(input.edges_input(), len(signs))
            return MixedSignCoxeterGraph(signs, edges), None
        except Exception as exc:
            return None, str(exc)

    @reactive.calc
    def active_order() -> tuple[tuple[int, ...] | None, str | None]:
        g, err = current_graph()
        if g is None:
            return None, err
        mode = input.ordering_mode()
        if mode == "linear":
            return tuple(range(g.n)), None
        if mode == "bipartite":
            if not g.is_bipartite():
                return tuple(range(g.n)), "Graph is not bipartite; falling back to linear ordering."
            return g.bipartite_principal_order(), None
        try:
            vals = [int(x.strip()) for x in input.custom_order().split(",") if x.strip()]
            if sorted(vals) != list(range(g.n)):
                return tuple(range(g.n)), f"Custom order must be a permutation of 0..{g.n - 1}."
            return tuple(vals), None
        except Exception as exc:
            return tuple(range(g.n)), str(exc)

    @render.plot
    def graph_plot():
        g, err = current_graph()
        fig, ax = plt.subplots(figsize=(5.5, 4.0))
        if g is None:
            ax.text(0.5, 0.5, f"Input error:\n{err}", ha="center", va="center")
            ax.axis("off")
            return fig
        G = nx.Graph()
        for i in range(g.n):
            G.add_node(i, sign=g.signs[i])
        for (u, v), w in g.edges.items():
            G.add_edge(u, v, weight=w)
        pos = nx.spring_layout(G, seed=42)
        colors = ["#2563eb" if g.signs[i] > 0 else "#dc2626" for i in range(g.n)]
        nx.draw_networkx_nodes(G, pos, node_color=colors, node_size=650, ax=ax)
        labels = {i: f"{i}({'+' if g.signs[i] > 0 else '-'})" for i in range(g.n)}
        nx.draw_networkx_labels(G, pos, labels=labels, font_color="white", font_size=9, ax=ax)
        nx.draw_networkx_edges(G, pos, width=2, edge_color="#475569", ax=ax)
        edge_labels = {(u, v): (str(w) if w != 3 else "") for (u, v), w in g.edges.items()}
        nx.draw_networkx_edge_labels(G, pos, edge_labels=edge_labels, font_size=9, ax=ax)
        ax.set_title("Blue = (+) vertex, Red = (-) vertex")
        ax.axis("off")
        return fig

    @render.ui
    def structural_ui():
        g, err = current_graph()
        if g is None:
            return ui.p(f"Error: {err}", class_="text-danger")
        comps = len(g.connected_components())
        num_edges = len(g.edges)
        cyclomatic = num_edges - g.n + comps
        sig = g.signature()
        return ui.HTML(
            f"""
            <table class="table table-sm">
              <tr><th>Vertices</th><td>{g.n}</td><th>Edges</th><td>{num_edges}</td></tr>
              <tr><th>Connected</th><td>{'Yes' if g.is_irreducible() else f'No ({comps} components)'}</td>
                  <th>Tree</th><td>{'Yes' if g.is_tree() else 'No'}</td></tr>
              <tr><th>Bipartite</th><td>{'Yes' if g.is_bipartite() else 'No'}</td>
                  <th>Cyclomatic number</th><td>{cyclomatic}</td></tr>
              <tr><th>Classical (all +)</th><td>{'Yes' if g.is_classical() else 'No'}</td>
                  <th>Signature (p, q, z)</th><td>{sig.as_tuple()} ({sig.classify()})</td></tr>
            </table>
            """
        )

    @render.ui
    def spectral_ui():
        g, err = current_graph()
        if g is None:
            return ui.p(f"Error: {err}", class_="text-danger")
        order, note = active_order()
        rho_active = g.spectral_radius(order)
        rho_lin = g.spectral_radius(tuple(range(g.n)))
        poly = g.principal_polynomial(order)
        factored = g.factor_principal_polynomial(order)
        mm = mahler_measure(poly)
        if g.is_bipartite():
            rho_bip = g.spectral_radius(g.bipartite_principal_order())
            ratio = rho_bip / rho_lin if rho_lin > 0 else float("nan")
            bip_row = f"<tr><th>Bipartite ρ</th><td>{rho_bip:.6f}</td><th>Bip / Lin ratio</th><td>{ratio:.4f}</td></tr>"
        else:
            bip_row = "<tr><th>Bipartite ρ</th><td colspan='3'>N/A (graph is not bipartite)</td></tr>"
        note_html = f"<p class='text-warning small'>{note}</p>" if note else ""
        return ui.HTML(
            note_html
            + f"""
            <table class="table table-sm">
              <tr><th>Active Order</th><td>{list(order or ())}</td><th>Active ρ</th><td><strong>{rho_active:.6f}</strong></td></tr>
              <tr><th>Linear ρ</th><td>{rho_lin:.6f}</td><th>Mahler Measure</th><td>{mm:.6f}</td></tr>
              {bip_row}
            </table>
            <p><strong>Principal polynomial:</strong> <code>{sp.sstr(poly.as_expr())}</code></p>
            <p><strong>Factored:</strong> <code>{sp.sstr(factored)}</code></p>
            """
        )

    @render.text
    def matrices_out():
        g, err = current_graph()
        if g is None:
            return f"Error: {err}"
        order, _ = active_order()
        U = g.howlett_U(order)
        w = g.principal_element(order)
        howlett_ok = w == -(U.inv() * U.T)
        eigs = np.linalg.eigvals(np.array(w.tolist(), dtype=float))
        eigs_sorted = sorted(eigs, key=lambda z: -abs(z))
        eig_lines = "\n".join(f"  {z.real:+.6f} {z.imag:+.6f}j  (|λ| = {abs(z):.6f})" for z in eigs_sorted)
        return (
            f"Howlett identity w == -U^(-1) U^T: {howlett_ok}\n\n"
            f"Eigenvalues (sorted by |λ|):\n{eig_lines}\n\n"
            f"Bilinear Form B:\n{sp.pretty(g.B)}\n\n"
            f"Principal Element w:\n{sp.pretty(w)}"
        )

    @render.ui
    def theorem_checker_ui():
        g, err = current_graph()
        if g is None:
            return ui.p(f"Error: {err}", class_="text-danger")
        order, _ = active_order()
        U = g.howlett_U(order)
        w = g.principal_element(order)
        howlett_ok = w == -(U.inv() * U.T)
        rows = []
        for thm in theorems:
            tid = thm["id"]
            if tid == "howlett_formula":
                check = "✅ Holds on current graph" if howlett_ok else "❌ Failed"
            elif tid == "coxeter_conjugacy_bipartite":
                check = "✅ Applicable (graph is bipartite)" if g.is_bipartite() else "— Graph is not bipartite"
            elif tid == "bipartite_principal_radius":
                if g.is_bipartite():
                    r_lin = g.spectral_radius()
                    r_bip = g.spectral_radius(g.bipartite_principal_order())
                    check = f"✅ Applicable (ρ_bip={r_bip:.4f} vs ρ_lin={r_lin:.4f})"
                else:
                    check = "— Graph is not bipartite"
            elif tid == "a_tilde_minus_even_iso":
                if input.preset() == "a_tilde_minus_4":
                    cert = verify_a_tilde_minus_isomorphism(4)
                    check = f"✅ Verified (~A_-4 ≅ W(D_5), |W|={cert.order_W_D})"
                elif input.preset() == "a_tilde_minus_2":
                    cert = verify_a_tilde_minus_isomorphism(2)
                    check = f"✅ Verified (~A_-2 ≅ W(D_3), |W|={cert.order_W_D})"
                else:
                    check = "— Select ~A_{-2} or ~A_{-4} preset"
            elif tid == "example_3_29_hyperbolic":
                sig = g.signature().classify()
                check = f"✅ Hyperbolic ({sig}, ρ={g.spectral_radius():.4f})" if sig == "hyperbolic" else f"— Signature is {sig}"
            else:
                check = "ℹ️ Reference theorem"

            lean_cell = (
                f"<a href='{thm['lean_url']}' target='_blank'><code>{thm['lean_symbol']}</code></a>"
                if thm.get("lean_url")
                else "—"
            )
            rows.append(
                f"<tr><td><strong>{thm['dissertation_ref']}</strong>: {thm['title']}</td>"
                f"<td>{lean_cell}</td><td>{thm['status']}</td><td>{check}</td></tr>"
            )
        return ui.HTML(
            "<table class='table table-sm table-striped'>"
            "<thead><tr><th>Dissertation Result</th><th>Lean 4</th><th>Registry Status</th><th>Live Check</th></tr></thead>"
            f"<tbody>{''.join(rows)}</tbody></table>"
        )

    @render.text
    def export_out():
        g, err = current_graph()
        if g is None:
            return f"Error: {err}"
        signs_py = ["+" if s > 0 else "-" for s in g.signs]
        edges_py = [(u, v, int(w) if w != sp.oo else "oo") for (u, v), w in sorted(g.edges.items())]
        py_code = (
            "from mixed_sign_coxeter import MixedSignCoxeterGraph\n\n"
            f"g = MixedSignCoxeterGraph(\n    signs={signs_py!r},\n    edges={edges_py!r},\n)\n"
            "print('Spectral radius:', g.spectral_radius())\n"
            "print('Principal polynomial:', g.principal_polynomial())\n"
        )
        json_data = json.dumps({"signs": signs_py, "edges": edges_py, "signature": g.signature().as_tuple()}, indent=2)
        tikz_nodes = "\n".join(
            f"  \\node[circle,draw,fill={'blue!20' if s > 0 else 'red!20'}] (v{i}) at ({i * 1.5:.1f},0) {{{i}}};"
            for i, s in enumerate(g.signs)
        )
        tikz_edges = "\n".join(f"  \\draw (v{u}) -- node[above] {{{w}}} (v{v});" for (u, v), w in sorted(g.edges.items()))
        return f"--- Python ---\n{py_code}\n--- JSON ---\n{json_data}\n\n--- TikZ ---\n\\begin{{tikzpicture}}\n{tikz_nodes}\n{tikz_edges}\n\\end{{tikzpicture}}"


app = App(app_ui, server)
