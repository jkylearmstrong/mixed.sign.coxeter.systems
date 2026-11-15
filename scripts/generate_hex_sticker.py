"""Generate the Mixed-Sign Coxeter Systems hex sticker (SVG + transparent PNG)."""

from __future__ import annotations

import math
from pathlib import Path

import matplotlib.patches as patches
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
ASSETS = ROOT / "assets"
ASSETS.mkdir(parents=True, exist_ok=True)

# Color palette (FSU Garnet + Lean Blue + Warm Parchment)
BG_CENTER = "#FAF7F2"
BG_EDGE = "#F5F1EB"
GARNET = "#782F40"
LEAN_BLUE = "#1E6BD6"
GRAPHITE = "#333333"
MATH_TEXT = "#222222"


def pointy_hex_vertices(cx: float, cy: float, r: float) -> list[tuple[float, float]]:
    # Pointy-top regular hexagon: angles 90, 30, -30, -90, -150, 150 deg
    angles = [math.radians(90 - 60 * k) for k in range(6)]
    return [(cx + r * math.cos(a), cy + r * math.sin(a)) for a in angles]


def build_svg() -> str:
    W, H = 600, 693
    cx, cy = W / 2, H / 2
    outer = pointy_hex_vertices(cx, cy, 336)
    inner = pointy_hex_vertices(cx, cy, 322)
    outer_pts = " ".join(f"{x:.2f},{y:.2f}" for x, y in outer)
    inner_pts = " ".join(f"{x:.2f},{y:.2f}" for x, y in inner)

    # Signed graph vertices arranged to suggest a lowercase phi around rho(phi)
    # 6 vertices: top-left(+), top-right(-), mid-left(-), mid-right(+), bot-left(+), bot-right(-)
    nodes = [
        (215, 195, "+", GARNET),
        (385, 195, "-", LEAN_BLUE),
        (165, 290, "-", LEAN_BLUE),
        (435, 290, "+", GARNET),
        (215, 385, "+", GARNET),
        (385, 385, "-", LEAN_BLUE),
    ]
    edges = [
        (0, 1),
        (0, 2),
        (1, 3),
        (2, 4),
        (3, 5),
        (4, 5),
        (0, 4),  # vertical-ish phi stem / diagonal
        (1, 5),
    ]
    edge_svg = "\n".join(
        f'  <line x1="{nodes[u][0]}" y1="{nodes[u][1]}" '
        f'x2="{nodes[v][0]}" y2="{nodes[v][1]}" '
        f'stroke="{GRAPHITE}" stroke-width="3.5" stroke-linecap="round" opacity="0.88"/>'
        for u, v in edges
    )
    node_svg = "\n".join(
        f'  <circle cx="{x}" cy="{y}" r="16" fill="{color}" stroke="{BG_CENTER}" stroke-width="2.5"/>\n'
        f'  <text x="{x}" y="{y + 5}" text-anchor="middle" font-family="DejaVu Sans, Arial, sans-serif" '
        f'font-size="16" font-weight="bold" fill="#FFFFFF">{sign}</text>'
        for x, y, sign, color in nodes
    )

    return f"""<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}">
  <defs>
    <radialGradient id="parchment" cx="50%" cy="46%" r="60%">
      <stop offset="0%" stop-color="{BG_CENTER}"/>
      <stop offset="100%" stop-color="{BG_EDGE}"/>
    </radialGradient>
    <path id="topArc" d="M 95,180 L 300,62 L 505,180" fill="none"/>
  </defs>

  <!-- Outer Hex -->
  <polygon points="{outer_pts}" fill="url(#parchment)" stroke="{GRAPHITE}" stroke-width="8" stroke-linejoin="round"/>
  <polygon points="{inner_pts}" fill="none" stroke="{GRAPHITE}" stroke-width="1.5" stroke-linejoin="round" opacity="0.35"/>

  <!-- Top Polynomial -->
  <text x="{cx}" y="128" text-anchor="middle" font-family="Georgia, 'Times New Roman', serif"
        font-size="18" fill="{MATH_TEXT}" letter-spacing="0.4" opacity="0.85">
    &#955;&#8308; &#8722; 3&#955;&#179; + 2&#955;&#178; &#8722; 3&#955; + 1
  </text>

  <!-- Signed Coxeter Graph -->
{edge_svg}
{node_svg}

  <!-- Central Spectral Radius -->
  <rect x="236" y="255" width="128" height="64" rx="12" fill="{BG_CENTER}" opacity="0.92"/>
  <text x="{cx}" y="302" text-anchor="middle" font-family="Georgia, 'Times New Roman', serif"
        font-style="italic" font-size="48" font-weight="bold" fill="{MATH_TEXT}">&#961;(&#966;)</text>

  <!-- Title Typography -->
  <text x="{cx}" y="468" text-anchor="middle" font-family="Georgia, 'Times New Roman', serif"
        font-size="33" font-weight="bold" fill="{MATH_TEXT}">Mixed-Sign</text>
  <text x="{cx}" y="510" text-anchor="middle" font-family="Georgia, 'Times New Roman', serif"
        font-size="33" font-weight="bold" fill="{MATH_TEXT}">Coxeter Systems</text>

  <!-- Bottom Lean 4 & URL -->
  <text x="{cx}" y="566" text-anchor="middle" font-family="'DejaVu Sans Mono', Consolas, monospace"
        font-size="13.5" fill="{LEAN_BLUE}" font-weight="bold">theorem principal_radius :</text>
  <text x="{cx}" y="608" text-anchor="middle" font-family="DejaVu Sans, Arial, sans-serif"
        font-size="11.5" fill="{GRAPHITE}" opacity="0.75">jkylearmstrong.github.io</text>
</svg>
"""


def build_png() -> None:
    fig, ax = plt.subplots(figsize=(6, 6.93), dpi=200)
    fig.patch.set_alpha(0.0)
    ax.set_facecolor("none")
    ax.set_xlim(0, 600)
    ax.set_ylim(693, 0)  # match SVG y-down coordinates
    ax.set_aspect("equal")
    ax.axis("off")

    cx, cy = 300, 346.5
    outer = pointy_hex_vertices(cx, cy, 336)
    inner = pointy_hex_vertices(cx, cy, 322)
    ax.add_patch(patches.Polygon(outer, closed=True, facecolor=BG_EDGE, edgecolor=GRAPHITE, linewidth=5.5, joinstyle="round"))
    ax.add_patch(patches.Polygon(inner, closed=True, facecolor="none", edgecolor=GRAPHITE, linewidth=1.0, alpha=0.35, joinstyle="round"))

    ax.text(
        cx, 126, r"$\lambda^4 - 3\lambda^3 + 2\lambda^2 - 3\lambda + 1$",
        ha="center", va="center", fontsize=14, color=MATH_TEXT, alpha=0.88,
    )

    nodes = [
        (215, 195, "+", GARNET),
        (385, 195, "−", LEAN_BLUE),
        (165, 290, "−", LEAN_BLUE),
        (435, 290, "+", GARNET),
        (215, 385, "+", GARNET),
        (385, 385, "−", LEAN_BLUE),
    ]
    edges = [(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (4, 5), (0, 4), (1, 5)]
    for u, v in edges:
        ax.plot([nodes[u][0], nodes[v][0]], [nodes[u][1], nodes[v][1]], color=GRAPHITE, lw=2.8, alpha=0.88, zorder=1)
    for x, y, sign, color in nodes:
        ax.scatter([x], [y], s=520, color=color, edgecolors=BG_CENTER, linewidths=2.0, zorder=2)
        ax.text(x, y, sign, ha="center", va="center", color="white", fontsize=13, fontweight="bold", zorder=3)

    ax.text(
        cx, 290, r"$\rho(\varphi)$",
        ha="center", va="center", fontsize=34, fontweight="bold", color=MATH_TEXT,
        bbox=dict(boxstyle="round,pad=0.25", facecolor=BG_CENTER, edgecolor="none", alpha=0.92),
        zorder=4,
    )
    ax.text(cx, 462, "Mixed-Sign", ha="center", va="center", fontsize=24, fontweight="bold", family="serif", color=MATH_TEXT)
    ax.text(cx, 504, "Coxeter Systems", ha="center", va="center", fontsize=24, fontweight="bold", family="serif", color=MATH_TEXT)
    ax.text(cx, 562, "theorem principal_radius :", ha="center", va="center", fontsize=10.5, fontweight="bold", family="monospace", color=LEAN_BLUE)
    ax.text(cx, 604, "jkylearmstrong.github.io", ha="center", va="center", fontsize=9, color=GRAPHITE, alpha=0.75)

    plt.tight_layout(pad=0)
    fig.savefig(ASSETS / "hex-sticker.png", transparent=True, bbox_inches="tight", pad_inches=0.05)
    plt.close(fig)


if __name__ == "__main__":
    (ASSETS / "hex-sticker.svg").write_text(build_svg(), encoding="utf-8")
    build_png()
    print("Generated:", ASSETS / "hex-sticker.svg", "and", ASSETS / "hex-sticker.png")
