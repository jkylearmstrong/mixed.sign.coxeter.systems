"""Generate the Mixed-Sign Coxeter Systems hex sticker (SVG + transparent PNG)."""

from __future__ import annotations

import math
from pathlib import Path

import matplotlib.patches as patches
import matplotlib.pyplot as plt

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
    angles = [math.radians(90 - 60 * k) for k in range(6)]
    return [(cx + r * math.cos(a), cy + r * math.sin(a)) for a in angles]


# Slightly enlarged 6-vertex graph framing rho(phi) cleanly without touching it
NODES = [
    (200, 178, "+", GARNET),
    (400, 178, "-", LEAN_BLUE),
    (138, 290, "-", LEAN_BLUE),
    (462, 290, "+", GARNET),
    (200, 402, "+", GARNET),
    (400, 402, "-", LEAN_BLUE),
]
EDGES = [
    (0, 1),
    (0, 2),
    (1, 3),
    (2, 4),
    (3, 5),
    (4, 5),
    (0, 4),
    (1, 5),
]


def build_svg() -> str:
    W, H = 600, 693
    cx, cy = W / 2, H / 2
    outer = pointy_hex_vertices(cx, cy, 336)
    inner = pointy_hex_vertices(cx, cy, 322)
    outer_pts = " ".join(f"{x:.2f},{y:.2f}" for x, y in outer)
    inner_pts = " ".join(f"{x:.2f},{y:.2f}" for x, y in inner)

    edge_svg = "\n".join(
        f'  <line x1="{NODES[u][0]}" y1="{NODES[u][1]}" '
        f'x2="{NODES[v][0]}" y2="{NODES[v][1]}" '
        f'stroke="{GRAPHITE}" stroke-width="3.8" stroke-linecap="round" opacity="0.88"/>'
        for u, v in EDGES
    )
    node_svg = "\n".join(
        f'  <circle cx="{x}" cy="{y}" r="18" fill="{color}" stroke="{BG_CENTER}" stroke-width="2.5"/>\n'
        f'  <text x="{x}" y="{y + 6}" text-anchor="middle" font-family="DejaVu Sans, Arial, sans-serif" '
        f'font-size="18" font-weight="bold" fill="#FFFFFF">{sign}</text>'
        for x, y, sign, color in NODES
    )

    return f"""<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}">
  <defs>
    <radialGradient id="parchment" cx="50%" cy="46%" r="60%">
      <stop offset="0%" stop-color="{BG_CENTER}"/>
      <stop offset="100%" stop-color="{BG_EDGE}"/>
    </radialGradient>
  </defs>

  <!-- Outer Hex -->
  <polygon points="{outer_pts}" fill="url(#parchment)" stroke="{GRAPHITE}" stroke-width="8" stroke-linejoin="round"/>
  <polygon points="{inner_pts}" fill="none" stroke="{GRAPHITE}" stroke-width="1.5" stroke-linejoin="round" opacity="0.35"/>

  <!-- Top Polynomial -->
  <text x="{cx}" y="122" text-anchor="middle" font-family="Georgia, 'Times New Roman', serif"
        font-size="18" fill="{MATH_TEXT}" letter-spacing="0.4" opacity="0.85">
    &#955;&#8308; &#8722; 3&#955;&#179; + 2&#955;&#178; &#8722; 3&#955; + 1
  </text>

  <!-- Signed Coxeter Graph -->
{edge_svg}
{node_svg}

  <!-- Central Spectral Radius (no background box) -->
  <text x="{cx}" y="304" text-anchor="middle" font-family="Georgia, 'Times New Roman', serif"
        font-style="italic" font-size="52" font-weight="bold" fill="{MATH_TEXT}">&#961;(&#966;)</text>

  <!-- Title Typography -->
  <text x="{cx}" y="476" text-anchor="middle" font-family="Georgia, 'Times New Roman', serif"
        font-size="33" font-weight="bold" fill="{MATH_TEXT}">Mixed-Sign</text>
  <text x="{cx}" y="516" text-anchor="middle" font-family="Georgia, 'Times New Roman', serif"
        font-size="33" font-weight="bold" fill="{MATH_TEXT}">Coxeter Systems</text>

  <!-- Bottom Lean 4 & URL -->
  <text x="{cx}" y="568" text-anchor="middle" font-family="'DejaVu Sans Mono', Consolas, monospace"
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
    ax.set_ylim(693, 0)
    ax.set_aspect("equal")
    ax.axis("off")

    cx, cy = 300, 346.5
    outer = pointy_hex_vertices(cx, cy, 336)
    inner = pointy_hex_vertices(cx, cy, 322)
    ax.add_patch(patches.Polygon(outer, closed=True, facecolor=BG_EDGE, edgecolor=GRAPHITE, linewidth=5.5, joinstyle="round"))
    ax.add_patch(patches.Polygon(inner, closed=True, facecolor="none", edgecolor=GRAPHITE, linewidth=1.0, alpha=0.35, joinstyle="round"))

    ax.text(
        cx, 120, r"$\lambda^4 - 3\lambda^3 + 2\lambda^2 - 3\lambda + 1$",
        ha="center", va="center", fontsize=14, color=MATH_TEXT, alpha=0.88,
    )

    for u, v in EDGES:
        ax.plot([NODES[u][0], NODES[v][0]], [NODES[u][1], NODES[v][1]], color=GRAPHITE, lw=3.0, alpha=0.88, zorder=1)
    for x, y, sign, color in NODES:
        disp = "−" if sign == "-" else "+"
        ax.scatter([x], [y], s=600, color=color, edgecolors=BG_CENTER, linewidths=2.2, zorder=2)
        ax.text(x, y, disp, ha="center", va="center", color="white", fontsize=14, fontweight="bold", zorder=3)

    ax.text(
        cx, 290, r"$\rho(\varphi)$",
        ha="center", va="center", fontsize=38, fontweight="bold", color=MATH_TEXT, zorder=4,
    )
    ax.text(cx, 470, "Mixed-Sign", ha="center", va="center", fontsize=24, fontweight="bold", family="serif", color=MATH_TEXT)
    ax.text(cx, 512, "Coxeter Systems", ha="center", va="center", fontsize=24, fontweight="bold", family="serif", color=MATH_TEXT)
    ax.text(cx, 564, "theorem principal_radius :", ha="center", va="center", fontsize=10.5, fontweight="bold", family="monospace", color=LEAN_BLUE)
    ax.text(cx, 604, "jkylearmstrong.github.io", ha="center", va="center", fontsize=9, color=GRAPHITE, alpha=0.75)

    plt.tight_layout(pad=0)
    fig.savefig(ASSETS / "hex-sticker.png", transparent=True, bbox_inches="tight", pad_inches=0.05)
    plt.close(fig)


if __name__ == "__main__":
    (ASSETS / "hex-sticker.svg").write_text(build_svg(), encoding="utf-8")
    build_png()
    print("Regenerated:", ASSETS / "hex-sticker.svg", "and", ASSETS / "hex-sticker.png")
