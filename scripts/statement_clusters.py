"""Semantic TF-IDF clustering of the 107 dissertation statements.

Ports the TF-IDF + cosine-distance + complete-linkage hierarchical clustering
analysis to pure Python + NumPy (no scikit-learn or SciPy required) and compares
the resulting latent semantic clusters against both:

1. The dissertation's linear section structure (Chapters 1--3), and
2. The Lean 4 module dependency-graph views defined in
   ``scripts/lean_module_graph.py``.

Usage::

    python scripts/statement_clusters.py
    python scripts/statement_clusters.py --k 6 --top-terms 10
    python scripts/statement_clusters.py --k 6 --plot assets/statement_clusters.png
"""

from __future__ import annotations

import argparse
import csv
import math
import re
from collections import Counter, defaultdict
from pathlib import Path
from typing import Sequence

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
STATEMENTS_CSV = ROOT / "original" / "mixed_sign_coxeter_statements_lean.csv"

# English + mathematical boilerplate stop words (matching the R analysis).
STOP_WORDS: frozenset[str] = frozenset({
    "a", "an", "and", "any", "are", "as", "at", "be", "because", "been",
    "between", "both", "but", "by", "can", "considered", "corollary",
    "defined", "definition", "do", "does", "each", "either", "every",
    "example", "for", "from", "given", "has", "have", "if", "iff", "in",
    "into", "is", "it", "its", "lemma", "let", "may", "more", "no", "not",
    "note", "of", "on", "one", "only", "or", "other", "proposition",
    "remark", "same", "seen", "show", "since", "so", "some", "such",
    "suppose", "than", "that", "the", "their", "them", "then", "there",
    "these", "this", "those", "to", "two", "we", "when", "where", "which",
    "while", "will", "with", "would",
    # Common LaTeX formatting macros that carry no topical signal
    "mathbb", "mathrm", "mathcal", "widetilde", "frac", "left", "right",
    "ldots", "cdots", "cdot", "times", "approx", "forall", "mid",
})

_TOKEN_RE = re.compile(r"[a-z]{2,}")


def load_statements(csv_path: Path = STATEMENTS_CSV) -> list[dict[str, str]]:
    """Load the 107 dissertation statements from CSV."""
    with csv_path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def tokenize(text: str, stop_words: frozenset[str] = STOP_WORDS) -> list[str]:
    """Lowercase alphabetic tokenization with stop-word removal."""
    return [tok for tok in _TOKEN_RE.findall(text.lower()) if tok not in stop_words]


def build_tfidf_matrix(
    docs: Sequence[str],
    min_term_count: int = 2,
    stop_words: frozenset[str] = STOP_WORDS,
) -> tuple[np.ndarray, list[str]]:
    """Build an L2-normalized TF-IDF matrix ``(n_docs, n_vocab)`` and vocabulary list."""
    tokenized = [tokenize(doc, stop_words=stop_words) for doc in docs]
    total_counts = Counter(tok for tokens in tokenized for tok in tokens)
    vocab = sorted(tok for tok, cnt in total_counts.items() if cnt >= min_term_count)
    if not vocab:
        return np.zeros((len(docs), 0), dtype=float), []

    index = {tok: j for j, tok in enumerate(vocab)}
    n_docs = len(docs)
    tf = np.zeros((n_docs, len(vocab)), dtype=float)
    df = np.zeros(len(vocab), dtype=float)

    for i, tokens in enumerate(tokenized):
        if not tokens:
            continue
        counts = Counter(tok for tok in tokens if tok in index)
        for tok, cnt in counts.items():
            j = index[tok]
            tf[i, j] = cnt / len(tokens)
            df[j] += 1.0

    idf = np.log((1.0 + n_docs) / (1.0 + df)) + 1.0
    mat = tf * idf
    norms = np.linalg.norm(mat, axis=1, keepdims=True)
    nonzero = norms[:, 0] > 0
    mat[nonzero] /= norms[nonzero]
    return mat, vocab


def cosine_distance_matrix(tfidf: np.ndarray) -> np.ndarray:
    """Pairwise cosine distance matrix for L2-normalized rows (zero rows have distance 1)."""
    sim = tfidf @ tfidf.T
    dist = np.clip(1.0 - sim, 0.0, 2.0)
    np.fill_diagonal(dist, 0.0)
    return dist


def hierarchical_clusters(
    tfidf: np.ndarray,
    k: int,
    linkage: str = "ward",
) -> list[int]:
    """Deterministic agglomerative clustering into ``k`` 1-based clusters.

    Supported ``linkage`` methods: ``"ward"`` (minimum-variance on L2-normalized
    TF-IDF vectors, avoiding sparse cosine-distance tie chaining), ``"complete"``,
    and ``"average"`` (on pairwise cosine distances).
    """
    n = tfidf.shape[0]
    if n == 0:
        return []
    if not 1 <= k <= n:
        raise ValueError(f"k must satisfy 1 <= k <= {n}, got {k}")
    if linkage not in {"ward", "complete", "average"}:
        raise ValueError(f"Unsupported linkage {linkage!r}; choose ward, complete, or average")

    clusters: list[list[int]] = [[i] for i in range(n)]
    if linkage == "ward":
        centroids = tfidf.astype(float).copy()
        sizes = np.ones(n, dtype=float)
        while len(clusters) > k:
            m = len(clusters)
            best_cost = math.inf
            best_pair = (0, 1)
            for i in range(m - 1):
                diff = centroids[i + 1 :] - centroids[i]
                sq = np.einsum("ij,ij->i", diff, diff)
                weights = (sizes[i] * sizes[i + 1 :]) / (sizes[i] + sizes[i + 1 :])
                costs = weights * sq
                j_rel = int(np.argmin(costs))
                if costs[j_rel] < best_cost:
                    best_cost = float(costs[j_rel])
                    best_pair = (i, i + 1 + j_rel)
            a, b = best_pair
            na, nb = sizes[a], sizes[b]
            centroids[a] = (na * centroids[a] + nb * centroids[b]) / (na + nb)
            sizes[a] = na + nb
            clusters[a] = clusters[a] + clusters[b]
            clusters.pop(b)
            centroids = np.delete(centroids, b, axis=0)
            sizes = np.delete(sizes, b)
    else:
        cdist = cosine_distance_matrix(tfidf)
        sizes = np.ones(n, dtype=float)
        while len(clusters) > k:
            m = len(clusters)
            best_d = math.inf
            best_pair = (0, 1)
            for i in range(m):
                for j in range(i + 1, m):
                    if cdist[i, j] < best_d:
                        best_d = float(cdist[i, j])
                        best_pair = (i, j)
            a, b = best_pair
            na, nb = sizes[a], sizes[b]
            if linkage == "complete":
                merged_row = np.maximum(cdist[a], cdist[b])
            else:
                merged_row = (na * cdist[a] + nb * cdist[b]) / (na + nb)
            cdist[a, :] = merged_row
            cdist[:, a] = merged_row
            cdist[a, a] = 0.0
            sizes[a] = na + nb
            clusters[a] = clusters[a] + clusters[b]
            clusters.pop(b)
            cdist = np.delete(np.delete(cdist, b, axis=0), b, axis=1)
            sizes = np.delete(sizes, b)

    clusters.sort(key=lambda members: (-len(members), min(members)))
    labels = [0] * n
    for cid, members in enumerate(clusters, start=1):
        for idx in members:
            labels[idx] = cid
    return labels


def top_terms_by_cluster(
    docs: Sequence[str],
    labels: Sequence[int],
    top_n: int = 10,
    stop_words: frozenset[str] = STOP_WORDS,
) -> dict[int, list[tuple[str, float]]]:
    """Compute the most distinctive words per cluster using cluster-level TF-IDF."""
    cluster_ids = sorted(set(labels))
    cluster_tokens: dict[int, Counter[str]] = {c: Counter() for c in cluster_ids}
    for doc, cid in zip(docs, labels):
        cluster_tokens[cid].update(tokenize(doc, stop_words=stop_words))

    doc_freq: Counter[str] = Counter()
    for cid in cluster_ids:
        for tok in cluster_tokens[cid]:
            doc_freq[tok] += 1

    n_clusters = len(cluster_ids)
    result: dict[int, list[tuple[str, float]]] = {}
    for cid in cluster_ids:
        counts = cluster_tokens[cid]
        total = sum(counts.values()) or 1
        scored = [
            (tok, (cnt / total) * math.log((1.0 + n_clusters) / (1.0 + doc_freq[tok])))
            for tok, cnt in counts.items()
        ]
        scored.sort(key=lambda pair: (-pair[1], pair[0]))
        result[cid] = scored[:top_n]
    return result


def section_crosstab(
    rows: Sequence[dict[str, str]],
    labels: Sequence[int],
) -> tuple[list[int], list[str], np.ndarray]:
    """Return ``(cluster_ids, sections, count_matrix)``."""
    cluster_ids = sorted(set(labels))
    sections = sorted(
        {r.get("section", "").strip() or "?" for r in rows},
        key=lambda s: [int(p) if p.isdigit() else 999 for p in s.split(".")],
    )
    c_idx = {c: i for i, c in enumerate(cluster_ids)}
    s_idx = {s: j for j, s in enumerate(sections)}
    grid = np.zeros((len(cluster_ids), len(sections)), dtype=int)
    for r, cid in zip(rows, labels):
        sec = r.get("section", "").strip() or "?"
        grid[c_idx[cid], s_idx[sec]] += 1
    return cluster_ids, sections, grid


def lean_view_crosstab(
    rows: Sequence[dict[str, str]],
    labels: Sequence[int],
) -> tuple[list[int], list[str], np.ndarray]:
    """Compare semantic clusters against the Lean 4 views in ``lean_module_graph.py``."""
    import importlib.util

    spec = importlib.util.spec_from_file_location(
        "lean_module_graph", ROOT / "scripts" / "lean_module_graph.py"
    )
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    mod_to_view = {m: f"V{i + 1}" for i, (_, mods) in enumerate(mod.VIEWS) for m in mods}
    view_names = [f"V{i + 1}" for i in range(len(mod.VIEWS))] + ["Unmapped"]
    cluster_ids = sorted(set(labels))
    c_idx = {c: i for i, c in enumerate(cluster_ids)}
    v_idx = {v: j for j, v in enumerate(view_names)}
    grid = np.zeros((len(cluster_ids), len(view_names)), dtype=int)

    for r, cid in zip(rows, labels):
        lf = (r.get("lean_file") or "").strip()
        first = lf.split(";")[0].strip() if lf else ""
        stem = Path(first).stem if first else ""
        vname = mod_to_view.get(stem, "Unmapped")
        grid[c_idx[cid], v_idx[vname]] += 1
    return cluster_ids, view_names, grid


def cluster_statements(
    csv_path: Path = STATEMENTS_CSV,
    k: int = 6,
    min_term_count: int = 2,
    linkage: str = "ward",
) -> tuple[list[dict[str, str]], list[int], dict[int, list[tuple[str, float]]]]:
    """Run the full TF-IDF + hierarchical clustering pipeline."""
    rows = load_statements(csv_path)
    docs = [r.get("statement", "") for r in rows]
    tfidf, _ = build_tfidf_matrix(docs, min_term_count=min_term_count)
    labels = hierarchical_clusters(tfidf, k=k, linkage=linkage)
    terms = top_terms_by_cluster(docs, labels)
    return rows, labels, terms


def plot_cluster_heatmaps(
    rows: Sequence[dict[str, str]],
    labels: Sequence[int],
    output_path: Path,
) -> Path:
    """Save a 2-panel heatmap comparing semantic clusters vs. sections and Lean views."""
    import matplotlib.pyplot as plt

    cids, sections, sec_grid = section_crosstab(rows, labels)
    _, views, view_grid = lean_view_crosstab(rows, labels)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12.5, 4.6), gridspec_kw={"width_ratios": [1.8, 1.0]})

    for ax, grid, xlabels, title in [
        (ax1, sec_grid, sections, "Semantic Clusters vs. Dissertation Sections"),
        (ax2, view_grid, views, "Semantic Clusters vs. Lean 4 Graph Views"),
    ]:
        im = ax.imshow(grid, aspect="auto", cmap="viridis")
        ax.set_xticks(range(len(xlabels)))
        ax.set_xticklabels(xlabels, rotation=45, ha="right", fontsize=8.5)
        ax.set_yticks(range(len(cids)))
        ax.set_yticklabels([f"C{c} (n={int(grid[i].sum())})" for i, c in enumerate(cids)], fontsize=9)
        ax.set_title(title, fontsize=11, pad=8)
        for i in range(grid.shape[0]):
            for j in range(grid.shape[1]):
                val = int(grid[i, j])
                if val > 0:
                    color = "black" if val > grid.max() * 0.6 else "white"
                    ax.text(j, i, str(val), ha="center", va="center", color=color, fontsize=8, fontweight="bold")
        fig.colorbar(im, ax=ax, fraction=0.046, pad=0.04)

    plt.tight_layout()
    output_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output_path, dpi=180, bbox_inches="tight")
    plt.close(fig)
    return output_path


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--k", type=int, default=6, help="number of clusters (default: 6)")
    parser.add_argument(
        "--linkage",
        choices=("ward", "complete", "average"),
        default="ward",
        help="agglomerative linkage method (default: ward)",
    )
    parser.add_argument("--min-term-count", type=int, default=2, help="minimum corpus term count")
    parser.add_argument("--top-terms", type=int, default=8, help="distinctive terms shown per cluster")
    parser.add_argument("--plot", type=Path, default=None, help="optional path to save heatmap PNG")
    args = parser.parse_args(argv)

    rows, labels, terms = cluster_statements(
        k=args.k, min_term_count=args.min_term_count, linkage=args.linkage
    )
    cids, views, view_grid = lean_view_crosstab(rows, labels)

    print(
        f"Clustered {len(rows)} dissertation statements into k={args.k} "
        f"TF-IDF ({args.linkage}) clusters:\n"
    )
    for i, cid in enumerate(cids):
        size = sum(1 for c in labels if c == cid)
        top_str = ", ".join(tok for tok, _ in terms[cid][: args.top_terms])
        v_dist = ", ".join(
            f"{views[j]}:{int(view_grid[i, j])}"
            for j in range(len(views))
            if view_grid[i, j] > 0
        )
        print(f"  Cluster {cid} (n={size:2d}) | Views: {v_dist}")
        print(f"    Top TF-IDF terms: {top_str}")

    if args.plot is not None:
        saved = plot_cluster_heatmaps(rows, labels, args.plot)
        print(f"\nSaved heatmap to {saved}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
