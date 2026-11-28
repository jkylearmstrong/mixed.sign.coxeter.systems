"""Tests for scripts/statement_clusters.py (TF-IDF statement clustering)."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def _load(name: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / f"{name}.py")
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


sc = _load("statement_clusters")


def test_cluster_statements_partitions_all_107_items():
    rows, labels, terms = sc.cluster_statements(k=6)
    assert len(rows) == 107
    assert len(labels) == 107
    assert set(labels) == {1, 2, 3, 4, 5, 6}
    assert set(terms.keys()) == {1, 2, 3, 4, 5, 6}
    assert all(len(v) > 0 for v in terms.values())


def test_section_and_lean_view_crosstabs_sum_to_total():
    rows, labels, _ = sc.cluster_statements(k=6)
    _, sections, sec_grid = sc.section_crosstab(rows, labels)
    _, views, view_grid = sc.lean_view_crosstab(rows, labels)
    assert len(sections) > 0
    assert sec_grid.sum() == len(rows)
    assert view_grid.sum() == len(rows)
    assert "V1" in views


def test_complete_linkage_is_deterministic():
    _, labels1, _ = sc.cluster_statements(k=4)
    _, labels2, _ = sc.cluster_statements(k=4)
    assert labels1 == labels2
