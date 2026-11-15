"""Verify data/theorems.yml stays synchronized with Lean 4 and Python sources."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
THEOREMS_PATH = ROOT / "data" / "theorems.yml"


def _load_script(name: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


registry = _load_script("sync_theorem_registry")


def test_registry_has_required_fields():
    theorems = yaml.safe_load(THEOREMS_PATH.read_text(encoding="utf-8"))["theorems"]
    assert len(theorems) >= 7
    for entry in theorems:
        for field in ("id", "dissertation_ref", "title", "statement", "python_ref",
                      "python_url", "status", "preset"):
            assert entry.get(field), f"{entry.get('id')}: missing {field}"


def test_registry_symbols_exist_and_links_are_current():
    """Every Lean/Python symbol exists and every URL points at its declaration line.

    If this fails only because line numbers drifted, run
    ``python scripts/sync_theorem_registry.py`` to rewrite the anchors.
    """
    errors, fixes = registry.check()
    assert not errors, "\n".join(errors)
    stale = [f"{i}.{f} -> {u}" for i, fs in fixes.items() for f, u in fs.items()]
    assert not stale, "Stale registry links (run scripts/sync_theorem_registry.py):\n" + "\n".join(stale)


def test_split_refs_handles_multiple_symbols():
    assert registry.split_refs("a / b") == ["a", "b"]
    assert registry.python_name("MixedSignCoxeterGraph.A_n([1, 1, -1])") == "A_n"
    assert registry.python_name("principal_search.alternating_square") == "alternating_square"


def test_lean_links_in_prose_pages_point_at_declarations():
    """README, website pages and the writeup link Lean names to the right lines.

    Run ``python scripts/sync_theorem_registry.py`` to refresh drifted anchors.
    """
    stale = registry.check_docs()
    assert not stale, "\n".join(f"{p.name}: {n}" for p, ns in stale.items() for n in ns)
