"""The Lean module diagrams on the website are generated from real imports."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def _load(name: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


graph = _load("lean_module_graph")


def test_every_module_is_placed_and_imported_by_root():
    assert graph.validate(graph.module_imports()) == []


def test_every_module_has_a_caption():
    assert set(graph.module_imports()) <= set(graph.LABELS)


def test_lean_verification_page_diagrams_are_current():
    """Run ``python scripts/lean_module_graph.py`` if this fails."""
    assert graph.main(["--check"]) == 0


def test_rendered_edges_match_imports():
    imports = graph.module_imports()
    block = graph.render(imports)
    for mod, deps in imports.items():
        for dep in deps:
            assert f"  {dep} --> {mod}" in block
    assert block.count(" --> ") == sum(len(d) for d in imports.values())
