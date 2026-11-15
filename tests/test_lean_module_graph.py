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
    """Every import is drawn exactly once: inside a view, or on an overview edge."""
    imports = graph.module_imports()
    block = graph.render(imports)
    where = graph.view_of(imports)
    for mod, deps in imports.items():
        for dep in deps:
            if where[dep] == where[mod]:
                assert block.count(f"  {dep} --> {mod}\n") == 1
            else:
                assert block.count(f"{dep} → {mod}") == 1
    assert block.count(" --> ") == sum(1 for m, ds in imports.items() for d in ds if where[d] == where[m])


def test_each_module_is_drawn_once():
    block = graph.render(graph.module_imports())
    for mod in graph.module_imports():
        assert block.count(f'  {mod}["') == 1
