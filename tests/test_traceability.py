"""Verify data/theorems.yml stays synchronized with Lean 4 and Python sources."""

from __future__ import annotations

from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
THEOREMS_PATH = ROOT / "data" / "theorems.yml"
LEAN_DIR = ROOT / "lean" / "MixedSignCoxeter"
PY_DIR = ROOT / "src" / "mixed_sign_coxeter"


def test_theorems_registry_matches_lean_and_python():
    data = yaml.safe_load(THEOREMS_PATH.read_text(encoding="utf-8"))
    theorems = data["theorems"]
    assert len(theorems) >= 7

    lean_corpus = "\n".join(
        p.read_text(encoding="utf-8") for p in LEAN_DIR.glob("*.lean")
    )
    py_corpus = "\n".join(p.read_text(encoding="utf-8") for p in PY_DIR.glob("*.py"))

    for entry in theorems:
        lean_sym = entry.get("lean_symbol", "")
        if lean_sym and lean_sym != "—":
            assert lean_sym in lean_corpus, f"Missing Lean symbol {lean_sym!r}"

        py_url = entry.get("python_url", "")
        assert py_url, f"Missing python_url for {entry['id']}"
        # Check at least one identifier from python_ref appears in src/mixed_sign_coxeter
        py_ref = entry["python_ref"].split("(")[0].split("/")[0].split(".")[-1].strip()
        assert py_ref in py_corpus, f"Missing Python symbol {py_ref!r}"
