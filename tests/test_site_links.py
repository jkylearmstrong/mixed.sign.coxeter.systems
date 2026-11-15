"""Unit tests for scripts/check_site_links.py (run on the rendered site in CI)."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("check_site_links", ROOT / "scripts" / "check_site_links.py")
links = importlib.util.module_from_spec(spec)
sys.modules["check_site_links"] = links
spec.loader.exec_module(links)


def test_flags_links_outside_site_and_missing_files(tmp_path: Path):
    site = tmp_path / "docs"
    (site / "assets").mkdir(parents=True)
    (site / "assets" / "logo.png").write_bytes(b"")
    (tmp_path / "assets").mkdir()
    (site / "index.html").write_text(
        '<img src="assets/logo.png"><img src="../assets/logo.png">'
        '<a href="missing.html#x">x</a><a href="https://example.org">e</a>'
        '<a href="#top">t</a><a href="mailto:a@b.c">m</a>',
        encoding="utf-8",
    )
    problems = links.broken_links(site)
    assert problems == [
        "index.html: ../assets/logo.png points outside the published site",
        "index.html: missing.html#x does not exist",
    ]


def test_site_sources_do_not_link_outside_the_project():
    """Quarto copies only files inside website/, so ``../`` links 404 on Pages."""
    import re

    for path in [*(ROOT / "website").glob("*.qmd"), ROOT / "website" / "_quarto.yml"]:
        text = path.read_text(encoding="utf-8")
        text = re.sub(r"(?s)```\{python\}.*?```", "", text)  # code may read ../src etc.
        text = text.replace("output-dir: ../docs", "")
        assert "../" not in text, f"{path.name} links outside website/"
