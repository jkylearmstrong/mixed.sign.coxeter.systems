"""Fail if the rendered site links to local files that are not published.

GitHub Pages serves ``docs/`` under ``/mixed.sign.coxeter.systems/``, so any
``href``/``src`` that resolves outside ``docs/`` (for example ``../assets/...``)
or to a missing file is a 404 for visitors.  Run after ``quarto render website``::

    python scripts/check_site_links.py            # checks docs/
    python scripts/check_site_links.py path/to/site
"""

from __future__ import annotations

import re
import sys
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parent.parent
ATTR = re.compile(r"""(?:href|src|poster|data-src)\s*=\s*["']([^"']+)["']""", re.I)
EXTERNAL = re.compile(r"^(?:[a-z][a-z0-9+.-]*:|//|#)", re.I)


def broken_links(site: Path) -> list[str]:
    site = site.resolve()
    problems = []
    for page in sorted(site.glob("*.html")):
        html = page.read_text(encoding="utf-8", errors="replace")
        for ref in sorted(set(ATTR.findall(html))):
            if EXTERNAL.match(ref) or "{" in ref:
                continue
            path = unquote(urlsplit(ref).path)
            if not path:
                continue
            target = (page.parent / path).resolve()
            if site not in target.parents and target != site:
                problems.append(f"{page.name}: {ref} points outside the published site")
            elif not target.exists():
                problems.append(f"{page.name}: {ref} does not exist")
    return problems


def main(argv: list[str]) -> int:
    site = Path(argv[0]) if argv else ROOT / "docs"
    problems = broken_links(site)
    for problem in problems:
        print(problem, file=sys.stderr)
    print(f"checked {len(list(site.glob('*.html')))} pages: {len(problems)} broken links")
    return 1 if problems else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
