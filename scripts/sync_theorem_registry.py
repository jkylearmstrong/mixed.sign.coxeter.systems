"""Keep ``data/theorems.yml`` source links pointing at the right lines.

Every registry entry links a dissertation result to a Lean 4 declaration
(``lean_symbol`` / ``lean_url``) and a Python implementation (``python_ref`` /
``python_url``).  Line anchors such as ``#L211`` drift whenever a source file is
edited, so this script recomputes them from the sources:

* ``lean_symbol`` may list several declarations separated by `` / ``; the URL
  points at the declaration of the first one, in whichever module defines it.
* ``python_ref`` may list several references separated by `` / ``; each is
  reduced to its last dotted component (``MixedSignCoxeterGraph.A_n([1, 1, -1])``
  becomes ``A_n``) and the URL points at the first matching ``def``/``class``.

Usage::

    python scripts/sync_theorem_registry.py          # rewrite anchors in place
    python scripts/sync_theorem_registry.py --check  # exit 1 if anything is stale

The same line anchors are refreshed in the prose pages listed in ``DOC_FILES``:
any Markdown link of the form ``[`lean_name`](.../SomeModule.lean#L123)`` is
re-pointed at the line where ``lean_name`` is declared.

``tests/test_traceability.py`` runs the check, so CI fails when an anchor drifts.
The YAML file is edited line by line so comments and formatting are preserved.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "data" / "theorems.yml"
LEAN_DIR = ROOT / "lean" / "MixedSignCoxeter"
PY_DIR = ROOT / "src" / "mixed_sign_coxeter"
REPO_BLOB = "https://github.com/jkylearmstrong/mixed.sign.coxeter.systems/blob/main/"

_LEAN_DECL = r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(?:private|protected|noncomputable)[ \t]+)*" \
    r"(?:theorem|lemma|def|abbrev|structure|instance|inductive)[ \t]+{name}(?![\w'.])"
DOC_FILES = [
    ROOT / "README.qmd",
    ROOT / "README.md",
    ROOT / "docs" / "mixed_sign_coxeter.qmd",
    ROOT / "docs" / "verifications.md",
    *sorted((ROOT / "website").glob("*.qmd")),
]
_DOC_LINK = re.compile(
    r"\[`([\w'.]+)`\]\(" + re.escape(REPO_BLOB) + r"(lean/MixedSignCoxeter/\w+\.lean)(?:#L(\d+))?\)"
)
_PY_DECL = r"(?m)^[ \t]*(?:def|class)[ \t]+{name}\b"


@dataclass(frozen=True)
class Location:
    path: Path
    line: int

    def url(self) -> str:
        return f"{REPO_BLOB}{self.path.relative_to(ROOT).as_posix()}#L{self.line}"


def split_refs(value: str) -> list[str]:
    return [part.strip() for part in value.split(" / ") if part.strip()]


def python_name(ref: str) -> str:
    """``MixedSignCoxeterGraph.A_n([1, 1, -1])`` -> ``A_n``."""
    return ref.split("(")[0].strip().split(".")[-1]


def find_decl(name: str, files: list[Path], pattern: str) -> Location | None:
    regex = re.compile(pattern.format(name=re.escape(name)))
    for path in files:
        text = path.read_text(encoding="utf-8")
        match = regex.search(text)
        if match:
            line = text.count("\n", 0, match.start()) + 1
            # The regex may start on a blank line consumed by ``^[ \t]*``.
            while not text.splitlines()[line - 1].strip():
                line += 1
            return Location(path, line)
    return None


def lean_files() -> list[Path]:
    return sorted(LEAN_DIR.glob("*.lean"))


def python_files() -> list[Path]:
    return sorted(PY_DIR.glob("*.py"))


def expected_urls(entry: dict) -> tuple[dict[str, str], list[str]]:
    """Return ``({field: expected_url}, [errors])`` for one registry entry."""
    expected: dict[str, str] = {}
    errors: list[str] = []
    ident = entry.get("id", "?")

    lean_symbol = (entry.get("lean_symbol") or "").strip()
    if lean_symbol and lean_symbol != "—":
        locations = []
        for sym in split_refs(lean_symbol):
            loc = find_decl(sym, lean_files(), _LEAN_DECL)
            if loc is None:
                errors.append(f"{ident}: Lean declaration {sym!r} not found in {LEAN_DIR.name}/")
            locations.append(loc)
        if locations and locations[0] is not None:
            expected["lean_url"] = locations[0].url()
    elif entry.get("lean_url"):
        errors.append(f"{ident}: lean_url set but lean_symbol is empty")

    python_ref = (entry.get("python_ref") or "").strip()
    if not python_ref:
        errors.append(f"{ident}: missing python_ref")
    else:
        found = None
        for ref in split_refs(python_ref):
            loc = find_decl(python_name(ref), python_files(), _PY_DECL)
            if loc is None:
                errors.append(f"{ident}: Python definition {python_name(ref)!r} not found")
            elif found is None:
                found = loc
        if found is not None:
            expected["python_url"] = found.url()
    return expected, errors


def check(registry: Path = REGISTRY) -> tuple[list[str], dict[str, dict[str, str]]]:
    data = yaml.safe_load(registry.read_text(encoding="utf-8"))
    errors: list[str] = []
    fixes: dict[str, dict[str, str]] = {}
    seen: set[str] = set()
    for entry in data["theorems"]:
        ident = entry.get("id", "?")
        if ident in seen:
            errors.append(f"duplicate id {ident!r}")
        seen.add(ident)
        expected, entry_errors = expected_urls(entry)
        errors.extend(entry_errors)
        for field, url in expected.items():
            if entry.get(field) != url:
                fixes.setdefault(ident, {})[field] = url
    return errors, fixes


def apply_fixes(fixes: dict[str, dict[str, str]], registry: Path = REGISTRY) -> None:
    lines = registry.read_text(encoding="utf-8").splitlines(keepends=True)
    current = None
    for i, line in enumerate(lines):
        m = re.match(r"^\s*-\s+id:\s*(\S+)", line)
        if m:
            current = m.group(1).strip("\"'")
            continue
        m = re.match(r'^(\s*)(lean_url|python_url):', line)
        if m and current in fixes and m.group(2) in fixes[current]:
            lines[i] = f'{m.group(1)}{m.group(2)}: "{fixes[current][m.group(2)]}"\n'
    registry.write_text("".join(lines), encoding="utf-8")


def sync_doc_links(text: str) -> tuple[str, list[str]]:
    """Re-point ``[`name`](...Module.lean#Lnn)`` links at ``name``'s declaration."""
    notes: list[str] = []

    def repl(match: re.Match) -> str:
        name, path, line = match.groups()
        loc = find_decl(name, lean_files(), _LEAN_DECL)
        if loc is None:
            if line:  # anchored link to a symbol that no longer exists
                notes.append(f"Lean declaration {name!r} not found (linked as {path}#L{line})")
            return match.group(0)
        new = f"[`{name}`]({loc.url()})"
        if line is None and loc.path.relative_to(ROOT).as_posix() == path:
            return match.group(0)  # un-anchored link to the right file: leave it
        if new != match.group(0):
            notes.append(f"{name}: {path}#L{line} -> {loc.url()[len(REPO_BLOB):]}")
        return new

    return _DOC_LINK.sub(repl, text), notes


def check_docs() -> dict[Path, list[str]]:
    stale = {}
    for path in DOC_FILES:
        if path.exists():
            text = path.read_text(encoding="utf-8")
            new, notes = sync_doc_links(text)
            if notes:
                stale[path] = notes
    return stale


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true", help="report stale links, do not write")
    args = parser.parse_args(argv)

    errors, fixes = check()
    for err in errors:
        print(f"error: {err}", file=sys.stderr)
    for ident, fields in fixes.items():
        for field, url in fields.items():
            print(f"{'stale' if args.check else 'fixed'}: {ident}.{field} -> {url}")
    if not args.check and fixes:
        apply_fixes(fixes)
    doc_stale = check_docs()
    for path, notes in doc_stale.items():
        for note in notes:
            print(f"{'stale' if args.check else 'fixed'}: {path.relative_to(ROOT)}: {note}")
        if not args.check:
            path.write_text(sync_doc_links(path.read_text(encoding="utf-8"))[0], encoding="utf-8")
    return 1 if errors or (args.check and (fixes or doc_stale)) else 0


if __name__ == "__main__":
    raise SystemExit(main())
