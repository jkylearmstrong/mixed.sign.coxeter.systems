"""Static soundness checks on the Lean 4 sources.

``lake build`` succeeds even when a proof uses ``sorry`` (it only warns), so the
"sorry-free" claim on the website is enforced here: no ``sorry``/``admit``, no
new ``axiom`` declarations, and no ``native_decide`` (which trusts the compiler).
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
LEAN_FILES = sorted((ROOT / "lean" / "MixedSignCoxeter").glob("*.lean")) + [
    ROOT / "lean" / "MixedSignCoxeter.lean"
]


def strip_comments_and_strings(text: str) -> str:
    """Remove nested ``/- ... -/`` block comments, ``--`` line comments and strings."""
    out, depth, i = [], 0, 0
    while i < len(text):
        two = text[i:i + 2]
        if two == "/-":
            depth += 1
            i += 2
        elif two == "-/" and depth:
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif two == "--":
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            j = i + 1
            while j < len(text) and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


FORBIDDEN = re.compile(r"(?<![\w.'])(sorry|admit|native_decide)(?![\w'])|^\s*(?:private\s+)?axiom\s", re.M)


@pytest.mark.parametrize("path", LEAN_FILES, ids=lambda p: p.name)
def test_no_sorry_admit_or_axiom(path: Path):
    code = strip_comments_and_strings(path.read_text(encoding="utf-8"))
    hits = [m.group(0).strip() for m in FORBIDDEN.finditer(code)]
    assert not hits, f"{path.name} contains {hits}"


def test_comment_stripper():
    assert "sorry" not in strip_comments_and_strings("/- a /- sorry -/ b -/ x -- sorry\n\"sorry\"")
