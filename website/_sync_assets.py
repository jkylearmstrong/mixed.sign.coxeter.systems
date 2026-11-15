"""Quarto pre-render hook: copy the shared ``assets/`` folder into the site.

The Quarto project lives in ``website/`` and renders to ``../docs``.  Quarto only
publishes resources that sit *inside* the project directory, so links such as
``../assets/hex-sticker.png`` resolve outside the published site and 404 on
GitHub Pages.  The repository keeps a single canonical ``assets/`` folder at the
root (the README and the hex-sticker generator use it), and this hook mirrors
the files the site needs into ``website/assets/`` (git-ignored) before every
render, so pages can link to ``assets/...``.
"""

from __future__ import annotations

import shutil
from pathlib import Path

WEBSITE = Path(__file__).resolve().parent
SOURCE = WEBSITE.parent / "assets"
TARGET = WEBSITE / "assets"
PATTERNS = ("*.png", "*.svg", "slides/*.mp4")


def sync() -> list[Path]:
    copied = []
    for pattern in PATTERNS:
        for src in sorted(SOURCE.glob(pattern)):
            dst = TARGET / src.relative_to(SOURCE)
            if dst.exists() and dst.stat().st_size == src.stat().st_size \
                    and dst.stat().st_mtime >= src.stat().st_mtime:
                continue
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dst)
            copied.append(dst)
    return copied


if __name__ == "__main__":
    for path in sync():
        print(f"synced {path.relative_to(WEBSITE)}")
