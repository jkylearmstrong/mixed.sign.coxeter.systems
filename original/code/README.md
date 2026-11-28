# Extraction pipeline — "Principal Elements of Mixed-Sign Coxeter Systems" (J.K. Armstrong, FSU 2012)

This package contains the exact code used to extract all 107 numbered mathematical
statements (with proofs, pages and sections) from the dissertation PDF into:

    mixed_sign_coxeter_statements.csv   (107 rows, columns: number, type, statement, page, section, proof)

## Contents

```
code/
├── slice_items.py      # Step 1: PDF -> items_raw.json  (font-based state machine)
├── prep_chunks.py      # Step 2: split items into transcription chunks
├── write_ch1.py        # Step 3a: Chapter 1 transcription (7 items, hand-transcribed)
├── fix_notation.py     # Step 4: batch notation corrections on the clean JSON
├── audit_notation.py   # Step 5: QA helper (find suspicious notation patterns)
├── assemble_csv.py     # Step 6: merge, clean, sort, write CSV + full QA
├── data/
│   ├── items_raw.json        # output of Step 1 (107 items, raw text)
│   ├── clean_ch1.json        # transcribed items, Chapter 1 (7)
│   ├── clean_ch2a.json       # transcribed items, 2.1-2.35 (35)
│   ├── clean_ch2b.json       # transcribed items, 2.36-2.65 (30)
│   ├── clean_ch3a.json       # transcribed items, 3.1-3.20 (20)
│   └── clean_ch3b.json       # transcribed items, 3.21-3.35 (15)
└── README.md
```

The `data/` folder is included so the final CSV can be regenerated from Step 6
onward without re-running the transcription step.

## Requirements

- Python 3.8+
- PyMuPDF (`pip install pymupdf`)
- The dissertation PDF at the path hard-coded in each script
  (`/home/z/my-project/upload/FSU_migr_etd-4697.pdf`). Adjust the
  `PDF` / `BASE` / `OUT` path constants at the top of each script if you
  run it elsewhere — paths were written for the original sandbox and are
  absolute on purpose.

## Pipeline order

```
PDF ──slice_items.py──> items_raw.json ──prep_chunks.py──> chunks/*.json
    ──(transcription: clean_*.json; ch1 via write_ch1.py)──
    ──fix_notation.py──> audit_notation.py ──assemble_csv.py──> final CSV
```

| Step | Script | Input -> Output |
|------|--------|-----------------|
| 1 | `slice_items.py` | PDF -> `work/items_raw.json` |
| 2 | `prep_chunks.py` | `items_raw.json` -> `work/chunks/ch{1,2a,2b,3a,3b}.json` |
| 3 | transcription (AI-assisted, PDF-grounded) + `write_ch1.py` | chunks -> `work/clean_*.json` |
| 4 | `fix_notation.py` | `clean_*.json` (in place, ~30 fixes) |
| 5 | `audit_notation.py` | read-only pattern audit |
| 6 | `assemble_csv.py` | `clean_*.json` -> final CSV + QA report |

To regenerate the CSV from the included data only:

```bash
# edit BASE in assemble_csv.py to point at ./data/ (i.e. the included JSONs)
python assemble_csv.py
```

## How the extraction works (Step 1)

The dissertation is typeset in Computer Modern, which makes the layout
machine-readable through span fonts. `slice_items.py` walks every line of
every page and classifies it by the font of its first span:

| Signal | Meaning |
|--------|---------|
| `CMBX` first span matching `^\w+ \d+\.\d+(\(title\))?\.` | item header (Theorem 2.38., Definition 2.3., ...) |
| `CMBX12` line following a `d.d`-style line | section title text |
| `CMTI` line starting with `Proof` | proof header |
| `■` (font MSAM10, right margin) | QED tombstone — end of proof |
| line at `y0 > 700`, centered, all digits | footer page number |

Other implementation details worth knowing:

- **Page mapping**: printed page = PDF page − 11 for PDF pages 12–78; the
  script verifies this on every page and reports mismatches.
- **Ligature normalization**: `\ufb00`–`\ufb04` (ff, fi, fl, ffi, ffl) are
  expanded. Without this, "Definition" appears as "Deﬁnition" and item
  headers are missed — this was the #1 silent-failure bug.
- **`sort=False`** in `get_text('dict')`: PyMuPDF re-orders spans by default,
  which scrambles multi-segment display formulas.
- **State machine**: a `collect` region tracks whether subsequent lines belong
  to a statement or to a proof; the QED tombstone or the next header closes it.
- **Validation**: after the walk it checks each chapter for gaps/missing
  numbers (Ch1: 1–7, Ch2: 1–65, Ch3: 1–35 — none missing).

## Transcription step (Step 3)

Raw PDF text keeps the linearized math of a two-column-era LaTeX file
(e.g. matrices spilled across lines, `A_1-` for `\Gamma_{-}`). The raw items
were transcribed into LaTeX-style inline math by reading the PDF pages for
each chunk and cross-checking ambiguous glyphs against their font/size/baseline
data. Chapter 1 (7 items) was fully hand-verified and lives in
`write_ch1.py` as a literal. The five `clean_*.json` files are the final
transcription results and are included so this step does not need repeating.

Notation conventions used in the CSV:

- LaTeX-style inline math without `$` delimiters (`\Gamma_{-}`, `s_1 s_2 \cdots s_n`, `\mathcal{O}`).
- Block matrices inlined as `[A, B; C, D]` (rows separated by `;`).
- Display formulas folded inline; multi-line alignment collapsed to one line.
- Original spelling kept as printed (e.g. "Sylvesters criterion"), typos not corrected.
- Text physically present after a proof's tombstone but not part of the proof is excluded.

## Notation fixes applied (Step 4, `fix_notation.py`)

Verified against glyph coordinates (minus sign at 8 pt below the baseline =
subscript, not superscript):

- `\widetilde{A}^{-n}` -> `\widetilde{A}_{-n}` (and `-2`, `-4`, `-(n)` variants)
- `\Gamma^-` -> `\Gamma_{-}`
- stray `]` after `A_n(+, -)` graph names removed
- standalone group symbol `\mathcal{O}` vs plain `O(V)` disambiguated (rendered-page check)
- dangling meta-sentence trimmed from 2.43

## QA (Step 6, built into `assemble_csv.py`)

The assembler re-opens the written CSV and checks: duplicates, empty
statements/sections, malformed page numbers, newline or non-ASCII characters
in cells, leftover artifacts (■, TODO, XXX, undefined, NaN, 【, U+FFFD), and
numbering completeness per chapter. It prints `problems: NONE` on the final
run and also prints sample rows (including 2.38) for spot-checking.
