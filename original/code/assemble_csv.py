#!/usr/bin/env python3
"""Assemble final CSV: number, type, statement, page, section, proof. With full QA."""
import csv
import json
import re

BASE = '/home/z/my-project/work/'
OUT = '/home/z/my-project/download/mixed_sign_coxeter_statements.csv'

FILES = ['clean_ch1.json', 'clean_ch2a.json', 'clean_ch2b.json', 'clean_ch3a.json', 'clean_ch3b.json']

SECTIONS = {
    '1': 'Introduction',
    '1.1': 'Classical Coxeter Systems', '1.2': 'Reflection Systems',
    '1.3': 'Mixed-sign Coxeter systems', '1.4': 'Main results', '1.5': 'Organization',
    '2': 'Reflection systems', '2.1': 'Basic definitions and properties', '2.2': 'Relations in W',
    '2.3': 'Conjugate reflection systems and reflection diagrams',
    '2.4': 'Bipartite orderings and proof of Theorem 1.4', '2.5': 'Classification',
    '2.5.1': 'Irreducible reflection systems', '2.5.2': 'Classification by signature',
    '2.6': 'Principal elements', '2.6.1': 'Proof of Theorem 1.1', '2.6.2': 'Principal polynomials',
    '3': 'Mixed-sign Coxeter systems (chapter introduction)',
    '3.1': 'Root systems of rank 2 mixed-sign Coxeter systems',
    '3.1.1': 'Positive node case', '3.1.2': 'Negative node case', '3.1.3': 'Mixed-sign case',
    '3.2': 'Presentation of mixed-sign Coxeter groups',
    '3.3': 'The Deletion Property and proof of Theorem 1.2',
    '3.4': 'Odd cycles with negative nodes', '3.5': 'Classification by principal elements',
    '3.5.1': 'Eigenvalues of principal elements in An-type mixed-sign Coxeter systems',
    '3.5.2': 'Bipartite principal elements',
}

def clean_cell(t):
    t = t.replace('\u201c', '"').replace('\u201d', '"').replace('\u2019', "'").replace('\u2018', "'")
    t = t.replace('\u2212', '-')
    t = re.sub(r' +', ' ', t).strip()
    t = re.sub(r' +([,.;:!?)])', r'\1', t)
    t = re.sub(r'\( +', '(', t)
    return t

items = []
for f in FILES:
    items += json.load(open(BASE + f))

# sort by chapter/num to guarantee document order
def key(n):
    ch, k = n.split('.')
    return (int(ch), int(k))
items.sort(key=lambda it: key(it['number']))

rows = []
for it in items:
    sec = it['section']
    sec_label = f"{sec} {SECTIONS.get(sec, '')}".strip()
    rows.append({
        'number': it['number'],
        'type': it['type'],
        'statement': clean_cell(it['statement']),
        'page': it['page'],
        'section': sec_label,
        'proof': clean_cell(it['proof']),
    })

with open(OUT, 'w', newline='', encoding='utf-8-sig') as fh:
    w = csv.DictWriter(fh, fieldnames=['number', 'type', 'statement', 'page', 'section', 'proof'])
    w.writeheader()
    w.writerows(rows)
print('wrote', OUT, 'with', len(rows), 'data rows')

# ---------------- QA ----------------
with open(OUT, 'r', encoding='utf-8-sig', newline='') as fh:
    rd = list(csv.DictReader(fh))
print('reopen: rows =', len(rd), '| cols =', list(rd[0].keys()))

problems = []
seen = set()
for r in rd:
    n = r['number']
    if n in seen:
        problems.append(f'{n}: duplicate')
    seen.add(n)
    if not r['statement'].strip():
        problems.append(f'{n}: empty statement')
    if not r['page'].strip().isdigit():
        problems.append(f'{n}: bad page {r["page"]!r}')
    if not r['section'].strip():
        problems.append(f'{n}: empty section')
    for f in ['number', 'type', 'statement', 'section', 'proof']:
        v = r[f]
        for bad in ['\u25a0', 'TODO', 'XXX', 'undefined', 'NaN', '\u3010', '\ufffd']:
            if bad in v:
                problems.append(f'{n}: artifact {bad!r} in {f}')
        if '\n' in v or '\r' in v:
            problems.append(f'{n}: newline in {f}')
        na = [c for c in v if ord(c) > 127]
        if na:
            problems.append(f'{n}: non-ascii {na!r} in {f}')

# completeness
nums = [r['number'] for r in rd]
for ch, mx in [(1, 7), (2, 65), (3, 35)]:
    have = sorted(int(n.split('.')[1]) for n in nums if n.startswith(f'{ch}.'))
    miss = sorted(set(range(1, mx + 1)) - set(have))
    if miss:
        problems.append(f'ch{ch} missing: {miss}')

print('problems:', problems if problems else 'NONE')

# sample rows
print()
for n in ['2.38', '1.1', '3.7']:
    r = next(x for x in rd if x['number'] == n)
    print(f"--- {n} | {r['type']} | p{r['page']} | {r['section']}")
    print('  stmt:', r['statement'][:220])
    print('  proof:', (r['proof'][:150] + '...') if len(r['proof']) > 150 else r['proof'])
