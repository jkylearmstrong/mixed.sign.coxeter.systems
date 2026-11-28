#!/usr/bin/env python3
"""Apply notation fixes to clean JSON files (subscript tildes/Gamma-minus, calligraphic O, stray brackets, 2.43 trim)."""
import json

BASE = '/home/z/my-project/work/'
FILES = ['clean_ch2a.json', 'clean_ch2b.json', 'clean_ch3a.json', 'clean_ch3b.json']

# global replacements (verified via glyph positions: minus is subscript in A-tilde/A-minus and Gamma-minus)
GLOBAL = [
    ('\\widetilde{A}^{-2}', '\\widetilde{A}_{-2}'),
    ('\\widetilde{A}^{-n}', '\\widetilde{A}_{-n}'),
    ('\\widetilde{A}^{-4}', '\\widetilde{A}_{-4}'),
    ('\\widetilde{A}^{-(n)}', '\\widetilde{A}_{-(n)}'),
    ('\\widetilde{A}^{-}_n', '\\widetilde{A}_{-n}'),
    ('\\Gamma^-', '\\Gamma_{-}'),
]

import re
def fix_text(t):
    for a, b in GLOBAL:
        t = t.replace(a, b)
    # stray ']' right after graph name parens, e.g. 'A_2(+, -)]'
    t = re.sub(r'(A_\d\(\s*[+-],\s*[+-]\s*\))\]', r'\1', t)
    return t

count = 0
for n in FILES:
    arr = json.load(open(BASE + n))
    for it in arr:
        for f in ['statement', 'proof', 'notes']:
            new = fix_text(it[f])
            if new != it[f]:
                count += 1
                it[f] = new

# targeted calligraphic O fixes (standalone subgroup O; O(V) stays plain)
targeted = {
    ('clean_ch2a.json', '2.8', 'statement'): [
        ('We use O for the subgroup of O(V)', 'We use \\mathcal{O} for the subgroup of O(V)'),
    ],
    ('clean_ch2a.json', '2.29', 'statement'): [
        ('P \\in O with', 'P \\in \\mathcal{O} with'),
        ('The set O is precisely', 'The set \\mathcal{O} is precisely'),
    ],
    ('clean_ch2a.json', '2.30', 'statement'): [
        ('P \\in O then', 'P \\in \\mathcal{O} then'),
    ],
    ('clean_ch2a.json', '2.32', 'statement'): [
        ('P \\in O then', 'P \\in \\mathcal{O} then'),
    ],
    ('clean_ch2a.json', '2.32', 'proof'): [
        ('Let P \\in O with', 'Let P \\in \\mathcal{O} with'),
        ('since P \\in O then', 'since P \\in \\mathcal{O} then'),
    ],
}
for (fn, num, field), reps in targeted.items():
    arr = json.load(open(BASE + fn))
    it = next(x for x in arr if x['number'] == num)
    for a, b in reps:
        if a not in it[field]:
            print('WARN: not found:', fn, num, field, a[:40])
        else:
            it[field] = it[field].replace(a, b)
            count += 1
    json.dump(arr, open(BASE + fn, 'w'), indent=1, ensure_ascii=False)

# re-dump all files with fixes
for n in FILES:
    arr = json.load(open(BASE + n))
    for it in arr:
        for f in ['statement', 'proof', 'notes']:
            it[f] = fix_text(it[f])
    json.dump(arr, open(BASE + n, 'w'), indent=1, ensure_ascii=False)

# trim dangling meta-sentence in 2.43
arr = json.load(open(BASE + 'clean_ch2b.json'))
it = next(x for x in arr if x['number'] == '2.43')
marker = ' Theorem 1.4, which states that'
if marker in it['statement']:
    it['statement'] = it['statement'].split(marker)[0].rstrip()
    it['notes'] = (it['notes'] + '; ' if it['notes'] else '') + 'dangling Theorem 1.4 restatement sentence dropped'
    count += 1
json.dump(arr, open(BASE + 'clean_ch2b.json', 'w'), indent=1, ensure_ascii=False)

print('applied', count, 'fixes')
# verify leftovers
bad = 0
for n in FILES:
    arr = json.load(open(BASE + n))
    for it in arr:
        for f in ['statement', 'proof']:
            if '\\Gamma^-' in it[f] or '\\widetilde{A}^{-' in it[f]:
                print('LEFTOVER:', n, it['number'])
                bad += 1
print('leftovers:', bad)
