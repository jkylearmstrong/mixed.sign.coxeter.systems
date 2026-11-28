#!/usr/bin/env python3
"""Audit and fix notation in clean JSON files: Gamma/tilde subscripts, stray brackets, O calligraphic."""
import json
import re
from collections import Counter

FILES = ['clean_ch2a.json', 'clean_ch2b.json', 'clean_ch3a.json', 'clean_ch3b.json']
BASE = '/home/z/my-project/work/'

c = Counter()
for n in FILES:
    arr = json.load(open(BASE + n))
    for it in arr:
        for f in ['statement', 'proof']:
            txt = it[f]
            for m in re.findall(r'\\Gamma[\^_]\{?[^ }\)]{0,4}\}?', txt):
                c[m] += 1
            for m in re.findall(r'\\widetilde\{A\}[\^_]\{?[^ }\)]{0,6}\}?', txt):
                c[m] += 1
            if re.search(r'\]', txt):
                for m in re.findall(r'A_[^\s]*\)\]', txt):
                    c['STRAY_BRACKET ' + m] += 1
            for m in re.findall(r'\bO\b(?![a-zA-Z])', txt):
                pass
print('notation counts:')
for k, v in c.most_common(30):
    print(f'  {v:3d}  {k}')

# occurrences of plain standalone O (as the orthogonal group) per item
print()
print('plain O occurrences (candidate for mathcal):')
for n in FILES:
    arr = json.load(open(BASE + n))
    for it in arr:
        for f in ['statement', 'proof']:
            txt = it[f]
            for m in re.finditer(r'(?<![\\a-zA-Z])O(?![a-zA-Z])', txt):
                ctx = txt[max(0, m.start() - 45):m.end() + 35]
                print(f'  {n[6:12]} {it["number"]} {f}: ...{ctx}...')
