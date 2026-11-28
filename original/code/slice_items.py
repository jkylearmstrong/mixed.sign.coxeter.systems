#!/usr/bin/env python3
"""Slice numbered mathematical items (with statements/proofs) from the FSU dissertation PDF.

Output: /home/z/my-project/work/items_raw.json
"""
import fitz
import re
import json
from collections import defaultdict

PDF = '/home/z/my-project/upload/FSU_migr_etd-4697.pdf'
OUT = '/home/z/my-project/work/items_raw.json'

TYPES = r'(Definition|Remark|Example|Proposition|Lemma|Corollary|Theorem|Conjecture|Notation|Property|Question)'
HEADER_RE = re.compile(r'^\s*' + TYPES + r'\s+(\d+)\.(\d+)\s*(?:\(([^)]*)\))?\s*\.\s*(.*)$')
SECTION_RE = re.compile(r'^\s*(\d+)\.(\d+)(?:\.(\d+))?\s*$')
CHAPTER_RE = re.compile(r'^\s*(CHAPTER\s+\d+|APPENDIX\s+[A-D]|Bibliography|Biographical\s+Sketch|ACKNOWLEDGMENTS|ABSTRACT)\s*$', re.I)
PROOF_RE = re.compile(r'^\s*Proof\b(?:\.|\s+of\b)')

doc = fitz.open(PDF)
lines = []
printed_by_pdf = {}

LIG = {'\ufb00': 'ff', '\ufb01': 'fi', '\ufb02': 'fl', '\ufb03': 'ffi', '\ufb04': 'ffl'}
PUA = re.compile(r'[\uf800-\uf8ff]')

def normalize(s):
    for k, v in LIG.items():
        s = s.replace(k, v)
    s = PUA.sub('', s)
    return s

for pno in range(len(doc)):
    d = doc[pno].get_text('dict')
    page_lines = []
    footer_num = None
    for b in d['blocks']:
        if b['type'] != 0:
            continue
        for l in b['lines']:
            spans = [(s['font'], normalize(s['text'])) for s in l['spans']]
            text = ''.join(t for _, t in spans)
            if not text.strip():
                continue
            page_lines.append({'spans': spans, 'text': text, 'y0': l['bbox'][1], 'x0': l['bbox'][0]})
    for ln in page_lines:
        t = ln['text'].strip()
        if ln['y0'] > 700 and 250 < ln['x0'] < 360 and re.fullmatch(r'\d{1,2}', t):
            footer_num = int(t)
    printed_by_pdf[pno + 1] = footer_num
    for ln in page_lines:
        if ln['y0'] > 700 and re.fullmatch(r'\d{1,2}', ln['text'].strip()):
            continue  # footer
        ln['pdf_page'] = pno + 1
        ln['printed'] = footer_num
        lines.append(ln)

bad = [(p, v) for p, v in printed_by_pdf.items() if 12 <= p <= 78 and v != p - 11]
print('page mapping mismatches:', bad)

for ln in lines:
    t = ln['text']
    f0 = ln['spans'][0][0]
    ln['kind'] = 'text'
    if CHAPTER_RE.match(t) and f0.startswith('CMBX'):
        ln['kind'] = 'chapter'
        continue
    m = SECTION_RE.match(t)
    if m and f0.startswith('CMBX'):
        ln['kind'] = 'section'
        ln['secnum'] = f"{m.group(1)}.{m.group(2)}" + (f".{m.group(3)}" if m.group(3) else '')
        continue
    m = HEADER_RE.match(t)
    if m and f0.startswith('CMBX'):
        ln['kind'] = 'item'
        ln['item'] = {
            'type': m.group(1),
            'number': f"{m.group(2)}.{m.group(3)}",
            'title': (m.group(4) or '').strip(),
            'first': (m.group(5) or '').strip(),
        }
        continue
    if PROOF_RE.match(t) and f0.startswith('CMTI'):
        ln['kind'] = 'proof_header'
        ln['proof_of'] = None
        mp = re.match(r'^\s*Proof\s+of\s+(?:' + TYPES.replace('(', '(?:') + r'\s+)?(\d+)\.(\d+)', t)
        if mp:
            ln['proof_of'] = f"{mp.group(1)}.{mp.group(2)}"
        continue

# section titles
sections = {}
for i, ln in enumerate(lines):
    if ln['kind'] == 'section':
        title_parts = []
        j = i + 1
        while j < len(lines) and lines[j]['kind'] == 'text' and lines[j]['spans'][0][0].startswith('CMBX12'):
            title_parts.append(lines[j]['text'].strip())
            j += 1
        sections[ln['secnum']] = ' '.join(title_parts).strip()
print('sections found:', len(sections))
for k in sorted(sections, key=lambda s: [int(x) for x in s.split('.')]):
    print('  ', k, '=', sections[k][:70])

# state machine walk
items = []
seen = set()
current_section = None
current_chapter = None
collect = None  # ('statement', item) | ('proof', item, region, closed) | None

for ln in lines:
    k = ln['kind']
    if k == 'chapter':
        mch = re.match(r'^\s*CHAPTER\s+(\d+)', ln['text'], re.I)
        current_chapter = int(mch.group(1)) if mch else None
        current_section = None
        collect = None
        continue
    if k == 'section':
        current_section = ln['secnum']
        collect = None
        continue
    if k == 'item':
        it = ln['item']
        number = it['number']
        if number in seen:
            collect = None  # restated header (e.g. Theorem 1.1 in 2.6.1) just ends region
            continue
        seen.add(number)
        item = {
            'number': number, 'type': it['type'], 'title': it['title'],
            'page': ln['printed'], 'pdf_page': ln['pdf_page'],
            'section': current_section or (str(current_chapter) if current_chapter else None),
            'statement_lines': [it['first']] if it['first'] else [],
            'proofs': [],
            'order': len(items),
        }
        items.append(item)
        collect = ('statement', item, None, False)
        continue
    if k == 'proof_header':
        tgt = collect[1] if collect and collect[0] == 'statement' else None
        if ln['proof_of']:
            base = ln['proof_of']
            tgt = next((it for it in items if it['number'] == base), tgt)
        if tgt is None:
            collect = None
            continue
        reg = {'header': ln['text'].strip(), 'lines': [], 'tail': [], 'page': ln['printed'], 'of': ln['proof_of']}
        tgt['proofs'].append(reg)
        collect = ('proof', tgt, reg, False)
        continue
    if collect:
        mode, tgt, reg, closed = collect
        if '■' in ln['text']:
            if mode == 'proof':
                closed = True
                before, _, _after = ln['text'].partition('■')
                if before.strip():
                    reg['lines'].append(before)
                collect = (mode, tgt, reg, True)
                continue
            else:
                collect = (mode, tgt, reg, True)
                continue
        if closed:
            if mode == 'proof':
                reg['tail'].append(ln['text'])
            continue
        if mode == 'statement':
            tgt['statement_lines'].append(ln['text'])
        else:
            reg['lines'].append(ln['text'])

by_ch = defaultdict(list)
for it in items:
    ch, n = it['number'].split('.')
    by_ch[int(ch)].append(int(n))
print('\n--- validation ---')
for ch in sorted(by_ch):
    nums = sorted(by_ch[ch])
    missing = sorted(set(range(1, max(nums) + 1)) - set(nums))
    print(f'chapter {ch}: {len(nums)} items, range 1..{max(nums)}, missing: {missing}')

json.dump(items, open(OUT, 'w'), indent=1)
print('\nwrote', OUT, 'with', len(items), 'items')
