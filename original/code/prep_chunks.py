#!/usr/bin/env python3
"""Prepare transcription chunks from items_raw.json for the 4 chapter chunks."""
import json
import os

items = json.load(open('/home/z/my-project/work/items_raw.json'))
os.makedirs('/home/z/my-project/work/chunks', exist_ok=True)

def prep(it):
    proofs = []
    for p in it['proofs']:
        header = p['header']
        # body starts with the remainder of the header line after 'Proof.' / 'Proof of X.Y.'
        rest = header
        m = None
        import re
        m = re.match(r'^\s*Proof(?:\s+of\s+[^.]*?)?\.\s*(.*)$', header)
        if m:
            rest = m.group(1).strip()
        body_lines = ([rest] if rest else []) + list(p['lines'])
        proofs.append({
            'page': p['page'],
            'of': p['of'],
            'body': '\n'.join(body_lines),
            'tail_after_qed': '\n'.join(p['tail']),
        })
    return {
        'number': it['number'],
        'type': it['type'],
        'title': it['title'],
        'page': it['page'],
        'section': it['section'],
        'pdf_page_statement': it['pdf_page'],
        'statement_raw': '\n'.join(it['statement_lines']),
        'proofs': proofs,
    }

chunks = {
    'ch2a': lambda n: n.startswith('2.') and 1 <= int(n.split('.')[1]) <= 35,
    'ch2b': lambda n: n.startswith('2.') and int(n.split('.')[1]) >= 36,
    'ch3a': lambda n: n.startswith('3.') and 1 <= int(n.split('.')[1]) <= 20,
    'ch3b': lambda n: n.startswith('3.') and int(n.split('.')[1]) >= 21,
}

for name, pred in chunks.items():
    sel = [prep(it) for it in items if pred(it['number'])]
    out = f'/home/z/my-project/work/chunks/{name}.json'
    json.dump(sel, open(out, 'w'), indent=1, ensure_ascii=False)
    print(name, len(sel), 'items ->', out)

# ch1 for myself
sel = [prep(it) for it in items if it['number'].startswith('1.')]
json.dump(sel, open('/home/z/my-project/work/chunks/ch1.json', 'w'), indent=1, ensure_ascii=False)
print('ch1', len(sel), 'items')
