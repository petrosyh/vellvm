#!/usr/bin/env python3
"""Statistics over the archived NI test corpus (~/ni_corpus/programs/*.ll)."""
import glob, re, statistics as st, sys
from collections import Counter

import os
CORPUS = sys.argv[1] if len(sys.argv) > 1 else os.environ.get('NI_CORPUS_DIR', '/tmp/ni_corpus/programs')
files = sorted(glob.glob(CORPUS + '/*.ll'))
if not files:
    sys.exit("corpus empty")

OPCODES = ('add','sub','mul','shl','udiv','sdiv','lshr','ashr','urem','srem',
           'and','or','xor','icmp','select','load','store','getelementptr',
           'alloca','call','br','switch','ret','phi','ptrtoint','inttoptr',
           'bitcast','zext','sext','trunc','freeze','insertvalue','extractvalue')

lines_l, instrs_l, funcs_l, blocks_l, loops = [], [], [], [], 0
op_hist = Counter()
maxf = (0, None)
for f in files:
    txt = open(f, errors='replace').read()
    ls = [l.strip() for l in txt.splitlines()]
    nonempty = [l for l in ls if l]
    n = len(nonempty)
    lines_l.append(n)
    if n > maxf[0]:
        maxf = (n, f)
    funcs_l.append(sum(1 for l in nonempty if l.startswith('define')))
    blocks_l.append(sum(1 for l in nonempty if re.match(r'^[%A-Za-z0-9_.]+:', l)))
    ni = 0
    for l in nonempty:
        m = re.match(r'(?:%[^=]+=\s*)?(?:tail\s+)?([a-z_]+)', l)
        if m and m.group(1) in OPCODES:
            op_hist[m.group(1)] += 1
            ni += 1
    instrs_l.append(ni)
    # crude loop detector: a br targeting a label defined earlier in the same fn
    seen_lbl, has_loop = set(), False
    for l in nonempty:
        if l.startswith('define'):
            seen_lbl = set()
        m = re.match(r'^([%A-Za-z0-9_.]+):', l)
        if m:
            seen_lbl.add(m.group(1))
        for tgt in re.findall(r'label\s+%([A-Za-z0-9_.]+)', l):
            if tgt in seen_lbl:
                has_loop = True
    loops += has_loop

def row(name, data):
    q = st.quantiles(data, n=10)
    print(f"{name:<14} avg={st.mean(data):8.1f}  med={st.median(data):6.0f}  "
          f"p90={q[8]:6.0f}  min={min(data):4d}  max={max(data):5d}")

print(f"programs: {len(files)}")
row("lines", lines_l)
row("instructions", instrs_l)
row("functions", funcs_l)
row("basic blocks", blocks_l)
print(f"loop-containing programs: {loops} ({100*loops/len(files):.1f}%)")
print(f"longest program: {maxf[0]} lines  ({maxf[1]})")
print("\ninstruction histogram (top 15, % of all instructions):")
tot = sum(op_hist.values())
for op, c in op_hist.most_common(15):
    print(f"  {op:<15} {c:8d}  {100*c/tot:5.1f}%")
