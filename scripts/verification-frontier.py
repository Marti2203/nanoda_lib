#!/usr/bin/env python3
"""Which kernel functions could be verified next.

A function is ON THE FRONTIER when every function it calls is already known to
Verus -- verified inside a `verus!` block, or given an `assume_specification`.

Two mistakes this tool exists to not repeat:
  * a function's own name appears on its signature line, so including that line
    in the body text makes every function look like it calls itself. Bodies
    start BELOW the signature.
  * callees live in other files. Checking only the current file made
    `handle_rec_args_aux` look ready when it calls `self.whnf`, which is in the
    48-function cycle and blocked behind all of it.
"""
import re, sys, glob
from collections import OrderedDict

def verus_spans(src, L):
    out = []
    for m in re.finditer(r'^\s*(?:::vstd::prelude::)?verus! \{', src, re.M):
        st = src[:m.start()].count('\n'); d = 0
        for i in range(st, len(L)):
            d += L[i].count('{') - L[i].count('}')
            if d == 0 and i > st:
                out.append((st, i)); break
    return out

FN = r'\s*(?:pub(?:\(crate\))? )?(?:open |closed |uninterp )?(?:proof |spec |exec )?fn (\w+)'
known, allfns = set(), set()
for f in glob.glob('src/*.rs'):
    src = open(f).read(); L = src.split('\n'); sp = verus_spans(src, L)
    for i, l in enumerate(L):
        m = re.match(FN, l)
        if m:
            allfns.add(m.group(1))
            if any(a <= i <= b for a, b in sp): known.add(m.group(1))
    for m in re.finditer(r'assume_specification.*?\[[^\]]*?::(\w+)\s*\]', src):
        known.add(m.group(1))

target = sys.argv[1] if len(sys.argv) > 1 else 'src/inductive.rs'
src = open(target).read(); L = src.split('\n'); sp = verus_spans(src, L)
fns = [(i, re.search(r'fn (\w+)', l).group(1)) for i, l in enumerate(L)
       if re.match(r'\s*(pub(\(crate\))? )?fn \w+', l)]
rows = []
for k, (i, n) in enumerate(fns):
    if any(a <= i <= b for a, b in sp): continue
    end = fns[k + 1][0] if k + 1 < len(fns) else len(L)
    body = re.sub(r'^\s*//.*$', '', '\n'.join(L[i + 1:end]), flags=re.M)   # BELOW the signature
    calls = set(re.findall(r'(?:\.|\b)(\w+)\s*\(', body))
    unknown = sorted(c for c in calls if c in allfns and c not in known)   # ANY file
    bl = re.sub(r'\|\|', 'OR', body)
    blockers = OrderedDict(
        unwrap=len(re.findall(r'\.unwrap\(\)|\.expect\(', bl)),
        panic=len(re.findall(r'\bpanic!\(|\bassert(?:_eq)?!\(', bl)),
        slice=len(re.findall(r'\[\s*\w+\s*[,\]]', bl)) and 0,
        forloop=len(re.findall(r'\bfor \w+ in ', bl)),
        whilelet=len(re.findall(r'\bwhile let ', bl)),
        closure=len(re.findall(r'\|[\w\s,:&]*\|\s*[\{\w]', bl)))
    rows.append((len(unknown), sum(blockers.values()), end - i, n, unknown, blockers))
rows.sort(key=lambda r: (r[0], r[1], r[2]))
print("%-30s %6s %5s  %s" % ("function", "lines", "blk", "unknown callees"))
for u, bt, sz, n, unk, b in rows[:20]:
    tag = ','.join("%s=%d" % (k, v) for k, v in b.items() if v)
    print("  %-28s %6d %5d  %s" % (n, sz, bt, ', '.join(unk[:4]) if unk else ('-- FRONTIER --  ' + tag)))
print("\n%d of %d functions in %s are on the frontier"
      % (sum(1 for r in rows if r[0] == 0), len(rows), target))
