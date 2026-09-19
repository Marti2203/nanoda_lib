#!/usr/bin/env bash
# The kernel-rewrite register's audit. The VERUS-REWRITE(..) markers in the
# source are the ground truth; docs/VERUS_REWRITES.md is a derived index that
# can drift. This checks every marked function is named in the register.
#
# Attribution rule: a marker belongs to the function whose CONTIGUOUS doc block
# contains it. "The next fn after the marker" is wrong -- it misattributes
# wherever a marked function is followed by an unmarked one.
set -uo pipefail
cd "$(dirname "$0")/.."
python3 - <<'PY'
import re
from collections import OrderedDict
reg = open('docs/VERUS_REWRITES.md').read()
files = ['src/tc.rs','src/inductive.rs','src/expr.rs','src/level.rs','src/name.rs',
         'src/util.rs','src/env.rs','src/quot.rs']
d = OrderedDict()
for path in files:
    try: L = open(path).read().split('\n')
    except FileNotFoundError: continue
    for i, l in enumerate(L):
        if 'VERUS-REWRITE' not in l: continue
        j, owner = i + 1, None
        while j < len(L):
            s = L[j].lstrip()
            if re.match(r'(pub(\(crate\))? )?fn \w+', s):
                owner = re.search(r'fn (\w+)', s).group(1); break
            if s.startswith(('///', '//', '#[')) or s == '': j += 1; continue
            break
        if owner is None:
            prev = [k for k in range(i, 0, -1)
                    if re.match(r'\s*(pub(\(crate\))? )?fn \w+', L[k])]
            owner = re.search(r'fn (\w+)', L[prev[0]]).group(1) if prev else '?'
        kind = re.search(r'VERUS-REWRITE\(([^),]*)', l).group(1)
        d.setdefault((path.split('/')[-1], owner), set()).add(kind)
missing = [(f, o, sorted(k)) for (f, o), k in d.items() if o not in reg]
print("%d marked rewrites across %d functions" % (
    sum(len(k) for k in d.values()), len(d)))
if missing:
    print("\nUNREGISTERED (%d):" % len(missing))
    for f, o, k in missing: print("   %-18s %-26s %s" % (f, o, ','.join(k)))
    raise SystemExit(1)
print("all registered in docs/VERUS_REWRITES.md")
PY
