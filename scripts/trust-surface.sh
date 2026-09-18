#!/bin/sh
# The trust surface, counted across BOTH forms an axiom can take.
#
# Counting only `assume_specification` understates it: an `external_body`
# `proof fn` with an `ensures` is exactly as much of an assumption, and this
# crate has plenty. `uninterp spec fn` is NOT counted -- withholding a
# definition is not a claim.
rev=${1:-HEAD}
python3 - "$rev" <<'PY'
import subprocess, sys, re
rev = sys.argv[1]
files = subprocess.run(['git','ls-tree','-r','--name-only',rev,'--','src/'],
                       capture_output=True, text=True).stdout.split()
a = b = 0
for f in files:
    if not f.endswith('.rs'): continue
    c = subprocess.run(['git','show',f'{rev}:{f}'], capture_output=True, text=True).stdout.split('\n')
    for i, L in enumerate(c):
        if re.match(r'\s*(pub )?assume_specification', L): a += 1
        if re.match(r'\s*(pub )?proof fn', L) and i > 0 and 'external_body' in c[i-1]: b += 1
print(f"{rev}:  assume_specification={a}  external_body proof fn={b}  TOTAL CLAIMS={a+b}")
PY
