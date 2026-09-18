#!/bin/sh
# The trust surface, counted across BOTH forms an axiom can take.
#
# Counting only `assume_specification` understates it: an `external_body`
# `proof fn` with an `ensures` is exactly as much of an assumption, and this
# crate has plenty. `uninterp spec fn` is NOT counted -- withholding a
# definition is not a claim.
#
# With no argument, measures the WORKING TREE. Pass a revision to measure that
# instead. (Measuring `HEAD` before committing reports the old state, which has
# already produced one wrong commit message.)
python3 - "$@" <<'PY'
import subprocess, sys, re, glob
rev = sys.argv[1] if len(sys.argv) > 1 else None
if rev:
    files = subprocess.run(['git','ls-tree','-r','--name-only',rev,'--','src/'],
                           capture_output=True, text=True).stdout.split()
    read = lambda f: subprocess.run(['git','show',f'{rev}:{f}'],
                                    capture_output=True, text=True).stdout.split('\n')
else:
    files = sorted(glob.glob('src/**/*.rs', recursive=True))
    read = lambda f: open(f).read().split('\n')
a = b = 0
for f in files:
    if not f.endswith('.rs'): continue
    c = read(f)
    for i, L in enumerate(c):
        if re.match(r'\s*(pub )?assume_specification', L): a += 1
        if re.match(r'\s*(pub )?proof fn', L) and i > 0 and 'external_body' in c[i-1]: b += 1
print(f"{rev or 'working tree'}:  assume_specification={a}  "
      f"external_body proof fn={b}  TOTAL CLAIMS={a+b}")
PY
