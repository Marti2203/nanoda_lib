#!/bin/sh
# The trust surface, counted across BOTH forms an axiom can take, and split by
# whether the axiom actually CLAIMS anything.
#
# Counting only `assume_specification` understates it: an `external_body`
# `proof fn` with an `ensures` is exactly as much of an assumption, and this
# crate has plenty. `uninterp spec fn` is NOT counted -- withholding a
# definition is not a claim.
#
# The claiming/claim-free split matters because the raw total moves for two
# very different reasons. A claim-free `assume_specification` (no `ensures`)
# exists only so a call can be made in verified code; Verus assumes NOTHING
# about it, so it cannot make a proof wrong. The `Env` accessors are like this.
# An axiom WITH an `ensures` is a real assumption. Both add 1 to the total, and
# conflating them has already flattered one headline.
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

spec_claim = spec_free = proof_claim = exec_claim = exec_free = 0
for f in files:
    if not f.endswith('.rs'): continue
    c = read(f)
    for i, L in enumerate(c):
        if re.match(r'\s*(pub )?assume_specification', L):
            # scan forward to the terminating ';' -- an `ensures` before it
            # means the axiom claims something
            claims = False
            for j in range(i, min(i + 60, len(c))):
                if re.search(r'\bensures\b', c[j]): claims = True
                if re.search(r';\s*$', c[j]): break
            if claims: spec_claim += 1
            else:      spec_free  += 1
        if re.match(r'\s*(pub )?proof fn', L) and i > 0 and 'external_body' in c[i-1]:
            proof_claim += 1
        # external_body EXEC fns. One with a contract is exactly as much of an
        # assumption as the other two forms -- `kernel_fail`'s `ensures false`
        # says it diverges, and nothing checks that. Counting only the first two
        # forms missed these entirely.
        if re.match(r'\s*(pub(\(crate\))? )?fn \w', L):
            j, ext = i - 1, False
            while j >= 0:
                t = c[j].strip()
                if t.startswith('#['):
                    if t == '#[verifier::external_body]': ext = True
                    j -= 1; continue
                if t.startswith('//'): j -= 1; continue
                break
            if ext:
                contract = False
                for k in range(i, min(i + 40, len(c))):
                    if re.match(r'\s*(ensures|requires)\b', c[k]): contract = True
                    if re.match(r'\s*\{', c[k]) or c[k].rstrip().endswith('{'): break
                if contract: exec_claim += 1
                else:        exec_free  += 1

claiming = spec_claim + proof_claim + exec_claim
free = spec_free + exec_free
print(f"{rev or 'working tree'}:")
print(f"  CLAIMING    {claiming:3}   (assume_specification with ensures={spec_claim}, "
      f"external_body proof fn={proof_claim}, external_body exec fn with a contract={exec_claim})")
print(f"  claim-free  {free:3}   (callable, promises nothing: "
      f"assume_specification={spec_free}, external_body exec fn={exec_free})")
print(f"  TOTAL       {claiming + free:3}")
PY
