# `leq_core`: why it isn't verified, and what it would take

Status: **open**. Working code is parked on branch `leq-core-clique-wip`
(commit `92709c3`), which is deliberately **not green**. The main line stays
clean; nothing here is committed to it.

This is a design note, not a plan of record. It exists so the next attempt
starts from what was actually established rather than re-deriving it.

## 1. The clique, and why it is *not* a proof cycle

`leq_core` sits in a five-function mutual recursion:

```
simplify ──> is_zero / is_one ──> leq ──> leq_core ──> simplify
                                            │
                                            └──> leq_imax_by_cases ──> subst_simp ──> simplify
```

This *looks* like it forces axioms: you cannot verify `simplify` without a
contract for `is_zero`, whose contract needs `leq`'s, which needs `leq_core`'s,
which needs `simplify`'s.

**It does not.** Every contract in the clique is stated over `interp`, a *spec*
function. So no contract depends on another being **proven** — only on its being
**stated**. Verus checks each body against the others' stated contracts. With
`exec_allows_no_decreases_clause` (partial correctness, the crate's stance
everywhere else) there is no well-founded order to supply, and the knot unties.

This was the main thing the attempt established, and it generalises: *do not
reach for an axiom because an exec clique looks circular.*

## 2. What already verifies on the WIP branch

- **`simplify` preserves denotation** —
  `forall rho. interp(to_model(result), rho) == interp(to_model(ptr), rho)`.
  This was impossible while `is_zero`/`is_one` were contract-free, because the
  `IMax` arm's shortcut (`if is_zero(l) || is_one(l) { r_simp }`) is only sound
  when the left side denotes 0 or 1. Each of its five branches is sound for a
  *different* reason and needed its own proof.
- `is_zero`, `is_one`, `leq`, `subst_simp` all carry real contracts.
- The two claim-free `is_zero`/`is_one` axioms are gone.

## 3. The blocker: `diff` can overflow

`leq_core(l, r, diff)` takes `diff: isize`. Two arms move it:

```rust
(Succ(s, ..), _) => self.leq_core(s, r_in, diff - 1),
(_, Succ(s, ..)) => self.leq_core(l_in, s, diff + 1),
```

Verus must discharge these as overflow-free, which needs a bound on `diff` that
is **preserved by the recursion**. No interval is closed under ±1, so the bound
has to come from a measure that decreases when a `Succ` is peeled.

The mirror `verified_leq_core` sidesteps this entirely: it is `decreases fuel`,
and fuel caps the recursion depth, hence `|diff|`. **The kernel has no fuel.**

### Why the obvious measures fail

| | `Succ` peel | `IMax` rewrite arms |
|---|---|---|
| `depth` | decreases ✓ | **increases** ✗ |
| `lw` | **flat** ✗ (`lw(Succ(a)) == lw(a)`) | decreases ✓ |

The two rewrite arms are

```
IMax(a, IMax(x,y))  ->  Max(IMax(a,y), IMax(x,y))
IMax(a, Max(x,y))   ->  Max(IMax(a,x), IMax(a,y))   (then simplify)
```

Both **duplicate a subterm** (`y` in the first, `a` in the second), so any
measure that counts `Succ` nodes can grow there — which rules out the direct
"bound `diff` by the number of remaining `Succ`s" argument.

## 4. The untried lead: prove termination with a lexicographic measure

`lw` was built in an earlier session specifically for the rewrite arms and has
the lemmas `lw_decreases_imax_imax` and `lw_decreases_imax_max`. Checking the
arms by hand:

| arm | `lw(l) + lw(r)` |
|---|---|
| `(Succ(s,..), _)` / `(_, Succ(s,..))` | flat |
| `(Max(a,b), _)` | decreases — `lw(Max(a,b)) = 1 + max(..) > lw(a)`, `> lw(b)` |
| `(Param\|Zero, Max(x,y))` | decreases, same reason on the right |
| both `IMax` rewrite arms | decreases, by the two existing lemmas |

So `lw` decreases on **every** arm except the two `Succ` arms — and `depth`
decreases on exactly those. That makes

> **`(lw(l) + lw(r), depth(l) + depth(r))`, lexicographic**

a candidate **termination** measure — which would be a result in its own right,
since the kernel currently guarantees no termination for `leq_core`.

**But one arm breaks it, and I worked the case out rather than leaving it
open.** `leq_imax_by_cases` fires when an `IMax`'s second argument is a `Param`.
It substitutes that parameter with `Zero` and with `Succ(param)`, re-simplifies,
and recurses on both.

- The `Zero` case is fine. `IMax(a, Zero)` simplifies to `Zero`, so `lw` drops
  from `lw(a) + 1` to `0`.
- The **`Succ(param)` case is flat**, which is fatal for a lexicographic measure
  whose second component also fails to decrease:

```
before:  lw(IMax(a, Param p))      = lw(a) + 2*lw(Param p) + 1 = lw(a) + 1

after:   simplify(IMax(a, Succ(p)))  takes simplify's `Succ` sub-arm,
         which returns combining(simplify(a), Succ(p)) = Max(a', Succ(p))
         (combining only folds when BOTH sides are Succ; otherwise Max)

         lw(Max(a', Succ(p)))      = 1 + max(lw(a'), lw(Succ(p)))
                                   = 1 + max(lw(a'), 0)
                                   = 1 + lw(a')
```

and `lw(a') <= lw(a)` is all `simplify` guarantees (it is weight-**non**-increasing,
not decreasing), so the result is `<= lw(a) + 1` — **equal in the worst case**.

`depth` does not save it either: `Max(a', Succ(p))` is no shallower than
`IMax(a, Param p)`, and generally deeper.

**So `(lw, depth)` lexicographic is refuted.** A working measure has to charge
the `Succ(param)` substitution something that `lw` does not — the substitution
replaces a weight-0 leaf (`Param`) with another weight-0 term (`Succ(Param)`),
which is precisely why `lw` cannot see it. Any candidate should be tested
against this case *first*; it is the cheapest way to rule one out.

## 5. Even with termination, `diff` needs its own argument

Termination does not hand over a `diff` bound: the number of `Succ` peels along
a path is bounded by a *function of* the measure, not by the measure. Because
the rewrite arms duplicate subterms, that function is not obviously linear.

Two routes, neither attempted:

1. **Ghost bound parameter.** Add `Ghost(bound): Ghost<nat>` to `leq_core` and
   `leq_imax_by_cases`, require `|diff| <= bound`, and let the termination proof
   justify a concrete initial value. A `Ghost` parameter is **erased at compile
   time**, so this is closer to a proof annotation than to a rewrite — it does
   not change the executable. It does change the signature, so call sites need
   `Ghost(..)` arguments. See the `Ghost(x): Ghost<nat>` pattern-param form.
2. **Weaken the contract.** State `leq_core`'s postcondition only under a
   hypothesis that `diff` stayed in range, and discharge that hypothesis at the
   `leq` entry point where `diff == 0`. Probably unsatisfying, since the
   hypothesis is what we cannot prove.

## 6. Order of work, if resumed

1. **Find a measure that charges the `Succ(param)` substitution.** `(lw, depth)`
   is refuted (§4) and its failure case is the cheap test for any replacement.
   The substitution swaps a weight-0 `Param` for a weight-0 `Succ(Param)`, so
   the measure must see something other than weight — perhaps the number of
   distinct parameters still eligible for the `by_cases` split, which strictly
   decreases each time one is eliminated.
2. Prove termination with it. Drop `exec_allows_no_decreases_clause` from
   `leq_core`.
3. Only then attack the `diff` bound, via the ghost parameter.
4. Retire `verified_leq_core` (131 lines, 15 call sites).

Step 1 is the whole problem. Steps 2-4 are ordinary work.

Also still open on that branch: `leq_imax_by_cases` exceeds the rlimit — try
`#[verifier::spinoff_prover]` before raising the limit.
