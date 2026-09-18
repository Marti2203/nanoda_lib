# `leq_core`: why it isn't verified, and what it would take

Status: **open, and now load-bearing.** Working code is parked on branch
`leq-core-clique-wip` (commit `92709c3`), which is deliberately **not green**.
The main line stays clean; nothing here is committed to it.

**What changed on 2026-09-18** (commit `2382e1f`): the main line now carries an
`assume_specification` for `TcCtx::leq` stating exactly the contract this note
is about —

```
result ==> forall rho. interp(to_model(l), rho) <= interp(to_model(r), rho)
```

— and SEVEN kernel functions are verified against it (`is_zero`, `is_one`,
`is_nonzero`, `eq_antisymm`, `eq_antisymm_many` in `level.rs`; `def_eq_sort`,
`def_eq_const` in `tc.rs`). Two of those, `is_zero` and `is_one`, were
themselves claim-free axioms and retired, so the trust surface went 105 -> 104.

That raises the value of finishing this note's §4, and lowers the risk: the
consumers are already written against the exact contract the proof will
establish, so finding the measure retires the axiom without touching them. The
measure is the whole remaining job, exactly as §4 says.

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

## 4. The measure: three candidates, all refuted

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

**One arm needs a third component.** `leq_imax_by_cases` fires when an `IMax`'s
second argument is a `Param`. It substitutes that parameter with `Zero` and with
`Succ(param)`, re-simplifies, and recurses on both. On that arm `lw` is **flat**:

```
lw(Param p) == 0,  lw(Zero) == 0,  lw(Succ(Param p)) == lw(Param p) == 0
```

so both replacements have the same weight as what they replace, `lw` is
compositional, and therefore `lw(subst(l)) == lw(l)`. `simplify` is
weight-non-increasing (already proven), so `lw` cannot increase — but it need
not strictly decrease either. `depth` does not help: `Max(a', Succ(p))` is no
shallower than `IMax(a, Param p)`.

> **Correction.** An earlier version of this note claimed `lw` *increases* here
> and called the measure refuted. That computation charged `Succ` a weight of 1,
> which is a different function from `lw` — `lw(Succ(a)) == lw(a)`. The
> conclusion was wrong and the measure is not refuted.

### The third component: parameters in `IMax` second position

Let `imax_params(l)` be the set of `p` such that `IMax(_, Param p)` occurs in
`l`. This is exactly what `by_cases` consumes: substituting `p` turns every
`IMax(_, Param p)` into `IMax(_, Zero)` or `IMax(_, Succ(Param p))`, and
`simplify` collapses both, so `p` leaves the set and nothing new enters.

| arm | `lw` sum | `imax_params` count | `depth` sum |
|---|---|---|---|
| `Succ` peel (both) | flat | flat | **decreases** |
| `Max` arms | **decreases** | — | — |
| both `IMax` rewrites | **decreases** | — | — |
| `leq_imax_by_cases` | flat | **decreases** | — |

which makes

> **`(lw(l)+lw(r), |imax_params(l) ∪ imax_params(r)|, depth(l)+depth(r))`,
> lexicographic**

the candidate. Note the `IMax(a, Max(x,y)) -> Max(IMax(a,x), IMax(a,y))` rewrite
*can* add a parameter to the set (if `x` is a `Param`), which is why the count
cannot come first — `lw` has to absorb those arms, and it does.

### The crux — and `imax_params` is refuted too

The component has to strictly decrease at `by_cases`. It does not. Witness:

```
lhs = Max( IMax(a, Param p),  IMax(c, Max(Param q, Param p)) )

imax_params(lhs) = {p} u ip(a) u ip(c)     -- q is NOT in it, it sits under a Max
```

`by_cases` fires on `p`. In the `p := Zero` branch:

```
subst    -> Max( IMax(a, Zero),  IMax(c, Max(Param q, Zero)) )
simplify:
   IMax(a', Zero)            -> Zero                     (simplify's Zero sub-arm)
   Max(Param q, Zero)        -> combining(Param q, Zero)
                             -> Param q                  (combining's (_,Zero) => l)
   IMax(c', Param q)         -> imax(c', Param q)        (simplify's fall-through)
   combining(Zero, IMax(..)) -> IMax(c', Param q)        (combining's (Zero,_) => r)

imax_params(result) = ip(c') u {q}
```

`p` left the set, but **`q` entered it** — `simplify` collapsed the `Max` that
had been hiding it. The cardinality need not decrease.

**The obvious repair also fails.** Counting parameters anywhere inside an
`IMax`'s second *subtree* (rather than directly in second position) fixes the
`Zero` branch — `q` is inside the subtree both before and after — but breaks the
other one: in the `p := Succ(Param p)` branch, `IMax(c, Max(Param q, Param p))`
becomes `IMax(c, Max(Param q, Succ(Param p)))`, and `p` is still inside an
`IMax` second subtree. Neither variant decreases on both branches.

So: `lw` cannot see the substitution, `depth` grows on the rewrites, and both
parameter-counting variants are refuted by concrete witnesses. Any further
candidate should be run against **both** of the above before any Verus work.

*Retained in `level_model.rs` anyway:* `imax_params` and its four proven lemmas
(`_finite`, `_succ`, `_max_sub`, `_imax_imax`). They are correct statements and
the natural building blocks if a combined measure is found; they are not, on
their own, the answer.

### A fourth candidate that survives both witnesses

**Status: checked on paper against both refutations above, NOT proven and NOT
implemented.** Recorded because it threads exactly the gap between the two
refuted variants, which is the first candidate to do so.

> `undet_imax_params(l)` = the set of `p` such that some `IMax(_, X)` occurs in
> `l` and `Param p` occurs somewhere in `X` at a position **not underneath any
> `Succ`**.

The two refuted variants are its neighbours, and each fails on the side the
other survives:

| variant | `Zero` branch | `Succ` branch |
|---|---|---|
| `imax_params` (direct position only) | **fails** — `q` enters when `simplify` collapses the `Max` hiding it | ok |
| whole subtree | ok — `q` is inside both before and after | **fails** — `p` is still inside the subtree |
| **`undet_imax_params`** (subtree, minus what sits under a `Succ`) | ok — `q` is counted *before* as well as after, so it never "enters" | ok — `p := Succ(Param p)` puts **every** occurrence of `p` under a `Succ`, so `p` leaves |

The idea it encodes: `by_cases` does not remove the parameter, it makes the
parameter's zero-ness **syntactically decided**. `p := Zero` erases it; `p :=
Succ(Param p)` keeps it but wraps every occurrence in a `Succ`, which is exactly
the syntactic marker for "known nonzero". Counting only the still-undecided
occurrences is what makes both branches strictly decrease. Neither neighbour
sees this, because one ignores the wrapping and the other ignores the nesting.

**Why the count can come FIRST this time.** §4 noted that a direct-position
count cannot be the leading component, because
`IMax(a, Max(x,y)) -> Max(IMax(a,x), IMax(a,y))` promotes `x`'s parameters into
direct position and so grows it. Under this definition they were already counted
(inside `X = Max(x,y)`, not under a `Succ`), so that rewrite leaves the set
unchanged. Which gives:

> **`(|undet(l) u undet(r)|, lw(l)+lw(r), depth(l)+depth(r))`, lexicographic**

| arm | count | `lw` | `depth` |
|---|---|---|---|
| `Succ` peel (both) | non-increasing | flat | **decreases** |
| `Max` arms | non-increasing | **decreases** | — |
| `IMax(a, IMax(x,y))` rewrite | non-increasing (`x` leaves second position) | **decreases** | — |
| `IMax(a, Max(x,y))` rewrite | flat | **decreases** | — |
| `leq_imax_by_cases` | **decreases** | — | — |

### What is proven, and what is left

`undet_imax_params` and `params_outside_succ` are DEFINED in `level_model.rs`,
and the four structural arm facts are **proven**:

| lemma | says |
|---|---|
| `undet_imax_params_succ` | peeling an outer `Succ` changes nothing — it hides no `IMax` |
| `undet_imax_params_max_sub` | each `Max` branch contributes a subset |
| `undet_imax_params_imax_imax` | `IMax(a,IMax(x,y)) -> Max(IMax(a,y),IMax(x,y))` is non-increasing; `x`'s params leave as `x` moves out of second position |
| `undet_imax_params_imax_max` | `IMax(a,Max(x,y)) -> Max(IMax(a,x),IMax(a,y))` is **exactly equal** — which is what lets the count lead the order |

**The `by_cases` arm is proven too** — the step all three earlier candidates
died on. Three more lemmas, all verified:

| lemma | says |
|---|---|
| `params_outside_succ_subst_single` | substituting `p := v`, where `v` has no `p` outside a `Succ`, leaves no `p` outside a `Succ` |
| `undet_imax_params_subst_single` | the same for the measure itself; its `IMax` case is where `params_outside_succ` does the work |
| `undet_imax_params_by_cases_drops` | instantiated at `by_cases`' two actual values: after `p := Zero` **and** after `p := Succ(Param p)`, `p` is not in the set |
| `undet_imax_params_subst_no_growth` | and nothing ELSE arrives — substitution is structural, so the set can only shrink |

The last two together are the strict decrease: `p` was in the set (that is why
`by_cases` fired — it fires on an `IMax` whose second argument is a `Param`),
`p` is not in it afterwards, and no other parameter entered. A strict subset of
a finite set has smaller cardinality.

Both branch values satisfy the hypotheses, for the two different reasons the
candidate turns on: `Zero` erases every occurrence, and `Succ(Param p)` keeps
them all but puts each under a `Succ`, where `params_outside_succ` is blind by
construction. That second line is precisely what the refuted subtree variant
could not see.

### `simplify` non-growth — proven

`by_cases` re-simplifies after substituting, so the decrease above only survives
if `simplify` does not undo it. Both `simplify` and `combining` now carry it as
an `ensures`, proven in place with their bodies unchanged:

```
undet_imax_params(result).subset_of(undet_imax_params(ptr))
params_outside_succ(result).subset_of(params_outside_succ(ptr))
```

`combining` needed it first, since `simplify` routes three of its four arms
through it. Every `combining` arm returns an input, a `Succ` over a combined
pair, or the `Max` — none can add a parameter to either set, and the `Succ`
fold pushes a `Succ` OUTWARD, which keeps everything beneath it covered rather
than exposing it.

### Where the first component stands

Every arm is now proven for `|undet(l) u undet(r)|`:

| arm | status |
|---|---|
| `Succ` peel (both) | non-increasing — `undet_imax_params_succ` |
| `Max` arms | non-increasing — `undet_imax_params_max_sub` |
| `IMax(a,IMax(x,y))` rewrite | non-increasing — `undet_imax_params_imax_imax` |
| `IMax(a,Max(x,y))` rewrite | flat — `undet_imax_params_imax_max` |
| `leq_imax_by_cases` | **strictly decreases** — `undet_imax_params_by_cases_drops` + `undet_imax_params_subst_no_growth` |
| `simplify`/`combining` in between | cannot undo it — clauses on both |

**What this is, and is not.** The mathematical obstacle §4 recorded is cleared:
three candidates were refuted by witnesses, and the fourth is proven to have the
decrease property on every arm. That was "the whole task" in §6's sense.

What remains is assembly, and it is not nothing:

1. Wire the lexicographic measure into `leq_core` as an actual `decreases`
   clause and discharge each arm against it, combining the first component with
   the existing `lw` lemmas (`lw_decreases_imax_imax`, `lw_decreases_imax_max`)
   and `depth`.
2. ~~Tie the exec `leq_imax_by_cases` to the spec substitution the lemmas are
   stated over.~~ **DONE.** `subst_simp` is verified in place and carries the
   bridge as an `ensures`: for the single-key shape `leq_imax_by_cases` actually
   builds, the substituted parameter is not in `undet_imax_params` of the
   result, and the set does not grow. `subst_level`'s existing contract already
   produced exactly the `subst_level_spec(l, seq![p], seq![v])` form the lemmas
   are stated over, so this was a matter of naming `p` and `v` and chaining
   `simplify`'s non-growth clause. `simplify` also gained the counter frame it
   had been missing.
3. Then §5: the `diff` bound follows, `exec_allows_no_decreases_clause` comes
   off `leq_core`, and the `leq` axiom added in `2382e1f` retires onto the
   proof, with its seven consumers untouched.

So: the hard part is done and step 2 of the wiring with it. **Step 1 is all
that is left**, and it is the one that needs the whole clique at once — a
`decreases` clause on `leq_core` means every arm discharged together, against a
measure combining this component with `lw` and `depth`.

Do not describe this as a termination proof until step 1 verifies.

Finiteness needs nothing: this vstd deprecates `Set::finite` because every `Set`
is finite, which is why `imax_params_finite` now raises a warning.

## 5. Termination gives the `diff` bound for free

Once a strictly-decreasing measure `M` exists, the overflow problem dissolves.
Carry

> `|diff| + M(l, r) <= 1_000_000_000`

as a precondition. Every arm that moves `diff` by one also strictly decreases
`M`, so the sum is non-increasing; every other arm leaves `diff` alone and
decreases `M`, so the sum decreases. No interval needs to be closed under ±1 —
that was the thing that looked impossible, and it is only impossible *without*
a measure.

This is why §4 is the whole task. There is no second problem after it.

## 6. Order of work, if resumed

1. **Find a measure.** This is the whole problem, and it is harder than it
   looks: three candidates are now refuted by explicit witnesses (§4). Do not
   start Verus work on a fourth until it has been run against both `by_cases`
   branches on paper.
2. Prove termination with the three-component measure. Drop
   `exec_allows_no_decreases_clause` from `leq_core`.
3. The `diff` bound then follows *immediately*, with no extra argument: carry
   `|diff| + M <= 1_000_000_000` where `M` is the measure. Every arm that moves
   `diff` by one strictly decreases `M`, so the sum is non-increasing. This is
   why termination is worth having — it is not a separate problem from the
   overflow, it is the same one.
4. Retire `verified_leq_core` (131 lines, 15 call sites).

Also still open on that branch: `leq_imax_by_cases` exceeds the rlimit — try
`#[verifier::spinoff_prover]` before raising the limit.
