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

So: the hard part of §4 is done and step 2 of the wiring with it. But step 1 is
bigger than this note has been saying, and the correction matters enough to
state on its own.

### Correction to §6: there IS a second problem

§6 said "§4 is the whole task. There is no second problem after it." That is
**wrong**, and measuring the call graph is what shows it.

`decreases` on a mutually recursive function needs a measure that decreases at
EVERY edge of the clique, not just at the arms of one member. And the clique in
`level.rs` is not `leq_core` plus `by_cases` — it is **seven functions, 239
lines**:

```
is_one, is_zero, leq, leq_core, leq_imax_by_cases, simplify, subst_simp
```

with, among others, the cycle

```
simplify -> is_zero -> leq -> leq_core -> simplify
```

`simplify` is inside the recursion, not beneath it. Its `IMax` arm calls
`is_zero(l_simp)`, `is_zero` is `leq(x, zero)`, `leq` is
`leq_core(simplify(l), simplify(r), 0)`, and `leq_core` calls `simplify` again.

So the measure of §4 governs `leq_core`'s own arms, which is what it was built
for and what is now proven. It says nothing yet about the `simplify -> is_zero`
edge, where the argument is a level that `simplify` has just produced. Closing
that plausibly needs idempotence of `simplify` (so `simplify(l_simp)` is `l_simp`
rather than fresh work) or a size argument on the original call — neither of
which exists here today.

**This does not devalue §4.** Three candidates were refuted and a fourth is
proven on every `leq_core` arm; that was real and it was the blocker everyone
kept hitting. It does mean there is a second measure problem over a larger
clique — which the next section proposes an answer to.

### A candidate measure for the whole clique

**Status: every edge checked on paper, the supporting lemmas proven, the
`decreases` clauses NOT yet written.**

> **`(|undet(args)|, lw(args), phase, level_depth(args))`, lexicographic**
>
> — note the order: **phase comes BEFORE `level_depth`**, see the correction below
>
> where `args` means the sum/union over the function's level arguments, and
>
> | fn | `simplify` | `subst_simp` | `leq_imax_by_cases` | `leq_core` | `leq` | `is_zero` | `is_one` |
> |---|---|---|---|---|---|---|---|
> | phase | 0 | 1 | 2 | 3 | 4 | 5 | 6 |

The phase component is the trick, and the ordering is not arbitrary. Two edges
go *up* in phase, and each is paid for by an earlier component dropping
strictly:

- `leq_imax_by_cases -> leq_core` climbs 2 → 3, and `undet` strictly decreases
  (proven, `051d44e`).
- `simplify -> is_zero` climbs 0 → 5, and `lw` strictly decreases:
  `lw(IMax(l,r)) = lw(l) + 2·lw(r) + 1 > lw(l) >= lw(simplify(l))`, the last
  step by `simplify`'s existing `lw`-non-increasing contract.

Everything else goes *down* in phase, or drops `lw`, or drops `level_depth`.
All seventeen edges of the clique:

| decreases via | edges |
|---|---|
| `undet` | `by_cases -> leq_core` |
| `lw` | both `Max` arms, both `IMax` rewrites, `leq_core -> simplify`, `simplify -> is_zero`/`is_one`, `simplify -> simplify` at `Max`/`IMax` |
| phase | the seven edges with same-or-smaller arguments |
| `level_depth` | `leq_core`'s `Succ` peels, `simplify`'s `Succ` arm — the two places `lw` is deliberately blind, since `lw(Succ a) == lw(a)` |

### Correction: `phase` must come before `level_depth`

An earlier version of this section ordered the measure
`(undet, lw, level_depth, phase)`. **That fails**, on exactly one edge:

```
subst_simp(level) -> simplify(subst_level(level, [p], [Succ(Param p)]))
```

Substituting `p := Succ(Param p)` adds a `Succ` node at every occurrence, so
`level_depth` **grows** there. `undet` is non-increasing and `lw` is flat, so
with `level_depth` third the tuple increases before any component strictly
drops, and the edge is not discharged.

With `phase` third it falls through to the phase drop (1 → 0) and is fine.
Nothing else is affected: the two edges that genuinely need `level_depth`
(`leq_core`'s `Succ` peels and `simplify`'s `Succ` arm) keep the same phase, so
a later `level_depth` still decides them.

`lw` being flat on that edge is itself a fact worth having: `lw_subst_preserved`
proves that substituting a WEIGHTLESS value leaves `lw` exactly unchanged, and
both of `by_cases`' values are weightless — `lw(Zero) == 0` and
`lw(Succ(Param p)) == lw(Param p) == 0`, since `lw` ignores `Succ` by design.
That is the same blindness that forces `level_depth` to exist, paying off in the
other direction.

All seventeen edges were re-checked mechanically under both orders: the
corrected one discharges every edge, the documented one fails exactly this.

`level_depth` is new (`level_model.rs`) and exists precisely for that third row.
Its supporting facts are proven: `level_depth_succ`, `lw_max_gt`,
`lw_imax_gt_left`, `undet_imax_params_imax_left_sub`.

### The model-side toolkit is complete

Everything the `decreases` clauses will consume is defined and proven:

| | |
|---|---|
| definitions | `undet_imax_params`, `params_outside_succ`, `level_depth` |
| arm facts | `_succ`, `_max_sub`, `_imax_imax`, `_imax_max`, `_imax_left_sub` |
| `by_cases` | `_subst_single`, `_by_cases_drops`, `_subst_no_growth`, `_contains_imax_param` |
| cardinality | `undet_len_mono`, `undet_len_strict`, **`undet_len_decreases_at_by_cases`** |
| `lw` / depth | `lw_max_gt`, `lw_imax_gt_left`, `level_depth_succ`, plus the pre-existing `lw_decreases_imax_*` |
| exec side | `subst_simp`'s bridge; `simplify`/`combining` non-growth |

`undet_len_decreases_at_by_cases` is the capstone. The measure's first component
is a SET, but `decreases` needs a well-founded value, so what the clause
actually uses is its cardinality — and that lemma composes the three proven
facts (the parameter is in the set before, not after, and nothing else arrived)
into the strict `<` the clause consumes. It is stated in exactly that form.

### A loose end the plumbing must pick up

`subst_simp` now carries `requires` — that `ks`/`vs` are equal-length and
`Param`-shaped, and, for the measure clause, that `vs` is a single weightless
value with empty `undet`/`params_outside_succ`. Its **only** caller is
`leq_imax_by_cases`, which is NOT in `verus!`, so **nothing currently checks
those preconditions**.

That is not unsound — `subst_simp`'s body was verified under them, and no
verified code consumes its ensures yet — but it is an unenforced contract, and
the kind that quietly becomes a problem. Checked by hand against the real call
site, they hold: `param_slice` is `[param]` with `param` a `Param` level,
`zero_slice` is `[zero]`, `succ_param_slice` is `[succ(param)]`, all length 1,
and both substituted values are weightless (`lw(Zero) == 0`,
`lw(Succ(Param p)) == 0`).

**When `leq_imax_by_cases` moves into `verus!`, it has to discharge them.** They
are satisfiable — that is the point of checking now rather than discovering a
vacuous contract later.

### Both mechanical unknowns are cleared

Two things could have sunk this approach independently of the mathematics. Both
were probed before committing to the plumbing, and both came back clean:

1. **`Set::len()` in a `decreases`.** The first component is a set; a
   `decreases` clause needs a well-founded value. `len()` is available here and
   monotone under subset via `vstd::set_lib::lemma_len_subset`. Probe run,
   turned into `undet_len_mono`/`undet_len_strict`.
2. **A phase constant across mutually recursive EXEC functions.** Two exec
   functions, one keeping its argument and dropping a phase, the other raising
   the phase and dropping the argument — the clique measure's exact shape — and
   it verifies. Probe run and removed; recorded at the site like a contradiction
   detector.

Probe before writing seven interlocking contracts, not after. Neither result was
obvious, and either failure would have meant a different measure entirely.

### What "plumbing" actually means — three of the seven are not verified at all

Worth stating precisely, because "add a `decreases` clause" undersells it.
`level.rs` has its verified section starting at the `VERIFIED KERNEL CODE`
banner; everything above it is an ordinary `impl` block Verus never sees. Of the
seven clique members:

| | in `verus!` | has a contract |
|---|---|---|
| `simplify` | yes | yes |
| `subst_simp` | yes | yes |
| `is_zero`, `is_one` | yes | yes |
| **`leq`** | **no** | no |
| **`leq_core`** | **no** | no |
| **`leq_imax_by_cases`** | **no** | no |

So `leq_core`'s `diff - 1` is not overflow-checked today because the function is
not checked at all — which is also why the crate is green while §3 describes an
unproven overflow.

The remaining work is therefore: move three functions into `verus!`, give them
contracts (that part exists on `leq-core-clique-wip`), AND add the four-component
`decreases` to all seven. It is the WIP branch plus the measure, not an
increment on top of what is on the main line. Budget accordingly: a mutual
clique cannot go green piecewise, so none of it lands until all of it does.

**What is left is plumbing in the sense that no idea is missing**: write the
four-component `decreases` on all seven functions and discharge each edge
against the table above. Still a real chunk —
a mutual clique cannot go green piecewise, so seven contracts land together or
not at all — but every mathematical ingredient is on the shelf and both
mechanisms are known to work.

The one shape to expect: `leq_core`'s measure is over BOTH arguments, so the
pair form `undet_len_decreases_at_by_cases_pair` is the one its `by_cases` arms
consume, not the single-level capstone.

Do not describe any of this as a termination proof until those clauses verify.

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

### Correction: the `diff` bound does NOT follow for free

The paragraph above says "carry `|diff| + M <= 1e9`" and treats it as immediate.
It is not, and the gap is specific: **that inequality needs `M` to be a SCALAR**
that strictly decreases on every arm moving `diff` and is non-increasing
elsewhere. The measure §4 produces is **lexicographic**, and a sum needs one
number.

`diff` moves only on the two `Succ` arms. Arm by arm:

| arm | `diff` | `undet` | `lw` | `level_depth` |
|---|---|---|---|---|
| `Succ` peel (either side) | ±1 | flat | flat | **decreases** |
| `Max` arms | — | flat | **decreases** | decreases |
| `IMax` rewrites | — | flat | **decreases** | **grows** (~+1) |
| `by_cases` | — | **decreases** | flat | **grows**, by one `Succ` per occurrence of `p` |

So no single component works, and the obvious collapse
`M = undet*A + lw*B + depth` needs

- `B >= 2`, to cover `depth` growing by about one at the `IMax` rewrites while
  `lw` drops by at least one;
- `A` greater than how much `lw*B + depth` can grow at `by_cases` — and there
  `depth` grows by one `Succ` per OCCURRENCE of `p`, bounded only by the term
  size.

#### …and a correction to THAT: no ceiling is needed

The paragraph above originally concluded that `A` needs a term-size ceiling,
because `depth` "grows by one `Succ` per occurrence of `p`". **That is wrong,
and the error is a specific confusion worth naming: it is true of SIZE and
false of DEPTH.** `level_depth` is a `max`, not a sum. Substituting
`p := Succ(Param p)` at a hundred occurrences still raises the height by at
most one, because every path only gains the one `Succ` at its leaf.

Proven (`level_model.rs`):

| lemma | bound |
|---|---|
| `level_depth_subst_le` | `depth(subst(l, p, v)) <= depth(l) + 1` when `depth(v) <= 1` — and both `by_cases` values qualify (`depth(Zero) = 0`, `depth(Succ(Param p)) = 1`) |
| `level_depth_imax_imax_le` | the `IMax`/`IMax` rewrite raises height by at most 1 — duplicating `y` costs nothing under a `max` |
| `level_depth_imax_max_le` | same for the `IMax`/`Max` rewrite |

So every growth is bounded by **one**, and the collapse needs no ceiling:

> **`M = 2·|undet(l) ∪ undet(r)| + 2·(lw(l) + lw(r)) + depth(l) + depth(r)`**

| arm | change in `M` |
|---|---|
| `Succ` peel | `undet` flat, `lw` flat, `depth` −1 → **−1** |
| `Max` arms | `lw` −≥1 → −2, `depth` non-increasing → **≤ −2** |
| `IMax` rewrites | `lw` −≥1 → −2, `depth` +≤1 → **≤ −1** |
| `by_cases` | `undet` −≥1 → −2, `lw` flat, `depth` +≤1 → **≤ −1** |

Every arm strictly decreases, `M` is a single `nat`, and §5's
`|diff| + M <= 1e9` therefore works as originally written — `diff` moves only on
the `Succ` arms, where `M` drops by one, so the sum never rises.

**That gap is closed.** `combining` and `simplify` both carry the height bound
now, proven in place with their bodies unchanged:

```
combining :  level_depth(result) <= 1 + max_nat(level_depth(l), level_depth(r))
simplify  :  level_depth(result) <= level_depth(ptr)
```

`combining` needed it first, since `simplify` routes three arms through it. And
`subst_simp` carries all three components across the real substitution:

```
undet_imax_params(result) subset_of undet_imax_params(level)
lw(result)          ==  lw(level)
level_depth(result) <=  level_depth(level) + 1
```

So every ingredient of

> **`M = 2·|undet(l) ∪ undet(r)| + 2·(lw(l) + lw(r)) + depth(l) + depth(r)`**

is proven, on the model side and across the exec functions `by_cases` actually
calls.

### The two goals are separable — and only one of them is urgent

This note has been conflating them, so: **termination** (dropping
`exec_allows_no_decreases_clause`) and **the `diff` overflow** are different
problems, and the second does not need the first.

`|diff| + M <= 1e9` is an **invariant of the recursion**, not a consequence of
termination:

| arm | `|diff|` | `M` | sum |
|---|---|---|---|
| `Succ` peel (either) | ≤ +1 | −1 | non-increasing |
| `Max` arms | +0 | ≤ −2 | decreases |
| `IMax` rewrites | +0 | ≤ −1 | decreases |
| `by_cases` | +0 | ≤ −1 | decreases |

Carry it as a `requires` and every recursive call re-establishes it, under plain
`exec_allows_no_decreases_clause` — the crate's stance everywhere else. **No
`decreases` clause, and therefore no seven-function clique measure, is needed to
discharge the overflow.** The clique measure remains the route to termination if
that is ever wanted; it is not on the path to the contracts.

### `leq_measure` is defined and every arm is proven

```
M(l, r) = 3·|undet(l) ∪ undet(r)| + 2·(lw(l) + lw(r)) + depth(l) + depth(r)
```

The weights are **forced**, and a first draft got one wrong:

- `lw` gets **2** — the `IMax` rewrites drop `lw` by ≥1 while `depth` grows by
  ≤1 on the rewritten side.
- `undet` gets **3**, not 2 — `by_cases` substitutes into **both** sides, so
  `depth` can grow by one *each*, +2 total, against a drop of ≥1 in `undet`.
  With weight 2 that arm comes out non-strict.

| lemma | arm | `dM` |
|---|---|---|
| `leq_measure_succ_left` / `_right` | `Succ` peel | **exactly −1** |
| `leq_measure_max_left` | `Max` arms | ≤ −2 |
| `leq_measure_imax_imax` | `IMax`/`IMax` rewrite | ≤ −1 |
| `leq_measure_imax_max` | `IMax`/`Max` rewrite | ≤ −1 |
| `leq_measure_by_cases` | `by_cases`, both sides substituted | ≤ −1 |

The `Succ` figure being **exact** is what matters for the overflow: that is the
only arm where `diff` moves, and `|diff|` rises by at most one there, so
`|diff| + M` never rises.

### The `diff` overflow is SOLVED — tested, on branch `leq-core-port-wip`

§3 has called the `diff` overflow the blocker since this note was written. It is
dischargeable, and that is now demonstrated rather than argued. Branch
`leq-core-port-wip` (commit `741af8c`, deliberately **not green**, same
convention as `leq-core-clique-wip`) carries `leq_core` with

```
requires diff + leq_measure(l_in, r_in) <= 1_000_000_000,
         diff - leq_measure(l_in, r_in) >= -1_000_000_000,
```

and **every recursive call re-establishes it. Zero precondition errors remain**
— `Succ` peels via the exact −1, both `Max` sides, all four `IMax` rewrites, and
`by_cases`. A constant interval could never do this, which is exactly why
`leq-core-clique-wip` stalled on `-1e9 <= diff <= 1e9`.

Thirteen of `leq_core`'s fifteen semantic arms are proven there too.

### The one thing left: `simplify`'s denotation preservation

```
forall rho. interp(to_model(result), rho) == interp(to_model(ptr), rho)
```

`leq-core-clique-wip` proves it in about 60 lines of per-arm reasoning. The two
unproven `leq_core` arms are both `IMax`/`Max` rewrites, which re-simplify, so
they need it and nothing else does.

Worth noting **why it is statable at all now, and was not this morning**: the
clause is sound only because `simplify`'s `IMax` arm shortcuts when the left
side denotes 0 or 1 — and `is_zero`/`is_one` only acquired those contracts
today, when the `leq` axiom let them be verified. Retiring that axiom is what
makes proving it possible, which is the opposite of how it looked going in.

### What the remaining work actually is

1. Move `leq`, `leq_core`, `leq_imax_by_cases` into `verus!` with the contracts
   from `leq-core-clique-wip` (they are sound as written), replacing that
   branch's unpreservable `-1e9 <= diff <= 1e9` with `|diff| + M <= 1e9`.
2. `leq_core`'s callers must establish `M(l, r) <= 1e9`. Because `leq`,
   `is_zero` and `simplify` are mutually recursive, this cannot be a plain
   precondition threaded upward — it has to be an **arena-wide cap axiom**, the
   `local_type_cap()` pattern this crate already uses.

**The trade that makes it worth doing:** +1 cap axiom, −1 `leq` axiom. The count
is unchanged, but what is assumed gets much weaker — "levels in this arena have
bounded measure" instead of "the universe-ordering decision procedure is sound"
— and three more kernel functions become verified rather than trusted.

So the answer to "ceiling or scalar measure" is **scalar measure, no ceiling** —
which is the outcome worth having, since a ceiling on `leq_core` could not have
been discharged the way the `u16` counter's was: `leq_core` returns `bool` on
the verdict path and has nothing to decline to.

## 6. Order of work, if resumed

1. **Find a measure for `leq_core`'s arms.** DONE -- §4's fourth candidate,
   proven. (Three earlier candidates are refuted by explicit witnesses; do not
   start Verus work on a fifth without running it against both `by_cases`
   branches on paper first.)
1b. **Find a measure for the rest of the seven-function clique**, in particular
   the `simplify -> is_zero` edge. NOT done, and not anticipated by this note
   until the call graph was measured -- see the correction above.
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
