# Kernel bodies rewritten for Verus

**Every entry here is a debt, not a decision.** Each one is a place where the
kernel's source differs from what upstream nanoda wrote, purely because Verus
cannot follow the construct. Semantics are preserved in each case, but the
governing project rule is that the original code decides
(`project_original_code_decides`), and "semantics preserved" is an argument,
not a proof. **Come back to each of these when the upstream gap closes and
restore the original body.**

Diff base: the tag `pre-kernel-rewrites`. Everything at or before it verifies
the kernel AS WRITTEN — the only kernel changes up to there are proof
annotations, moving a function inside `verus!`, and renaming locals that
shadowed an `ensures` parameter. To see every rewrite since:

```
git diff pre-kernel-rewrites -- src/expr.rs src/level.rs src/tc.rs \
                                src/util.rs src/inductive.rs src/quot.rs
```

Each rewrite also carries a `// VERUS-REWRITE(<construct>):` marker at the
site, so `grep -rn "VERUS-REWRITE" src/` finds them all without git.

## Why not fix Verus instead

Two upstream fixes landed this way already (#2935 merged, #2944 open), so it is
the preferred route when the fix is small. These two are not.

| Construct | Verus status | Size of the fix |
|---|---|---|
| Closure capturing `&mut self` (e.g. `.map(\|l\| self.subst_level(l, ..))`) | Explicit, deliberate limitation: *"Verus does not currently support closures capturing a mutable reference"* | Deep. Mutable capture interacts with the ownership and prophecy model, not a missing case. |
| Slice patterns (`while let [tl @ .., binder] = xs`) | Flat `unsupported_err!` at `rust_to_vir_expr.rs` `PatKind::Slice` | Substantial. VIR has no pattern form for it (`PatternX` is `Wildcard`/`Var`/`Binding`/`Constructor`/`Or`/`Range`/`Expr`), so it needs a new form or a desugaring plus the exhaustiveness story, spanning `rust_to_vir_expr`, `vir/ast`, and `sst_to_air`. |

Measured cost of NOT fixing them: 43 closure sites and 2 slice-pattern sites
across the kernel, but only the ones on the path to a function actually being
verified ever need touching.

## Register

Entries are added as rewrites land, newest last.

### 1. `TcCtx::subst_levels` — `src/level.rs`

Two changes, of which the second is the one to look at hardest.

**(a) `.map(closure).collect()` → `for` loop.** Verus rejects the closure
outright: it captures `&mut self` to call `self.subst_level`. The loop iterates
the same `ls.iter().copied()` and pushes the same values in the same order.
Low risk: this is the mechanical form of the same fold.

**(b) `alloc_levels(Arc::from(out))` → `alloc_levels_slice(out.as_slice())`.**
Only `alloc_levels_slice` has a specification. The two are *argued* equal, not
proven: both look the pointer up in `export_file.dag.uparams` first and return
an `ExportFile` pointer if found; otherwise `alloc_levels` calls
`insert_full` on the local dag and relies on `IndexSet`'s dedup to return the
existing index, while `alloc_levels_slice` checks `get_index_of` on the local
dag first and only allocates the `Arc` on a genuine miss. Same returned
pointer, different allocation traffic.

**This is the weakest link in the file.** If any rewrite here is wrong, it is
most likely this one. Restoring (a) needs only the Verus closure fix; restoring
(b) needs `alloc_levels` to get a specification, which is independent of Verus
and could be done at any time — it would be a sibling of the
`alloc_levels_slice` axiom already present. Doing (b) would remove the argument
above entirely, and is the cheaper of the two to undo.

### 2. `TcCtx::subst_expr_levels` — `src/expr.rs`

`assert_eq!(self.read_levels(ks).len(), self.read_levels(vs).len());` becomes

```ignore
if self.read_levels(ks).len() != self.read_levels(vs).len() {
    panic!("subst_expr_levels: ks and vs have different lengths");
}
```

Verus cannot compile `assert_eq!` at all — `core::panicking::AssertKind` and
`core::panicking::assert_failed` are both unsupported types/functions, so this
is a hard stop rather than a proof difficulty.

**Lowest risk of anything in this file.** It is the desugaring of the macro:
same panic, same condition, same message channel. It is also *provably
unreachable* given the function's precondition, so the check is dead code under
the contract — which is why swapping it costs nothing semantically. Restore it
when Verus supports the `assert_eq!` expansion.

### 3. `TcCtx::inst_aux` — `src/expr.rs`, `Var` arm only

```ignore
// original
substs.iter().rev().nth((dbj_idx - offset) as usize).copied().unwrap_or(e)

// now
let k = (dbj_idx - offset) as usize;
if k < substs.len() { substs[substs.len() - 1 - k] } else { e }
```

`Iterator::nth` has no spec in vstd — and unlike `Option::copied` (which this
line also needed, and which was added upstream instead of worked around), `nth`
is a consuming adapter method whose spec is not a one-liner.

Risk: low, but higher than entry 2. `iter().rev().nth(k)` is the `k`-th element
from the end, i.e. `substs[len - 1 - k]`, and `None`/`unwrap_or(e)` is the
`k >= len` case. The index arithmetic is the thing to re-check if this is ever
suspected — it reads the same way the model's own `subst_full` does
(`substs[(substs.len() - 1 - (i - offset))]`), which is some independent
confirmation. Restore when `nth` gets a spec.

### 4. `TcCtx::abstr_aux` — `src/expr.rs`, `Local` arm only

```ignore
// original
locals.iter().rev().position(|x| *x == e)
      .map(|pos| self.mk_var(u16::try_from(pos).unwrap() + offset))
      .unwrap_or(e)

// now
let n = locals.len();
let mut pos: usize = 0;
while pos < n && locals[n - 1 - pos] != e { pos = pos + 1; }
if pos < n { self.mk_var((pos as u16) + offset) } else { e }
```

Two closures Verus cannot take: a predicate inside `position`, and a
`&mut self`-capturing one inside `map`.

**Highest risk in this file after entry 1**, on two counts, both worth
re-checking if anything here is ever suspected:

- The `u16::try_from(pos).unwrap()` panic path is gone. The rewrite relies on
  the function's `locals@.len() + offset <= 60000` precondition instead, which
  makes `pos as u16` lossless — but that is a proof obligation moved to callers
  where the original had a runtime check.
- The search direction. `iter().rev().position(p)` counts from the END, so
  position `pos` is element `n - 1 - pos`. The model's `find_from_end` peels
  from the same end, and `find_from_end_first_match` (added with this) is what
  ties the loop to it.

| # | Function | File | Construct | Reason |
|---|---|---|---|---|
| 1 | `subst_levels` | `src/level.rs` | closure capturing `&mut self`; unspecified `alloc` variant | see above |
| 2 | `subst_expr_levels` | `src/expr.rs` | `assert_eq!` is uncompilable by Verus | see above |
| 3 | `inst_aux` (`Var` arm) | `src/expr.rs` | `Iterator::nth` has no spec | see above |
| 4 | `abstr_aux` (`Local` arm) | `src/expr.rs` | closures in `position` and `map` | see above |
| 5 | `unfold_apps_fun`, `num_args`, `unfold_apps_stack` | `src/expr.rs` | `while let` carries no exit reason | see below |
| 6 | `pi_telescope_size` | `src/expr.rs` | `while let` (uniformity with entry 5) | desugaring |
| 7 | `get_nth_pi_binder` | `src/expr.rs` | `return` inside a range `for` | desugaring |
| 8 | `replace_pfx`, `get_pfx` | `src/name.rs` | or-pattern with a match guard; or-pattern needing per-arm unfolding | desugaring |
| 9 | `abstr_pi_telescope`, `abstr_lambda_telescope` | `src/expr.rs` | slice patterns are unsupported outright | index walk |
| 10 | `is_never_zero` | `src/level.rs` | a tail `match` carries no per-arm knowledge out | bind arm results |
| 11 | `all_uparams_defined` | `src/level.rs` | `Iterator::any` has no spec, and the same tail-`match` issue | index loop + bind |
| 12 | `infer_sort` | `src/tc.rs` | `assert!` on a REACHABLE rejection path | `kernel_check` wrapper |
| 13 | `get_rec_rule` | `src/tc.rs` | `return` inside a `for` (same as entry 7) | index walk |
| 16 | `unfold_def` | `src/tc.rs` | `?` operator; `Vec::into_iter` has no spec | `match` + slice |
| 17 | `mk_nullary_ctor` | `src/tc.rs` | `?`; and an UNGUARDED index Verus rejects | `match` + a bounds guard |
| 18 | `expand_eta_struct_aux` | `src/tc.rs` | `?`; range-`for`; an unguarded `.unwrap()` AND an unguarded index | `match` + `while` + two guards |
| 19 | `infer_const` | `src/tc.rs` | closure; `assert!`; a `panic!` with nothing to decline to; a precondition that had to be re-established | accessor swap + `kernel_check` + `kernel_fail` + hoisted check |
| 20 | `mk_majors` | `src/inductive.rs` | `Iterator::enumerate` has no spec; an unguarded index | index walk + a length check |
| 14 | `eq_antisymm_many` | `src/level.rs` | closure capturing `&mut self` inside `zip().all()` | index walk |
| 15 | `def_eq_sort`, `def_eq_const` | `src/tc.rs` | tail-`match` again (entry 10) | bind arm results |


### 5. The three spine helpers — `src/expr.rs`

```ignore
// original
while let App { fun, .. } = self.read_expr(e) { e = fun; }

// now
loop { match self.read_expr(e) { App { fun, .. } => { e = fun; } other => { .. break } } }
```

Verus accepts `while let` and proves the invariant — but carries nothing out of
the loop about *why* it stopped, so the exit cannot conclude the head is not an
`App`. The `loop`/`match` form is its literal desugaring, and is how
`unfold_apps` is already written in the kernel a few functions away.

**Lowest risk in this file, with entry 2.** It is a desugaring, not a
reformulation. Two things were needed on top, and neither is a body change: a
loop `ensures` clause for the exit-only fact, and `num_args` gaining a ceiling
on the spine length, since nothing else in it bounds the `usize` counter.

On the loop clauses: a Verus loop has `invariant` (survives a `break`),
`invariant_except_break` (does not), and `ensures` (proven at each exit). The
invariant needs no repeating in the `ensures` — only a fact that holds *solely*
at exit belongs there.


### 6-7. The two telescope helpers — `src/expr.rs`

Both are desugarings, in the same low-risk class as entries 2 and 5.

`pi_telescope_size`: `while let` to `loop`/`match`, purely to keep the family
uniform — its exit needs no extra fact, unlike entry 5.

`get_nth_pi_binder`: the original walks with `for _ in 0..n` containing a
`return None`. Returning out of a `for` leaves the ghost iterator mid-flight, so
it is spelled as the `while` over an explicit index that it desugars to.

**Worth noting about both contracts, and not a rewrite issue:** they are
one-directional on purpose. `to_model_of_expr` sends BOTH `Pi` and `Lambda` to
`ExprSpec::Bind`, so a telescope that stops at a `Lambda` is indistinguishable
in the model from one that ran out of binders. `pi_telescope_size` therefore
claims its result is *a* peelable count, not the maximal one, and
`get_nth_pi_binder` says nothing about its `None` case. Claiming more would be
claiming something false.


### 8. The two name walkers — `src/name.rs`

`replace_pfx`: Verus rejects *"a match arm containing both an or-pattern (|) and
a match-guard"*, so `Str(..) | Num(..) if n == outgoing` is split into two
guarded arms. Order is preserved, so the two are equivalent.

`get_pfx`: `Str(pfx, ..) | Num(pfx, ..)` is split so each branch can unfold
`root_of` at its own constructor, and `sfx` is bound so the proof can name the
node's shape. Bodies are identical between the two arms.

Both are the lowest-risk kind: no control flow changes, no reordering.


### 9. The two kernel telescopes — `src/expr.rs`

```ignore
// original
while let [tl @ .., binder] = binders { e = self.abstr_pi(*binder, e); binders = tl; }

// now
let mut n = binders.len();
while n > 0 { e = self.abstr_pi(binders[n - 1], e); n = n - 1; }
```

Verus rejects slice patterns outright — `PatKind::Slice` is a flat
`unsupported_err!` in `rust_to_vir_expr.rs`, not a proof difficulty. The index
walk takes the same element in the same order.

Risk: low, but check the direction if ever suspected. `[tl @ .., binder]` binds
the LAST element, so the walk goes `binders[n-1]` downward — a telescope is
built from the inside out. Getting this backwards would silently reverse the
binder order, and the model contract (`abstr_pi_telescope_model`, which peels
`drop_last`) is what pins it.


### 10-11. The two verified level predicates — `src/level.rs`

Both are the lowest-risk class, alongside entries 2 and 5: no control flow
changes, no reordering, no arm bodies touched.

`is_never_zero`: each arm's result is bound to a local before being returned.
A `match` in tail position carries nothing per-arm out to the postcondition, so
the arm's own fact cannot be stated about the result without a name for it.
This is a *proof* limitation rather than a missing feature, and it recurs — the
memo-cache work hit the same wall. Restore by inlining the locals if Verus ever
propagates per-arm knowledge out of a tail `match`.

`all_uparams_defined`: the same binding, plus the `Param` arm's

```ignore
// original
self.read_levels(params).iter().copied().any(|x| x == level)

// now
let ls = self.read_levels(params);
let mut i = 0; let mut found = false;
while i < ls.len() { if ls[i] == level { found = true; } i = i + 1; }
found
```

`Iterator::any` has no spec in vstd — the same gap `nth` has (entry 3), and
unlike `Option::copied`, not a one-liner to add: `any` is a short-circuiting
consumer whose spec has to talk about the prefix it examined.

Risk: low, and the one thing to re-check if ever suspected is that the loop
does NOT short-circuit where the original does. It scans the whole list and
records a hit. Same answer, more work — and `found` is only ever set, never
cleared, so an early match cannot be lost. Restore when `any` gets a spec.


### 12. The kernel's rejection checks — `src/tc.rs` and beyond

```ignore
// original
assert!(self.ctx.all_uparams_defined(l, declar_info.uparams))

// now
crate::util::kernel_check(
    self.ctx.all_uparams_defined(l, declar_info.uparams),
    "infer_sort: level mentions an undeclared universe parameter",
);
```

This one is different in kind from entry 2, and the difference matters.

Entry 2 replaced an `assert_eq!` that Verus cannot COMPILE, on a path the
function's own precondition already proves unreachable. Here the macro compiles
fine; what fails is the proof. Verus specifies `panic!` with `requires false`,
so every panic has to be shown unreachable — and the kernel's rejection checks
are emphatically reachable. Rejecting a malformed declaration is their job. No
precondition will ever discharge them, because adding one would mean assuming
the very thing the kernel is checking.

`kernel_check` is `external_body` so Verus does not look inside, and it states
NOTHING — no `ensures`. It adds no trust claim (the trust-surface count tracks
`assume_specification`s and `external_body` PROOF fns; this is an exec fn that
promises nothing), and Verus treats it as possibly returning normally, which is
the conservative reading: code after the call still verifies without assuming
the check passed.

**Expect this to recur across every `tc.rs` function.** It is the generic
adapter for the kernel's abort-on-bad-input style, not a one-off. Restoring the
macro needs Verus to offer a sanctioned "reachable abort" in exec code, which
is a language question rather than a missing spec.


### 17. `mk_nullary_ctor`'s unguarded index — `src/tc.rs`

The only entry so far that changes behaviour on an input rather than just
re-spelling one, which is why it is worth reading carefully.

```ignore
// original
let ctor_name = all_ctor_names[0];

// now
if all_ctor_names.len() == 0 { return None }
let ctor_name = all_ctor_names[0];
```

An inductive with NO constructors — `False`, `Empty` — would panic on that
index. Verus rejected it, which is the point: nothing in the code establishes
that the list is non-empty.

**It is unreachable from the one call site.** `to_ctor_when_k` calls it only
when `rec.is_k`, and a K-like recursor belongs to an inductive with exactly one
constructor. So the guard fires on no input the checker can actually reach, and
the two versions agree everywhere reachable.

The function already returns `Option`, so `None` is the natural total answer
rather than an invented one: the caller reads it as "K-reduction does not
apply" and carries on. Restoring the original needs a precondition saying the
constructor list is non-empty, which in turn needs `get_inductive` to promise
something about the declaration — the same declaration-content model that
`infer_const` and `expand_eta_struct_aux` are waiting on.

Same family as the three unchecked `u16` arithmetic sites recorded elsewhere
(`abstr_aux`'s offset, `fvar_to_bvar`'s subtraction, `dbj_level_counter`'s
increment): real, unreachable with well-formed input, and unchecked until
something forced the question.


### 18. `expand_eta_struct_aux` — two more unguarded panics

Same shape as entry 17, twice over, in the function that expands a structure
value into an explicit constructor application.

```ignore
// was
let ConstructorData { num_params, num_fields, .. } =
    self.env.get_constructor(&ctor_name0).unwrap();
...
for i in 0..((*num_params) as usize) { out = self.ctx.mk_app(out, args[i]) }

// now
let ConstructorData { .. } = match self.env.get_constructor(&ctor_name0) {
    Some(p) => p, None => return None,
};
if args.len() < (*num_params) as usize { return None }
```

- the `.unwrap()` panics if a structure's first constructor name is not
  registered as a constructor;
- `args[i]` panics if the head application supplies fewer arguments than the
  structure has parameters.

Both hold for well-formed input and neither is expressed in the code. For a
well-typed `e_type` the second is a fact about the CALLER, which is exactly the
kind of thing a contract would carry and a bare index does not. The function
returns `Option`, so both decline.

Restoring either needs `get_constructor`/`get_structure` to promise something
about the declaration, which is the declaration-content model still outstanding.


### 19. `infer_const` — and `kernel_fail`, for a panic with nowhere to go

Four changes, of which the last is the interesting one.

- **accessor swap.** `get_declar(..).map(|x| x.info()).cloned()` becomes
  `env_model::get_declar_info_ty(..)`, which is DEFINED as
  `env.get_declar(n).map(|d| (d.info().uparams, d.info().ty))`. Same lookup,
  same fields, and the closure was one Verus cannot take anyway. The wrapper is
  what carries a contract.
- **`assert!` → `kernel_check`**, as entry 12.
- **`panic!` → `kernel_fail`.** This function returns `ExprPtr`, so unlike
  entries 17 and 18 there is nothing to decline to. `kernel_fail` is the
  diverging counterpart of `kernel_check`: `external_body`, claim-free, and
  Verus treats its result as an arbitrary `T` it knows nothing about — the
  conservative reading, since any postcondition would have to hold for that
  arbitrary value. It cannot be used to smuggle a fact in.
- **hoisted arity check.** `subst_expr_levels` panics on an arity mismatch, and
  entry 2 turned that panic into a PRECONDITION — provably unreachable there,
  but only because the caller is meant to guarantee it. `infer_const` is that
  caller and did not. The same check now sits one frame earlier, written as
  `if .. { return kernel_fail(..) }` so the fallthrough actually learns the
  equality. Same condition, same abort.

That last point is worth generalising: **entry 2 moved an obligation rather than
discharging it**, and this is where it landed. Expect the same wherever a
rewrite replaced a runtime check with a precondition.

`get_declar_info_ty`'s axiom also gained `!has_fv(ty)`, exactly as
`get_declar_val` did for values: a stored declaration TYPE cannot mention a
local constant either, and `nlbv == 0` is only the de Bruijn half.
