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
