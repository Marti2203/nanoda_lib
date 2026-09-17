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

| # | Function | File | Construct | Reason |
|---|---|---|---|---|
| 1 | `subst_levels` | `src/level.rs` | closure capturing `&mut self`; unspecified `alloc` variant | see above |
| 2 | `subst_expr_levels` | `src/expr.rs` | `assert_eq!` is uncompilable by Verus | see above |
