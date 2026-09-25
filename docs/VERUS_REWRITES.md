# Kernel rewrites

Every place where `nanoda_lib`'s original code was changed to let Verus verify
it. The goal is for this list to shrink to nothing.

**The `VERUS-REWRITE(..)` markers in the source are the ground truth**; this
file is a derived index. `scripts/rewrite-register-audit.sh` checks that every
marked function appears here. It cannot check that the *reasons* are still
true — see "Retesting" at the end, which is the more important discipline.

Current: **174 marked rewrites across 104 functions** (counted by `scripts/rewrite-register-audit.sh`).

---

## 1. Rewrites that a change to Verus or vstd would remove

These are not decisions. Each exists because something is missing upstream, and
each would revert if that were supplied.

### Match guards with mutation in the arm — 2 rewrites (reopened 2026-09-25)

`check_positivity1` (`src/inductive.rs`): the guard itself calls a `&mut self`
method (`_any if !self.has_ind_occ(..)`), so it is the `if` before the match on
the same read.

`large_elim_test_aux` (`src/inductive.rs`): a guarded arm inside a `loop`
(`Pi { .. } if rem_params != 0 => ..`) loses the loop invariant at the `_ =>
break` arm, although the same facts hold at the loop head. It looks like the
same resolution gap as below, surfacing at a `break` instead of a postcondition;
it needs a minimal repro and a fork fix. The guard is the `if` at the top of the
arm meanwhile.

Earlier history:

Seven functions had their match guards moved into the arm body, recorded as
"a guarded arm whose body calls `&mut self` makes the postcondition
unprovable". The cause was a Verus bug, not a limitation: resolution
inference dropped any resolution whose first safe point was a
`MatchIntermediate` block (where a failed pattern and a failed guard rejoin),
so on the fallthrough path of every guarded arm a mutable reference was never
resolved and `final(self)` was unconstrained. Upstream had it as a
completeness TODO in `test_match_guards`. Fixed on the fork (branch
`fix-guard-resolution`) by forwarding such resolutions to the block's
successors; repro in `docs/verus-issues/`. All seven are back to the
kernel's guards (`try_reduce_nat` keeps a rewrite, now tagged for its slice
patterns).

### `Option` equality — 0 rewrites, CLOSED

Five comparisons `Some(p) == c` had been rewritten through `opt_expr_eq` /
`opt_expr_is` / `opt_name_is` because `<Option<T> as PartialEq>::eq` is
claim-free in vstd. That reason had gone stale: `Ptr` implements
`PartialEqSpecImpl` (`util_model.rs`), so vstd's trait-level `eq` contract
applies to `Option<Ptr<_>>`. Retested and reverted.

### `Iterator::any` — 0 rewrites, CLOSED

Both `all_uparams_defined` and `contains_param` are back to the kernel's own
`.iter().copied().any(..)`.

Two things were needed, and neither is a vstd change:

1. an explicitly **annotated closure** — `|x: T| -> (r: bool) ensures ..` —
   which is what lets `any`'s `f.ensures((item,), _)` reach the use site;
2. for the **bidirectional** case, naming the trigger term. `any`'s `!r` clause
   is triggered on `old(self).remaining()[i]`, so the proof has to write that
   term before the `forall` will fire:

```ignore
assert(IteratorSpec::remaining(&it0)[i] == ls@[i]);
```

`contains_param`'s contract is `result == (exists ..)` and must stay so —
`inductive_model` consumes the false direction, and a one-directional version
verifies locally while breaking two proofs there.

### `Iterator::zip` — 2 rewrites

| function | file | why, precisely |
|---|---|---|
| `eq_antisymm_many` | `src/level.rs` | its closure captures `&mut self` — rejected outright, see above |
| `ctor_app_params_ok` | `src/inductive.rs` | see below |

`zip` itself has a full spec upstream (#2858), so "no spec" is the wrong
reason for either.

`ctor_app_params_ok`'s original is
`for (app, param) in ctor_apps.iter().copied().zip(local_params.iter().copied())`.
Two separate things block it, and only one is about `zip`:

1. the **tuple pattern** `(app, param)` in the `for` — "only variables are
   supported here, not general patterns". Destructuring inside the body
   instead (`for pair in ..` then `let (app, param) = pair;`) clears this, and
   the function then compiles;
2. what is left is the **postcondition**, which is bidirectional
   (`result == (.. && forall i ..)`) and so needs each loop step related back
   to a slice INDEX. A `for` over a `Zip` gives an iterator-shaped invariant,
   and bridging that to `ctor_apps@[k]` is the same missing link as `any`'s.

So the index walk stays. The `any` sites turned out NOT to need a new lemma —
an annotated closure plus naming the trigger term was enough (see above) — but
that technique does not transfer here, because a `for` over a `Zip` gives an
iterator-shaped invariant rather than an `ensures` to instantiate. Rewriting it
with `enumerate` was tried and is worse: `Iterator::enumerate` has no spec
either, and it changes the kernel's line more, not less.

### `Iterator::enumerate` — 6 rewrites

| function | file | missing |
|---|---|---|
| `mk_majors` | `src/inductive.rs` | `enumerate` |
| `which_valid_ind_app` | `src/inductive.rs` | `enumerate`: with the fork's specification the loop body still cannot show `ind_const == st.ind_consts@[i]` (tried 2026-09-25) |
| `mk_recursors` | `src/inductive.rs` | `enumerate` over the block inductives |
| `mk_ind_tys_env_ext` | `src/inductive.rs` | `enumerate` over the block inductives |
| `mk_minors1group` | `src/inductive.rs` | `enumerate` over the constructors; also the iterators handed to `foldl_apps`/`abstr_pis` bound to locals so the proof can name their elements (same calls) |
| `handle_rec_args_minor` | `src/inductive.rs` | `enumerate` over `rec_args`; also the reversed index iterator and the two `xs` iterators bound to locals so the proof can name their elements (same calls) |

All three of `nth`, `position` and `enumerate` have now been **specified on the
fork** (`d5d5e80fa`) — they genuinely had none, checked directly rather than
taken from the comments.

Two of the three reverted on the strength of it. `inst_aux`'s `Var` arm is back
to the kernel's
`substs.iter().rev().nth((dbj_idx - offset) as usize).copied().unwrap_or(e)`,
and `abstr_aux`'s `Local` arm has its `position(|x| *x == e)` back — only the
`.map` is still rewritten, because *that* closure captures `&mut self` (it is
counted under the `&mut self` heading above, not here).

`mk_majors` keeps its rewrite regardless: it also has an unguarded index worth
guarding.

### An unspecified `alloc` variant — 2 rewrites

`subst_levels` (`src/level.rs`), which also has a closure capturing
`&mut self`; `mk_elim_level` (`src/inductive.rs`), `alloc_levels(Arc::from(base))`
→ `alloc_levels_slice(base.as_slice())`, the same hash-consed allocation.

---

### A temporary in a `for` loop's iterator expression — 1 rewrite

`for l in self.read_levels(ls).iter().copied()` is rejected with E0716: Verus's
`for` desugaring drops the temporary `Arc` while the iterator still borrows it.
Binding the call to a local first is behaviour-identical.

| function | file |
|---|---|
| `no_dupes_all_params` | `src/level.rs` |

### `flat_map` / `map` + `collect` — 8 rewrites

`st.minors.iter().flat_map(|v| v.iter().copied()).collect::<Vec<ExprPtr>>()`
and `hs.iter().map(|x| x.name).collect::<Vec<_>>()`: vstd specifies neither
`flat_map` nor `collect` through a closure adapter (`collect` instantiates its
postcondition at the adapter's unresolved `Item` projection). They are the
verified free functions `flatten_minors` (result `flat_ptrs(minors@)`),
`ind_names` and `ctor_names` (`src/inductive.rs`), the scans they stand for;
same elements, same order.

| function | file |
|---|---|
| `flatten_minors`, `ind_names`, `ctor_names`, `rec_names_set` (the definitions) | `src/inductive.rs` |
| `check_inductive_declar` (the recursor-name set through `rec_names_set`) | `src/inductive.rs` |
| `mk_rec_rules`, `mk_recursors`, `mk_ind_tys_env_ext` | `src/inductive.rs` |

`handle_rec_ctor_args_rec_rule` and `mk_recursor_aux` call them too (their
markers are under `index-walk` / `rec-ty-split`).

### `Box<dyn Error>` — 1 rewrite

Verus cannot declare `core::error::Error` for a `dyn` type: an
`external_trait_specification` for it fails the trait-conflict check on its
`Debug`/`Display` supertraits. `check_declar_info` keeps its original
signature as an unverified wrapper that only formats the error; its checks run
in `check_declar_info_core`, which returns the sort and an `ok` flag.

| function | file |
|---|---|
| `check_declar_info` | `src/tc.rs` |

## 2. Rewrites needing a Verus language feature

### Slice patterns — 4 rewrites

| function | file |
|---|---|
| `abstr_pi_telescope` | `src/expr.rs` |
| `abstr_lambda_telescope` | `src/expr.rs` |
| `init_k_target` | `src/inductive.rs` |
| `large_elim_test` | `src/inductive.rs` |

Unsupported outright, confirmed on current upstream:

```
rust_to_vir_expr.rs:  PatKind::Slice(..) => unsupported_err!(pat.span, "slice patterns", pat)
```

Each is an index walk instead. (Recently landed *index range* syntax — #2913,
#2959 — is a different feature and does not help here.)

### Closures capturing `&mut self` — 12 rewrites

| function | file |
|---|---|
| `subst_levels` | `src/level.rs` |
| `eq_antisymm_many` | `src/level.rs` |
| `str_lit_to_ctor_reducing` | `src/tc.rs` |
| `abstr_aux` (`.map` only) | `src/expr.rs` |
| `def_eq_app` | `src/tc.rs` |
| `args_def_eq_rev` | `src/tc.rs` |
| `check_declar` (the value check, lifted into the verified `check_declar_value`) | `src/tc.rs` |
| `has_ind_occ` (the closure given to `find_const` is `find_const_named` over the block constants' names, read out first; `find_const_named` is `find_const_aux`'s traversal and memo with that predicate) | `src/inductive.rs` |
| `is_nested_ind_app` (the same: its `find_const` closure tests the block's type names, so it is `find_const_named` over `ind_names` of the block) | `src/inductive.rs` |
| `is_recursive` (its `with_ctx` closure is inlined after the two lines `with_ctx` runs -- a fresh `LeanDag`, a `TcCtx` over it -- and its `return true` returns the same value; the `find_const` closure is `find_const_named` over `all_ind_names`; the `for` over constructor names is the scan by index) | `src/inductive.rs` |
| `check_inductive_declar` (each `self.with_ctx(|ctx| ..)` is the fresh `LeanDag` and `TcCtx` it builds, then the body; each `ctx.with_tc(limit, |tc| ..)` / `ctx.with_tc_and_env_ext(ext, limit, |tc| ..)` is the environment it builds -- `env_model::ctx_env` / `ctx_env_ext`, i.e. the same `new_env` / `Env::new_w_temp_ext`, trusted to match the context (option A) -- and `TypeChecker::new` on the same context, then the body. Same calls, same order) | `src/inductive.rs` |
| `has_nested_pfx` (the closure given to `find_e` is `find_nested_pfx_aux`, `find_aux`'s traversal and memo with that predicate; the debug-build `debug_assert_eq!(.., format!(..))` is the same check behind the claim-free `debug_check_nested_pfx`, since Verus does not process `format!`) | `src/expr.rs` |

Rejected outright, and the message is explicit:

```
Verus does not currently support closures capturing a mutable reference
(mutably captured variable `self`)
```

Each is spelled as the `match`/index walk the adapter desugars to. This is the
one blocker left in the 46-function `def_eq` cycle that is not an `.unwrap()`.

### A borrow passed as a raw pointer — 5 rewrites

`debug_assert!(!std::ptr::eq(old, new))` is rejected ("dereferencing a
pointer ... the dereference is implicit"): Verus does not model the implicit
`&T` to `*const T` coercion. The same call sits behind the claim-free
`env_model::same_object` (`#[verifier::external_body]`, no contract).

| function | file |
|---|---|
| `assert_nonnested_tys_def_eq` | `src/inductive.rs` |
| `assert_nonnested_ctors_def_eq` | `src/inductive.rs` |
| `assert_nonnested_rec_rule_def_eq`, `assert_nonnested_recursors_def_eq` (`assert!(!std::ptr::eq(..))`) | `src/inductive.rs` |
| `restore_and_check` | `src/inductive.rs` |

### Formatted panic messages and `&A == &B` — 2 rewrites

`ck_recursor_names_simple`: the mismatch `panic!` formats `debug_print` output,
which Verus cannot process, so the same `panic!` sits behind the claim-free
`recursor_names_mismatch` (`#[verifier::external_body]`, returns `!`); and
`&derived == from_parser` is `derived == *from_parser` -- the same comparison,
written on the sets, where the fork's `HashSet` `PartialEq` specification
applies (`&A`'s forwarding `eq` carries none).

| function | file |
|---|---|
| `ck_recursor_names_simple` | `src/inductive.rs` |

### A local named `old` — 2 rewrites

`old` is Verus's pre-state operator in contracts and loop invariants; a
parameter or pattern binding named `old` in scope turns every `old(self)` into
a call of that local (E0618). Renamed where a contract or invariant is in its
scope: `assert_nonnested_rec_rule_def_eq`'s parameter (`old_uparams`) and
`assert_nonnested_recursors_def_eq`'s pattern binding (`old_d`). Bindings named
`old` whose scope holds no contract (`assert_nonnested_tys_def_eq`,
`restore_and_check`, ...) are unchanged.

| function | file |
|---|---|
| `assert_nonnested_rec_rule_def_eq` | `src/inductive.rs` |
| `assert_nonnested_recursors_def_eq` | `src/inductive.rs` |

### An exit proof inside a `while let` — 2 rewrites

`unfold_apps` and `unfold_apps_stack` (`src/expr.rs`) are `loop` + `match`;
so is `abstr_pis` (`src/expr.rs`), whose `while let Some(b) = binders.next_back()`
needs the iterator's emptiness at exit.

`while let` itself is fine — Verus desugars it to exactly that and it accepts
`invariant`/`ensures`. The problem is narrower: these two put a `proof` block
in the **wildcard arm**, establishing that the spine stops there
(`spine_args(e).reverse() =~= empty`), and the desugaring generates that arm so
there is nowhere to write it. A `while let ... else { proof { .. } }` form
would close this.

---

## 3. Rewrites that are proof structure, not a Verus limitation

These will never be fixed upstream. The construct was accepted; the *proof*
needed a different shape.

| function | file | what |
|---|---|---|
| `is_never_zero` | `src/level.rs` | tail `match` — each arm's fact must be stated about a bound result |
| `def_eq_sort`, `def_eq_const` | `src/tc.rs` | same |
| `get_pfx`, `replace_pfx` | `src/name.rs` | or-pattern — `root_of` must unfold at each constructor, so the arms cannot share a body |
| `def_eq_binder_aux`, `whnf_no_unfolding_aux` | `src/tc.rs` | or-pattern of two tuples; slice pattern |
| `infer_const` | `src/tc.rs` | accessor shape, and an arity check hoisted one frame |
| `infer` | `src/tc.rs` | both cache lookups go through the verified readers `cached_infer_check`/`cached_infer_no_check` — same lookups, and they hand back the caches' claims |
| `is_nat_zero`, `pred_of_nat_succ` | `src/expr.rs` | `read_bignum(..).map(|n| n.is_zero()).unwrap_or(false)` and `read_bignum(ptr)?`, `n - 1u8` → `read_bignum_value`, `biguint_is_zero`, `biguint_pred` |
| `try_string_lit_expansion` | `src/tc.rs` | the `matches!(..) \|\| matches!(..)` bound in two steps so the swapped call's claim can be turned around; same calls, same short-circuit |
| `def_eq_local` | `src/tc.rs` | `x_id == y_id` → `fvar_id_eq` — `FVarId`'s derived `PartialEq` is an unspecified call |
| every `name_cache` read | `src/expr.rs`, `src/tc.rs`, `src/quot.rs` | `name_cache.x` → `name_cache.x()`: the fields are private so that `NameCache` can carry a type invariant (each populated slot holds the name it is named after). The accessor returns the field; the axiom it replaces, `name_cache_ids_ok`, quantified over every `NameCache` value and was refutable by a proof over two fabricated caches |
| `reduce_rec` | `src/tc.rs` | the recursor's counts, major index and rules read through `env_model::get_recursor_data` (literally those fields, with the environment model's claim) instead of off `rec`; the three argument iterators bound to names so the proof can state what each yields; `args.len()` read once so the proof knows the length fits a `usize` |
| `get_rec_rule` | `src/tc.rs` | `for r in rec_rules.iter().copied()` → the same front-to-back scan by index, so the invariant can say no earlier rule matched (the contract names the FIRST matching rule, which is the model's `find_rule`) |
| `get_applied_def` | `src/tc.rs` | the two `get_declar` lookups → `env_model::get_declar_hint`, which is literally that match and carries the name claim |
| `def_eq` | `src/tc.rs` | the two `c_bool_true()` results in the `Bool.true` shortcut are bound to locals where they are called, and the `&&` becomes a nested `if` (same calls, same order, same short-circuit), so the proof can name the pointer each comparison matched |
| `check_ctor` | `src/inductive.rs` | parameter `mut ctor_type_cursor` → `ctor_type_in` with a `let mut` copy (the claim names the entry value) |
| `check_positivity1` | `src/inductive.rs` | parameter `mut ctor_type_cursor` → `ctor_type_in` with a `let mut` copy (the claim names the entry value) |
| `large_elim_test_aux` | `src/inductive.rs` | parameters `mut ctor_type_cursor, mut rem_params` → `ctor_type_in, rem_params_in` with `let mut` copies (the claim names the entry values); the iterator and the result of the final `all` bound to `it`/`r`, so the proof can name what `all` saw |
| `abstr_pis` | `src/expr.rs` | parameters `mut binders, mut body` → `binders_in, body_in` with `let mut` copies (the claim names the entry values); the `IterSpec` bound `foldl_apps` already carries |
| `mk_ctors_env_ext` | `src/inductive.rs` | the two `for` loops (the inner over `.iter().copied().enumerate()`) → front-to-back scans by index |
| `mk_minors`, `mk_rec_rules`, `handle_rec_ctor_args_rec_rule` | `src/inductive.rs` | `for x in v.iter()` / `.iter().copied()` → the same front-to-back scan by index, so the invariant can say which element produced each output (and, in `mk_rec_rules`, where the constructor's minor sits in the flattened list); `handle_rec_ctor_args_rec_rule` also binds the iterators handed to `foldl_apps` to locals, and uses `flatten_minors` |
| `specialize_nested`, `specialize_nested_aux` | `src/inductive.rs` | the `for` loops (over the block's headers, over a clone of header `i`'s constructors, and `for (n, e) in map.iter()` over the specialized-type table) → scans by index / by position (`get_index`); the clone of header `i` is bound to a local (a temporary in a `for` iterator is rejected); `get_mut(i)` + `mem::replace(&mut old.ctors, ..)` → `set(i, ..)` of the same header with the new constructors (`i` is in range, so the kernel's `None => panic!` arm cannot fire); the iterator handed to `abstr_pis` bound to a local |
| `replace_if_nested` | `src/inductive.rs` | `.iter().find(..)` over the specialized-type table → the scan by position it stands for; the two `for`s over the container's `Arc` name lists → scans by index; iterators handed to `foldl_apps`/`abstr_pis` bound to locals; the container's and each constructor's `(uparams, ty)` read through `env_model::get_declar_info_ty` (the same `info`, carrying the claim that the uparams are `Param`s; the `get_inductive`/`get_constructor` reads and their `?` rejections stay); the universe-arity test `subst_expr_levels` panics on made one frame earlier, as in `infer_const` |
| `replace_f` | `src/inductive.rs` | the iterators handed to `foldl_apps` (`.iter().copied()`, `.skip(np)`) bound to locals so the proof can name their elements |
| `mk_specialized_rec_to_unspecialized_map`, `restore_recursor1` | `src/inductive.rs` | `for x in arc.iter().copied().skip(n)` / `for rule in arc.iter().copied()` → the scans by index they stand for |
| `assert_nonnested_recursors_def_eq` | `src/inductive.rs` | `for new_rec in recursors` and the rule loop over `old_rec_rules.iter().zip(new_rec_rules.iter())` → the scans by index they stand for (`zip` has no specification) |
| `restore_recursors` | `src/inductive.rs` | `for rec_name in base_rec_names.iter().copied()` → the `loop` over `next()` it desugars to, the set's iterator and its copy bound to locals so the proof can name what is left of the set; `for .. in map.keys().copied()` → the scan by position (`get_index`) |
| `assert_nonnested_rec_rule_def_eq`, `assert_nonnested_recursors_def_eq` | `src/inductive.rs` | the universe-arity test `subst_expr_levels` panics on, made one frame earlier (as `infer_const`) |
| `check_inductive_declar` | `src/inductive.rs` | `tc.check_declar_info(d).unwrap()` → its verdict part: the declared type tested closed (`assert_closed`), then `check_declar_info_core` (an inductive is not a theorem, so `ok` is always true and the `Err` arm cannot fire); the wrapper's two shadow observations are not made for inductive declarations. The `any` over the block's names (same `is_recursive` calls, same early stop) and every `for` over a slice, `Vec` or map → scans by index; `for r in recursors.clone()` clones each element in turn; `specialize_nested`'s index of the block's first type is tested one frame earlier (the kernel panics there on an empty block) |
| `lazy_delta_step` | `src/tc.rs` | parameters `mut x, mut y` → `x_in, y_in` with `let mut x = x_in` — the claim is about the entry values, which a mutated parameter cannot name inside the loop |
| `do_nat_bin` | `src/tc.rs` | each operation through its `biguint_*` wrapper, which calls the same `util::nat_*` function (or `Pow::pow`, `==`, `<=`) and carries the value contract |
| `reduce_proj` | `src/tc.rs` | `get_constructor(&name)?.num_params` read through `get_constructor_num_params`, defined as exactly that and carrying the environment's claim |
| `reduce_quot` | `src/tc.rs` | the major premise's index is chosen first, then one `get` and one `whnf` -- the same work as the original's two branches |
| `def_eq_quick_check` | `src/tc.rs` | the `eq_cache` lookup goes through `cached_eq`, the same lookup with the cache's claim |
| `get_bignum_from_expr`, `get_bignum_succ_from_expr` | `src/expr.rs` | `read_bignum(..).cloned()` / `read_bignum(..)? + 1` through `read_bignum_value` / `biguint_succ`, which say which number |
| `mk_rec_rule1` | `src/inductive.rs` | the rule's value is built by the verified `mk_rec_rule_val` (the same calls, same order), which proves its binder arity is params + motives + minors + constructor arguments; `mk_rec_rule1` itself is verified in place and assembles the `RecRule` |
| `mk_recursor_aux` | `src/inductive.rs` | the recursor's type is built by the verified `mk_recursor_ty` (the same calls, same order), which proves its binder arity; `mk_recursor_aux` itself is verified in place and proves the recorded counts are those lengths, so the arity is the counts plus one. The fork specifies `Arc::<[T]>::from` (slice and `Vec`); the name list goes through `ind_names` |
| `check_quot`, `check_eq` | `src/quot.rs` | the expected types are built by the verified `quot_expected_type` / `eq_expected_type` / `eq_refl_expected_type` (the same constructions, same order within each); the shells keep the name lookups, the choice of declaration, the environments and the `assert_def_eq` calls, and are themselves verified in place: the environment through `env_model::ctx_env` (`new_env` with option A's trusted match), `match .. .as_ref() { &[x] => .. }` as the length test and index it stands for, formatted panics behind claim-free helpers (`eq_malformed`, `eq_uparam_count`, `eq_ctor_count`, `invalid_quot`), and both sides of each `assert_def_eq` tested closed (`assert_closed`) |
| `nat_lit_to_constructor` | `src/expr.rs` | `read_bignum(..).unwrap()` → `read_bignum_value` (its `.cloned()`), `is_zero`/`Sub::sub(n, 1u8)` → `biguint_is_zero`/`biguint_pred`, the config flag through `nat_extension_on()` (`Config` is opaque); the local `n` renamed because the contract names the pointer |

The bodies are the kernel's; what changed is where results are bound.

---

## 4. Rewrites that close a real robustness gap

**These should not be reverted.** Each closed a place where the kernel would
panic or wrap on input it does not check. None is a soundness bug — a panic is
still a rejection — but each is an improvement.

| function | file | was |
|---|---|---|
| `mk_nullary_ctor` | `src/tc.rs` | `all_ctor_names[0]` unguarded (unreachable from its one call site, but nothing says so) |
| `reduce_proj` | `src/tc.rs` | `num_params + idx` is guarded (`checked_add`, decline) -- nothing bounds either side and there is nothing wider to widen to |
| `check_inductive_spec_0th`, `check_inductive_specs_mutual1` | `src/inductive.rs` | the binder walk's `i += 1` on a `usize` that nothing bounds (the walk runs until the cursor stops being a `Pi`); overflow is a rejection (`checked_add`). Cannot fire on a real term |
| `is_valid_ind_app` | `src/inductive.rs` | `np + num_indices` on `usize`, which nothing bounds for Verus; overflow panics, as in a debug build (`checked_add`). The index walk over `np..len` replaces `for .. in &ctor_apps[np..]` (a `RangeFrom` slice fails precondition discharge) |
| `mk_unique` | `src/util.rs` | `self.unique_counter += 1` on a `u32`, which WRAPS in a release build: after 2^32 locals two different locals would share an id, which unlike the others here could make distinct locals compare equal. Overflow is a rejection now (`checked_add`) |
| `infer_proj` | `src/tc.rs` | `get_structure` states nothing, so two consistency checks were added that never fail on a well-formed environment: the structure's first constructor is the one the environment model records (`get_structure_first_ctor`), and the constructor's own parameter count equals the inductive's (`get_constructor_num_params`) — the projection typing rule is stated with the constructor's |
| `to_ctor_when_k` | `src/tc.rs` | K-like replacement additionally tests that the major premise's type is a proposition (`is_prop`) — the kernel relies on K-like recursors existing only for `Prop` inductives, which is what makes the swap a proof-irrelevance step; never fails on a well-formed environment, costs one inference when K fires |
| `def_eq_unit`, `try_eta_struct_aux` | `src/tc.rs` | the structure's constructor and its field count tested against the environment model's records, as in `infer_proj` (decline otherwise; never fails on a well-formed environment) |
| `expand_eta_struct_aux` | `src/tc.rs` | two consistency checks on the environment, as in `infer_proj`, never failing on a well-formed one: the structure's constructor is the one the environment model records, and so is the constructor's field count (declines otherwise) |
| `reduce_rec` | `src/tc.rs` | the recursor's parameters, motives and minor premises are TESTED to precede its major premise (declines otherwise) — true of every well-formed recursor, and the rule instance's argument prefix assumes it |
| `reduce_rec` | `src/tc.rs` | a recursor rule's right-hand side with loose de Bruijn indices was used as is; it is now TESTED closed (`num_loose_bvars == 0`, beside the existing `has_fvars` test) and declined otherwise — a well-formed rule is closed |
| `expand_eta_struct_aux` | `src/tc.rs` | an unguarded index |
| `mk_majors` | `src/inductive.rs` | `st.local_indices[idx]` unguarded |
| `mk_majors` | `src/inductive.rs` | a major premise's type is TESTED closed (`num_loose_bvars == 0`) before `mk_unique`, which now requires it: `local_type_wf` states every local's type is closed, and without the requirement verified code could create one that is not and refute it. The type is the inductive applied to locals, so the check never fails on a well-formed declaration |
| `infer_const` | `src/tc.rs` | the declaration's type is TESTED closed (`!has_fvars`, `num_loose_bvars == 0`; `kernel_check`) — the export parser does not check it, and `get_declar_info_ty`'s specification used to claim it, which a malformed export refutes. Never fails on a well-formed export |
| `infer_proj` | `src/tc.rs` | the same closedness test on the structure constructor's type |
| `unfold_def` | `src/tc.rs` | a declaration value that is not closed is not unfolded (declines) — same reason, for `get_declar_val`'s former claim. Never true of a well-formed export |
| `Ptr` | `src/util.rs` | the struct is defined inside `verus!` with PRIVATE fields (were `pub` for a transparent registration), so verified code cannot build or alter a pointer; specifications read it through `raw_of` / `arena_of` |
| `mk_dbj_level`, `remake_dbj_level`, `mk_unique` | `src/util.rs` | a local's type is TESTED closed before the local is stored (`assert!`); `local_type_wf` states it of every stored local, and unverified callers never checked it. Never fails on a well-formed declaration |
| `go1` (`ExprBVar`) | `src/parser.rs` | a bound variable at index `u16::MAX` is rejected when read; it was stored, and its loose-bvar count overflows on first use while `read_expr` claims every stored `Var` is below `u16::MAX` |
| `gen_elim_level` | `src/inductive.rs` | `i += 1` in an unbounded `loop` (panics at `u64::MAX` -- the crate builds with overflow checks) |
| `abstr_aux` | `src/expr.rs` | `offset + 1` under a binder and the index sum `pos + offset` panic on `u16` overflow (overflow checks are on); both made explicit (the index check also excludes `u16::MAX` itself, which no stored `Var` may hold). With `inst` needing no depth bound at all, this is what retired the arena axiom `depth < 60000` (refutable by allocating a deep term) |
| `leq_core` | `src/level.rs` | `diff - 1` / `diff + 1` in the `Succ` arms panic on `isize` overflow (overflow checks are on); the same checks are made explicit, which is what replaced the arena axiom bounding `leq_measure` (refutable by allocating ~500M nested levels) |
| `NAME`/`LEVEL` hash constants | `src/name.rs`, `src/level.rs` | `STR_HASH`, `NUM_HASH`, `SUCC_HASH`, `MAX_HASH`, `IMAX_HASH`, `PARAM_HASH` widened from `pub(crate)` to `pub` (visibility only): the public `alloc_name`/`alloc_level` specifications name them in their canonical-hash precondition |
| `pi_telescope_size` | `src/expr.rs` | `size += 1` on a `u16` panics on overflow (overflow checks are on); the check is explicit, which replaced the `depth <= 60000` precondition no caller could discharge. Nothing the original accepted is rejected |
| `mk_ctors_env_ext` | `src/inductive.rs` | `pi_telescope_size(ctor.ty) - num_params` panics on `u16` underflow; the same check, explicit. Never fires on a constructor `check_ctor` accepted |
| `mk_rec_rule1` | `src/inductive.rs` | `pi_telescope_size(ctor.ty) as usize - np` panics on underflow; the same check, explicit, on the size bound to `tele`. Never fires on a constructor `check_ctor` accepted |
| `assert_closed`, `specialize_nested`, `specialize_nested_aux` | `src/inductive.rs` | the types the inductive checker opens with `get_local_params` (the block's first type, each constructor type before specialization) and every type and constructor type it hands on (the final loop, which tested `!has_fvars` only) are TESTED closed -- no locals and no loose de Bruijn indices -- through the new helper `assert_closed`. The export parser checks neither; the verified steps after it require `level_free`. Never fails on a well-formed declaration |
| `replace_if_nested` | `src/inductive.rs` | a nested container's type and its constructors' types are tested free of locals before `subst_expr_levels` (which requires it), as in `infer_proj`. Never fails on a well-formed export |
| `restore_e`, `check_restored_recursor1`, `check_restored_ctor1`, `assert_nonnested_tys_def_eq`, `assert_nonnested_ctors_def_eq` | `src/inductive.rs` | the terms restored from, and every pair handed to `assert_def_eq`, are TESTED closed first (`assert_closed`): opening a recursor's parameters with fresh locals needs it, and it is what puts both sides of the comparison in scope. The export's declarations and the temporary environment's are closed when well formed |
| `assert_nonnested_rec_rule_def_eq`, `assert_nonnested_recursors_def_eq`, `restore_and_check` | `src/inductive.rs` | every pair handed to `assert_def_eq`, and the constructed rule value / imported type substituted into, TESTED closed first (`assert_closed`), as in `check_restored_recursor1` |
| `assert_nonnested_recursors_def_eq` | `src/inductive.rs` | the imported recursor's universe parameters are TESTED to be distinct parameters (`no_dupes_all_params`, the test `check_declar_info` makes of every declaration it checks) before `subst_expr_levels` substitutes for them. Never fails on a well-formed export |
| `check_inductive_declar` | `src/inductive.rs` | the mutual-block limit `start + size` panics on overflow; the same check, explicit |
| `abstr_aux_levels` | `src/expr.rs` | `num_open_binders + 1` under each binder panics on overflow (the crate builds with `overflow-checks = true`, release included); the same check is made explicit at exactly that point, so the result can carry `levels_fit`. Nothing the original accepted is rejected. Replaces the old `open levels + depth < 60000` precondition, which no caller could discharge |

---

## 5. `panic!` and `assert!` on rejection paths — CLOSED (fork `4d9e23468`)

The kernel's panics are rejections, not bugs, and vstd specified every panic
as `requires false`. They used to be routed through two trusted helpers,
`util::kernel_check` / `util::kernel_fail`. nanoda now builds vstd with its
`allow_panic` feature, under which (fork `4d9e23468`) `panic!`, `assert!`,
`assert_eq!` and `Option`/`Result` `unwrap`/`expect` may be reached and do
not return. The original `panic!`/`assert!`/`.unwrap()` text is back at
every rejection site, and both helpers are deleted.

What the feature costs: any panic in the crate now counts as a rejection
rather than a verification error. The checks this project ADDED (overflow
points, closedness and environment-consistency tests) are plain `assert!` /
`panic!` with messages, and are registered under section 4.

## Retesting

A rewrite's justification is a claim about Verus, and it decays — Verus gains
features and vstd gains specifications while the comment stays put. Retested
2026-09-21; three claims were false and one was a fillable gap, and acting on
them removed 15 rewrites:

| claim | verdict |
|---|---|
| `while let` carries no exit reason | false — it desugars correctly and takes loop headers |
| returning out of a `for` leaves the ghost iterator mid-flight | false, for range *and* iterator loops |
| the `?` operator is unusable | false |
| `assert_eq!` is uncompilable | it was *unspecified*; fixed in fork `79263cd85` |

**Retest before relying on a reason, and prefer a probe to a comment.** The
cheapest probe is a three-line function using the construct in isolation,
verified with `cargo verus focus -- --verify-only-module M --verify-function f`.

See `docs/VSTD_GAPS.md` for the upstream side of this.
