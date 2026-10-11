# Kernel rewrites

Every place where `nanoda_lib`'s original code was changed to let Verus verify
it. The goal is for this list to shrink to nothing.

**The `VERUS-REWRITE(..)` markers in the source are the ground truth**; this
file is a derived index. `scripts/rewrite-register-audit.sh` checks that every
marked function appears here. It cannot check that the *reasons* are still
true — see "Retesting" at the end, which is the more important discipline.

Current: **217 marked rewrites across 124 functions** (counted by `scripts/rewrite-register-audit.sh`).

---

## 1. Rewrites that a change to Verus or vstd would remove

These are not decisions. Each exists because something is missing upstream, and
each would revert if that were supplied.

### Match guards with mutation in the arm — 0 rewrites, CLOSED (2026-10-11)

Both are back to the kernel's guards: `check_positivity1`'s
`_any if !self.has_ind_occ(..) => return` and `large_elim_test_aux`'s
`Pi { .. } if rem_params != 0 => ..` inside its `loop`. Retested on the fork
merged with upstream 2026-10-11 and they verify unchanged; the loop-invariant
loss at the `break` recorded 2026-09-25 no longer reproduces.

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

### `Iterator::zip` — 1 rewrite

| function | file | why, precisely |
|---|---|---|
| `eq_antisymm_many` | `src/level.rs` | its closure captures `&mut self` — rejected outright, see above |

`ctor_app_params_ok` is back to the kernel's
`for (app, param) in ctor_apps.iter().copied().zip(local_params.iter().copied())`
(2026-10-11). Both earlier blockers are gone: a tuple pattern in a `for` is
accepted now, and the bidirectional postcondition goes through once the
loop's own sequence is stated as the zipped pairs,

```ignore
forall|k: int| 0 <= k < local_params@.len() ==> #[trigger] it.seq()[k] == (ctor_apps@[k], local_params@[k]),
```

together with `local_params.len() == local_params@.len()`: the spec-mode
`len()` is a `usize`, which is what lets the `usize` positions the iterator
reports stand for `int` indices.

### `Iterator::enumerate` — 0 rewrites, CLOSED (2026-10-11)

`mk_majors`, `which_valid_ind_app`, `mk_recursors`, `mk_ind_tys_env_ext`,
`mk_minors1group` and `handle_rec_args_minor` are back to the kernel's
`for (i, x) in v.iter()[.copied()].enumerate()`. The fork's specification
(`d5d5e80fa`, upstream PR #2904) was enough all along; what the 2026-09-25
attempt lacked was the loop invariant naming the iterator's sequence,

```ignore
v.len() == v@.len(),
it.seq().len() == v@.len(),
forall|k: int| 0 <= k < v@.len() ==> #[trigger] it.seq()[k] == (k as usize, v@[k]),
```

after which the body knows `(i, x) == it.seq()[it.index()]`. `mk_majors`'s
explicit length test went with its rewrite: the function requires
`ind_consts.len() <= local_indices.len()`, so the kernel's
`st.local_indices[idx]` is proven in bounds.

`nth` and `position` are specified too (`position` is upstream's #2849 now,
which also checks the closure's precondition on every element):
`inst_aux`'s `Var` arm is the kernel's
`substs.iter().rev().nth((dbj_idx - offset) as usize).copied().unwrap_or(e)`,
and `abstr_aux`'s `Local` arm has its `position(|x| *x == e)` back — only the
`.map` is still rewritten, because *that* closure captures `&mut self` (it is
counted under the `&mut self` heading above, not here).

### An iterator handed to a call, bound to a local first

`let it = v.iter().copied(); self.ctx.foldl_apps(f, it)` instead of
`self.ctx.foldl_apps(f, v.iter().copied())`: the callee's postcondition is
stated over the iterator's `remaining()`, and a proof can only connect that
to `v@` for an iterator it can name. Inlining it back loses the fact
(retested on `mk_majors`, 2026-10-11). Same calls, same order.

| function | file |
|---|---|
| `mk_majors`, `mk_minors1group`, `handle_rec_args_minor`, `handle_rec_ctor_args_rec_rule` | `src/inductive.rs` |
| `mk_rec_rule_val` (constructor arguments, induction hypotheses), `mk_recursor_ty` (the indices) | `src/inductive.rs` |

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

### `flat_map` / `collect` — 4 rewrites

`.map(|x| x.name).collect()` is the kernel's again where it stood alone
(2026-10-11): `mk_ind_tys_env_ext`'s two name lists (into `Arc<[NamePtr]>`)
and `mk_recursor_aux`'s `all_inductives` (into a `Vec`, then `Arc::from`).
The closure is annotated (`|x: &IndTyHeader| -> (n: NamePtr) ensures n == x.name { x.name }`),
which is what lets `collect` state its elements; collecting into `Arc<[T]>`
needed a `FromIteratorSpecImpl` for `Arc<[T]>`, added on the fork.
`ctor_names` is gone.

What remains is `flat_map`, which vstd does not specify at all
(`core::iter::FlatMap` is unsupported), and two places where the list feeds a
closure that captures `&mut self`:

| function | file |
|---|---|
| `flatten_minors` (`st.minors.iter().flat_map(|v| v.iter().copied()).collect()`), called by `mk_rec_rules`, `mk_recursors`, `handle_rec_ctor_args_rec_rule` | `src/inductive.rs` |
| `ind_names` (the block's names, read out for `is_nested_ind_app`'s `find_const` closure; its body is the kernel's `map` + `collect`) | `src/inductive.rs` |
| `rec_names_set`, called by `check_inductive_declar` (the recursor-name set) | `src/inductive.rs` |

### `Box<dyn Error>` — 1 rewrite

Verus cannot declare `core::error::Error` for a `dyn` type: an
`external_trait_specification` for it fails the trait-conflict check on its
`Debug`/`Display` supertraits. Every caller of `check_declar_info` did
`.unwrap()` on its result, so that is what is verified:
`check_declar_info_unwrap` runs the checks (`check_declar_info_core`, after
testing the declared type closed) and, for a theorem whose type is not a
proposition, hands off to the claim-free `declar_info_failure`, which builds the
same `Box<dyn Error>` and unwraps it -- the same message, the same panic. The
`Result`-returning wrapper is gone.

| function | file |
|---|---|
| `check_declar_info_unwrap` | `src/tc.rs` |

### Derived `Clone` — 7 rewrites

Verus accepts `#[derive(Clone)]` on a kernel type but gives the derived
`clone` no postcondition, so each derive was paired with a trusted
`assume_specification` saying the copy is the original. The derives are
written out instead, as `impl Clone` blocks inside `verus!` that prove
`r == *self` (for `IndTyHeader`, field-wise, its `Vec` of `Copy` headers
element by element). Each is exactly the derive's expansion: every field
cloned, a `Copy` field copied. Retired six claiming specifications. Undo if
Verus comes to specify derived `Clone`s.

| function | file | was |
|---|---|---|
| `Clone for RecRule`, `InductiveData`, `ConstructorData`, `RecursorData`, `Declar` (`clone`) | `src/env.rs` | `#[derive(Clone)]` |
| `Clone for CtorHeader`, `IndTyHeader` (`clone`) | `src/inductive.rs` | `#[derive(Clone)]` |

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

### Formatted panic messages and `&A == &B` — 3 rewrites

`ck_recursor_names_simple`: the mismatch `panic!` formats `debug_print` output,
which Verus cannot process, so the same `panic!` sits behind the claim-free
`recursor_names_mismatch` (`#[verifier::external_body]`, returns `!`); and
`&derived == from_parser` is `derived == *from_parser` -- the same comparison,
written on the sets, where the fork's `HashSet` `PartialEq` specification
applies (`&A`'s forwarding `eq` carries none).

| function | file |
|---|---|
| `ck_recursor_names_simple` | `src/inductive.rs` |
| `replace_dbj_level` (the not-a-local `panic!`, behind `replace_dbj_level_not_local`) | `src/util.rs` |

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
| `infer_let`, `infer_lambda` | `src/tc.rs` | the level `infer_sort_of` returns (in `Check` mode) is bound to a local instead of discarded, so the check claim can name the binder type's sort; same call |
| `infer` | `src/tc.rs` | both cache lookups go through the verified readers `cached_infer_check`/`cached_infer_no_check` — same lookups, and they hand back the caches' claims |
| `is_nat_zero`, `pred_of_nat_succ` | `src/expr.rs` | `read_bignum(..).map(|n| n.is_zero()).unwrap_or(false)` and `read_bignum(ptr)?`, `n - 1u8` → `read_bignum_value`, `biguint_is_zero`, `biguint_pred` |
| `try_string_lit_expansion` | `src/tc.rs` | the `matches!(..) \|\| matches!(..)` bound in two steps so the swapped call's claim can be turned around; same calls, same short-circuit |
| `def_eq_local` | `src/tc.rs` | `x_id == y_id` → `fvar_id_eq` — `FVarId`'s derived `PartialEq` is an unspecified call |
| every `name_cache` read | `src/expr.rs`, `src/tc.rs`, `src/quot.rs` | `name_cache.x` → `name_cache.x()`: the fields are private so that `NameCache` can carry a type invariant (each populated slot holds the name it is named after). The accessor returns the field; the axiom it replaces, `name_cache_ids_ok`, quantified over every `NameCache` value and was refutable by a proof over two fabricated caches |
| `reduce_rec` | `src/tc.rs` | the recursor's counts, major index and rules read through `env_model::get_recursor_data` (literally those fields, with the environment model's claim) instead of off `rec`; the three argument iterators bound to names so the proof can state what each yields; `args.len()` read once so the proof knows the length fits a `usize` |
| `check_all_declars_serial` | `src/tc.rs` | `for declar in self.declars.values()` → the front-to-back scan by index (`get_index`), so the invariant can say every earlier declaration is certified |
| `get_rec_rule` | `src/tc.rs` | `for r in rec_rules.iter().copied()` → the same front-to-back scan by index, so the invariant can say no earlier rule matched (the contract names the FIRST matching rule, which is the model's `find_rule`) |
| `get_applied_def` | `src/tc.rs` | the two `get_declar` lookups → `env_model::get_declar_hint`, which is literally that match and carries the name claim |
| `def_eq` | `src/tc.rs` | the two `c_bool_true()` results in the `Bool.true` shortcut are bound to locals where they are called, and the `&&` becomes a nested `if` (same calls, same order, same short-circuit), so the proof can name the pointer each comparison matched |
| `check_ctor` | `src/inductive.rs` | parameter `mut ctor_type_cursor` → `ctor_type_in` with a `let mut` copy (the claim names the entry value) |
| `check_positivity1` | `src/inductive.rs` | parameter `mut ctor_type_cursor` → `ctor_type_in` with a `let mut` copy (the claim names the entry value) |
| `large_elim_test_aux` | `src/inductive.rs` | parameters `mut ctor_type_cursor, mut rem_params` → `ctor_type_in, rem_params_in` with `let mut` copies (the claim names the entry values); the iterator and the result of the final `all` bound to `it`/`r`, so the proof can name what `all` saw |
| `abstr_pis` | `src/expr.rs` | parameters `mut binders, mut body` → `binders_in, body_in` with `let mut` copies (the claim names the entry values); the `IterSpec` bound `foldl_apps` already carries |
| `specialize_nested`, `specialize_nested_aux` | `src/inductive.rs` | the `for` loops (over the block's headers, over a clone of header `i`'s constructors, and `for (n, e) in map.iter()` over the specialized-type table) → scans by index / by position (`get_index`); the clone of header `i` is bound to a local (a temporary in a `for` iterator is rejected); `get_mut(i)` + `mem::replace(&mut old.ctors, ..)` → `set(i, ..)` of the same header with the new constructors (`i` is in range, so the kernel's `None => panic!` arm cannot fire); the iterator handed to `abstr_pis` bound to a local |
| `replace_if_nested` | `src/inductive.rs` | `.iter().find(..)` over the specialized-type table → the scan by position it stands for; the two `for`s over the container's `Arc` name lists → scans by index; iterators handed to `foldl_apps`/`abstr_pis` bound to locals; the container's and each constructor's `(uparams, ty)` read through `env_model::get_declar_info_ty` (the same `info`, carrying the claim that the uparams are `Param`s; the `get_inductive`/`get_constructor` reads and their `?` rejections stay); the universe-arity test `subst_expr_levels` panics on made one frame earlier, as in `infer_const` |
| `replace_f` | `src/inductive.rs` | the iterators handed to `foldl_apps` (`.iter().copied()`, `.skip(np)`) bound to locals so the proof can name their elements |
| `mk_specialized_rec_to_unspecialized_map`, `restore_recursor1` | `src/inductive.rs` | `for x in arc.iter().copied().skip(n)` / `for rule in arc.iter().copied()` → the scans by index they stand for |
| `assert_nonnested_recursors_def_eq` | `src/inductive.rs` | `for new_rec in recursors` and the rule loop over `old_rec_rules.iter().zip(new_rec_rules.iter())` → the scans by index they stand for (`zip` has no specification) |
| `restore_recursors` | `src/inductive.rs` | `for rec_name in base_rec_names.iter().copied()` → the `loop` over `next()` it desugars to, the set's iterator and its copy bound to locals so the proof can name what is left of the set; `for .. in map.keys().copied()` → the scan by position (`get_index`) |
| `assert_nonnested_rec_rule_def_eq`, `assert_nonnested_recursors_def_eq` | `src/inductive.rs` | the universe-arity test `subst_expr_levels` panics on, made one frame earlier (as `infer_const`) |
| `check_inductive_declar` | `src/inductive.rs` | `tc.check_declar_info(d).unwrap()` → its verdict part: the declared type tested closed (`assert_closed`), then `check_declar_info_core` (an inductive is not a theorem, so `ok` is always true and the `Err` arm cannot fire). The `any` over the block's names (same `is_recursive` calls, same early stop) and every `for` over a slice, `Vec` or map → scans by index; `for r in recursors.clone()` clones each element in turn; `specialize_nested`'s index of the block's first type is tested one frame earlier (the kernel panics there on an empty block) |
| `check_declar` | `src/tc.rs` | each `with_tc_and_declar(info, |tc| ..)` / `with_ctx(|ctx| ..)` inlined (a fresh `LeanDag` + `TcCtx`, `ctx_env` limited by the name, `TypeChecker::new` with the declaration); the recursor arm's formatted rejections behind claim-free `recursor_*` helpers (the same `with_ctx` + `panic!`); its `for` over the recursor's inductives a scan by index |
| `Env::new`, `Env::new_w_temp_ext`, `ctx_env`, `ctx_env_ext` | `src/env.rs`, `src/env_model.rs` | the environment takes, as a ghost argument erased at run time, the arenas its declarations belong to (`Env` gains a ghost field `ids` and a type invariant: every declaration it holds is owned by them). Unverified callers (the pretty printer, `with_tc_and_env_ext`, tests) pass `Ghost::assume_new()`; `ctx_env` / `ctx_env_ext` build it from the context's arena ids. `new_w_temp_ext`'s `EnvLimit::ByName` cutoff, `declars.get_index_of(&n).unwrap_or(0)`, is read through `get_full` (the same lookup; `get_index_of` has no specification, `get_full` says where the key sits) so the environment can state its cutoff |
| `get_declar`, `get_temp_declar` | `src/env.rs` | `self.temp_declars.as_ref().and_then(|ext| ext.get(n)).or_else(|| self.get_old_declar(n))` → the `match` it stands for (`get_temp_declar` first, then `get_old_declar`); same lookups, same order |
| `lazy_delta_step` | `src/tc.rs` | parameters `mut x, mut y` → `x_in, y_in` with `let mut x = x_in` — the claim is about the entry values, which a mutated parameter cannot name inside the loop |
| `do_nat_bin` | `src/tc.rs` | each operation through its `biguint_*` wrapper, which calls the same `util::nat_*` function (or `Pow::pow`, `==`, `<=`) and carries the value contract |
| `reduce_proj` | `src/tc.rs` | `get_constructor(&name)?.num_params` read through `get_constructor_num_params`, defined as exactly that and carrying the environment's claim |
| `reduce_quot` | `src/tc.rs` | the major premise's index is chosen first, then one `get` and one `whnf` -- the same work as the original's two branches |
| `def_eq_quick_check` | `src/tc.rs` | the `eq_cache` lookup goes through `cached_eq`, the same lookup with the cache's claim |
| `get_bignum_from_expr`, `get_bignum_succ_from_expr` | `src/expr.rs` | `read_bignum(..).cloned()` / `read_bignum(..)? + 1` through `read_bignum_value` / `biguint_succ`, which say which number |
| `mk_rec_rule1` | `src/inductive.rs` | the rule's value is built by the verified `mk_rec_rule_val` (the same calls, same order), which proves its binder arity is params + motives + minors + constructor arguments; `mk_rec_rule1` itself is verified in place and assembles the `RecRule` |
| `mk_recursor_aux` | `src/inductive.rs` | the recursor's type is built by the verified `mk_recursor_ty` (the same calls, same order), which proves its binder arity; `mk_recursor_aux` itself is verified in place and proves the recorded counts are those lengths, so the arity is the counts plus one. The fork specifies `Arc::<[T]>::from` (slice and `Vec`) |
| `check_quot`, `check_eq` | `src/quot.rs` | the expected types are built by the verified `quot_expected_type` / `eq_expected_type` / `eq_refl_expected_type` (the same constructions, same order within each); the shells keep the name lookups, the choice of declaration, the environments and the `assert_def_eq` calls, and are themselves verified in place: the environment through `env_model::ctx_env` (`new_env` with option A's trusted match), `match .. .as_ref() { &[x] => .. }` as the length test and index it stands for, formatted panics behind claim-free helpers (`eq_malformed`, `eq_uparam_count`, `eq_ctor_count`, `invalid_quot`), and both sides of each `assert_def_eq` tested closed (`assert_closed`) |
| `nat_lit_to_constructor` | `src/expr.rs` | `read_bignum(..).unwrap()` → `read_bignum_value` (its `.cloned()`), `is_zero`/`Sub::sub(n, 1u8)` → `biguint_is_zero`/`biguint_pred`, the config flag through `nat_extension_on()` (`Config` is opaque); the local `n` renamed because the contract names the pointer |
| `ExportFile` (field `ind_name_to_recursor_names`) | `src/util.rs` | `pub` → `pub(crate)` (nothing outside the crate reads it). Verus refuses a type invariant on a struct whose fields are all public outside the crate, and `ExportFile` now carries one: its name cache's arena is its dag's (docs/ARENA_STORAGE.md, stage 2) |
| `alloc_expr` | `src/util.rs` | as `alloc_name`: `insert_full` → `arena_insert`, `Ptr::from` → `Ptr::from_in` (ghost arguments) |
| `alloc_string` | `src/util.rs` | as `alloc_name`: the insertion goes through `LeanDag::insert_export_string` (`arena_insert`), `Ptr::from` → `Ptr::from_in` |
| `alloc_bignum` | `src/util.rs` | as `alloc_name`, and the two `?` on the arenas become matches: the checker's arena is taken out, inserted into with its token and put back (`LeanDag::insert_export_bignum`); same lookups, same `None`s |
| `alloc_level` | `src/util.rs` | as `alloc_name`: `insert_full` → `arena_insert`, `Ptr::from` → `Ptr::from_in` (ghost arguments) |
| `LeanDag::zero` (`zero`) | `src/util.rs` | `Ptr::from` → `Ptr::from_in`, as in `alloc_name` |
| `alloc_name` | `src/util.rs` | `insert_full` → `arena_insert` (pins the appended position of the arena's history) and `Ptr::from` → `Ptr::from_in` (takes the arena); both extra arguments are ghost, erased at run time |
| `LeanDag::anonymous` (`anonymous`) | `src/util.rs` | `Ptr::from` → `Ptr::from_in`, as in `alloc_name` |
| `TcCtx::new` | `src/util.rs` | a ghost block (erased at run time) marks the context's fresh dag as a checker's dag serving the context's export file, which `ctx_ok` (part of `owns`) records |
| `LeanDag::new` | `src/util.rs` | `LeanDag` gains a ghost `toks` field (erased at run time): the history tokens of docs/ARENA_STORAGE.md, which its type invariant ties to the stored sets. `new` fills it with `Tracked::assume_new()` |

The bodies are the kernel's; what changed is where results are bound.

---

## 4. Rewrites that close a real robustness gap

**These should not be reverted.** Each closed a place where the kernel would
panic or wrap on input it does not check. None is a soundness bug — a panic is
still a rejection — but each is an improvement.

| function | file | was |
|---|---|---|
| `mk_nullary_ctor` | `src/tc.rs` | `all_ctor_names[0]` unguarded (unreachable from its one call site, but nothing says so). Also three consistency checks that never fail on a well-formed environment and a well-typed major premise (tested-env): the constructor belongs to the inductive (`get_constructor_inductive_is`), takes `num_params` parameters (`get_constructor_num_params`), and the type supplies them -- the K-like step's claim is stated with the constructor's records |
| `reduce_proj` | `src/tc.rs` | `num_params + idx` is guarded (`checked_add`, decline) -- nothing bounds either side and there is nothing wider to widen to |
| `whnf_same`, `handle_rec_args_aux` | `src/inductive.rs` | the induction hypothesis's telescope is walked through `whnf_same`: each `whnf` is tested to denote its input (`model_eq`; a rejection otherwise), so the walk reads the recursive field's declared type itself (S6.6b). Not used where a field's type may legitimately unfold (`is_rec_argument` keeps plain `whnf`: `optParam`, `outParam` fields). Never fails on a type Lean exports |
| `handle_rec_args_minor` | `src/inductive.rs` | a recursive argument's inferred type (`infer_then_whnf`) is tested to be its declared binder type (`model_eq`; a rejection otherwise), so the induction hypothesis is built from the constructor's field (S6.6b). Never fails on a constructor Lean exports |
| `handle_rec_ctor_args_rec_rule` | `src/inductive.rs` | a recursive argument's inferred type (`infer_then_whnf`) is tested to be its declared binder type (`model_eq`; a rejection otherwise), so the rule's induction hypothesis is built from the constructor's field (S6.6b). Never fails on a constructor Lean exports |
| `sep_nonrec_rec_ctor_args` | `src/inductive.rs` | a field whose type is not a Pi is tested to be recursive (`is_rec_argument`) exactly when its type is literally a block inductive at the parameters (`ind_app_shape`, a new syntactic test; a rejection otherwise), so the recursor's hypotheses sit at the syntactic recursive positions (S6.6b, `recs_syn`). Fields with Pi types (`Acc.intro`'s) are not tested. Never fails on a constructor Lean exports. Also `while-let-exit`: the field walk's `while let Pi { .. } = read_expr(cursor)` is the `loop`/`match` it stands for, so the exit fact (the cursor is no Pi) reaches the proof |
| `assert_nonnested_rec_rule_def_eq` | `src/inductive.rs` | returns (instead of nothing) whether the generated rule at the exported recursor's universe parameters is the exported rule syntactically (`model_eq`, constructor names by `==`); the caller ignores it, so nothing new is rejected. False for inductives whose binder types carry `outParam`/`optParam`/`autoParam` (Lean's export strips them) |
| `assert_nonnested_recursors_def_eq` | `src/inductive.rs` | returns whether every exported recursor is the generated one syntactically (its type through `subst_expr_levels` the other way round, and every rule; `rec_old`); `check_inductive_declar` ignores the result, so nothing new is rejected |
| `literal_whnf`, `check_inductive_spec_0th`, `check_inductive_specs_mutual1` | `src/inductive.rs` | an inductive's type is tested to be a literal telescope (tested-env): each step's `whnf` must find its Pi (or the closing sort) already there, and the walk must end in a sort as it stands; a rejection otherwise. The walk then reads the declared type itself, which the canonical recursor (`rec_canon`) is stated over (S6.6b). Never fails on a type Lean exports |
| `check_inductive_spec_0th`, `check_inductive_specs_mutual1` | `src/inductive.rs` | the binder walk's `i += 1` on a `usize` that nothing bounds (the walk runs until the cursor stops being a `Pi`); overflow is a rejection (`checked_add`). Cannot fire on a real term |
| `is_valid_ind_app` | `src/inductive.rs` | `np + num_indices` on `usize`, which nothing bounds for Verus; overflow panics, as in a debug build (`checked_add`). The index walk over `np..len` replaces `for .. in &ctor_apps[np..]` (a `RangeFrom` slice fails precondition discharge) |
| `mk_unique` | `src/util.rs` | `self.unique_counter += 1` on a `u32`, which WRAPS in a release build: after 2^32 locals two different locals would share an id, which unlike the others here could make distinct locals compare equal. Overflow is a rejection now (`checked_add`) |
| `infer_proj` | `src/tc.rs` | `get_structure` states nothing, so two consistency checks were added that never fail on a well-formed environment: the structure's first constructor is the one the environment model records (`get_structure_first_ctor`), and the constructor's own parameter count equals the inductive's (`get_constructor_num_params`) — the projection typing rule is stated with the constructor's. A third check (tested-input): the field index is below the constructor's field count (`get_constructor_num_fields`); out of range, the walk runs past the constructor's telescope into its result type, which a well-formed environment never reduces to a Pi, so the kernel rejects such input anyway -- regularity of the field type is stated over the constructor's telescope |
| `infer` (literal arms) | `src/tc.rs` | a literal's type constant (`Nat`, `String`) is tested declared without universe parameters at a sort (`lit_type_declared`) -- what makes the literal's inferred type a type; never fails on an export that declares the type before using its literals |
| `check_quot` | `src/quot.rs` | the declared type is also checked as any declaration's is (inferred in `Check` mode to a sort, in the declaration's own environment); the comparison with the expected type does not show the type is a type. Never fails on the quotient declarations Lean exports |
| `check_inductive_declar` | `src/inductive.rs` | a structure's constructor (one constructor, no indices) is tested to name the structure back and to have the structure shape (`TcCtx::ctor_shape_ok`: `np + nf` Pi binders over the structure at the constructor's universe parameters, applied to the parameters); never fails on a structure Lean exports. And the inductive type's declared type is also checked as any declaration's is, in the environment before it and with its own universe parameters; the block's own check runs in an environment that already holds the block, which cannot certify the type. Never fails on a block Lean exports |
| `check_declar` (recursor arm) | `src/tc.rs` | the recursor's rules are checked too (`check_rec_rules`): each value tested closed and inferred in `Check` mode, in the whole environment (a recursive type's rules call the recursor itself), so its universe levels are the recursor's; the block's checker only compares them with the rules it builds, by conversion. Never fails on the rules Lean exports |
| `check_declar` (constructor arm) | `src/tc.rs` | the constructor's parameters are checked against its inductive's (tested-input): the inductive is declared before it with the same universe parameters (pointer-equal `uparams`), the inductive's type has at least `num_params` Pi binders, and the closed term `λ (f : C) (x_i : A_i), f x_0 .. x_{np-1}` over those binders (`TcCtx::ctor_param_term`) is inferred in `Check` mode. It certifies E2' (`ctor_params_ok`). Never fails on a constructor Lean accepted |
| `check_declar` (recursor arm), `assert_rule_ctors_declared` | `src/tc.rs` | each of the recursor's rules names a constructor declared before the recursor (tested-input; `Env::get_constructor` in the environment before it). Certifies the recursor's constructors are in its certificate's environment -- what makes the canonical twin's decision stable along the export (`twins_stable`, docs/TYPED_TARGET.md T3). Never fails on a block Lean exports: a block's constructors precede its recursors |
| `check_ctor` | `src/inductive.rs` | each constructor parameter's type is the inductive's structurally (`model_eq`, binder names aside), tested before nanoda's own `assert_def_eq`, which only requires conversion (tested-input). Gives the canonical shape its syntactic parameters (`gen_shape_ok`, docs/TYPED_TARGET.md B6a); stricter than nanoda's `def_eq`. Never fails on a constructor Lean exports: Init's 808 constructors restate their inductive's parameters |
| `check_ctor` (result levels) | `src/inductive.rs` | the constructor's result is headed by its inductive at exactly the block's universe parameters (`levels_ptr_eq` with `st.uparams`), tested after `is_valid_ind_app`, which compares levels only up to equivalence (`eq_antisymm`) (tested-input). Gives the canonical shape its syntactic result (`gen_shape_ok`); stricter than nanoda. Never fails on a constructor Lean exports: Init's 808 constructors end at their inductive's own parameters |
| `check_inductive_spec_0th` (walk length) | `src/inductive.rs` | the inductive's literal binder walk covers its parameters (`i >= local_params.len()`), tested after the walk (tested-input): `get_local_params` reads the parameters through `whnf`, the walk literally. Gives the canonical shape its parameter telescope (`shape_exists`). Never fails on a type Lean exports: its parameters are binders |
| `assert_nonnested_ctors_def_eq` (model check) | `src/inductive.rs` | each constructor the checker built (the block header's, rebuilt by `specialize_nested`) is the exported one structurally (`model_eq`, binder names aside), tested before nanoda's `assert_def_eq` of the export against the temporary declaration (tested-input); the loops are index walks and the `old` binding is `old_c`. Gives the certificate the declared constructor types (`ctor_old`). Never fails on a block Lean exports: a non-nested constructor is rebuilt as declared |
| `assert_nonnested_tys_def_eq` (model check) | `src/inductive.rs` | the block's first inductive, as the checker walked it (its header's type), is the exported one structurally (`model_eq`) and closed (`assert_closed`), tested after nanoda's comparisons (tested-input). Gives the certificate the declared inductive type and its closedness (`ind_old`). Never fails on a block Lean exports |
| `assert_nonnested_recursors_def_eq` (major head) | `src/inductive.rs` | the exported recursor's major premise, read syntactically (`major_head_name`, `rec_major_head`), is headed by its block inductive (`st.all[n]`), as is the generated recursor's, tested after nanoda's `assert_def_eq` of the two types (tested-input). Gives the twin the inductive `rec_canon::rec_ind` reads off the exported type (`rec_conv`, `block_cert`). Never fails on a recursor Lean exports |
| `check_declar` (recursor major head) | `src/tc.rs` | every exported single-motive recursor's major premise, read syntactically (`major_head_name`), is headed by one of the recursor's own `all_inductives` (tested-input; a nested block's auxiliary recursors eliminate e.g. `List T`, with more motives, and are not tested). `rec_arm_ok` records it; with the parser's recursor table (`rec_names_of`) it makes a simple block's recursor the only one whose major premise is that block's inductive (`rec_scope_g`'s uniqueness). Never fails on a recursor Lean exports |
| `check_declar` (constructor form) | `src/tc.rs` | the constructor's declared type, read literally (`inductive::ctor_form_ok`: `pi_telescope_size`, `pi_body`, the body's head and argument count), is a telescope over its inductive at the constructor's own universe parameters, fully applied, and the inductive's type ends in a sort (tested-input). Recorded in `ctor_e2_cert`; what the judgment reads of every constructor (`kclaims::ctor_form`) with or without its inductive's recursor. nanoda's block check establishes it only for the block's own constructors. Never fails on a constructor Lean exports (Init.Core 3875, Init 57424) |
| `check_declar` (constructor listed) | `src/tc.rs` | the constructor's inductive is an inductive (nanoda tested only that the name exists) that lists the constructor at its `ctor_idx` (tested-input). `check_declar` ensures `ctor_listed`, collected as `export_sound::all_ctors_listed`. Never fails on a constructor Lean exports |
| `check_declar` (recursor rules listed) | `src/tc.rs` | a single-motive recursor's rules are its major premise's inductive's constructors, in order, each rule's field count the constructor's `num_fields` (tested-input; `rules_listed`, recorded in `rec_arm_ok`). What the judgment reads of a recursor's rules (`ind_ok`'s constructor and field-count clauses). Never fails on a recursor Lean exports |
| `assert_nonnested_recursors_def_eq` (restated counts) | `src/inductive.rs` | `RecursorData::aux_data_ck` is not verified (it compares hash sets), so the counts it compares (parameters, indices, motives, minors) are compared again, verified, right after it (restated-check). Never fails where `aux_data_ck` passed; gives `rec_conv` the exported recursor's table data |
| `assert_nonnested_recursors_def_eq` (universe parameters) | `src/inductive.rs` | the exported recursor's universe parameters are its inductive's, possibly behind one fresh one (the motive's universe), by name (`rec_uparams_ok`, `rec_lps_ok`), not only of the right arity (tested-input). What the twin reads (`twin::rec_core`). Never fails on a recursor Lean exports |
| `assert_nonnested_ctors_def_eq` (constructor data) | `src/inductive.rs` | the exported constructor's inductive and parameter count are the block's (tested-input; `aux_data_ck`, unverified, compares them with the temporary declaration's). Recorded in `ctor_old`; what the twin's constructor tables read. Never fails on a block Lean exports |
| `assert_nonnested_ctors_def_eq` (constructor index) | `src/inductive.rs` | the exported constructor's `ctor_idx` is its position in the block (tested-input). `aux_data_ck` compares it with the temporary declaration's, but the temporary map keeps the last of two same-named header constructors, so a block listing one constructor twice passes nanoda's own checks; this rejects it, as Lean's kernel does. Recorded in `ctor_idx_old`; gives `block_ok` distinct constructors (`ctors_distinct`). Never fails on a block Lean exports |
| `check_inductive_declar` (block links) | `src/inductive.rs` | three tested-input checks tying the export to nanoda's branch: a block nanoda finds nested is exported as nested (`ind.is_nested`); a non-nested block's state holds exactly the exported inductives; a single block's first type is the declaration checked. What the block certificate is conditioned on (`block_cert`: single, non-nested). Never fail on a block Lean exports |
| `check_inductive_declar` (constructors' constants) | `src/inductive.rs` | each of the block's constructors mentions only constants declared before the inductive, or the block's inductives (`TcCtx::consts_known` in the environment before the inductive; a single block may mention only its own inductive, `inductive::block_names`; tested-input). Certifies `ctors_known`: a field's type mentions only constants ranked below its inductive, which the model's field codes take (docs/TYPED_TARGET.md R3b). nanoda checks the constructors with only the block's inductives added, but over a block bound the parser supplies (`mutual_block_sizes`), so this was not certified. Never fails on a block Lean exports |
| `to_ctor_when_k` | `src/tc.rs` | K-like replacement additionally tests that the major premise's type is a proposition (`is_prop`) — the kernel relies on K-like recursors existing only for `Prop` inductives, which is what makes the swap a proof-irrelevance step; never fails on a well-formed environment, costs one inference when K fires |
| `def_eq_unit`, `try_eta_struct_aux` | `src/tc.rs` | the structure's constructor and its field count (and, in `try_eta_struct_aux`, its parameter count) tested against the environment model's records, as in `infer_proj` (decline otherwise; never fails on a well-formed environment) |
| `expand_eta_struct_aux` | `src/tc.rs` | the structure type's argument count is tested to EQUAL the parameter count (it was `>=`), and the constructor's parameter count against the environment model's record: the expansion's claim is stated with both; a structure has no indices, so neither fails on a well-typed structure type |
| `expand_eta_struct_aux` | `src/tc.rs` | two consistency checks on the environment, as in `infer_proj`, never failing on a well-formed one: the structure's constructor is the one the environment model records, and so is the constructor's field count (declines otherwise) |
| `reduce_rec` | `src/tc.rs` | the recursor's parameters, motives and minor premises are TESTED to precede its major premise (declines otherwise) — true of every well-formed recursor, and the rule instance's argument prefix assumes it |
| `reduce_rec` | `src/tc.rs` | a recursor rule's right-hand side with loose de Bruijn indices was used as is; it is now TESTED closed (`num_loose_bvars == 0`, beside the existing `has_fvars` test) and declined otherwise — a well-formed rule is closed |
| `expand_eta_struct_aux` | `src/tc.rs` | an unguarded index |
| `mk_majors` | `src/inductive.rs` | a major premise's type is TESTED closed (`num_loose_bvars == 0`) before `mk_unique`, which now requires it, as `alloc_expr` requires every stored local's type closed. The type is the inductive applied to locals, so the check never fails on a well-formed declaration |
| `infer_const` | `src/tc.rs` | the declaration's type is TESTED closed (`!has_fvars`, `num_loose_bvars == 0`; `kernel_check`) — the export parser does not check it, and `get_declar_info_ty`'s specification used to claim it, which a malformed export refutes. Never fails on a well-formed export |
| `infer_proj` | `src/tc.rs` | the same closedness test on the structure constructor's type |
| `unfold_def` | `src/tc.rs` | a declaration value that is not closed is not unfolded (declines) — same reason, for `get_declar_val`'s former claim. Never true of a well-formed export |
| `Ptr` | `src/util.rs` | the struct is defined inside `verus!` with PRIVATE fields (were `pub` for a transparent registration), so verified code cannot build or alter a pointer; specifications read it through `raw_of` / `arena_of` |
| `mk_dbj_level`, `remake_dbj_level`, `mk_unique` | `src/util.rs` | a local's type is TESTED closed before the local is stored (`assert!`); `alloc_expr` requires it of every local it stores, and unverified callers never checked it. Never fails on a well-formed declaration |
| `ExportBuilder::add_expr_var` (was `go1`'s `ExprBVar` arm) | `src/export_builder.rs` | a bound variable at index `u16::MAX` is rejected when read; it was stored, and its loose-bvar count overflows on first use while `read_expr` claims every stored `Var` is below `u16::MAX` |
| `ExportBuilder::level_ptr` (was `Parser::get_levels_ptr`) | `src/export_builder.rs` | a `Const`'s level indices are tested to be stored already, as a name's and an expression's always were; an out-of-range index made a dangling level pointer. Never fails on an export Lean writes |
| `gen_elim_level` | `src/inductive.rs` | `i += 1` in an unbounded `loop` (panics at `u64::MAX` -- the crate builds with overflow checks) |
| `abstr_aux` | `src/expr.rs` | `offset + 1` under a binder and the index sum `pos + offset` panic on `u16` overflow (overflow checks are on); both made explicit (the index check also excludes `u16::MAX` itself, which no stored `Var` may hold). With `inst` needing no depth bound at all, this is what retired the arena axiom `depth < 60000` (refutable by allocating a deep term) |
| `leq_core` | `src/level.rs` | `diff - 1` / `diff + 1` in the `Succ` arms panic on `isize` overflow (overflow checks are on); the same checks are made explicit, which is what replaced the arena axiom bounding `leq_measure` (refutable by allocating ~500M nested levels) |
| `NAME`/`LEVEL` hash constants | `src/name.rs`, `src/level.rs` | `STR_HASH`, `NUM_HASH`, `SUCC_HASH`, `MAX_HASH`, `IMAX_HASH`, `PARAM_HASH` widened from `pub(crate)` to `pub` (visibility only): the public `alloc_name`/`alloc_level` specifications name them in their canonical-hash precondition |
| `RecursorData::major_idx` | `src/env.rs` | the `u16` sum `num_params + num_motives + num_minors + num_indices` panics on overflow (overflow checks are on); the same check, explicit, on the sum computed in `u32`. This is what let the recursors map be DEFINED from the environment's contents (its `major_idx` field is the sum), retiring the claim-free `major_idx` specification |
| `alloc_expr` | `src/util.rs` | children in the context's own tier are TESTED to be already stored (`child_stored`) before an expression is appended, as in `alloc_name`; never fires |
| `alloc_level` | `src/util.rs` | a child in the context's own tier is TESTED to be already stored before a level is appended, as in `alloc_name`; never fires |
| `alloc_name` | `src/util.rs` | a prefix in the context's own tier is TESTED to be already stored (`idx < len`) before a name is appended (`panic!` otherwise). Every pointer the checker holds came from an earlier allocation, so it never fires; it is what lets the appended node's children be placed before it, which the arena history's denotation needs |
| `pi_telescope_size` | `src/expr.rs` | `size += 1` on a `u16` panics on overflow (overflow checks are on); the check is explicit, which replaced the `depth <= 60000` precondition no caller could discharge. Nothing the original accepted is rejected |
| `mk_ctors_env_ext` | `src/inductive.rs` | `pi_telescope_size(ctor.ty) - num_params` panics on `u16` underflow; the same check, explicit. Never fires on a constructor `check_ctor` accepted |
| `mk_rec_rule1` | `src/inductive.rs` | `pi_telescope_size(ctor.ty) as usize - np` panics on underflow; the same check, explicit, on the size bound to `tele`. Never fires on a constructor `check_ctor` accepted |
| `assert_closed`, `specialize_nested`, `specialize_nested_aux` | `src/inductive.rs` | the types the inductive checker opens with `get_local_params` (the block's first type, each constructor type before specialization) and every type and constructor type it hands on (the final loop, which tested `!has_fvars` only) are TESTED closed -- no locals and no loose de Bruijn indices -- through the new helper `assert_closed`. The export parser checks neither; the verified steps after it require `level_free`. Never fails on a well-formed declaration |
| `replace_if_nested` | `src/inductive.rs` | a nested container's type and its constructors' types are tested free of locals before `subst_expr_levels` (which requires it), as in `infer_proj`. Never fails on a well-formed export |
| `restore_e`, `check_restored_recursor1`, `check_restored_ctor1`, `assert_nonnested_tys_def_eq`, `assert_nonnested_ctors_def_eq` | `src/inductive.rs` | the terms restored from, and every pair handed to `assert_def_eq`, are TESTED closed first (`assert_closed`): opening a recursor's parameters with fresh locals needs it, and it is what puts both sides of the comparison in scope. The export's declarations and the temporary environment's are closed when well formed |
| `assert_nonnested_rec_rule_def_eq`, `assert_nonnested_recursors_def_eq`, `restore_and_check` | `src/inductive.rs` | every pair handed to `assert_def_eq`, and the constructed rule value / imported type substituted into, TESTED closed first (`assert_closed`), as in `check_restored_recursor1` |
| `assert_nonnested_recursors_def_eq` | `src/inductive.rs` | the imported recursor's universe parameters are TESTED to be distinct parameters (`no_dupes_all_params`, the test `check_declar_info` makes of every declaration it checks) before `subst_expr_levels` substitutes for them. Never fails on a well-formed export |
| `check_inductive_declar` | `src/inductive.rs` | the mutual-block limit `start + size` panics on overflow; the same check, explicit |
| `check_declar_info_unwrap`, `check_declar` | `src/tc.rs` | every declaration's type (and a definition's value) is TESTED closed before it is checked; the export parser checks neither. Never fails on a well-formed export |
| `abstr_aux_levels` | `src/expr.rs` | `num_open_binders + 1` under each binder panics on overflow (the crate builds with `overflow-checks = true`, release included); the same check is made explicit at exactly that point, so the result can carry `levels_fit`. Nothing the original accepted is rejected. Replaces the old `open levels + depth < 60000` precondition, which no caller could discharge |
| `LeanDag::new`, `LeanDag::new_export` | `src/util.rs` | the anonymous name and level zero were inserted by `LeanDag::new`, so every checker's dag held copies of the export file's two nodes; they are inserted into the export file's dag only (`new_export`, called by `ExportBuilder::new`). The copies were never reached (allocation finds the export file's first), and with the arena denotations defined they made `to_model_name_injective` refutable: two distinct owned pointers, both denoting the anonymous name |
| `Parser` | `src/parser.rs`, `src/export_builder.rs` | the parser only decodes lines; every pointer it made (`Ptr::from`, whose arena tag was `Ghost::assume_new()`) and every node, list and declaration it stored is made by the verified `ExportBuilder`, through the same insertions in the same order (a skipped axiom's parts are still read). `finish` builds the recursor-name table (`.entry(..).or_insert(..).insert(..)` is `remove`, `insert`, `insert`: the same map) and the `ExportFile`, and ENSURES `export_ok`, `export_rec_names_ok` and `export_blocks_ok`, which were assumed of the parser's output. The constructor/inductive consistency check stays in the parser, unverified, same code |

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

Retested again 2026-10-11, after merging upstream into the fork (37
commits; upstream now carries the fork's `HashMap`/`HashSet` `with_hasher`,
`Option::copied`, `<[T]>::reverse`, `<[T]>::contains` and `position`
specifications, so the fork's copies were dropped):

| claim | verdict |
|---|---|
| a `&mut self` call in a match guard breaks the postcondition | false — both guard rewrites reverted |
| `enumerate`'s element/index pairing does not reach the proof | false — it does, with the loop's `it.seq()` named in the invariant |
| a tuple pattern in `for` is rejected | false |
| a `for` over `.copied()` does not discharge its invariants | false |
| `collect` cannot go through a `map` closure | false for an annotated closure into a `Vec`; into `Arc<[T]>` it needed a fork `FromIteratorSpecImpl` |
| an iterator argument can be inlined | still false — the proof cannot name it |
| `flat_map`, slice patterns, closures capturing `&mut self`, `&T` as `*const T`, E0716 in a `for` | still unsupported |

**Retest before relying on a reason, and prefer a probe to a comment.** The
cheapest probe is a three-line function using the construct in isolation,
verified with `cargo verus focus -- --verify-only-module M --verify-function f`.

See `docs/VSTD_GAPS.md` for the upstream side of this.
