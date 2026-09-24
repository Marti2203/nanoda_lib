# Kernel rewrites

Every place where `nanoda_lib`'s original code was changed to let Verus verify
it. The goal is for this list to shrink to nothing.

**The `VERUS-REWRITE(..)` markers in the source are the ground truth**; this
file is a derived index. `scripts/rewrite-register-audit.sh` checks that every
marked function appears here. It cannot check that the *reasons* are still
true — see "Retesting" at the end, which is the more important discipline.

Current: **70 marked rewrites across 48 functions** (counted by `scripts/rewrite-register-audit.sh`).

---

## 1. Rewrites that a change to Verus or vstd would remove

These are not decisions. Each exists because something is missing upstream, and
each would revert if that were supplied.

### Match guards with mutation in the arm — 0 rewrites, CLOSED (fork `8f4061822`)

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

### `Iterator::enumerate` — 1 rewrite

| function | file | missing |
|---|---|---|
| `mk_majors` | `src/inductive.rs` | `enumerate` |

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

### An unspecified `alloc` variant — 1 rewrite

`subst_levels` (`src/level.rs`), which also has a closure capturing
`&mut self`.

---

## 2. Rewrites needing a Verus language feature

### Slice patterns — 3 rewrites

| function | file |
|---|---|
| `abstr_pi_telescope` | `src/expr.rs` |
| `abstr_lambda_telescope` | `src/expr.rs` |
| `init_k_target` | `src/inductive.rs` |

Unsupported outright, confirmed on current upstream:

```
rust_to_vir_expr.rs:  PatKind::Slice(..) => unsupported_err!(pat.span, "slice patterns", pat)
```

Each is an index walk instead. (Recently landed *index range* syntax — #2913,
#2959 — is a different feature and does not help here.)

### Closures capturing `&mut self` — 3 rewrites

| function | file |
|---|---|
| `subst_levels` | `src/level.rs` |
| `eq_antisymm_many` | `src/level.rs` |
| `str_lit_to_ctor_reducing` | `src/tc.rs` |
| `abstr_aux` (`.map` only) | `src/expr.rs` |
| `def_eq_app` | `src/tc.rs` |
| `args_def_eq_rev` | `src/tc.rs` |

Rejected outright, and the message is explicit:

```
Verus does not currently support closures capturing a mutable reference
(mutably captured variable `self`)
```

Each is spelled as the `match`/index walk the adapter desugars to. This is the
one blocker left in the 46-function `def_eq` cycle that is not an `.unwrap()`.

### An exit proof inside a `while let` — 1 rewrite

`unfold_apps` and `unfold_apps_stack` (`src/expr.rs`) are `loop` + `match`.

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
| `lazy_delta_step` | `src/tc.rs` | parameters `mut x, mut y` → `x_in, y_in` with `let mut x = x_in` — the claim is about the entry values, which a mutated parameter cannot name inside the loop |
| `do_nat_bin` | `src/tc.rs` | each operation through its `biguint_*` wrapper, which calls the same `util::nat_*` function (or `Pow::pow`, `==`, `<=`) and carries the value contract |
| `reduce_proj` | `src/tc.rs` | `get_constructor(&name)?.num_params` read through `get_constructor_num_params`, defined as exactly that and carrying the environment's claim |
| `reduce_quot` | `src/tc.rs` | the major premise's index is chosen first, then one `get` and one `whnf` -- the same work as the original's two branches |
| `def_eq_quick_check` | `src/tc.rs` | the `eq_cache` lookup goes through `cached_eq`, the same lookup with the cache's claim |
| `get_bignum_from_expr`, `get_bignum_succ_from_expr` | `src/expr.rs` | `read_bignum(..).cloned()` / `read_bignum(..)? + 1` through `read_bignum_value` / `biguint_succ`, which say which number |
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
| `gen_elim_level` | `src/inductive.rs` | `i += 1` in an unbounded `loop` (panics at `u64::MAX` -- the crate builds with overflow checks) |
| `abstr_aux` | `src/expr.rs` | `offset + 1` under a binder and the index sum `pos + offset` panic on `u16` overflow (overflow checks are on); both made explicit (the index check also excludes `u16::MAX` itself, which no stored `Var` may hold). With `inst` needing no depth bound at all, this is what retired the arena axiom `depth < 60000` (refutable by allocating a deep term) |
| `leq_core` | `src/level.rs` | `diff - 1` / `diff + 1` in the `Succ` arms panic on `isize` overflow (overflow checks are on); the same checks are made explicit, which is what replaced the arena axiom bounding `leq_measure` (refutable by allocating ~500M nested levels) |
| `NAME`/`LEVEL` hash constants | `src/name.rs`, `src/level.rs` | `STR_HASH`, `NUM_HASH`, `SUCC_HASH`, `MAX_HASH`, `IMAX_HASH`, `PARAM_HASH` widened from `pub(crate)` to `pub` (visibility only): the public `alloc_name`/`alloc_level` specifications name them in their canonical-hash precondition |
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
