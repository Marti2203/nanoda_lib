# Verifying `tc.rs`: the measured shape of the job

Status: **open, and now scoped**. `tc.rs` was opened to Verus on 2026-09-18
(commit `9217544`); two functions are verified in place. This note records what
the file's call graph actually looks like, because the shape decides the plan
and it is not the shape it appears to be from the outside.

## 1. What the beachhead settled

Three things were suspected to block verifying `tc.rs` at all. Two were not
blockers:

| Suspected blocker | Reality |
|---|---|
| `TypeChecker` holds `ctx: &'x mut TcCtx` | **Not a blocker.** A struct with a mutable-reference field is fine as a transparent `#[verifier::external_type_specification]`. `self.ctx.succ(l)` and `self.declar_info` verify as written. |
| `InferFlag`, `DeclarInfo`, `RecRule` are outside `verus!` | **Not a blocker.** They need their own type specifications and nothing else. Watch for duplicates — `tc_model.rs` already declares `ExRecRule`, and Verus rejects two for one type. |
| The kernel's `assert!` rejection checks | **A real cost, and permanent.** See §2. |

This matters because the first one, had it been real, would have forced
restructuring the kernel — which the project's own rules
(`project_original_code_decides`) do not allow.

## 2. `kernel_check`, and why it is not going away

Verus specifies `panic!` with `requires false`: a panic must be proven
**unreachable**. The kernel's checks are reachable *by design* — rejecting a
malformed declaration is their entire job — and no precondition can ever
discharge them, because adding one would mean assuming the thing being checked.

So they route through `util::kernel_check(cond, msg)`: `external_body`, no
`ensures`. It states nothing, so it adds no trust claim, and Verus treats it as
possibly returning normally — the conservative reading, since code after the
call still has to verify without assuming the check passed.

Expect this in nearly every `tc.rs` function. It is the generic adapter for the
kernel's abort-on-bad-input style, not a one-off. Registered as VERUS-REWRITE
entry 12, and distinct from entry 2's `assert_eq!` case: that macro Verus cannot
*compile*, on a path a precondition proves unreachable; this one compiles fine
and its proof obligation is unsatisfiable on purpose.

## 3. The measurement that decides the plan

Reachable from `infer` in `tc.rs`: **62 functions, 1450 lines**. But the
reachable set is not the unit of work. The strongly-connected components are:

> **One cycle of 48 functions, 1229 lines.** Everything else is acyclic.

The cycle:

```
assert_def_eq, def_eq, def_eq_app, def_eq_binder_aux, def_eq_binder_multi,
def_eq_local, def_eq_nat, def_eq_proj, def_eq_quick_check, def_eq_unit, delta,
delta_try_nat, do_nat_bin, ensure_pi, infer, infer_app, infer_lambda, infer_let,
infer_pi, infer_proj, infer_sort_of, infer_then_whnf, iota_try_eta_struct,
is_proof, is_prop, lazy_delta_step, may_be_prop, proof_irrel_eq, reduce_proj,
reduce_quot, reduce_rec, shadow_check, shadow_check_rooted,
str_lit_to_ctor_reducing, to_ctor_when_k, try_eq_const_app, try_eta_expansion,
try_eta_expansion_aux, try_eta_struct, try_eta_struct_aux, try_reduce_nat,
try_string_lit_expansion, try_string_lit_expansion_aux, try_unfold_proj_app,
whnf, whnf_no_unfolding, whnf_no_unfolding_aux, whnf_no_unfolding_cheap_proj
```

`infer`, `whnf` and `def_eq` are all in it. There is no way to verify one
without the others.

### Is the cycle a *proof* cycle? No — but it is still all-or-nothing

The same argument that unties `leq_core`'s clique
(`docs/LEQ_CORE_TERMINATION.md` §1) applies here: contracts are stated over
*spec* functions, so no contract depends on another being **proven**, only on
its being **stated**. With `exec_allows_no_decreases_clause` there is no
well-founded order to supply. Verus checks each body against the others' stated
contracts, one at a time.

**But that does not make the work incremental**, and the reason is purely
operational: Verus verifies every function in the file. State a contract and the
body is immediately an obligation. There is no "assume this one for now" short
of `assume_specification`, which is an axiom — 48 of them would be absurd.

So the cycle is a single deliverable: write all 48 contracts, then drive the
whole set green together. Plan it that way from the start rather than
discovering it at function 30.

## 4. The part that IS incremental

Fourteen functions reachable from `infer` sit in **no cycle** and can be
verified one at a time, today:

| | Function | Needs |
|---|---|---|
| ✅ | `infer_sort` | done (`9217544`) |
| ✅ | `get_rec_rule` | done (`39f38ba`) |
| | `def_eq_sort`, `def_eq_const` | a contract for `eq_antisymm`/`eq_antisymm_many` → the `leq` clique (§5) |
| | `infer_const`, `unfold_def`, `get_applied_def`, `is_ctor_app`, `mk_nullary_ctor`, `expand_eta_struct_aux` | `Env::get_declar` + a matchable `Declar` — one shared piece, but a NEW trust boundary, not just type specs. See §7. |
| | `failure_cache_contains`, `failure_cache_insert` | `FxHashSet` views; no verified code in this crate uses a HashSet yet |
| | `pair_certified`, `smallest_infer_failure` | diagnostics, low value |

**The `Env` bridging is the highest-value next step in this file.** One piece of
work, six functions, and `unfold_def` among them is delta reduction itself.

## 5. The `leq` decision, stated so it can be taken deliberately

`def_eq_sort` and `def_eq_const` need `TcCtx::eq_antisymm`, which needs
`TcCtx::leq`, which needs `leq_core` — the documented open problem.

The shortcut: give `leq` an `assume_specification` claiming
`result ==> forall rho. interp(l, rho) <= interp(r, rho)`. That would verify
`eq_antisymm`, `eq_antisymm_many`, `is_zero`, `is_one`, `is_nonzero`,
`def_eq_sort` and `def_eq_const` in place, and since `is_zero`/`is_one` are
currently **claim-free** axioms the trust surface would go 105 → 104.

**The count would be lying.** Those two axioms assume nothing; a `leq` axiom
assumes the universe-ordering decision procedure is sound — about 100 lines
including `leq_core`. The number falls while what is actually assumed rises.

It would also paper over the one genuinely open research problem here. The WIP
branch shows the contract is provable *modulo* the `diff` measure, so this is a
proof waiting on one idea, not a permanent gap.

Not taken. Recorded here so it is a decision rather than an oversight.


## 6. `unfold_def` and its mirror are not the same function

Worth knowing before anyone tries the obvious retirement.
`tc_model.rs::verified_unfold_def_step_free` carries the contract the kernel's
`unfold_def` would want —

```
Some(r) => pstep_star(env_model_nofv(*env), to_model(e), to_model(r))
        && nlbv(to_model(r)) <= 0
```

— and every ingredient the kernel's body needs is already specified or verified:
`unfold_apps`, `try_const_info`, `read_levels`, `subst_expr_levels` and
`foldl_apps` are all done, and `Env::get_declar_val` has a rich
`assume_specification` in `env_model.rs`. So it looks like a direct swap.

It is not, because the mirror has a check the kernel does not:

```rust
if ctx.has_fvars(def_value) {
    return None;
}
```

The kernel's `unfold_def` contains no `has_fvars` call. The mirror therefore
DECLINES on definitions whose value contains a free variable, where the kernel
unfolds. That is safe in the shadow direction — declining only costs coverage,
it can never mis-certify — but it means the mirror is strictly more
conservative, and the two are not interchangeable.

The consequence for retirement: the mirror *tests* `!has_fv(val)` at run time,
and the kernel would have to *know* it. `get_declar_val`'s contract does not
supply it — it gives `nlbv(expr_to_model(val)) == 0`, which is about loose de
Bruijn indices escaping the body, a different property from containing a `Free`
node. So retiring the mirror onto the kernel needs a new claim: that a
declaration's value is closed in the free-variable sense too.

That claim is true of real Lean declarations and `get_declar_val`'s own doc
comment already gestures at it, but it is a new axiom and should be added
deliberately, with a non-degeneracy witness, rather than slipped in as part of
a retirement.


## 7. Correction: what the `Env` bridging actually costs

An earlier version of §4 said these six functions need "type specs for the `Env`
accessors and the `Declar` enum". That was wrong about the mechanism and it
understated the price. Corrected here rather than quietly edited, because the
wrong version was committed and the difference changes the ranking.

`ExEnv` is `#[verifier::external_body]` — **opaque on purpose**. `Env`'s
`IndexMap`-based storage is deliberately not reverse-engineered; only its
observable behaviour is axiomatised. So there is no "make it transparent and
read the fields" route, by design.

The established pattern is instead: a `pub(crate)` wrapper function outside
`verus!` that extracts exactly what is needed, plus one `assume_specification`
keyed on an uninterpreted model map. `env_model.rs` already holds NINE of them:

```
Env::get_declar_val      Env::visible_declar_names   Env::can_be_struct
get_declar_info_ty       get_declar_hint             get_constructor_num_params
get_recursor_data        get_structure_first_ctor    get_constructor_num_fields
get_recursor_is_k
```

**But those wrappers do not help a kernel function verified IN PLACE**, and that
is the whole point. They exist so the *shadow* never has to touch `Declar`. The
kernel's `get_applied_def` does not call `get_declar_hint`; it calls
`self.env.get_declar(&name)` and pattern-matches `Declar::Definition { .. }`
against `Declar::Theorem { .. }`. Verifying that body as written needs
`Env::get_declar` itself specified, returning `Option<&Declar>`, with `Declar`
matchable — a new boundary of a different shape from the nine.

So the honest price for those six functions is one new trust boundary covering
`get_declar`/`Declar`, not a free adaptation of existing work. Against a surface
of 105 claims that is not disqualifying, but it is a real cost and it should be
weighed against the alternatives rather than assumed to be the cheap option.

The one genuinely free item in that group is `unfold_def`, whose every
ingredient is already specified — and §6 explains why it is not free either.
