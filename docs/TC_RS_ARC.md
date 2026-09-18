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
| ✅ | `is_ctor_app`, `get_applied_def` | done — see §8 |
| | `infer_const`, `unfold_def`, `mk_nullary_ctor`, `expand_eta_struct_aux` | each needs a claim ABOUT the declaration, not just its kind — see §8 |
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

**TAKEN, deliberately, on 2026-09-18** (commit `2382e1f`, 681 verified / 0
errors, surface 105 -> 104). An earlier draft of this section argued against it
on the grounds that the count would be lying — those two axioms assume nothing,
while a `leq` axiom assumes the universe-ordering decision procedure is sound,
about 100 lines including `leq_core`. That argument is still correct about the
COUNT, and it is the wrong thing to optimise.

What the trade actually improves is **where the assumption sits**. Before, seven
functions were either assumed outright or simply unverified, and the two
claim-free axioms let `simplify` be verified only because it needs no property
of `is_zero`/`is_one` at all — it calls them to pick a branch. Now the
assumption is stated ONCE, at the single place the hard proof really lives, and
seven kernel functions are verified against it:

```
level.rs  is_zero, is_one, is_nonzero, eq_antisymm, eq_antisymm_many
tc.rs     def_eq_sort, def_eq_const
```

It is not a permanent gap. `docs/LEQ_CORE_TERMINATION.md` records that the
contract is proven on branch `leq-core-clique-wip` modulo one thing: a measure
that decreases on every `leq_core` arm, so the `isize` `diff` cannot overflow.
Find that measure and the axiom retires, with its seven consumers already
written against exactly the contract the proof will establish.

**One trap worth repeating.** The axiom's first draft carried a single trigger
keyed on its LEFT argument. `is_zero` puts its level there and verified; `is_nonzero`
puts its level on the RIGHT and did not — and the failure appeared as an
unprovable postcondition, with nothing pointing at triggers. A shared fact keyed
to only half its callers is a trap for the next consumer. It now carries two
trigger groups. Check this whenever an `assume_specification` relates two
arguments symmetrically.


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


## 8. The `Env`/`Declar` boundary, done — and cheaper than §7 feared

§7 said this was "a new trust boundary" and warned against assuming it was the
cheap option. It landed for **one claim-free axiom and three opaque type
registrations**, which is cheaper than that warning implied. Recording what the
shape turned out to be:

- `ExDeclar` went from `external_body` to **transparent**, so the kernel's
  `Declar::Constructor { .. }` / `Declar::Definition { .. }` tests are matchable.
- Its three payload types (`InductiveData`, `ConstructorData`, `RecursorData`)
  are registered but stay **opaque**. Nothing reads inside them, and keeping
  them opaque sidesteps their `Arc<[T]>` fields entirely. That is the trick:
  a transparent enum does not need transparent payloads.
- `Env::get_declar` gets a **claim-free** `assume_specification`. It states
  nothing — no model map, no correspondence — and exists only so the calls can
  be made at all.

The claim-free choice is what keeps the price honest, and it bounds what these
functions can promise. `is_ctor_app` proves its result names the expression's
SPINE HEAD; it does NOT prove the declaration is a constructor, because nothing
knows what a `Declar` is. `get_applied_def` proves only that the spine head is a
constant — its returned name is the declaration's own `info.name`, and with
`get_declar` claim-free nothing says that agrees with the head constant's name.
It does agree in practice, but that is a fact about the environment rather than
about the function, so it is not claimed.

**The remaining four need more than the kind.** `infer_const` and `unfold_def`
have to say what the declaration's TYPE or VALUE is, `mk_nullary_ctor` what its
constructor list is. Those want the keyed model maps `env_model.rs` already has
for other accessors (`get_declar_info_ty`, `get_declar_val`, ...), and a kernel
body that calls the wrapper rather than matching inline. That is the larger
boundary §7 was actually describing; it just is not what the kind tests needed.


## 9. The totality cost, measured

Verifying a kernel function makes Verus ask about every place it can panic. Four
such sites turned up in the first nine `tc.rs` functions, so it is worth knowing
the size of the whole population before planning the rest.

| file | `.unwrap()` | `.expect(` | `panic!` | indexing |
|---|---|---|---|---|
| `tc.rs` | 32 | 1 | 25 | 20 |
| `inductive.rs` | 44 | 2 | 26 | 32 |
| `util.rs` | 16 | 0 | 3 | 0 |
| `expr.rs` | 6 | 0 | 8 | 6 |
| `level.rs` | 0 | 0 | 3 | 7 |
| `quot.rs` | 2 | 0 | 6 | 0 |
| **total** | **100** | **3** | **71** | **65** |

**The three kinds are not the same job.**

- **`panic!` on a rejection path** — "this declaration is malformed". Reachable
  by design, discharged by `util::kernel_check`, which states nothing. Cheap and
  mechanical; see rewrite entry 12.
- **`.unwrap()` and indexing** — the kernel assuming something its CALLER
  established. These are the interesting ones. Each needs either a proof (which
  means the caller's fact becomes a precondition, and propagates) or a decline
  (cheap when the function already returns `Option`, impossible when it does
  not). Entries 17 and 18 are both of this kind.
- **`.expect(`** — three sites, same as `.unwrap()`.

Four have been closed so far, all by declining, all in functions that already
returned `Option`. That is the cheap case and it will not always be available:
`infer_const` returns `ExprPtr` and its `panic!` on a missing declaration has
nowhere to decline to, which is why it is still unverified.

None of the four were reachable with well-formed input. That is the expected
result and not a reason to skip the rest — an unreachable panic is still a
panic, and the audit is what turns "we believe it cannot happen" into "the
checker cannot do it".


## 10. There is no more low-hanging fruit

Measured at the end of the 2026-09-18 session, after ranking every kernel
function with neither a contract nor an `assume_specification` by how many call
sites it has:

```
 35  tc.rs    whnf                25  tc.rs    def_eq       18  tc.rs    infer
 33  util.rs  clear               31  util.rs  find_name    14  util.rs  alloc_string
 35  tc.rs    bump                17  tc.rs    conv_trace   15  tc.rs    shadow_enabled
```

Three kinds, and only one of them matters:

- **`whnf`, `def_eq`, `infer`** — the 48-function cycle. The most-used
  uncontracted functions in the kernel are exactly the ones that cannot be done
  piecemeal.
- **`clear`, `find_name`, `alloc_string`, `with_tc`** — arena and session
  plumbing. Contracts here would need storage-level specs and would say little;
  the `alloc_*` primitives that DO matter are already specified.
- **`bump`, `conv_trace`, `shadow_enabled`, `legacy_branch`, `conv_budget`** —
  diagnostics. Observation-only, never on a verdict path, nothing worth stating.

**So the remaining kernel verification work IS the cycle.** Everything reachable
around it has been done: `level.rs` is complete bar a vstd gap, `tc.rs`'s
independent set is exhausted at ten functions, `inductive.rs` is open with its
gate through.

### A measurement warning, because this survey was wrong twice first

Both errors came from regexing Rust, and both made the picture look better or
worse than it was:

1. Scanning for `ensures`/`requires` at the DEFINITION site marks every function
   specified by an `assume_specification` in a bridge file as "uncontracted".
   `read_expr`, `num_loose_bvars` and `has_fvars` all topped the first ranking
   and all already had contracts — one of them was nearly re-added verbatim.
2. Extracting the specified name from `assume_specification<'t, 'p> [TcCtx::<'t,
   'p>::read_expr]` needs a character class that admits the COMMA inside
   `<'t, 'p>`. Without it the pattern matches nothing and every function looks
   unspecified.

Cross-check any such ranking by grepping one or two of its top entries by hand
before acting on it.


## 11. What the cycle actually costs

The mirrors do not carry the cycle. Matching each of the 48 members against a
`verified_*` function of the SAME name:

> **5 of 48** have one — `def_eq`, `def_eq_app`, `def_eq_nat`,
> `try_eq_const_app`, `try_unfold_proj_app`, all in `tc_model.rs`.

The other **43 need contracts designed from scratch**. That is the real figure,
and it is worth stating because the opposite impression is easy to form: there
are 96 `verified_*` mirrors in the crate, `infer_shadow_claim` and `pstep_star`
give the contract SHAPES, and §3 records that the cycle is not a proof cycle. All
true, and none of it means the contracts exist.

(A first pass at this reported 12 by matching `verified_<name>_*` as well as
`verified_<name>`. That counts `verified_def_eq_sort` as a mirror of `def_eq`
and `verified_infer_sort` as a mirror of `infer` — different functions, both
already verified in place. Exact names only.)

So the cycle is: **48 functions, 1229 lines, 43 contracts to design, landing
together or not at all.** It is a multi-session arc and should be planned as
one, not approached function by function in the hope that it decomposes — §3
establishes that it does not.

The five with mirrors are the right place to start: their contracts are known to
be the right shape, having been proven once already against a parallel
implementation.


## 12. `quot.rs` is not a way around the cycle

Worth recording because it looks like one. `quot.rs` holds just two functions
(`check_eq`, `check_quot`), and a scan for cycle calls written as
`self.<name>(` reports **none** — which would make an entire kernel file
independently verifiable.

Reading it says otherwise. Both functions construct a local `TypeChecker` and go
through it:

```rust
let mut tc = TypeChecker::new(ctx, &env, Some(info));
tc.assert_def_eq(info.ty, expected);
```

Six such calls, none of them spelled `self.`. **A cycle-membership scan keyed on
`self.` misses every call made through a local receiver** — and this file is
built entirely that way.

It is also blocked several times over independently: 7 slice patterns
(unsupported outright, register entry 9), 3 `assert_eq!` (uncompilable, entry
2), 19 uses of the `arrow!`/`pi_telescope!` builder macros, and an
`unreachable!`.

So `quot.rs` waits on the cycle like everything else, and there is no fourth
front. `level.rs` is complete bar a vstd gap, `tc.rs`'s independent set is
exhausted, `inductive.rs` is open with its gate through, and `quot.rs` is not
independent at all.
