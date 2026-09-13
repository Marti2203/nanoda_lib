# Verifying nanoda with Verus

This document describes what was done to `nanoda_lib` to verify it with
[Verus](https://github.com/verus-lang/verus): what changed in the kernel, what the
verification layer proves, what it trusts, and what it measures.

The premise throughout has been **minimal change to the kernel**. The original checker
still decides every question; nothing verified sits on the verdict path.

---

## 1. The shape of the thing

`nanoda_lib` is a type checker for Lean 4 export files. Verifying it directly would mean
annotating `def_eq`, `whnf` and `infer` in place, which runs into the problem that those
functions only terminate on well-typed input (§5). Instead the arrangement is:

> **The original code decides. Verified routes run beside it as a *shadow certifier* and
> say whether they can produce a machine-checked certificate for the same verdict.**

With `NANODA_SHADOW` unset, `nanoda_bin` runs the original code path, unchanged, at the
original speed. With `NANODA_SHADOW=1`, every non-quick `def_eq` verdict, every top-level
inference, every constructor check, every generated recursor and several other decisions
are additionally handed to verified functions, and two counters are kept:

* **certified** — a verified route produced a proof of the claim the kernel just asserted;
* **disagreements** — a verified route *confirmed* a pair the original code rejected.

A disagreement has never occurred. It would mean either an unsound bridge (§4) or an
incompleteness in the original checker, and the counter exists to catch exactly that.

The certified share is the honest measure of how much of the real kernel's behaviour is
backed by proof. It is reported explicitly, including the count of pairs that were **not**
certified, so a near-miss cannot be rounded up to "100%".

---

## 2. What changed in the kernel

Against the pre-verification baseline (`b89e378`), across the seven kernel files:

| File | Added | What it is |
|---|---:|---|
| `src/tc.rs` | 929 | diagnostics module, shadow hooks, routed tests |
| `src/inductive.rs` | 178 | shadow hooks for constructors, inductive shapes, elimination level, recursors |
| `src/expr.rs` | 35 | `quot_kind_code`, `nat_bin_op_code` — name → small-code readers |
| `src/env.rs` | 20 | `visible_declar_names` |
| `src/quot.rs` | 17 | shadow hook comparing the quotient/`Eq` expected types |
| `src/util.rs` | 12 | `raw_bits`/`raw` accessors on `Ptr` |
| `src/main.rs` | 3 | print the report when `NANODA_ROUTE_STATS` is set |
| **Total** | **1,184 insertions, 10 deletions** | |

Roughly two thirds of `tc.rs`'s growth is tests and diagnostics rather than wiring: the
routed tests, the `route_stats` module (counters, the report line, the conversion failure
cache, the uncertified-pair printer), and the shadow hooks.

**All ten "deletions" are lines re-emitted with something appended.** Three are structural:

```
tc.check_ctor(&st, ind.name, ctor.ty)          → gained a semicolon
assert!(self.declars.get(ind_name).is_some())  → moved after a shadow-note block
Self { ctx: dag, env, tc_cache, declar_info }  → gained the shadow_memo field
```

The other seven are `def_eq`'s own branches, each re-emitted with a
`route_stats::legacy_branch(n)` tag so the report can say which unverified rule decided a
pair the verified routes could not certify:

```
FoundEqResult(short) => short   →   FoundEqResult(short) => { legacy_branch(5); short }
self.def_eq(x_n, y_n)           →   let r = self.def_eq(x_n, y_n); legacy_branch(7); r
```

No kernel logic was removed, reordered or rewritten.

The baseline kernel is 9,496 lines. The verification layer beside it is 24,289 — down from
48,025 once every definition nothing reaches was removed (§8 of the history: 27,676 lines,
in two sweeps).

---

## 3. What is proven

### 3.1 The relations

The verification layer defines the kernel's notions as relations over a syntactic model
(`ExprSpec`), and proves the metatheory it needs about them:

| Relation | Meaning |
|---|---|
| `pstep`, `pstep_star` | parallel reduction: β, ζ, δ, ι (recursor and projection), nat-literal folding |
| `defeq` | joinability under reduction, with confluence proven (Takahashi-style diamond, strip lemma, two-chain confluence) |
| `deq_c` / `deq` / `deq_any` | definitional equality: `defeq` plus the non-reduction leaves — sort/const level equivalence, η, quotient computation |
| `deq_p_c` / `deq_p` / `deq_p_any` | the above plus the rules that need typing: proof irrelevance, the unit rule, structure η |
| `types_to` | the typing relation, indexed by derivation height |

`deq` is a genuine inductive relation with chain-witnessed transitivity, proven reflexive,
symmetric, transitive and congruent, not a flat disjunction.

### 3.2 The certificates

Every verified route returns its claim, not just a boolean. For example
`verified_conv_p` returns `Some(true)` only together with
`deq_p_any(declar_types, env, lctx, x, y)`.

Three caches carry proofs rather than trust. `WhnfCert`, `InferCert` and `ConvCert` each
have private fields, a `#[verifier::type_invariant]` stating their claim, and a single
constructor that demands it. A cache hit hands back the answer *and* its proof, so
memoisation costs no trust — the analogue of the kernel's own `whnf_cache`, `eq_cache`
and inference caches.

### 3.3 The partial-correctness contract

`verified_infer_free` — the fuel-free inference — carries
`#[verifier::exec_allows_no_decreases_clause]`: it recurses the way the kernel does, with
no termination argument. What is proven is *if it returns a type, that type is derivable*.

This is deliberate, and it is the same contract Lean's own kernel has. Termination of the
real algorithm is **false** in general (reduction diverges on ill-typed input) and, where
it does hold, it is the normalization theorem for the calculus of inductive constructions
— not a local property one can attach to a function. Partial correctness is also
sufficient for soundness: a checker that loops never accepts a false theorem.

The alternative, which this project used for most of its life, is a fuel parameter. Fuel
does not prove the kernel's algorithm terminates; it replaces it with a truncated one that
does. The gap between those two programs is measurable, and it showed up directly as
uncertified pairs (§6).

Fuel is also expensive in proof. To recurse, a fuelled inference must re-establish a bound
on its own result's depth at every level, which is what `infer_result_depth_bound`,
`infer_depth_fixpoint_ok` and sixteen supporting lemmas existed to do — none of them with
any counterpart in the kernel. When the fuel-free inference gained its last arm (`Proj`,
which needed a depth bound on `infer(structure)` to instantiate the constructor telescope),
that whole algebra became unreachable and was deleted. Nothing about the kernel's
`infer_proj` needed it; it was the price of the fuel.

All the fuel-free inference asks for now is a term with no loose bound variables. The
linear fuel budget that used to gate it (`size * (fuel + 1) <= 60000`) went with the fuel,
and the size ceiling that came with that budget was turning away large-but-inferable terms
for no remaining reason — removing it took BitVec's inference share from 96.1% to 99.4%.

---

## 4. What is trusted

The verification layer's trust surface is:

| Kind | Count | What it is |
|---|---:|---|
| `assume_specification` | 164 | contracts for real kernel functions and arena operations |
| `#[verifier::external_body]` | 83 | bridges whose bodies Verus does not check |
| `uninterp spec fn` | 68 | uninterpreted model functions the bridges relate |

These fall into a few groups:

* **Arena operations.** `mk_app`, `mk_pi`, `inst`, `abstr`, `read_expr`, `num_loose_bvars`
  and friends are specified against the model (`to_model(mk_pi(..)) == Bind(..)`). The
  arena itself is not verified.
* **Environment readers.** `get_structure_first_ctor`, `get_constructor_num_params`,
  `get_constructor_num_fields`, `get_recursor_data` and their `_agrees` lemmas disclose
  that a declaration's data is what its environment reports.
* **Disclosed ceilings.** `env_global_cap`, `local_type_cap` and their well-formedness
  axioms assert that declaration types and local binder types in a real, already-checked
  environment are bounded.
* **Pointer identity.** `ptr_raw` is uninterpreted with no properties at all; a wrong
  answer can only send a cache lookup to the wrong slot, and a lookup returns a
  certificate that carries its own proof.

**What a bogus bridge would buy.** Because the original code decides, an unsound bridge
cannot make the checker accept a bad proof. It can only make the *certifier* claim to have
certified something it did not — which is what the disagreement counter is for.

---

## 5. Extensions to the conversion route

The conversion route follows `def_eq`'s own order: pointer equality, sort and constant
leaves, normalize both sides without unfolding, nat literals, proof irrelevance, lazy
delta, projection congruence, spine congruence, binders, quotient, η, K-like, and finally
the capped-whnf join and retry.

Four rules were added by reading the pairs the certifier could not confirm
(`NANODA_UNCERTIFIED=N` prints them), each mirroring a rule the kernel has:

| Rule | Kernel counterpart | What it says |
|---|---|---|
| **Unit** | `def_eq_unit` | if `x`'s type reduces to a structure whose single constructor takes no fields, and `y`'s type is convertible to it, then `x ≡ y` |
| **Structure η** | `try_eta_struct` | a term is equal to its own expansion `Ctor params* x.0 … x.(n-1)` |
| **Major-premise normalization** | `normalize_major_premise` | replace a stuck recursor's major premise with its η expansion so ι can fire — also under a projection, which is where `Prod.map` and friends hide it |
| **Quotient under a projection** | `reduce_quot` | `PSigma.fst (Quot.lift f h (Quot.mk r a))` |

Two details the proofs forced, worth knowing:

* Each of these leaves must be stated **symmetrically**, because `deq_p_c_symm` inverts
  every disjunct of the relation.
* Their side conditions are **up to reduction**, because the kernel whnfs an inferred type
  before looking at its head.

The structure-η and major-premise rules exist in the conversion route rather than in
reduction because `pstep` is deliberately typing-free: it has no access to a term's type,
so it cannot perform an η expansion that is only valid for a term of a structure type.

---

## 6. What is measured

Every non-quick `def_eq` confirmation, on real Lean 4 export files:

| Corpus | Certified | Share | Not certified |
|---|---:|---:|---:|
| `Init.Core` | 7,261 / 7,261 | 100.00% | **0** |
| `Init.Data.Int.Basic` | 13,205 / 13,205 | 100.00% | **0** |
| `Init.Omega` | 55,528 / 55,528 | 100.00% | **0** |
| `Init.Data.BitVec.Lemmas` | 562,968 / 563,027 | 99.99% | 59 |
| **full `Init`** (57,424 declarations) | **2,163,079 / 2,167,833** | **99.78%** | 4,754 |

Zero disagreements on all of them.

Other decisions, on `Init.Core`:

| Claim | Result |
|---|---|
| top-level inferences certified | 7,111 / 7,111 |
| constructor checks | 237 / 237 |
| inductive type shapes | 196 / 196 |
| quotient / `Eq` expected types | 2 / 2 |
| declaration types are sorts (theorems: `Prop`) | 3,871 / 3,871 |
| distinct universe parameters | 3,871 / 3,871 |
| recursor name sets | 194 / 194 |
| elimination level agrees with the kernel | 194 / 194 |
| recursor types agree with the kernel | 196 / 196 |
| recursor rules agree with the kernel | 237 / 237 |

Which route produced each certificate, on `Init.Core`: whnf-join 3,887, conversion 2,128,
lazy-delta 1,154, core 92.

Full `Init` was re-measured on 2026-09-13 against the current code (34 minutes): it had
stood at 99.4%, taken before the rules of §5 and the fuel-free inference landed.

The recursor claims are stronger than agreement alone. `verified_mk_recursor_ty` proves
the recursor's type has binder arity exactly
`num_params + num_motives + num_minors + num_indices + 1`, and
`verified_mk_rec_rule_val` proves a rule's value binds exactly
`num_params + num_motives + num_minors + ctor_args`. Those are the positions `reduce_rec`
splits an application at; if they disagreed with the terms built beside them, ι reduction
would read arguments from the wrong places.

---

## 7. Knobs

There are no budget knobs. Every cap, round count and search budget is a constant in the
source, with the measurement that justifies its value in a comment beside it:

| Constant | Value | Why |
|---|---:|---|
| `cap_k` | 500 | environment cap for the conversion route — the value its proofs are stated at |
| `cap_k_join` | 60000 | environment cap for the whnf-join route and the conversion retry; the maximum its proofs allow, so it does not limit what can be certified |
| `conv_budget` | 60 | conversion search budget; 20 left 5 more pairs uncertified on BitVec at identical runtime, and it plateaus at 60 |
| `conv_retries` | 0 | retries past a cached conversion failure; 0 is the original behaviour, larger values cost time without certifying more |
| `conv_join_rounds` | 256 | rounds for the capped whnf in the join |
| `whnf_rounds` | 256 | whnf step budget |
| major-eta rounds | 4 | rounds of iterated major-premise normalization |

`cap_k` is worth its own note. `verified_conv_p` and its whole family are proven under
`requires k <= 500`, and the call site that supplies it sits in `tc.rs`, outside `verus!`
— so nothing would have caught an environment variable handing the verified routes an
argument their proofs never covered. It used to be exactly that: `NANODA_CAP_K`, read
with no clamp. It is now the constant 500.

For whoever raises it: stating the conversion family at `k <= 60000` verifies with exactly
two failures, both the lazy-delta round's
`bound2 + d2³ + d2² + d2 + 10 <= 0xFFFF_0000`, which caps `d2` near 1625 and so `k` near
625. It also takes full verification from 11 seconds past ten minutes, and no measured
coverage gain pays for that yet.

What remains reads the environment, and none of it changes what the checker decides:

| Variable | Default | Effect |
|---|---|---|
| `NANODA_SHADOW` | off | run the shadow certifier at all — the opt-in that keeps it off the verdict path |
| `NANODA_ROUTE_STATS` | off | print the report |
| `NANODA_MEMO_STATS`, `NANODA_CONV_TRACE`, `NANODA_UNCERTIFIED`, `NANODA_CONV_FAIL_PRINT` | off | diagnostics |

The conversion **failure cache** (`conv_fail_seen_p`) has no counterpart in `def_eq`. It is
untrusted — `external_body` with no `ensures`, and a hit only produces `None`, which
carries no claim — but without it the route exceeds ten minutes on `Init.Omega` against
about three seconds with it. It stands in for the kernel's own memo caches, which this
route cannot reuse because a cached positive answer would have to carry its proof.

---

## 8. What is left

* **`Init.Data.BitVec.Lemmas`: 59 pairs**, and `Init`'s wider 4,754. A genuine long tail,
  and well characterised. A pair is a ROOT failure when no nested `def_eq` below it also
  failed to certify; of BitVec's 59, only **14 are roots** (down from 20 at 76), the other
  45 inheriting a failure from an argument.

  Ten of those fourteen are a stuck recursor — `Fin.rec`, `Nat.rec`, `Eq.rec` — facing a
  constructor application or a local that the kernel had already reached. Instrumenting
  the exact call the rule makes (`NANODA_UNCERTIFIED` prints it) settled what is and is
  not the problem:

  - structure eta **does** rewrite the major premise to a genuine `Fin.mk ..`;
  - ι **does** fire on the rewritten term — `verified_rec_step_capped` returns `Some`;
  - the term it fires to is headed by *another* stuck `Fin.rec`, which is why rewriting
    once and comparing looked like the rule not working. `verified_major_eta_fix` now
    iterates to a fixpoint;
  - and the pairs still do not close, at 1, 4 or 64 rounds, even with a full-budget
    conversion run on the fixpoint.

  So the remaining gap is in the ARGUMENTS, not the major premise. Both sides reach
  `Fin.mk`, and the fields then need `BitVec.toNat w (x * y)` against
  `(x.0.0 * y.0.0) % 2^w` — delta plus projection-of-constructor inside an argument
  position. That is the next root cause to chase.

  The other four roots are `Eq.rec` needing the kernel's K-like rule (`to_ctor_when_k`,
  which has no counterpart on the live path), and pairs whose heads already agree.

  Ruled out by measurement, so they are not worth retrying: the conversion budget (60 and
  200 both leave the same count), the conversion cap at 60000, the whnf-join cap, the
  lazy-delta gates (500 → 5000, rounds 32 → 128), bounded retries past a cached failure,
  removing the failure cache (Init.Core alone then exceeds ten minutes), adding the
  whnf-join route as a leaf inside conversion (same count, 30% slower), comparing the
  reduced one-sided rewrite against the other side's reduct (same count, 40% slower), and
  iterating major-premise normalization (same count).
* **The conversion route's `k ≤ 500`.** The one remaining cap that limits what can be
  proven; see §7 for exactly what blocks raising it.

---

## 9. Reproducing

```sh
# the checker, unchanged
./target/release/nanoda_bin ~/nanoda_corpora/init_core.json

# with the shadow certifier and its report
NANODA_SHADOW=1 NANODA_ROUTE_STATS=1 ./target/release/nanoda_bin ~/nanoda_corpora/init_core.json

# the pairs no route could confirm
NANODA_SHADOW=1 NANODA_UNCERTIFIED=40 ./target/release/nanoda_bin ~/nanoda_corpora/init_core.json

# verification (needs cargo-verus and a matching z3 on PATH)
export PATH=~/verus-fork/source/target/release:~/verus-fork/source/target-verus/release:$PATH
rm -rf target/verus-partial/debug/.fingerprint/nanoda_lib-*
cargo verus focus -- --rlimit 300 --num-threads 6
```

Current state: **495 functions verified, 0 errors**; 79 tests pass. Full verification takes
about 11 seconds.

Corpora are generated with [`lean4export`](https://github.com/leanprover/lean4export) and
live in `~/nanoda_corpora/`:

```sh
cd ~/lean4export && lake env .lake/build/bin/lean4export Init.Core > ~/nanoda_corpora/init_core.export
```
