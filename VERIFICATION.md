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
| `src/tc.rs` | 763 | diagnostics module, shadow hooks, routed tests |
| `src/inductive.rs` | 178 | shadow hooks for constructors, inductive shapes, elimination level, recursors |
| `src/expr.rs` | 35 | `quot_kind_code`, `nat_bin_op_code` — name → small-code readers |
| `src/env.rs` | 20 | `visible_declar_names` |
| `src/quot.rs` | 17 | shadow hook comparing the quotient/`Eq` expected types |
| `src/util.rs` | 12 | `raw_bits`/`raw` accessors on `Ptr` |
| `src/main.rs` | 3 | print the report when `NANODA_ROUTE_STATS` is set |
| **Total** | **1025 insertions, 3 deletions** | |

Within `tc.rs`'s 763 lines: 276 are routed tests, 261 are the `route_stats` diagnostics
module (counters, knobs, the report line, the conversion failure cache), and 224 are the
shadow hooks and their wiring. So roughly two thirds of the kernel diff is tests and
diagnostics.

**All three "deletions" are lines re-emitted with something appended:**

```
tc.check_ctor(&st, ind.name, ctor.ty)          → gained a semicolon
assert!(self.declars.get(ind_name).is_some())  → moved after a shadow-note block
Self { ctx: dag, env, tc_cache, declar_info }  → gained the shadow_memo field
```

No kernel logic was removed, reordered or rewritten. The kernel is 6,839 lines; the
verification layer beside it is 48,025.

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
| `Init.Data.BitVec.Lemmas` | 562,946 / 563,027 | 99.99% | 81 |

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

Full `Init` (57,424 declarations) last measured at 2,154,911 / 2,167,833 = **99.4%** with
0 disagreements, *before* the four rules of §5 and the fuel-free inference landed. It has
not been re-run since; the figure is a floor, not a current reading.

The recursor claims are stronger than agreement alone. `verified_mk_recursor_ty` proves
the recursor's type has binder arity exactly
`num_params + num_motives + num_minors + num_indices + 1`, and
`verified_mk_rec_rule_val` proves a rule's value binds exactly
`num_params + num_motives + num_minors + ctor_args`. Those are the positions `reduce_rec`
splits an application at; if they disagreed with the terms built beside them, ι reduction
would read arguments from the wrong places.

---

## 7. Knobs

All knobs are ours — the original kernel reads no environment variables. They steer the
certifier only.

| Knob | Default | Effect |
|---|---|---|
| `NANODA_SHADOW` | off | run the shadow certifier at all |
| `NANODA_ROUTE_STATS` | off | print the report |
| `NANODA_CAP_K` | 500 | environment cap for the conversion route — **not** freely raisable, conv's bounds assume `k ≤ 500` |
| `NANODA_CAP_K_JOIN` | 60000 | environment cap for the whnf-join route and the conversion retry; 60000 is the maximum the proofs allow, so it does not limit what can be certified |
| `NANODA_CONV_BUDGET` | 20 | conversion search budget |
| `NANODA_CONV_JOIN` | 256 | rounds for the capped whnf in the join |
| `NANODA_WHNF_ROUNDS` | 256 | whnf step budget |
| `NANODA_MEMO_STATS`, `NANODA_CONV_TRACE`, `NANODA_UNCERTIFIED`, `NANODA_CONV_FAIL_PRINT` | off | diagnostics |
| `NANODA_NO_CONV`, `NANODA_NO_CONV_FAIL` | off | experiment switches |

Two of these are load-bearing in a way worth flagging. `NANODA_CAP_K` is a real ceiling:
the conversion route's proofs are parameterised by it and assume `k ≤ 500`. And the
conversion **failure cache** (`conv_fail_seen_p`) has no counterpart in `def_eq`; it is
untrusted — `external_body` with no `ensures`, and a hit only produces `None`, which
carries no claim — but without it the route exceeds ten minutes on `Init.Omega` against
about three seconds with it. It stands in for the kernel's own memo caches, which this
route cannot reuse because a cached positive answer would have to carry its proof.

---

## 8. What is left

* **`Init.Data.BitVec.Lemmas`: 81 pairs.** A genuine long tail. Measured: our whnf agrees
  with the kernel's on both sides for these, so it is not a reduction gap; raising the
  lazy-delta size gate (500 → 5000) and rounds (32 → 128) changes nothing; only 4 of the
  81 have inference declining. They need further conversion *rules*, one class at a time,
  the way §5's four were added.
* **The fuel-free inference has no `Proj` arm.** Local, sort, constant, both literals,
  lambda, pi, let and application are done; `Proj` still falls back to the fuelled arm.
  That fallback is the last thing keeping the old fuelled family alive, and with it
  `infer_result_depth_bound`, `infer_depth_fixpoint_ok` and the `d`/`dd` ceilings threaded
  through ~30 sites.
* **`NANODA_CAP_K`.** The conversion route's `k ≤ 500` assumption is the remaining cap
  that actually limits what can be proven.
* **Full `Init`.** Needs a re-run (§6).

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

Current state: **1,273 functions verified, 0 errors**; 79 tests pass.

Corpora are generated with [`lean4export`](https://github.com/leanprover/lean4export) and
live in `~/nanoda_corpora/`:

```sh
cd ~/lean4export && lake env .lake/build/bin/lean4export Init.Core > ~/nanoda_corpora/init_core.export
```
