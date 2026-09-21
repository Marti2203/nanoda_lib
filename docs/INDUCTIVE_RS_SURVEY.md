# `inductive.rs`: surveyed, not started

Status: **the gate is open; one of 65 functions verified.** This note records
the structure so the next attempt does not have to rediscover it, in the same
spirit as `docs/TC_RS_ARC.md`.

## The good news: no cycle

`tc.rs`'s shape is one 48-function mutual clique containing `infer`, `whnf` and
`def_eq`, which has to land as a single deliverable.

**`inductive.rs` has no cycles at all.** Every function can in principle be
verified on its own, bottom-up. That is a materially better shape, and it is the
main reason this file may be cheaper than its 65 functions suggest.

## The gate: `InductiveCheckState`

Of the 65, **23 are leaves that never reach `tc.rs`'s `def_eq`/`whnf` cycle** —
the population that could be attacked without the big arc. What blocks them:

| blocker | count |
|---|---|
| takes `InductiveCheckState` | **14** |
| a closure Verus cannot take | 8 |
| `FxHashSet` (the `HashSet::with_hasher` vstd gap) | 2 |
| a slice pattern (unsupported outright) | 1 |
| nothing obvious | 3 |

(Functions can have more than one blocker.)

So `InductiveCheckState` is this file's gate the way the 48-cycle is `tc.rs`'s —
**one struct, 19 fields, `inductive.rs:231-286`** — and registering it would
unlock the largest single group. Whether it can be transparent is the first
question to answer: `Declar`'s payload types went transparent cheaply once their
`pub(crate)` fields were widened to `pub`, and its `Arc<[T]>` fields turned out
to be no obstacle, so the precedent is encouraging.

**Done.** `InductiveCheckState` is now TRANSPARENT, and it cost no new axioms —
type registrations are not claims:

- its 18 fields widened `private` → `pub`, as `Ptr`/`TcCtx`/`TcCache` were;
- `IndTyHeader` and `CtorHeader` widened to `pub` and registered OPAQUELY;
- `IndexMap` registered opaquely, which needs
  `#[verifier::reject_recursive_types]` on each of its three type parameters —
  Verus requires a variance marker on every parameter of an `external_body`
  datatype;
- `InductiveCheckState` itself transparent.

Same trick as `Declar`'s payloads: Verus needs the field types KNOWN, not
readable. `inductive.rs` also gained its first `verus!` block, and `mk_majors`
is verified in it — which incidentally turned up another unguarded index
(`st.local_indices[idx]`); see `mk_majors` in `docs/VERUS_REWRITES.md`.

The three with nothing obvious in the way — `header_of_ty` (17L), `is_nested`
(39L), `new` (27L) — are data-shuffling rather than checking, so they are a poor
first target despite being reachable. Prefer the state struct.

## Correction (2026-09-21): this is NOT the big open surface

This survey reads as though `inductive.rs` is where the remaining work is,
because it has the most unverified functions. Measured properly with
`scripts/verification-frontier.py` — a function is reachable when every
function it calls is already known to Verus — **only 2 of its 63 functions are
on the frontier**. Most of the file sits behind a handful of hubs, several of
which are in the `tc.rs` cycle (`whnf`, `assert_def_eq`), so they are blocked
behind all of it.

The richer surfaces are elsewhere: `expr.rs` 20 of 33, `util.rs` 33 of 68,
`env.rs` 16 of 20. Count the frontier, not the unverified functions.

`ctor_app_params_ok` and `init_k_target` have since been verified here, which
is most of what was reachable.

## Totality

`inductive.rs` holds **44 `.unwrap()`, 26 `panic!`, 32 indexing sites and 2
`.expect(`** — the largest concentration in the kernel, more than `tc.rs`. See
`docs/TC_RS_ARC.md` §9 for what each kind costs; the short version is that
`panic!` on a rejection path is cheap (`kernel_check`), and an `.unwrap()` or
index is the kernel assuming something its caller established, which needs
either a propagating precondition or a decline.

Expect this file to be where most of the remaining totality work lives.
