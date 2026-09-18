# `inductive.rs`: surveyed, not started

Status: **zero of 65 functions verified.** This note records the structure so
the next attempt does not have to rediscover it, in the same spirit as
`docs/TC_RS_ARC.md`.

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

The three with nothing obvious in the way — `header_of_ty` (17L), `is_nested`
(39L), `new` (27L) — are data-shuffling rather than checking, so they are a poor
first target despite being reachable. Prefer the state struct.

## Totality

`inductive.rs` holds **44 `.unwrap()`, 26 `panic!`, 32 indexing sites and 2
`.expect(`** — the largest concentration in the kernel, more than `tc.rs`. See
`docs/TC_RS_ARC.md` §9 for what each kind costs; the short version is that
`panic!` on a rejection path is cheap (`kernel_check`), and an `.unwrap()` or
index is the kernel assuming something its caller established, which needs
either a propagating precondition or a decline.

Expect this file to be where most of the remaining totality work lives.
