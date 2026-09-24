# Arena identity

## The problem

A pointer is a `u32`: bit 31 says which dag (export file or type-checker
context), bits 0–30 index into it. `to_model(p)` gives every pointer ONE
meaning. That holds only if there is one arena per tier. Two `TcCtx`s put
different nodes at the same index, and so do two export files. Verified code
holding both could see `expr_ptr_eq(p1, p2) == true` for pointers the model
says differ, and derive `false`.

The same single-export assumption sits behind `nat_zero_id()`,
`quot_kind_of`, `nat_bin_op_of` and the rest of the name-cache ids: each is
one global value, and two exports place `Nat.zero` at different indices.

Nothing does this today. The goal is for the verifier to rule it out, as a
stated property rather than a convention.

## The design

- A dag's id is `dag_arena(d)`, uninterpreted. `LeanDag` is opaque to the
  verifier and built only by unverified code, so no proof can show two dags,
  or their ids, equal. The allocation specifications state that a dag's id
  survives allocating into it.
- `Ptr` carries `arena: Ghost<nat>`; the allocation specifications say it is
  the id of the dag the pointer indexes into.
  Runtime `==` and `Hash` still see only `raw`. Pointers from different arenas
  are therefore different values to the verifier even when `raw` agrees.
- `owns(ctx, p)`: `p`'s tag is the id of the dag its marker selects,
  `ctx.dag` or `ctx.export_file.dag`. Every reader requires it. Every
  allocation ensures it of its result and requires it of the children.
- Each `&mut` context function keeps the arena ids unchanged (a frame), so
  `owns` facts survive calls.
- Hash tables keyed by pointers: the Verus fork's vstd conditions every
  `HashMap`/`HashSet` specification on `keys_obey_model(keys)`, the key model
  restricted to the keys in the table. `Ptr`'s trusted claim becomes: a set of
  pointers in which equal `raw` means equal pointer obeys it. The caches keep
  every key owned by their context, which gives exactly that.
- Name-cache ids become per-export.

## Stages

Each stage is one or more commits on branch `arena-identity`. The branch
merges only when no false axiom remains.

1. vstd `keys_obey_model` on the fork (done: fork `3c44a005a`).
2. Plumbing: the tag on `Ptr` (`Ghost::assume_new()` in `Ptr::from`; the
   tag is logical only, so no runtime value is needed), and runtime
   `==`/`Debug` written out on `raw` only. The items listed under
   "Known-false" below stay false until their stage lands.
3. Frames: `same_arenas(old, final)` on every `&mut` context function and
   axiom.
4. `owns` on readers and allocation, threaded through the verified
   functions' preconditions.
5. Key model: replace the `Ptr` key-model axioms, add the cache invariants.
6. Per-export name-cache ids.

## Known-false while the branch is open

Marked `ARENA-IDENTITY STAGE 2` in the source. Each is false only for
pointers from two different arenas.

| item | file | fixed in stage |
|---|---|---|
| `Ptr::eq`: `result == (*a == *b)` | `src/util_model.rs` | 4 |
| `PartialEqSpecImpl for Ptr`: `eq_spec` is `==` | `src/util_model.rs` | 4 |
| `name_id_injective` (now `external_body`) | `src/level_arena_bridge.rs` | 4 |
| `expr_id_injective` (now `external_body`) | `src/expr_arena_bridge.rs` | 4 |
| `ptr_obeys_key_model` and its tuple siblings | `src/util_model.rs` | 5 |
