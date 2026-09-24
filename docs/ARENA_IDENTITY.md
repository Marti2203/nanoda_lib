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

None as of stage 5. Stage 4 fixed `Ptr::eq`'s specification (now
`result == (a.raw == b.raw)`, and pointer equality when the tags agree),
`PartialEqSpecImpl for Ptr`, and `name_id_injective` / `expr_id_injective`
(proven again under `owns(c, a) && owns(c, b)`). Stage 5 replaced the
`obeys_key_model` axioms for pointer keys (below).

## What stage 4 added

- `owns(c, p)` on every reader, allocation and verified function that takes
  or returns a pointer; `owns_all` for pointer sequences. Ownership is a
  function of `arena_ids(c)`, so frames carry it across calls by congruence.
- `expr_children_owned` / `level_children_owned` / `name_children_owned`:
  readers ensure a node's children are owned, allocation requires it.
- The name cache carries the export arena's tag (a type-invariant clause);
  the export tier's id is DEFINED as that tag.
- `env_arena_ids(env)` / `env_owns` / `env_matches(env, c)`: environment
  lookups and records (`inductive_data_owned`, `constructor_data_owned`,
  `recursor_data_owned`) hand out pointers of the environment's arenas;
  `tc_wf` and the shadow routes require the environment to match the context.
- Cache invariants (`tc_wf`'s five caches, the expression caches, the shadow
  memo's certificates) carry ownership of keys and values.
- Comparisons that run with no context in scope (`ptr_in_seq`,
  `ctor_app_params_ok`, closures) are stated on `raw`, which is what the
  kernel's `==` computes; `owned_raw_eq` turns that into pointer equality
  where both pointers are known owned.

## What stage 5 changed

The five type-wide key-model axioms (`ptr_obeys_key_model` and the
`(Ptr, u16)`, `(Ptr, u16, u16)`, pointer-triple and `SortedPair` variants)
are gone. In their place, one axiom per key shape claims only what the
runtime `==` makes true: a key set on which componentwise-equal `raw` means
equal key obeys vstd's relativized `keys_obey_model`. The `*_owned_keys` and
`*_map_keys` lemmas derive that premise from ownership, and every cache
operation in verified code calls one against the table's state at that
point. The congruence-failure cache carries no claim and no longer asks for
a key model at all.
