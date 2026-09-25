# Arena storage: denotations defined from a history

## The problem

`to_model(p)` (expressions), `to_model` (levels) and `to_model_name` are
uninterpreted, and about two dozen trusted specifications say what the
readers return, what allocation stores, and what a pointer of a given shape
denotes (`read_*`, `alloc_*`, `zero`, `anonymous`, `is_*_shape_model`,
`arena_lctx_local`, the hash-consing injectivity axioms). Each is a separate
claim about the same fact: the dag holds, at a pointer's index, the node the
pointer denotes.

The arena-verification arc (2026-09-17) ruled out giving `to_model` a
context parameter: every allocation would change the denotation, and every
exec proof would thread monotonicity through it. The denotation has to stay
a function of the pointer alone.

## The design

- **A history per arena.** `arena_hist::<K>(id)` is the sequence of nodes an
  arena will ever hold, uninterpreted and fixed. A denotation is DEFINED
  over it: `to_model(p)` is the storage model already in
  `expr_arena_bridge.rs` (`expr_model_at2`'s recursion on tier, then index),
  read from the history of `p`'s own arena. It is a function of the pointer,
  as before; monotonicity is not needed because the history never changes.
- **The dag agrees with its history.** `LeanDag` gets a TYPE INVARIANT: each
  set's keys are a prefix of the history for the dag's id, the keys are
  distinct, and every stored node is well formed (cached flags, children
  owned and below). The invariant is assumed of values unverified code builds
  (the parser, `LeanDag::new`), which is the boundary the parser already is.
- **One trusted primitive: pinning.** Appending stores whatever the history
  says is at that position. `arena_pin` states it, and consumes a tracked
  `ArenaTok` that counts the positions pinned so far. The token is linear and
  cannot be forged (private fields, no constructor in verified code), so
  each position of each arena is pinned exactly once, by the element actually
  appended there: the history is a prophecy, and pinning resolves it.
- **Insert and pin in one call.** Verus checks a type invariant right after
  each mutation of a field. `arena_insert(&mut set, Tracked(&mut tok), k)`
  takes both as separate arguments, so the invariant is checked once, after
  the token has caught up. This is the one kernel change per allocator:
  `dag.exprs.insert_full(e)` becomes `arena_insert(..)` (registered).
- `insert_full` is specified `no_unwind`, which Verus requires for a `&mut`
  field access on a type-invariant struct. It can panic on capacity overflow.
  The only dag verified code mutates is the checking thread's own, which an
  unwinding panic drops with the thread, so a half-updated dag is never
  observed.

## What it retires

The readers and allocators become verified bodies, the shape axioms become
lemmas (a `Const`-shaped denotation comes only from a stored `Const`), and
hash-consing injectivity follows from distinct keys and canonical hashes.
What is added: `arena_pin`, the IndexSet specifications (third-party, like
IndexMap's), and a key-model fact per node type.

## Stages

0. IndexSet specifications (`indexmap_model.rs`).
1. (done) `arena_hist`, `ArenaTok`, `arena_pin`, `arena_insert`; `LeanDag` in
   `verus!` with tokens and the invariant; `dag_arena` defined.
2. (done) The export file's name-cache tag is its dag's id: `ExportFile` carries it as a type invariant; public contracts read the tag through the closed `ExportFile::arena`, and `export_ok` and its siblings are closed (unfolded by `export_ok_facts`).
3. (done) Names: `to_model_name` defined; `read_name`, `alloc_name`, `anonymous` verified.
4. (done) Levels: `to_model` defined; `read_level`, `alloc_level`, `zero` verified. The level-SEQUENCE arena (`read_levels`, `alloc_levels_slice`) waits on a vstd rule for looking up an `Arc<[T]>` by `&[T]`.
5. (done) Expressions: `to_model` defined, the payload projections (`const_name_of` and the rest) are the stored node's fields, the local serials are read from the history; `read_expr` and `alloc_expr` verified; `is_const_shape_model` and its three siblings are lemmas.
6. Not done yet. Each remaining arena fact, and what it waits on:
   - `read_levels`, `alloc_levels_slice` (the level-sequence arena): a vstd
     rule for looking up an `Arc<[T]>` key by `&[T]`.
   - `alloc_string`, `alloc_bignum`, `read_bignum_value`: a key-model fact
     for `Cow<str>` / `BigUint` (third-party types), which would replace
     them one for one or better.
   - `to_model_name_injective`, `level_ptr_eq_iff_same_model_param`
     (hash-consing): provable for STORED pointers from distinct keys,
     canonical hashes and checker/export disjointness, but callers only hold
     `owns`, which does not say stored; an out-of-range export pointer
     denotes the default. Stated for all owned pointers they are consistent
     only because the export history beyond its contents is left open.
   - `mk_unique`, `unique_serial_injective`: the unique counter lives in the
     context, not the dag, so "every stored unique serial is below the
     counter" has no home yet; and the pretty printer renames locals under
     the same id in its own context.
   - `str_lit_to_constructor`, `append_index_after`: string content
     (`format!`), not arena structure.

Also done along the way: the level (`mk_dbj_level`) and closing
(`replace_dbj_level`) local constructors, and the arena's local context
(`arena_lctx`, so `arena_lctx_local` is a lemma).

A soundness finding: defining the name denotation made
`to_model_name_injective` refutable, because every dag held a copy of the
anonymous name at index 0 (so two owned pointers provably denoted it).
Checker dags now start empty; see `Parser::new`.
