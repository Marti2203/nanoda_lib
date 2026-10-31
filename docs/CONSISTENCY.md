# Consistency (started 2026-10-31)

## Goal

For every export nanoda accepts, the resulting environment has a model in
set theory; in particular no accepted constant has type `False`. This is
con-leche's main theorem (`no_proof_of_False`), proved here for nanoda's
own checker. Nanoda's code does not change: what changes is what its
verified claims are proved against.

## Why a set model, and why without a typing judgment

The current end-to-end theorem goes through a typing judgment
(`docs/TYPED_TARGET.md`): the kernel's untyped conversion implies typed
conversion only through confluence, subject reduction and injectivity,
which are proven for the fragment. That is where `kh_hyp`'s fragment
hypotheses come from, and the domain model behind it cannot interpret
`Eq.rec` into `Type` (`project_eq_obstruction`).

Con-leche (Lean FRO; `whitepaper/Fragment` is a 30k-line self-contained
version) shows a route that needs none of that metatheory:

- `denote` maps every term to a set: total, structural on the term,
  reading no type. A binder's regime is read off the values: a function
  space is a truth value exactly when every fibre is one, an abstraction
  is the proof point `pt` exactly when every body value is.
- `well_denoted` replaces typing: recursive on the term, it records
  that an application's function lies in a function space whose domain
  holds the argument, and that binder domains and Pi fibres are types.
- One induction proves every rule of the checker sound: a reduction
  keeps the denotation of a well-denoted term that is not `pt`, a
  definitional-equality verdict means equal sets when neither side is
  `pt`, an inferred type contains the term's value.
- Inductive types are least fixed points, so large elimination is
  unproblematic.

## The trust addition

The set theory is an interface (`src/set_model.rs`): an external type
`ZSet` with uninterpreted operators and 20 `external_body` laws, which are
con-leche's `SetLib`. They hold in V_kappa for an inaccessible kappa
(with an omega-chain of inaccessibles for the universes), the standard
model of Lean's theory. Con-leche instantiates its interface on Mathlib's
`ZFSet`; Verus has no such library, so here the laws are trusted.
Inductive types will need the universe closure laws of con-leche's
`UnivLib` (pairing, union, power set, replacement, omega).

## Probe (2026-10-31): done

`src/set_model.rs`, 19 verified, module check under a minute:

- the interface, the two regimes, `sort_value`, `Model` (constants at
  concrete levels, locals, literals, projections), `denote`;
- `denote_shift`, `denote_subst`, `denote_shift_down` and the
  beta-substitution lemma `denote_subst1`;
- `well_denoted` and its transport along shift, subst and `subst1`;
- `beta_sound`: at a well-denoted redex that is not `pt`, the reduct is
  well-denoted and denotes the same set, with no premise on the argument.

Two Verus lessons: a closure written inside a recursive spec fn is not
identified with an identical closure written elsewhere, so the binder
body is a named spec fn (`denote_under`) in the recursion; and an
`exists` over a `spec_fn` with a trigger absent from its body gives a
`choose` nothing, so the lambda clause is stated pointwise
(`has_type_bound`).

## The claim shape this needs

`kconv` (`deq_p_any` in `Infer` mode) is a chain of steps, so it has
transitivity through arbitrary middle terms. `hyps_refuted.rs` shows what
that does in `Real` mode (every term converts with a proof), and the
same chain shape blocks semantic soundness: the middle of a chain is not
known to be well-denoted. Con-leche's `DefEq` has no transitivity; it
mirrors the algorithm instead: reduce one side and continue (`redL`),
`symm`, congruence, proof irrelevance, eta, sorts and constants by level
equality.

So the kernel claims need a relational description of nanoda's checker
of that shape (a rules tier), and the contracts of `whnf`, `def_eq` and
`infer` re-targeted to produce it. That is proof work on the claims only.

## The certification tax

Con-leche adds two checks Lean's kernel does not make: lambda congruence
and eta compare the bodies' types (except where a body's point-ness
cannot vary: a propositional domain, bodies not using the variable, or a
comparison at a known type). The reason is semantic: a definitional
equality only claims equal sets for sides that are not `pt`, so two
lambda bodies equal at every non-proof point could still disagree on
which points are proofs, unless both lie in one type.

Nanoda will meet the same obligation at its lambda congruence and eta.
Options, to decide when we get there: find the type from nanoda's call
site (comparisons at a known type need nothing); a named hypothesis; or a
tested-input check in the kernel (a code change, so the user's call).

## Stages

| stage | content |
|---|---|
| C1 | probe: interface, `denote`, `well_denoted`, beta (done) |
| C2 | the rest of the core: zeta, delta (constants via the model's assignment), sorts and levels, Pi formation, application, lambda, let; contexts (`Sat`) and `Infer` soundness |
| C3 | the rules tier: nanoda's reduction, definitional equality and inference as relations without free transitivity; soundness of each rule |
| C4 | re-target the `whnf`/`def_eq`/`infer` contracts to the rules tier |
| C5 | the environment model: definitions, axioms, inductives as least fixed points, recursors and iota, projections, structure and unit eta, Nat literals and the Nat extension, quotients |
| C6 | the main theorem: an accepted export has a model; no constant of type `False` |
