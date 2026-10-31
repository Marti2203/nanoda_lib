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

Con-leche proves its checker against a syntactic rules tier and then
proves the rules sound. Nanoda's claims are already stated per function
as conjunctions (`whnf_claim`, `def_eq_claim`, `kinfer_claim`), so the
semantic statements can be added to them directly, in con-leche's
`Motive.lean` shapes, quantified over every model of the environment and
every valuation satisfying the local context:

- reduction `e ~> r`: if `e` is well-denoted and not `pt`, then `r` is
  well-denoted and denotes the same set;
- conversion `x == y`: two well-denoted sides that are not `pt` denote
  the same set;
- inference `e : t`: `e` and `t` are well-denoted, `t` denotes a type,
  and `e`'s value is a member of it.

These compose the ways nanoda's proofs compose their claims: reductions
chain; a conversion after reducing a side ("reduce then continue") holds
because the reduct of a well-denoted non-`pt` side is well-denoted and
not `pt`; an inferred type moves along its whnf because a type is never
`pt`. A free transitivity through an arbitrary middle term does not
compose, and the survey of `kconv_trans`'s call sites (2026-10-31)
found the reduce-then-compare shape at the def_eq sites and reductions
of types at the inference sites. Locals are model data (`Model.locals`);
a context is satisfied when each local's value is a member of its type's
denotation, and a binder opened at a fresh local relates to `denote_under`
through the opening lemma.

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
| C2 | the core's semantics (done): the regimes' introduction and elimination laws (`lam_value_mem`, `app_mem_pi_value`), `Sort n : Sort (n+1)`, Pi formation at `imax`, zeta, opening a binder at a local (`denote_open`), unused locals (`denote_fresh_local`), level instantiation as a change of level valuation, closed terms reading no environment (`denote_agree`) |
| C3 | the semantic claims and their composition laws (`src/set_claims.rs`, done): `env_model`, `sat`, `sem_red` / `sem_conv` / `sem_infer` / `sem_type`; reductions chain, reduce-then-continue on either side, symmetry, an inferred type moves along a reduction or a conversion to a type; `delta_sound` |
| C4 | add the semantic claims to the `whnf`/`def_eq`/`infer` contracts; `whnf_claim` done (below) |
| C5 | the environment model: definitions, axioms, inductives as least fixed points, recursors and iota, projections, structure and unit eta, Nat literals and the Nat extension, quotients |
| C6 | the main theorem: an accepted export has a model; no constant of type `False` |

## The run's named hypothesis (option 2, chosen 2026-10-31)

The recursor step on a proof major is not sound in the model without a
check nanoda does not make: with `h : Acc r x` reducing to
`Acc.intro x' h'`, a proof's value says nothing about `x'`, so
`Acc.rec motive minor x h` (motive into `Type`) and its reduct can
denote different sets on a well-denoted but ill-typed input. Con-leche
checks the reduced major's type there; λ-congruence and eta have the
same kind of obligation (the bodies' types).

The user chose to keep nanoda unchanged and name these as a hypothesis
first (option 2), with the checks (option 1) as a later option. The
hypothesis is about the run: `no_unproven_step(export)`, the checker
took no step whose soundness is not proven, and each such step calls
`tc::ksem_red_unproven` where it is taken. The same mechanism stages
C4/C5: a step starts marked and its mark is removed when its soundness
is proven. At the end the marks left are option 2's residue.

## C4 progress

`whnf_claim` carries `ksem_red` (2026-10-31). Proven: beta (telescoped,
`sem_red_spine_reduce`), zeta, level simplification of a sort,
projection and spine-head congruence, chains. Marked unproven (C5):
string-literal expansion, delta in `whnf` and lazy delta's unfolding
(`delta_sound` covers it once level parameters are known distinct),
recursor steps (`rec_step_claim`), `Nat.succ` and binary-operation
folding, projection of a constructor (`reduce_proj_core`), quotient
steps.

## Next slice: conversion and inference together

`def_eq` and `infer` call each other (proof irrelevance infers both
sides' types), so their semantic halves land together, as the typed
claims did. Two shapes, after con-leche:

- checking inference establishes the invariant: from the run, the term
  and its type are well-denoted and the value is a member of the type
  (`sem_infer`);
- infer-only inference (nanoda's `InferOnly` flag) skips the argument
  check, so it cannot establish the invariant; its claim takes the
  term's well-denotedness as a premise and concludes con-leche's
  hereditary relation at the computed type (the value is the point, a
  member, or at a Pi a graph over its domain; `ClaimsIO.lean`). An
  infer-only conclusion never feeds a site that needs the
  establishing form; proof irrelevance consumes the premise form.

Conversion's cases: the quick check, sorts and constants at equal
levels, application congruence (the argument's slot domain is a type,
so both arguments are proofs or neither is), Pi congruence (fibres are
types, never the point), lazy delta (delta, then reduce-then-continue)
and proof irrelevance (vacuous once both sides are proofs) are proven
from the model; struct and unit eta and the literal comparisons are C5;
lambda congruence and eta are the option-2 residue unless the call site
supplies the bodies' type.
