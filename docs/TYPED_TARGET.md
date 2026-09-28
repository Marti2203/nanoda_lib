# The typed target (option 2, chosen 2026-09-27)

## Why

`tconv` -- the model's "real conversion", `deq_p` in `Real` mode -- relates
every pair of terms (`hyps_refuted.rs`): its congruence and untyped steps
pass through ill-typed terms, and one proof-irrelevance step then equates
anything. Real typing (`types_to` in `Real` mode) uses the same conversion
in its rules, so it is unsound too, and every kernel claim guarded by `kh`
is vacuous. Patching `deq_p` (typed chain middles, `target/work/t1m_wip.patch`,
`git stash` "T1m typed-chain WIP") runs into regularity everywhere the model
composes conversions through types.

Option 2 replaces the target: the specification of "really typed" and
"really convertible" becomes a TYPED JUDGMENT with presuppositions, of the
shape `ti_syntax` already has and for which typed inversion is proven
(`dom_fund.rs`: Pi/Sort injectivity, Pi/Sort disjointness).

## The judgment

`Σ; Γ ⊢ M ≡ N : A` (and `Σ; Γ ⊢ A type` as `A ≡ A : Sort l`), extending
`ti_syntax`:

- `Γ` stays de Bruijn (`Var`), as now.
- `Σ` is a SIGNATURE: the environment's constants (with universe-level
  parameters; definitions carry values) AND the kernel's local variables
  (`Free k`) as axioms. Kernel terms are closed over `Var` and mention
  locals as `Free`; treating locals as signature axioms types them directly,
  with no translation between the kernel's unordered local maps and de
  Bruijn contexts. A signature is well formed in some dependency order.
- Rules, added in stages (below), each carrying its presuppositions (both
  sides typed), as the existing Beta/Eta/congruence rules do.

## Stages

Each stage extends the judgment, its syntactic metatheory (renaming,
substitution, head reduction), the domain model and soundness, and
adequacy, keeping `pi_inj` / `sort_inj` / `pi_not_sort` proven.

| stage | content | model work |
|---|---|---|
| S1 | signature: constants (level instantiation, level-equivalent instances), locals as axioms, definitions' delta rule | constants denote via their values or as neutral (bottom) axioms; delta joins head reduction |
| S2 | `let` (zeta and congruence) | zeta in head reduction |
| S3 | restate the kernel's hypotheses and claims over the judgment on the S1-S2 fragment; retire `tconv` / Real `types_to` there | none |
| S4 | port the kernel claims (`cc`, `ci`, `cw`) and certificates to derivations, for the fragment | none |
| S5 | Nat/String literals and the Nat extension | literals as constructor forms |
| S6 | inductive types: constructors, recursors, iota, K-like reduction, projections, structure eta, unit eta | research: inductive codes and their relation clause (the paper covers Nat and Id only) |
| S7 | quotients | quotient reduction |

S3/S4 give the first end-to-end result: on terms of the fragment, the
kernel's accepted conversions and typings are derivable, and the typed
hypotheses it needs are theorems.

## Progress (2026-09-28)

| stage | commits | proven |
|---|---|---|
| S1 | 86a43a6, 6d65c4c, 9431845 | constants, locals, delta in the judgment; model unfolds definitions by constant rank; injectivity for the extension |
| S2 | b73379b | `let` (Zeta); model reads a `let` as its redex |
| S3 | be79d9b, 3378311, 7089ab4 | validity (`ti_valid`), chain Pi/Sort injectivity (`dom_fund`), generation (`ti_gen`), uniqueness of types and subject reduction under `sig_wf` (`ti_sr`) |
| S2′ | (port) | the kernel's `let` rule: Zeta types the body's instance, not the body under a binder (the kernel substitutes first, as Lean 4 does); the model reads a `let` as its instance, with the zeta-aware size `ti_zsize` as its measure |
| S4 | (port, in progress) | kernel locals: renaming and closing (`ti_locals`), the binder bridge (`kbind`); subject reduction for the kernel's parallel reduction, joinability and level equivalence give conversions (`jkernel`); every kernel claim lemma re-proved over the judgment (`kclaims`) |

Rules carry their presuppositions: Eta its codomain, Beta and Zeta their
right side's typing, ConstAx/ConstDef their instances' type conversion.
The kernel side has to supply these; each is available to it
(substitution, `inst_tm`, level-instance conversion).

## The port (S4)

The claims stay as the kernel states them (`cw`, `ci`, `cc`, `cwh`,
`tp_to`, `tt_to`), with `typed`, `tconv` and `jconv` now the judgment's.
What changed in their statements:

- `cc` is about the fragment's terms (`frag_term`: no literals or
  projections, which the judgment does not type yet); `ci`, `cw` and
  `tp_to` already only speak about typed terms.
- `kh` gains `cr_env` (Church-Rosser for eta-free conversion) and
  `lev_ok` (level-equivalent instances of a constant convert), and
  `frag_env` requires `Nat.zero`/`Nat.succ` undeclared. These are
  environment facts the export boundary has to discharge (P3).
- Untyped kernel conversion enters through joinability: `ceq` (eta-free)
  gives `jn` by Church-Rosser, and typed terms joinable modulo universe
  levels convert (`jkernel::jn_conv`). Eta has its own producers.

### The export theorem

`export_sound::export_kh` gives `kh` at every cutoff of a fully
certified export from `kh_hyp`, which names only what is about the
export itself rather than the checker: the fragment (`frag_env`, and
every declared type and value a fragment term) and the distinctness of
the export's built-in names (`names_ok`). Everything else is proved by
induction over cutoffs from the certificates:

- declared types are types, values typed at them, all closed and with
  their own universe levels (as before);
- a definition's value mentions only earlier declarations
  (`ti_level::d_consts`), so ranks by position are valid (`ranked_at`);
- every level instance of a declaration is typed (`ti_level::d_ls`,
  level instantiation of derivations), so the signature is well formed
  (`wf_at`);
- level-equivalent instances convert (`levok_at`, via `lveq_conv` in the
  certificate's environment, where the induction already has it);
- Church-Rosser's environment facts follow from the fragment and
  `names_ok` (`cr_env_of`).

## S6: inductive types (started 2026-09-28)

### What the paper gives

Section 3.4 of the paper adds `ℕ` with pattern matching, 3.5 the identity
type, 3.1-3.2 Σ and unit with η, 3.3 general recursion (`Y`, interpreted
as the supremum of its approximations). The recipe per type former:

- a code for the type (`N : U`) and value codes for the constructors
  (`0`, `S u`, with `S ⊥ ≠ ⊥`: seeing a constructor is an observation);
- semantic typing clauses for the values (`S u :_{n+1} N` when `u :_n N`;
  Id's `ref w` carries `w` below both endpoints);
- the logical relation at a value code reads the constructor off head
  reduction (`M ⇝* S M'` with `M'` related at `u`);
- the eliminator's adequacy by induction on the value code.

It claims the technique "should extend to general indexed inductive
types" but does not do it.

### The obstacle for Lean's inductives

Semantic typing (`dom_typing::has_type`) is on compacts only, with no
signature. A general constructor's field types are terms of the
signature (`cons (a : α) (l : List α)`); typing a value `cons(u, v)` at
`List(a)` needs `u : a`, i.e. the denotation of a signature term, and
`mem_w` in turn uses typing (a lambda's entries are typed), so the two
definitions would be mutually recursive with no decreasing measure.

### The design

- **Values carry their field codes.** A constructor value is
  `Con(c, ps, fs)`: the constructor, its parameter codes, and per field a
  pair (field type code, field value). `Con(c, ps, fs) :_{n+1} Ind(i, as)`
  when each field value is typed at its field code at stage `n`, the
  parameters are below the type's, and the field codes are types. This is
  signature-free. That the field codes are the RIGHT ones (denotations of
  the constructor's field types) is the interpretation's business:
  `⟦c⟧` only produces values whose field codes come from the field types'
  denotations. The eliminator recovers field typing from the value.
- **Type codes by name.** `Ind(i, as)`: the inductive's id and its
  argument codes (parameters, indices), atomic otherwise, so recursive
  occurrences need no infinite unfolding.
- **Indices.** A value's result indices sit below the type's (as Id's
  `ref w ≤ u`).
- **The recursor** is interpreted on saturated applications, by recursion
  on the major's value code (finite, so recursive calls on fields go
  down); its bare constant by its eta expansion. The rules' right-hand
  sides must be typed at their minor-premise types: a signature
  condition like `sig_wf` for definitions, which the kernel's inductive
  checker must establish at the export.
- **The judgment** gains, per inductive declaration in the signature
  (parameters, indices, constructors, recursor, rules): the constants are
  typed by `ConstAx` as now; a new `Iota` rule relates a saturated
  recursor application on a constructor application with the rule's
  instance, carrying both sides' typings (as `Beta`/`Zeta` do).

### Codes as built (S6.1-S6.2)

One compact serves both: `Nd(key, comps)`, never bottom, ordered and
joined pointwise. `key` is `Ty(i, prop)` for the code of inductive `i`
(`prop` when it lives in Prop) or `Con(i, c)` for a value built by
constructor `c`. Typing (`dom_typing::has_type`):

- `Nd(Ty(i, _), as) : U`, and `: Prop` when `prop`;
- `Nd(Con(i, c), cs) : Nd(Ty(i, false), ts)` when `cs` starts with
  `ts.len()` components each below the matching one of `ts` (parameters
  and indices), and the rest are pairs `(t, v)` with `t : U` and `v : t`
  one stage down (the fields, each with its own type code);
- nothing inhabits a Prop inductive but bottom, as for every
  proposition (`prop_inhabitant_bot` is unchanged).

Stability, typed joins and raising the type (Props 2.16-2.18) extend
with these clauses.

### Open: large elimination out of Prop

`Eq.rec` (and every subsingleton eliminator into Type) has no
interpretation in this model yet. Proofs denote bottom and bottom
inhabits every type, so a context with `e : 0 = 1` has a model, and
transport along `e` would have to turn an element of `P 0` into one of
`P 1`. The paper's identity type avoids this because it is
proof-relevant (`ref w` with `w` below both endpoints). Small
elimination is fine: both sides of its `Iota` are proofs, both bottom.
Until this is settled, the S6 signature condition excludes large
eliminators of Prop inductives; S6.7 is where it returns.

### Sub-stages

| | content |
|---|---|
| S6.1 | compacts: one data node `Nd(key, comps)` for type codes and constructor values, compared pointwise; order, join, compatibility, coherence, well-formedness (done) |
| S6.2 | semantic typing for them; the stage and join properties (Props 2.16-2.18) (done) |
| S6.3 | syntax: the signature carries the kernel's recursor tables (`Sig.ienv`); rule `Iota` relates a ready recursor application (`rec_ready`) to its rule instance (`rec_result`) where both sides are typed; renaming, substitution, local swap/close, level instantiation, validity, generation and signature extension cover it (done). `Iota` also asks `iota_ok(sig)`, the signature condition the model will need: for now "no recursors", so the rule is dead in the model until S6.4 states the real condition |
| S6.4 | interpretation of inductive constants, constructors, recursor applications; ideal properties; soundness incl. `Iota` |
| S6.5 | logical relation clauses; their properties; adequacy incl. `Iota`; injectivity re-proven |
| S6.6 | kernel side: `jsig` from the environment's inductive tables, SR for the kernel's recursor iota, `frag_env` relaxed; literals through `Nat` |
| S6.7 | projections, structure and unit eta, K-like reduction |

## The open fork before S4

The kernel reduces with iota, projections, literals, quotients, structure
and unit eta. None are rules of the judgment yet, and modelling them
(inductive codes and their relation clauses) is the research part (S6).
Porting the kernel claims first (S4) gives claims that hold for runs
staying in the S1-S2 fragment; extending the judgment first (S6) makes
the port total but needs the model extension.

## What stays

- The typed judgment and its metatheory (`ti_*`), the domain model and
  the typed inversion proof (`dom_*`).
- `def_eq ⊆ kconv` (Stage B of the kernel proof), as a statement about the
  kernel's own relation.

## What goes (as each stage replaces it)

- `tconv`, `kconv_wt`, Real / `InferWt` `types_to` and the `deq_p` family's
  typed leaves; the transport modules built on them (`weaken`,
  `swap_typed`, `subst_typed`, `subst_conv`, `level_typed`, `env_weaken`);
  `metatheory.rs`'s conditional theorem; `hyps_all`, `h_sr`, `h_sr_leaf`
  as stated.
