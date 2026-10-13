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

### S6.4 design: semantic constants

An inductive's type former, constructors and recursor have no values to
unfold, so the model gives each a *code function* on compacts and
interprets the constant as what lies below a compact `v` that is typed
at a member `A` of the constant's type (`A` and `v` chosen by the
membership witness) and that approximates the code function: a lambda
whose entries' outputs approximate it at the inputs so far, down the
constant's type telescope. Typing is part of membership, so "typed
within its type" holds by definition; join-closure needs only the
type's, which the `ConstAx` premise supplies.

- Type former: an axiom whose type is a Pi telescope ending in a sort
  (no table: any such axiom is an atomic type former). At full arity the
  output is below `Nd(Ty(I, prop), inputs)`, `prop` when the sort is
  zero.
- Constructor `c` of `I` (the kernel's constructor table): at full arity
  the value node, whose field type codes are the domains of `A` along the
  way and whose leading components are the arguments of `A`'s final
  type code (parameters and indices).
- Recursor: by recursion on the major's code. Bottom goes to bottom; a
  value of constructor `c_j` goes to the `j`-th minor applied to the
  fields and, for each recursive field, the recursor at that field's
  value (a lower code, so the recursion terminates).

`Iota` is then sound when every rule's right-hand side has the shape the
kernel generates, `λ params motives minors fields. minor_j fields
(rec ... field)...`: a syntactic condition on the tables, the real
`iota_ok`, which S6.6 gets from the (verified) inductive module that
builds the rules. Sub-steps, each ending green:

| | content |
|---|---|
| S6.4a | semantic type formers in `mem_w` (`sem_const`, `tf_fun`); soundness of their `ConstAx` (`dom_sem`); the relation at type codes (types: convertible; terms: bottom only, until constructors) and adequacy down the telescope (`dom_sem_rel`) (done) |
| S6.4b | semantic constructors (`cf_fun`: field type codes are the type element's domains; `code_ok` dispatches by kind) with soundness (`dom_sem`); the relation at constructor values (both sides reduce to applications of the constructor, fields related at their codes; `con_tm`) with all relation lemmas; adequacy by induction down the constructor's telescope (`dom_con_rel::cf_rel`) (done) |
| S6.4c | the semantic recursor; its typing by induction on the major |
| S6.4d | the real `iota_ok`; soundness of `Iota` |

### S6.4c/d design: the recursor

Scope: a recursor of one inductive (one motive), whose recursive fields
are direct (`I params idx'`, not `Π ys, I ...`). Mutual, nested and
reflexive inductives stay outside `iota_ok` and keep their recursors
uninterpreted (bottom); the kernel side then ports their iota steps only
once they are covered.

- The code function `RECVAL(inputs)` recurses on the major's code:
  bottom gives bottom; a value `Con(I, c_j)` gives minor `j` (the rule
  for `c_j`'s position) applied to the value's field values and then,
  for each recursive field in order (read off `c_j`'s declared type, not
  off the approximation, so the count matches the rule), `RECVAL` at the
  field value with the indices of the field's type code.
- Soundness of the axiom rule at the recursor needs `RECVAL` monotone and
  well formed, as for the other kinds.
- Soundness of `Iota` needs `⟦rec ... (c_j ps fs)⟧ = ⟦rhs_j ... fs⟧`. The
  hard direction needs a member of `⟦rec⟧` that is exactly `RECVAL` at
  given inputs, so `RECVAL`'s output must be typed at the motive's
  application: the semantic typing of the recursor, by induction on the
  major's code, with the type element of the recursor chosen large
  enough (join-closure of the type) that each minor's domains lie above
  the value's field codes.
- `iota_ok` becomes the real condition: every rule's right-hand side is
  `λ params motive minors fields. minor_j fields ihs` with `ihs` the
  recursor at each recursive field, all of the kernel's own shape.
- Head reduction takes iota steps (reducing the major first), so the
  relation's head expansion covers `rec ... m ⇝ rhs_j ... ⇝ minor fs ihs`;
  adequacy at the recursor is the paper's induction on the major's code:
  the major relates (by `con_tm`) to a constructor application with
  related fields, the minor's application clause relates the fields and
  the recursive results (by induction), and head expansion closes.

These three (typing of `RECVAL`, the real `iota_ok`, iota in head
reduction) land together: the recursor's adequacy needs `Iota`
derivations, which need the real `iota_ok`, whose soundness needs the
typing.

Status 2026-09-28: iota in head reduction (f668f26) and `recval` with
its well-formedness and monotonicity (e7a0430) are in. The typing of
`recval` needs each minor premise's type to end in the motive at its
constructor's indices and value, so `iota_ok` has to state the canonical
recursor type (motive and minor premise types derived from the
constructors' telescopes, rule right-hand sides of the kernel's shape),
and S6.6 has to show the kernel's inductive module builds exactly that.
That specification is the next piece of work.

### Found 2026-09-28: carried field codes break the recursor's typing

`rec_canon` (4cd6e34) specifies the canonical recursor. Working out the
typing of `recval` against it shows the S6.2 value design cannot carry
it. `recval` at a major `Con(c_j, ...)` is minor `j` applied to the
fields, typed (by `app_typed_at`) at the minor's element's codomain, a
member of `⟦motive ts_j (c_j params fields)⟧`, hence below
`motive ts' v'` where `v'` is a value of `c_j` whose field type codes
come from the element the minor's type chose. The major's value carries
field type codes from another element of the constructor's type. The
two values are compatible but neither lies below the other, so the
output is not typed at `motive idx major`. This already happens for
`Nat.succ` (the value carries `Nat`'s code or bottom for its field); it
is not about indices.

Redesign (agreed 2026-09-28), for canonical inductives (fields are
direct occurrences `I params idx` or do not mention `I`):

- Values are bare data: `Con(I, c)` with the field values only.
- A type code is `Ty(I, prop)` over the arguments and a table, one entry
  per constructor (in declaration order): code functions from the earlier
  fields to the next non-recursive field's type code, to a recursive
  field's index codes, and to the constructor's result index codes.
  The table depends on the parameters only, so a recursive field's type
  is the enclosing code with the field's indices and the same table: no
  nested copy, codes stay finite.
- Typing `Con(I, c) fields` at `Ty(I) args table`: each non-recursive
  field typed at its entry's code, each recursive field typed at the
  enclosing code re-indexed, and the result indices below the code's
  indices. Still signature-free.
- The type former's code function builds the table from the
  constructors' field types, recursive index terms and result index
  terms. None mentions `I` (canonicity), so they rank below `I` and
  `mem_w`'s measure still decreases; non-canonical axioms keep empty
  tables (only bottom inhabits them).
- The constructor's code function is the bare value; its type element
  supplies nothing to the value any more.
- The relation's constructor clause relates fields at the table's codes.

This replaces S6.2's typing clause and S6.4b's constructor code function
and adds tables to S6.4a's type former; S6.1 (compacts) and S6.3
(syntax) stay.

### The redesign as built

Working the plan above through changed it in four places.

- **Positions, not ids.** A value is `Con(I, p)` over its fields, `p`
  the constructor's position in `I`'s canonical recursor. Tables are
  lists of blocks in that order, so the table a value reads is found by
  position, which order and join respect. `p` is a `nat`, not a kernel
  id (no `u64` casts).
- **No indices in codes.** A canonical code keeps the parameters and the
  table only. Index codes made a recursive field's code differ from the
  enclosing one, and neither lay below the other.
- **Deterministic tables.** `dom_code::canon_code` computes the table
  from the signature: an entry is a marker (`Tag(1)`) for a direct
  recursive field, else `Tag(0)` over the code of the field's type.
  The type former's code function sits below the canonical code, and
  values are typed at their type's table.
- **Parameters.** A field whose type is a parameter (`x : α` in
  `List α`) could not be carried: raising a code needs the type
  relation of the value's own parameter argument at the larger code,
  and that argument is only convertible to the type's, while the
  relation is not closed under conversion. The canonical fragment is
  therefore, for now, inductives whose fields are direct occurrences
  or *closed* simple types (another type former applied to closed
  simple types): `rec_canon::simple_ty` has no variable case, and the
  typing asks every table entry to be an inductive's code or bottom
  (`dom_typing::tyc`). This covers `Nat`, `Bool`, enumerations and
  trees labelled by closed types; `List`, `Option` and `Prod` wait for
  the parametric case.

In this fragment every field value is bottom or itself a value, so the
relation's constructor clause (`dom_rel::con_tm`) needs neither the
stage nor the type's code: both sides reduce to applications of the
value's constructor with convertible declared field types and derivably
equal arguments, and each field above bottom is again related by the
clause. The relation at an inductive's code is that clause plus the
type's conversion, so raising, lowering and restaging at such codes are
immediate, and constructor adequacy needs no bound on the type
element's domains: a field above bottom is a value, so its domain is an
inductive's code, where the relation already is the clause.

### S6.4c/d plan after the redesign (2026-09-28)

Scope for the first recursor stage, beyond the closed-field fragment:
**no indices** (`ni == 0`: `Nat`, `Bool`, enumerations, trees), and a
Prop inductive eliminates only into Prop. Codes dropped indices, so for
an indexed family the minor premise's output type (the motive at the
constructor's index terms) cannot be compared with the motive at the
major's own indices. A Prop inductive's values are bottom, so its large
eliminator could not choose a minor.

The chain, bottom-up (each step a verified checkpoint; the recursor is
wired into `code_ok` only when the last one closes, because a nonempty
`⟦rec⟧` immediately owes the constant case of adequacy):

1. `rf_fun`: approximations of `recval` down the recursor's telescope,
   with level invariance, compatibility and joins (as `tf_fun`).
2. Membership bounds: a member of `⟦I P⟧` lies below
   `canon_code(I, ls, ⟦P⟧)`, and a member of `⟦c P fs⟧` below
   `Con(I, p)` over the fields' values.
3. The typing theorem: along the entry chain of a typed approximation,
   `recval` at typed inputs is typed at `T = app(motive, major)`. The
   minor's codomain chain `E` is typed by `app_typed_at`, which needs no
   domain match. By `cod_in_body` and bound 2, `E` lies in
   `⟦motive (c P fields)⟧` and below `T`, so `ty_weak` moves the typing
   up. A step approximation (a single entry chain ending at `recval`)
   is then typed at the type element that follows the chain's domains
   and ends at `T`, and `T` is in the motive's denotation.
4. Iota soundness, left in right: the member lies below a join of
   `recval` at typed entry chains. Each unfolds to the minor applied to
   fields and to step approximations at the recursive fields, which are
   members of `⟦rec ... field⟧` by 3. The right side's join closure then
   gives the member.
5. Iota soundness, right in left: typed witnesses come from the
   function's typing and projection (`proj`: typed, same application).
   The major's witness is typed at the canonical code, whose membership
   in `⟦I P⟧` is bound 2's other half.
6. Adequacy at the recursor: telescope induction as for constructors,
   then induction on the major's height. The major's clause gives a
   constructor application, head reduction takes iota and beta, and the
   minor's application clause takes the fields (projected onto the
   minor's inputs, so typed; a field above bottom is a value, so its
   domain is an inductive's code) and the recursive results (by
   induction). The output's type moves from `E` to the type element's
   codomain through `T`.
7. `iota_ok` becomes: every recursor is canonical within this scope,
   and its type is derivable (for the body join-closure `cod_in_body`
   needs).

### Recursor stage status (2026-09-28)

Done: the typing theorem (`dom_rec_ty::rec_step`), and both directions
of Iota soundness for the redex without extra arguments
(`dom_iota::iota_core_l2r`, `iota_core_r2l`). They are stated under
`rec_wired`, which is recursor membership as it will be once `code_ok`
interprets recursors, and under the fragment facts (`rec_scope`,
`r2l_ok`). Right in left needed two more facts:

- **Exact arity.** The Iota rule and typed head reduction fire only at a
  major of its constructor's exact arity (`ti_hred::rec_fire`). An over-
  or under-applied major denotes bottom, while the rule's right side
  need not. The kernel does not check arity; the kernel port derives it
  from the major's typing.
- **Levels.** The major's constructor levels are independent of the
  recursor's in the rule. This first stage takes universe-monomorphic
  inductives only, where they cannot matter.

Next, in order:
1. **Subject reduction for iota**, needed as soon as `iota_ok` admits
   recursors. The reduct `rhs[params, motive, minors, fields]` must be
   typed at the redex's type. With parameters this needs `I P ≡ I P'`
   to give `P ≡ P'`, which is injectivity the current relation does not
   give (the parametric route would). So the first real `iota_ok` takes
   inductives without parameters: `Nat`, `Bool`, enumerations, trees
   with closed labels.
2. **One landing:** interpret recursors in `code_ok` (then `rec_wired`
   is `mem_sem`), Iota soundness in `sound` (the cores with extra
   arguments), and the recursor's adequacy (telescope induction, then
   induction on the major through iota head expansion). They depend on
   each other: a nonempty recursor denotation owes adequacy, and
   adequacy needs Iota derivations.

#### The end of the recursor's telescope (proven 2026-09-29)

The telescope induction (`dom_rec_adeq::rf_rel`) carries a semantic side
(`rf_sem`) at one level instance `lsem`: the argument codes and values
form a chain along the recursor's domains, and the current code belongs
to the rest of the telescope. At the end, this gives `a <= app(p, wx)`
for the motive's value `p` and the major's value `wx`. The end itself is
proven by induction on the major's height:

1. The major is related at an inductive code, so `con_tm` holds: `x`
   head-reduces to `c_j args`.
2. `rec P ms x` head-reduces to `R = m_j args ihs`: the major reduces in
   place, then one iota step, then beta through the rule's lambdas. The
   conversion `rec P ms x ≡ R` is built from the rules
   (`dom_rec_conv::rec_conv_side`): congruence at the major (the relation
   carries `x ≡ cx`), the Iota rule, and a Beta chain through the rule's
   lambda telescope (`ti_beta::beta_upto`, by simultaneous substitution).
3. A walk down the minor's code applies it to the fields and then the
   IHs. Every argument is projected (`jproj`), which leaves the
   application and the codomain unchanged, so the walk ends at exactly
   `recval(fs)`. Field arguments are related through `con_mono`; IH
   arguments by the induction, at the walk's current domain code. Beside
   the walk, a membership walk at `lsem` (as `tele_step_fit` does) shows
   each IH code lies below `app(p, field)`, which is the IH instance's own
   `rf_sem`.
4. The walk's code `E` and the goal's `a` both lie below `T* = app(p, wx)`.
   The motive's relation at the major gives the type relation at `T*`, so
   the reduct's relation moves up to `T*` (`incr`), down to `a` (`decr`),
   and back to the redex by head expansion (`expand_tm`).

As built: `dom_rec_end::rec_end_at` (with the walk driver `walk_run`), and
`rf_rel` calls it at the end, so the recursor's telescope induction has no
hypothesis left beyond `rec_hyps(sig, c)`. It asks:

- `iota_ok`, and the model's facts for every recursor (`sig_rec`);
- the recursor in scope (`rec_scope`) over an inductive without
  parameters or universe levels;
- its constructors neither recursors nor definitions, its rules'
  right-hand sides well formed (`rule_rhs_ok`);
- its fields closed and level-invariant at every level instance.

The induction also carries the two heads, derivably equal (`rf_heads`),
because the recursive calls need `ih ≡ ih2` for the application clause;
they are rebuilt from the heads and the argument pairs (`spine_build2`).
The pieces: `dom_rec_red` (the reduction), `dom_rec_minor` (the minor's
type after its arguments), `dom_rec_walk` (the walk), `dom_rec_end`.

#### The landing (2026-09-29, option (a))

The recursor stage is in the judgment and the model:

- **`iota_ok` is syntactic**: every recursor is in the fragment
  `dom_rec_end::rec_frag` (canonical, in scope, no parameters or levels,
  constructors that are not recursors, well-formed rules, closed
  level-invariant fields). The old meaning, no recursors at all, is
  `no_recs`, which the kernel side keeps (`kh_hyp` implies it).
- **The Iota rule fires at exact arity and exact levels**: `rec_arity` also
  asks that the major's constructor carry as many universe levels as it
  declares. The kernel does not check either condition; a typed major has
  both, and S6.6 derives them.
- **The model's hypothesis** is `sig_sr(sig) := iota_ok ∧ ¬no_recs ⟹
  sig_rec`, where `sig_rec` is each recursor's model facts
  (`rec_model`): semantic constants, a non-Prop inductive, ranked
  fields, and, typed in the **recursor-stripped signature**
  (`ti_strip::strip`), the recursor's type, the constructors' types and
  each rule's body in its binders (`rule_typed`). No subject reduction:
  the relation's constructor clause carries the typed conversion of each
  side to its constructor reduct (`con_top`), and the redex's conversion
  comes from the rules (`dom_rec_conv`). `sound`, `adeq` and
  `fundamental` take `sig_sr`; it is vacuous without recursors, so the
  kernel side is unaffected.
- **Recursors are interpreted** where `rec_hyps` (= `sig_rec` ∧ `rec_frag`)
  holds: `code_ok` is then `rf_fun`, and `rec_wired` is a theorem
  (`dom_iota::rec_wired_holds`).
- **Soundness is well-founded** by the rank of the recursors fired first:
  `sound` decreases on `(irank(sig, d), d)` (`ti_strip::irank`: two more
  than the highest rank of a recursor an Iota or RecEta node fires, 0
  without). In the Iota case, derivations of the stripped signature have
  no Iota node (`ti_strip::strip_valid`, `irank_free`), so soundness can
  use them. The telescope lemmas take a syntax signature
  `ss` and a soundness oracle `sound_oracle(ss, sig)` instead of calling
  `sound`. Ordinary callers pass `ss = sig` with the oracle from the
  theorem (`sound_all`). The Iota cores pass `ss = strip(sig)` with the
  oracle built in `sound`'s Iota case.
- **Iota soundness** (`dom_iota_sound::sound_iota`) is the two core
  directions plus congruence of membership under the extra arguments.
  **Iota adequacy** (`dom_adeq::adeq_iota`) is head expansion over one
  firing step (`ti_hred_rec::fire_hstep`). **The recursor constant's
  adequacy** (`dom_rec_adeq::rec_adeq_core`) is the telescope induction
  started at no arguments.

Open, for S6.6: discharging `sig_sr` for kernel signatures with recursors.
It asks only typings in the stripped signature and signature facts, which
the kernel's checks of the inductive and its recursor establish (the
recursor, its constructors and its rules are checked without recursors).
Subject reduction is no longer assumed by the model, and `ti_sr::sr` now
holds for signatures in the fragment (`iota_ok ∧ sig_sr`, not only
`no_recs`): its Iota step is the Iota rule over `iota_sr`, whose rule
typings `dom_rec_conv::sr_ok_of` derives from the model's facts, and a
major reducing inside a recursor application is congruence.

### Open: parameters of any type (analysis 2026-09-28)

What failed: the constructor clause related a field at its table code
and at the field's *declared* type, read off the value's own constructor
application `c P^x fs`. Raising the type's code to a larger one raises a
parameter's code `A` to `A2`, and the field then needs the type relation
of `P^x_j` at `A2`. The hypothesis only relates the *term's type*, and
that type is `I Q idx` with `Q` merely convertible to `P^x`. The
relation is closed under head expansion, not conversion, so the gap does
not close.

The route that avoids conversion is the paper's treatment of Σ:
components ride in the type relation, and values are related at the
type's components.

- **Type relation at `Ty(I)`.** Both types head-reduce to applications
  of `I` (the reduct chosen, as for Pi and sorts), with
  `tchain(t, t2)`, and each *type* parameter pair related at the code's
  parameter code: `rel_ty(Q_j, Q2_j, A_j)`. Parameters that are not
  types are left unconstrained, and fields may not be typed by them.
- **Tables at the code's parameters.** A table entry is the field type
  evaluated at the code's parameter codes (`ceval` with the parameter
  values, as first written). The entries are components of the code, so
  the relation's height measure still decreases through them.
- **Fields at the type's parameters.** The constructor clause relates
  field `i` at its table code and at the field type instantiated with
  the *relation's* type's parameters `Q` (the `I`-reduct of `t`), not
  the value's `P^x`. Raising `a` to `a2` then finds `rel_ty(Q_j, Q_j,
  A2_j)` in `rel_ty(t, t, a2)`, and a lemma lifts it to the field's
  simple type by induction (a parameter: given; a former applied to
  simple types: its canonical code's clause, the arguments by
  induction). Conversion to another type `s` (`conv_tm`) goes through
  `rel_ty(t, s, a)`, whose parameter clause relates `Q` and `Q'`.
- **Adequacy needs no injectivity.** At a constructor, the end of the
  telescope *is* `I P^x idx` syntactically, so `Q = P^x`. At the
  recursor, the major's type is `I params idx` for the recursor's own
  parameter arguments, so the fields arrive at `field[params]`, exactly
  the minor premise's domains. With the declared-type clause, this step
  would need `P^x ≡ params`, which is injectivity of `I` under
  conversion. So this route helps the recursor too.
- **Type formers.** `tf_rel` must now also show the parameter clause.
  The Pi clause hands it related arguments at a sort-typed domain, and
  at `U` the term relation is the type relation, which is the clause.

Scope of that route: fields typed by type parameters, or by formers
applied to such simple types. Function-typed fields and fields
depending on earlier fields stay out; they need Pi codes built from the
table, a separate step. Cost: roughly today's redesign again (relation
clauses, the PER, monotonicity, stability and head-expansion lemmas,
the lifting lemma, `tf_rel`, `cf_end`). It is independent of the
recursor stage, which can proceed on the closed fragment first.

### Parameters: the design (2026-09-29, started)

Goal: inductives with parameters whose fields are typed by the parameters
or by type formers applied to them (`List A`, `Prod A B`, `Option A`,
trees over `A`). Fields depending on earlier fields and function-typed
fields stay out; indices and Prop come after.

Stages, each landing through the gate:

- **P1, codes and typing.** A table is evaluated at the code's parameter
  codes: `ceval` takes an environment of parameter codes, and a parameter
  variable evaluates to its code. `tyc` (entries are inductive codes)
  goes: entries are any codes typed at `U`, as `has_type` already asks.
  The fragment's field condition (`simple_ty`) admits parameter variables
  and formers applied to them.
- **P2, the relation.** At an inductive's code `Nd(Ty(I), [A_1..A_np, T])`
  both types head-reduce to applications of `I` whose parameters `Q_j`,
  `Q2_j` are related at `A_j` (for type parameters), and `tchain(t, t2)`.
  The constructor clause relates field `i` with the full relation, at its
  table code and at the field type instantiated with the *relation's*
  type's parameters `Q` (not the value's). So the clause is staged, and
  it recurses through the relation at a smaller code: the relation's
  measure becomes `(n, ht(a), k)`.
  Refined (2026-09-29, after P1a): the type clause relates the *table's
  field types* rather than the parameters. At `a = Nd(Ty(I), ..)`,
  `rel_ty(t, t2, a)` asks `tchain(t, t2)`, both sides reducing to `I`
  applied to parameters `Q`, `Q2`, and for every table entry holding a
  code `c`, the field type at the parameters related at `c`:
  `rel_ty(F[Q], F[Q2], c)`. That needs no canonical codes (joins and
  codomains of codes are not canonical), and monotonicity in the code
  (`incr`) reads the field types' relation at the larger code straight
  off the type clause. Only adequacy at a type former has to produce it
  from the arguments, and that is the lifting lemma of P3 (by rank and the
  field type's size). The constructor clause moves into the relation's
  recursive group, takes the stage, the type and the code, relates a field
  at an entry's code by `rel_tm` at `F[Q]`, and a recursive field by the
  clause itself at the same code. Order: **P2a** moves the clause into
  the group (the table's codes are still inductive codes, `tyc`, so the
  type clause stays `tchain`); **P2b** gives the type clause its table
  part and the fields their types at `Q`; then P1b drops `tyc` and P1c
  widens the fragment.
  P2a landed (a047f94). **P2b, what it takes** (2026-09-29): with
  entries other than inductive codes, a field related at one code must be
  moved to another (constructor adequacy: from the telescope's domain code
  to the result's table entry; the recursor's end: from the major's entry
  to the minor's domain). No coherence between two arbitrary codes of one
  type is available, so the move goes through the canonical code
  `C = ceval(F, parameters' codes)`: up to `C` by `incr`, down by `decr`.
  That needs (i) `rel_ty(F[Q], F[Q2], C)`, the lifting lemma (by rank and
  the field type's size; a parameter variable takes its relation from the
  type clause, a former applied to arguments is the type former's clause
  one rank down), and (ii) both codes below `C`: members of a
  constructor's telescope interpretation are bounded by the canonical
  codes along it (`closed_bound` for telescopes, with the parameters'
  codes in `ceval`'s environment, P1a). The lifting lemma needs the field
  types typed; the signature gives that as a fact next to `rec_model`'s
  typed constructor types (`fields_typed`), and canonical tables exist only
  where it holds (`tabled`), so the definitions stay acyclic.
  **P2b landed (2026-09-29).** As designed, with these findings:
  - The transfer bound is "a table below the canonical one"
    (`dom_lift::tbl_canon`: every entry below the canonical entry), since
    codes differ in their parameter components, which the relation never
    reads. Below it the lifting lemma needs no typing at any stage
    (`canon_rel`), and `con_below`/`field_below` replace P2a's `con_xfer`.
  - Constructor adequacy's codes are bounded along the constructor's
    telescope (`dom_ctor_bound::tb`, the parameters' values threaded
    through `cf_inv`); the bound is closed downward from any set it bounds
    (`tb_le_set`), which gives codomains and the membership lemma
    (`tb_mem`) without joins' well-formedness.
  - Model changes, all gating: canonical tables need `canon_ok` (a
    monomorphic inductive, not a constructor or recursor, with typed and
    ranked field types); a constructor's code function is interpreted only
    where its inductive has them (as a recursor's under `rec_hyps`); a
    simple field type's head is not a recursor.
  - **Universe polymorphism is out of the fragment** until its own stage:
    the relation's two sides may sit at different but equivalent level
    instances, and relating a field type at two instances needs a
    conversion between level-equivalent terms that the judgment does not
    provide as a lemma yet.
  P1b landed (90cb8e2): typing no longer asks entries to be inductive
  codes.
  **P1c + P3, the design (2026-09-29).** Fields typed by parameters
  (`List α`, `Option α`, `Prod α β`, and formers applied to them) enter
  together with the lemmas that use them, because every closed-fragment
  shortcut (`fq_closed`, `cf`, `closed_bound`, `con_below`) gets its
  parameter case at once:
  - Fragment: a field type is a direct occurrence or a simple type over the
    parameters (`Var` of a parameter, or another former applied to simple
    types); `fields_typed` states it typed in the parameters' context. The
    recursor fragment keeps closed fields (`fields_plain`) until P4.
  - Canonical bound with parameters: `tbl_canon(j, pv, a)`, entries below
    `ceval(F, pv)`. Downward closed, monotone in `pv`.
  - Lifting: `rel_ty(F[Q], F[Q2], c)` for `c` below `ceval(F, pv)`, by rank
    and `F`'s size, given the parameters' relation at every typed code
    below theirs; the `Var` case is that hypothesis, a former applied to
    arguments recurses with the arguments' codes as the parameters'.
  - Transfer: a parameter's code is arbitrary (a Pi code, say), so a field
    typed by a parameter moves through that code by `incr`/`decr` at the
    big stage, where the parameter's value is typed and related (the
    constructor induction records parameters as it records fields); a
    former applied to arguments moves by `con_below`, which takes the
    transfer for its parameters as a hypothesis in place of the closed
    fragment.
  - Open for P4: with the table clause, the relation gives no
    injectivity for parameters a field does not mention; the recursor's
    Iota with parameters needs the rule instance typed, which the
    parameters' conversion gives where fields mention them.
  **P1c+P3 landed (2504c79, 2026-09-29)** for fields that are a type
  parameter itself (`pvar_field`); `List α`, `Option α`, `Prod α β` and
  trees over `α` are in the model's constructor adequacy and type-former
  relation. Findings: a type former's argument needs no domain syntax
  (at a sort's code it is a type; at a Pi's or an inductive's code it is a
  value, below which only bottom is typed at `U`), so `tf_rel` carries
  every argument's relation (`tf_prel`); nested closed types get their
  parameters' relation and transfer from their own arguments by rank and
  size (`closed_rel`, `closed_below`); a parameter-typed field moves
  through the parameter's code at the high stage (`par_xfer`).
  **Still open for parameters:** (P3b) formers applied to parameters as
  field types (`Option α` as a field), the nested case of the same
  lemmas with the parameter relation threaded through; (P4) the recursor
  with parameters, whose proofs assume `np == 0` (`rec_frag`, the walk,
  the Iota cores, Iota's subject reduction) and whose Iota instance needs
  the major's parameters convertible with the recursor's.
  **P4a landed (2026-09-29): injectivity of the inductive in its type
  parameters.** The relation's inductive clause gains `pconv`: the
  applications the two types reduce to have convertible type parameters
  (those whose declared domain is a sort). `tf_rel` carries the former's
  telescope instance (`tf_shape`), so at each type-parameter argument the
  derivable conversion at the sort domain is a `tchain` step; the lifting
  lemma asks it, `closed_rel` gives it reflexively. `ind_inj_chain` /
  `ind_inj_args` (dom_fund) read it back through the fundamental lemma at
  the canonical code at bottom arguments, a member of every full
  application. Only type parameters convert this way: a value parameter's
  code is a value, below which only bottom is a type, so the relation
  says nothing of it; P4b needs the recursor's value parameters handled
  another way, or kept out of the fragment.
  **P4a' (typed parameter equality).** A `tchain` may pass through
  different universes, and Iota's subject reduction needs the congruence
  `ctor ps fs ≡ ctor ps' fs`, i.e. each type parameter equal *at its
  declared sort*. `pconv` therefore records `peq`: the chain and, when
  the inductive has no level parameters, `derivable(eq(g, a_q, a2_q,
  pdoms[q]))`. `tf_rel` gets it from the argument's conversion at the
  domain; the reflexive case in `closed_rel` cannot invert the typing of
  the closed type (spine inversion goes through uniqueness, which goes
  through Pi injectivity, i.e. through the fundamental lemma: a cycle), so
  `styped` gains `sdoms_typed`, a static signature fact: in a closed field
  type, a canonical former's type parameters are typed at their declared
  sorts in the stripped signature. The kernel port certifies it with
  `former_args_typed` (spine inversion, outside the cycle).
  **P4b-1: Iota's subject reduction with type parameters.** `iota_sr`
  holds for recursors whose parameters are all type parameters (`sr_ok`
  asks `pdoms[q] is Sort`, the inductive monomorphic and semantic). The
  major `c ps' fs` is typed at `I ps'` (`sr_major`) and, from the redex,
  at `I ps`; `ind_inj_args` gives `ps ≡ ps'` at their sorts
  (`sr_inj_fields`), the fields retype at `F[ps]` (`sr_field_conv`: a
  direct field by the chain `I ps' ~ I ps`, a parameter field by the
  parameter's equality, a closed one unchanged), the rule instance is
  typed at `motive (c ps fs)` (`sr_rule`), and `spine_cong` plus the
  motive's application give `motive (c ps fs) ≡ motive (c ps' fs)`
  (`sr_result`). The model's recursor stack still asks `np == 0`
  (`rec_frag`), so `sr_ok_of` only produces the `np == 0` case for now.
  **P4b-2 plan: the model's recursor stack with type parameters.** Survey
  (2026-09-29): `recval`/`rf_fun` already take parameter inputs and pass
  them to recursive calls unread, so the code function needs no change.
  Every `np == 0` traces to `rec_frag` (and `fields_plain`, which forces
  it on its own: a direct field `I vars(k, np)` is open). Five groups:
  - (C) index arithmetic with the motive at 0, minor `j` at `1 + j`, the
    major at `nmin + 1` (dom_rec_minor, dom_rec_red, dom_rec_conv,
    dom_rec_end `Rc`, `sound_iota`): shift by `np`, mechanical, ~22 fns.
  - (E) field types closed (`fields_plain`, `lift_closed`/`vsub_closed`):
    fields become `I vars(k, np)`, a parameter `Var`, or closed; instantiate
    at the parameter terms, ~12 fns.
  - (B) parameter codes: tables and field codes at `pv` = the parameter
    inputs' codes instead of `[]`/`bots(np)` (`fbnd`, `con_rel_arg`,
    `field_dom_bnd`, `rec_ctx`, `motive_top`, `major_bnd` — whose
    `tbl_canon_np0` is false for `np > 0` —, `typed_at_canon`, the
    constructor chain `cf_*`, the right-to-left Iota `r2l_*`), ~20 fns.
  - (D) the major `c ps' fs` against the recursor's `ps`: Iota drops `ps'`,
    so the typing (`rule_beta`, `rec_conv_side`) and the relation need
    `ps' ≡ ps` at their sorts. Not from `ind_inj_args`: it goes through the
    fundamental lemma, i.e. through adequacy (a cycle). From the relation
    instead: `con_tm` records that a constructor reduct's type parameters
    are `peq` to its type's reduct's (`pconv`'s counterpart for terms),
    established where constructor adequacy builds it. ~12 fns.
  - (A) the gate: `rec_frag` asks `pdoms` all sorts instead of `np == 0`,
    `fields_plain` becomes the three-kind field condition; last.
  Order: C and E as `np`-general restatements while the gate still holds
  (each a checkpoint), then D's relation clause, then B, then A.
  **P4b-2a (900b816)**: C/E for dom_rec_minor and dom_rec_red.
  **P4b-2b: D's relation clause.** `con_tm` carries `cpar` on both sides:
  the constructor reduct's type-parameter arguments are `peq` to those of
  the type's stuck reduct (keyed on the code's inductive). Constructor
  adequacy gets it from the relation itself (`cf_cpar`: the result type is
  the inductive at the arguments, and `rel_ty(t, t)`/`rel_ty(t, t2)` carry
  `pconv`); moving the clause to another type needs `pconv` between the
  two (`cpar_conv`, a new premise of `con_conv` and `con_below`, from
  `ty_nd`, `closed_rel`'s `rel_ty(r, r)`, or `direct_pconv` for a
  recursive field, whose type has the result's parameters).
  **P4b-2c: the redex conversion with parameters.** `rule_bty` (the rule
  body's type in the model hypothesis) states the constructor at the
  parameters and the fields (unchanged at `np == 0`; `iota_sr` uses it
  directly). `bty_inst`, `rule_beta` (field binders via `field_ctx` +
  `field_vsub`) and `rec_conv_side` hold for any `np`; the latter takes
  the constructor's own parameter arguments with `heads[q] ≡ pargs[q]` at
  their sorts — what `cpar` will supply — and converts the rule instance's
  type through `iota_sr::sr_result`. `major_dom`/`motive_form` state the
  inductive at the parameters.
  **P4b-2d: the end's context with parameters.** `Rc` carries the major
  constructor's own parameter arguments (`pargs`, `pargs2`); `pre`, the
  major's type `I xs<np` (`ind`, `ind2`) and the fields' types at the
  recursor's parameters (`fty`) are stated at `np`. `rec_ctx_intro` gets
  `xs[q] ≡ pargs[q]` from `cpar` (`major_pars`) and each field from the
  relation moved to the recursor's parameters (`rc_field_intro`, through
  `iota_sr::field_conv`, which builds `I ps ≡ I ps'` by congruence, so the
  model never calls injectivity). The fragment gains `pdoms_lv` (the
  parameters' domains are level-invariant). The walk down the minor
  (`walk_of`, `walk_shape`, `ih_code`, `motive_top`, `sides_ty`, ...)
  is done in P4b-2e; a parameter-typed field is still closed off by
  `rec_frag` in `rc_field_intro`.
  **P4b-2e: the walk down the minor with parameters.** `walk_of` and its
  lemmas place the minor at `np + 1 + j` and the motive at `np`;
  `walk_shape` types the fields at the recursor's parameters on each side,
  `walk_end_ty` ends at the motive at the constructor at the recursor's
  parameters (`cxr`). The sites still reading `np == 0` from `rec_frag`
  are explicit: `rc_field_intro` (parameter-typed fields), `motive_top`
  (the motive's domain in the empty environment; also relates `cx`
  where the walk ends at `cxr`), `walk_end_code` (the constructor's value
  over variables without parameters). They are group B's.
  **P4b-2f: the major's table at the parameters' codes.** `major_bnd`
  states the major's domain code below the canonical table at the
  parameters' values (`xs<np`), through `major_code`'s parameter codes
  (members of the parameter variables, so below their values) and the new
  `tbl_canon_mono`; `tbl_canon_np0` is gone. `rec_ctx` keeps the table at
  `Rc::pv` (the parameters' values), `fbnd`/`con_rel_arg` take `pv` (the
  recursive case passes it to `con_below` with its `ptr`/`pconv`
  premises), `field_dom_bnd` bounds the minor's lifted field binder at
  `pv`, and `msds_at` states the binder as the lifted field. Remaining
  explicit `np == 0` sites: `rc_field_intro` and `field_dom_bnd`
  (parameter-typed fields), `ih_flds`/`field_arg` (the parameters'
  transfer `ptr`), `motive_top`, `walk_end_code`.
  **P4b-2g: the parameters' transfer and the motive with parameters.**
  `rc_ptr` gives `ptr` and `pconv` for the major's type from the telescope
  invariant (each parameter is related at its value's code, a sort's, so
  to itself at its value, and `par_xfer` moves it), used by `ih_flds`,
  `field_arg` and `motive_top`. `motive_top` reads the motive's domain in
  the parameters' environment (bounded at `pv` by `ind_bound` +
  `tbl_canon_mono`), types it with `iota_sr::motive_at`, and relates the
  walk's end `cxr` to the major (`cxr_con`: the constructor clause for the
  constructor at the recursor's parameters, from the major's own, with
  `field_ty_chain` between the two field-type instances; `cxr_typed`).
  Left at `np == 0`: parameter-typed fields (`rc_field_intro`,
  `field_dom_bnd`) and `walk_end_code` — done in P4b-2h.
  **P4b-2h: the end of the recursor's telescope holds with type
  parameters.** `ctor_mem_le` takes the constructor over parameter
  variables then field variables (its code function skips the
  parameters), so `walk_end_code` is general. Parameter-typed fields get
  their own case in `rc_field` (related at their type, the parameter, at a
  code below the parameter's value), read from the constructor clause's
  entry in `rc_field_intro`, bounded by the parameter's value in
  `field_dom_bnd`, and moved by `par_xfer` in `field_arg_par` (with
  `rc_par`, factored out of `rc_ptr`). `field_arg` splits into
  `field_arg_ctx` (the stated context `fa_ctx`) and the two branches.
  dom_rec_end no longer reads `np == 0`; what still does: `rec_frag`
  itself (and `fields_plain`, which needs only its level-invariance half
  now), and dom_iota's constructor/right-to-left Iota chains.
  **P4b-2i (adf1ec3)**: `rule_chain` handles parameter-typed fields.
  **Finding (2026-10-01): Iota's soundness needs the parameters' equality
  as premises.** Right-to-left Iota rebuilds the major `c ps' fs` as a
  member: the constructor's step approximation must run at the
  recursor's parameter values (a parameter-typed field's value is typed
  only at its parameter's value; at bottom only bottom fits), so the
  constructor application's own parameters `ps'` need members above them,
  i.e. `ps ≡ ps'`. Soundness cannot get that by injectivity (soundness →
  injectivity → fundamental lemma → soundness), and the Iota node's
  premises (both sides typed) give no smaller derivation of it.
  **P4b-2j (user's choice): `Rule::Iota` takes the parameter premises.**
  `step_ok`'s Iota case asks `prems(ps, [m ≡ m : t, n ≡ n : t] ++
  iota_pjs(sig, g, m))`, `iota_pjs` (opaque) being `eq(g, ps_q, ps'_q,
  pdoms[q])` per parameter. Producers supply them: `iota_sr` (from
  `sr_inj_fields`), `ti_sr::sr_iota`, `dom_rec_conv::rec_conv_side` (its
  `heads[q] ≡ pargs[q]` hypothesis, from `cpar`). The derivation-walking
  lemmas that rebuild or inspect Iota nodes (renaming, substitution,
  signature extension, local swap/close) rename or substitute the
  premises (`pjs_psub`, `pjs_ext`, `pjs_ls`, `pjs_swap`, `pjs_close`).
  **P4b-2k: right-to-left Iota at the parameters' values.** The
  constructor chain (`cf_fields_ok`, `cf_ds`, `cf_chain`, `cf_val_typed`,
  `cf_step`) runs at the parameter values `pv` (typed along the declared
  domains, `dps`) instead of bottom: recursive fields at the canonical
  code at `pv`, parameter-typed fields at a code below their parameter's
  value (`ispvar`/`pvq`; the table's entry is that value, `cf_var`),
  closed ones as before. `ind_pv_mem`/`typed_at_pv` replace the
  bottom-parameter membership lemmas (by `tf_step` at the parameter chain
  and `canon_mono`). The right-to-left lemmas take `pv` from the rule's
  chain (`r2l_pv`, `r2l_pvar_field`), and `r2l_major` gives the
  constructor's own parameter arguments those values as members — from
  the Iota node's parameter premises, whose soundness `dom_sound` passes
  to `sound_iota`. `r2l_ok` asks type parameters and `pdoms_lv` instead
  of `np == 0`.
  **P4b-3 (134fbcb): recursors with type parameters enter the fragment.**
  `rec_frag` asks the parameters' declared domains to be sorts instead of
  `np == 0`, and the fields level-invariant (`fields_lv`) instead of
  closed. Every recursor whose parameters are types, and whose fields are
  direct occurrences, closed simple types or a parameter itself, is now in
  the model and its Iota sound.
  **P3b, the plan (2026-10-05): formers applied to parameters as field
  types** (`MyOpt α`, `Pair α Nat`, nested). `ceval` already reads
  parameter variables through `fpe`, so the codes need nothing; the
  predicates and the lemmas over them do.
  - Kind: `psimple(sig, ind, pdoms, np, k, e)` — a parameter's variable
    (`pvar_field`) or another former fully applied to `psimple`
    arguments; `pranked` its rank condition (variables allowed).
    `plow(e, k)` drops the `k` earlier fields' slots (`vsub(e, a + c) ==
    vsub(plow(e, k), a)` for `c.len() == k`).
  - Typing hypothesis: `fields_typed` asks a non-closed `psimple` field's
    `plow` typed at a sort in the parameters' context (`pctx`, the
    declared domains); instances follow by `d_sub` at a pair of parameter
    substitutions (`spair`), the type parameters of nested formers by
    `former_args_typed` in that context, and `F[ps] ≡ F[ps']` by the same
    substitution lemma with the parameters' `peq`.
  - Lifting (`ps_rel`), transfer (`ps_below`), member bound
    (`ps_bound`): by rank and size as `closed_rel`/`closed_below`/
    `closed_bound`, the variable case being the outer parameters'
    `prel`/`ptr`/environment bound, which the callers already hold
    (`canon_rel`, `con_below`, `tb_mem`).
  - Recursor side: the field kind gets its case in `rc_field`, the
    right-to-left chain (`cf_*`, `r2l_*`), `field_vsub`, `iota_sr`'s field
    conversion, the minor's field binders.
  - Gate: the fragment (`rec_canon`) admits `psimple` last, once every
    case is in.
  **P3b-1 (04adcb7)**: the kind, `plow`, `ptyped`, `ps_inst`, and the
  lifting/transfer lemmas `ps_rel`/`ps_below`.
  **P3b-2: the model admits formers over the parameters.** `rec_canon`'s
  field condition is `field_kind` (opaque: a direct occurrence or
  `psimple`); `fields_typed` asks `pfield_ok` of the fields that are
  neither closed nor a parameter. Their cases: `pfield_rel` in the lifting
  lemma, `pfield_below` in `con_below`, `cf_end_pfield` in constructor
  adequacy, `ps_bound` in the telescope bound, `ps_ceval_typed` in
  `canon_typed`. `con_below` now takes the target's parameter relation
  (`prel` at `t2`); its callers have it (`par_ok` at the high stage,
  `rc_ptr`, `closed_rel`/`ps_rel` on the arguments). The constructor
  induction records each type parameter's typing (`pty_ok` in `pr_ok`),
  which the substitution lemma needs.
  **P3b-3: the recursor with formers over the parameters.** No extra
  fragment clause: the typing cannot sit in `rec_frag` (typing →
  `iota_ok` → `rec_frag` is a definitional cycle), so the recursor-side
  lemmas that need it take `canon_ok` (`sr_ok`, `field_conv` &co, from
  `rec_canon_ok`) or `fields_typed` (`cf_fields_ok`, `r2l_ok`, with
  `scope_canon` tying `canon_shape` to `rshape`). Syntactic cases by
  `plow_vsub`/`plift_vsub`; Iota's subject reduction by `ps_field_eq`
  (substitution); the right-to-left chain by `ps_mem_transfer`
  (membership through renaming, the environments agreeing on the
  parameters' slots), `cf_fields_ok`'s third kind and `cf_ps_typed`; the
  recursor's end by a third walk path, `pfa_at` (`rc_field`, `fa_ctx`,
  `field_dom_ps`, `field_arg_ps` by `ps_below`).
  **Parameters: done for type parameters and monomorphic formers over
  them.** Open: value parameters; universe polymorphism (`Option.{u}`,
  `List.{u}` — most real formers).
  **Universe polymorphism, the design (2026-10-05, not started).** 42
  `lps.len() == 0` sites over 12 modules. What exists: `ceval`/`lsub`
  already evaluate codes at a level instance; the judgment's constant
  rules relate level-equivalent instances (`levs_eq` in
  `ConstAx`/`ConstDef`); `ti_level::d_ls` instantiates a derivation at one
  instance. Steps:
  - U1, metatheory: `d_ls2`, the pair form of `d_ls` — a derivation in
    the level parameters gives `e[vs] ≡ e[vs2] : T[vs]` for pointwise
    level-equivalent `vs`, `vs2` (by the constant rules' `levs_eq` and
    `Univ`), the level analogue of `d_sub` over an `spair`.
  - U2, codes: `canon_ok` and `tabled` drop `lps == 0`; tables at an
    instance evaluate fields at it (`centries` already passes `ls`);
    `canon_code` must be the same at level-equivalent instances (its key
    carries `is_prop_at`, which can differ: `Sort u` is Prop at `u = 0`,
    so restrict to inductives whose sort is never Prop — `Sort (u+1)`,
    `Type u` — until the Prop stage).
  - U3, the relation: `peq` asks the derivable equation only without
    level parameters; with them it gets the instance's domain
    (`pdoms[q][ls]`), and `pconv` the instances' level equivalence; the
    lifting/transfer lemmas take `ps_inst` composed with `d_ls2`.
  - U4, the recursor: `rec_frag` drops `ind lps empty`; the motive's
    extra universe and `elim_level` instance the rule bodies at
    `lv = motive :: ind's`; `fields_lv` becomes "fields at the ind's part
    of `lv`".
  The first concrete obstacle is U2's code identity across equivalent
  instances, which the relation (two sides at `ls`, `ls2`) needs.
  **U1 landed (ti_ls2):** `d_ls2` over `lpair` (the level analogue of
  `spair`: variables typed at their types' first instance, those types
  converting to the second). The computation rules (Beta, Zeta, Iota,
  Eta, Irr, Delta) need no rebuilding: each has a premise `n ≡ n : a`, so
  the node's first instance (`ls_move`: `d_ls`, then into `dl` by `d_sub`
  at the identity pair) chains with that premise's pair. Congruences
  mirror `d_sub`; the constant rules are rebuilt at the two instances
  (`lls_pair`). `ls_pair_nil` is the closed-term corollary.
  **U2a: codes are level-invariant.** `canon_lveq`/`ceval_lveq` (with
  `cblocks`/`centries`/`cargs`): codes at level-equivalent instances are
  equal, the Prop flag being semantic (`prop_lveq`). `canon_ok` and
  `rec_model` ask `never_prop` (the sort is above zero at every
  valuation; `never_prop_not` gives "not Prop" at every instance) — the
  restriction universe-polymorphic tables will keep until the Prop stage.
  Still `lps == 0` in `canon_ok`: the flip (2026-10-05 trial) breaks
  23 functions, the model lemmas that read a constructor's field types
  without their level instance (`ctor_field_ty`, `pvar_ty`, `direct_ty`,
  `ctor_result`, `fq_closed`, `field_facts`, `tb_mem`, …); U3 generalizes
  them to the instance (`subst_expr_levels(F, lps, ls)`, as `fq` reads).
  **U3a: level-blind codes.** A code reads its instance only through
  nested formers' Prop flags and table length checks, so when every
  former in a field is never-Prop or monomorphic (`former_blind`,
  `blind_ty`, `fields_blind`, now in `canon_ok`, `rec_model`, `r2l_ok`,
  `cf_fields_ok`), codes at ANY two instances of the same length are
  equal (`canon_blind`, `ceval_blind` & co). So `cf`, `tbl_canon` and
  `entry_canon` keep their instance-free signatures; U3b only carries
  the instance on the term side (`subst_expr_levels(F, lps, ls)` where
  `sl_none` gave `F`). Split for resource limits: `ftds_vsub` out of
  `sr_rule_arg`, `r2l_fit` out of `iota_core_r2l`.
  **U3b-0 (groundwork):** `fq` reads the reduct's instance padded to the
  declared length (`iinst`/`lpad`: the identity on typed terms, and
  `fields_typed` always applies to it, so no caller needs a length fact);
  `sl_kinds` (level substitution keeps the field kinds, `plow` commutes),
  `blind_sl`, `ceval_sl` (a blind type's code ignores its levels).
  **Finding (2026-10-05): the relation must carry the instances' level
  equivalence.** With `lps == 0` dropped, `field_rel` must relate a
  closed field at the two sides' instances, `F[ls]` and `F[ls2]`. Nothing
  in the relation says `ls ≡ ls2`: that would come from injectivity of
  the inductive in its levels, which the model cannot use (the same
  cycle as for parameters, P4a). So U3b adds to `pconv` the clause
  `levs_eq(iinst(ir t), iinst(ir t2))`; its producers have it (the same
  term on both sides in `closed_rel`/`ps_rel`; `ConstAx`'s `levs_eq` in
  the type-former adequacy; the monomorphic recursor), and `field_rel`
  then lifts `F[ls] ≡ F[ls2]` by `ls_pair_nil` (U1). Fields over the
  parameters (`pfield_ok`) stay monomorphic until U3c: their typing is in
  the parameters' context, whose sorts carry levels.
  **U3b-1 (2ec89be):** `pconv` (and the type-former adequacy's
  `tf_pconv`) carry `levs_eq` of the two sides' instances; the
  adequacy's base case has it from `ConstAx`, every other producer from
  relating a term to itself.
  **U3b-2a: closed fields at two instances.** `closed_rel2` (the lifting
  lemma's closed case at level-equivalent instances `F[ls1]`, `F[ls2]`),
  `closed_below2` (its transfer), sharing `closed_pconv`; the two
  instances convert by `closed_conv` (U1's `ls_pair_nil` in the empty
  context, weakened), nested formers' instances are level-equivalent by
  `lls_pair`, and a monomorphic nested former's parameter sorts are fixed
  by the instance (`elp_none_id`). The model's new signature hypothesis
  `sig_lps` (`sig_lp_ok` at every instance, as `export_sound` proves for
  kernel signatures) feeds `d_ls2`. Helpers in `dom_levels`; `sle_params`
  in `ti_ls2`.
  **U3b-2b: universe-polymorphic inductives have tables.** `canon_ok`
  no longer asks `lps == 0`; it asks `never_prop`, `fields_blind`,
  `sig_lps` and `lps_distinct` (so a constructor's result is at its own
  instance, `sl_plevels_id`). The model reads constructor types at their
  instance (`ctor_inst`; `ctor_result`/`direct_ty` report the inductive
  at the substituted levels; `ctor_field_ty` gives `F[ls]`), the
  constructor induction carries the instance (`cf_bnd`, lengths in
  `cf_inv` from `ConstAx`'s typing, `cf_bnd_blind` across sides), the
  member bounds take it (`ind_bound`, `var_ind_bound`, `tb_mem`;
  `closed_bound` asks `blind_ty` instead of `lps == 0`), and closed fields
  move by `closed_rel2`/`closed_below2`. Formers over the parameters
  (`pfield_ok`, `pty_ok`) stay monomorphic (U3c); recursors stay
  monomorphic (`rec_frag`, U4).
  **U4 worklist (2026-10-05 trial: `rec_frag` without `ind lps == 0`):**
  21 functions — the recursor's end (`major_dom`, `major_side`,
  `major_par_at`, `rc_field_intro`, `rc_fty_rec`, `rc_args2_typed`,
  `cxr_field`, `ctor_arg_ty`, `field_dom_bnd`, `walk_shape`,
  `walk_end_ty`, `walk_end_code`, `motive_form`, `motive_top`,
  `sides_ty`, `rec_red_left/right`), `field_ctx`/`rec_conv_side`
  (dom_rec_conv), `iota_rhs_mem` (dom_iota), `pjs_ls` (ti_level). The
  pattern is U3b's: the inductive appears in the recursor's telescope at
  the recursor's instance restricted to the inductive's parameters
  (`lv` minus the motive's universe), and its codes are blind.
  **U4a: Iota's parameter premises at the recursor's instance.**
  `iota_pjs` types each premise at `subst_expr_levels(pdoms[q], uparams,
  lv)`, as the recursor's own telescope reads its parameter domains at
  `lv`; for the current (level-invariant) fragment that is `pdoms[q]`
  (`iota_pdom_id`, from `rec_frag`'s `pdoms_lv`; `sr_ok` carries
  `pdoms_lv` too), so the rule's producers and rebuild lemmas need only
  that identity.
  **U4b-0 (groundwork):** `rinst(sig, rid, lv)` (the inductive's
  instance inside the recursor at `lv`) and `rinst_id` (a term over the
  inductive's level parameters at `lv` over `uparams` is the term at
  `rinst` over `lps`, by `sle_params` + `expr_compose`); `rec_scope`
  carries `rec_elp` (the inductive's and constructors' types mention
  only its level parameters; `rec_elp_parts`, `rec_elp_pdoms`);
  `rec_arity` checks the recursor's own instance length (level
  composition needs it); `iota_pdom_id` gives the premise type as the
  domain at `rinst`, and the rebuild lemmas no longer assume the
  identity (`pjs_ls` composes by `expr_compose`, `elp_mono`,
  `rec_lps_sub`). `step_swap` split (`step_swap_bind`).
  **U4b plan (from the 2026-10-05 flip, 32 functions):** Iota's subject
  reduction converts the major's constructor head from its own instance
  to `rinst` (`ConstAx` at the instances `ind_inj_args` shows
  level-equivalent), then runs at one instance `us` for the inductive and
  its constructors; the iota_sr / dom_rec_end / dom_iota lemmas take `us`
  where they now write `Const(ind, [])`.
  **U4b-1 (3aede90):** `rule_bty` and `motive_at` at `rinst`.
  **U4b-2: the parameters' typed equality at every instance.** `peq`
  takes the instance and states `x ≡ y : ptype(ind, ls, q)` (the declared
  sort at `ls`) for every inductive, not only monomorphic ones: Iota's
  premises need it for a polymorphic inductive, and injectivity
  (`ind_inj_args`, which now also reports the instances' level
  equivalence) reads it back. `pconv` and `cpar` use the left side's
  `iinst`; `peq_lv` moves a `peq` between level-equivalent instances
  (`pconv_symm`, `pconv_trans`, `cpar_conv`); `tf_pconv` states it at the
  former's own instance; `sdoms_typed`/`pdoms_typed` (the field typing
  hypotheses) give nested formers' parameters at their instanced sorts,
  `former_args_typed` likewise for every former; `closed_pconv` composes
  the instances (`lpad_sl`, `pdoms_elp`).
  **U4b-3: Iota's subject reduction at every instance.** `iota_sr` no
  longer assumes a monomorphic inductive. The major's constructor is typed
  at its own instance (`sr_major`), injectivity (`ind_inj_args`) shows
  that instance equivalent to the recursor's `rinst`, and `sr_switch`
  moves the constructor there (`ConstAx` between the two instances, its
  premise from `closed_conv` on the constructor's closed type; then
  `retype_spine`). Everything after runs at `rinst`: the constructor's
  telescope `ctel(us)` with the parameters at `ptype` and the fields at
  `cfu(us)` (`ctor_at`), the field lemmas (`ind_cong`, `field_conv`,
  `field_ty_chain`) taking the instance, and `sr_result` closing the chain
  at the major with the two-headed `spine_cong2`. Fields over the
  parameters only occur in monomorphic inductives (`ps_field_mono`).
  `sr_ok` drops `lps == 0`, `pdoms_lv` and the fields' level invariance,
  asking instead for the inductive semantic at `rinst` and the
  constructor's type closed. The monomorphic callers in `dom_rec_end` and
  `dom_rec_conv` bridge with `mono_at`.
  **U4b-4: the recursor's end at every instance; `rec_frag` drops
  `lps == 0`.** The relation's recursor case (`dom_rec_end`'s `Rc`) works
  at the recursors' instances `ri`/`ri2` of the inductive and at the
  majors' constructors' own instances `cl`/`cl2` (`rc_lv`: all four
  equivalent). Inside the fundamental lemma injectivity is not available
  (it is a corollary of it), so the levels come from the relation: the
  constructor clause `cpar` now also states that a constructor head with
  as many levels as the inductive is level-equivalent to its type's
  instance (`cf_cpar` establishes it, `cpar_conv` carries it), and the
  type clause's `pconv` relates `ri` and `ri2`. The constructor moves
  between instances by `ctor_lv` (`ConstAx` on its closed type, split out
  of `sr_switch`), a field's type by `cfu_conv` (`ind_lv` for a recursive
  field, `closed_conv` for a closed one), a parameter equation by
  `ptype_lv`, a field's bound by `fbnd_at` (codes ignore levels:
  `sl_kinds`, `ceval_sl`, `fields_typed` at every instance).
  `rec_conv_side` takes the major's instance `cl` with `levs_eq(rinst, cl)`
  as a premise; `rec_red`, `minor_dom`/`minor_end`, `msds_at`,
  `field_dom_bnd`, `ctor_mem_le`, `motive_form` and `rule_chain` take or
  produce the instance. `rec_model` now gives the inductive semantic at
  every instance and its type closed. Still assumed in `rec_frag`:
  `pdoms_lv` and `fields_lv` (used by the model's right-in-left Iota
  direction, `r2l_ok`, next).
  **U4b-5a: Iota's level condition.** The model's right-in-left Iota
  direction rebuilds the major at its constructor's own instance and needs
  that instance equivalent to the recursor's instance of the inductive
  (a parameter's sort can be Prop at one and not at the other). Like the
  parameter premises, the model cannot recover this by injectivity, so
  rule `Iota` asks for it (`iota_lv`). Subject reduction supplies it
  (`iota_sr`, by injectivity), the relation's Iota conversion from its
  premise (`rec_conv_side`); renaming, substitution, local swap/close and
  level instantiation and signature extension carry it (`pjs_*`,
  `rinst_ls`); it is opaque, so rules other than `Iota` do not unfold it.
  **U4b-5b: the model's Iota at every instance; `rec_frag` drops
  `pdoms_lv` and `fields_lv`.** The constructor step (`cf_fields_ok`,
  `cf_chain`, `cf_val_typed`, `cf_step`, `ind_pv_mem`, `typed_at_pv`,
  `ind_ty_plain`) works at the constructor's instance `cl`: the parameters
  typed along their sorts there (`pdoms_at`), the fields at `cfu(cl)`, the
  recursive ones at the canonical code at `cl`. The right-in-left
  direction reads the rule's binders at the recursor's instance `us` and
  moves to the major's `clv` (equivalent by `iota_lv`): a parameter's sort
  has the same members at equivalent levels (`sort_mem_lv`,
  `chain_pdoms_lv`), a closed field's two instances convert in the
  stripped signature so the soundness oracle gives them the same members
  (`r2l_closed_field`), the canonical code ignores the instance
  (`canon_blind`). `rec_model` makes the constructors semantic at every
  instance. With this the recursor fragment no longer restricts
  universes: universe-polymorphic inductives whose fields are recursive,
  closed or parameters (`List.{u}`, `Prod.{u,v}`, `Option.{u}`) are in it;
  fields over the parameters stay monomorphic (`pfield_ok`, U3c).
  **U3c: fields over the parameters at every instance.** `pfield_ok` no
  longer asks for a monomorphic inductive. Its typing (in the raw
  parameters' context) gives the field's typing at any two equivalent
  instances: `lpair_sorts` sets up `d_ls2` over the parameters' sorts,
  `ps_pair` instantiates and substitutes (`ps_inst2`). The relation's
  lifting lemmas for such fields (`ps_rel`, `ps_below`, `ps_pconv`) take
  two instances and relate the field at each type's own instance
  (`pfield_rel`/`pfield_below` read them off `iinst`); constructor
  adequacy states the parameters' typing at the constructor's instance
  (`pty_ok`, `pr_ok`, moved between the two sides' equivalent instances by
  `pr_ok_lv`; `cf_inv` records `levs_eq(ls, ls2)`). Codes ignore the
  levels (`ps_bound` asks `blind_ty`, `ceval_sl`), so the semantic bounds
  read the instanced field; the model's right-in-left Iota moves the
  field's members between the recursor's and the constructor's instance
  through its lowering (`ps_mem_plow`) and the soundness oracle on the
  `d_ls2` derivation in the parameters' context (`ps_mem_lv`, fitting by
  `chain_fits`). With this every field kind is universe-polymorphic:
  e.g. `Array.{u}`'s `List α` field is in the fragment.
- **P3, the lemmas.** PER, monotonicity, stability, head expansion,
  conversion, and the lifting lemma (a parameter related at `A` lifts to a
  field's simple type), then `tf_rel`, `cf_end`, constructor adequacy.
- **P4, the recursor with parameters.** The recursor stage generalized
  from `np == 0`: parameters in the telescope induction, the walk, the IH
  instances, the Iota cores. Subject reduction for Iota with parameters
  needs `I P ≡ I P'` to give `P ≡ P'`, which the parametric relation's
  parameter clause provides through the fundamental theorem.

### Prop stage plan (2026-10-05)

Order changed (agreed 2026-10-05): Prop before indices in Type. Codes
carry no indices (see "Found 2026-09-28"), so in the model a value of
`I ps idx` belongs to `I ps idx'` for every `idx'`, and the recursor's
value at a constructor is typed at the motive at the constructor's own
index terms, not at the major's: indexed families eliminating into Type
need a redesign of the code layer. Indexed families in Lean's core
library are almost all propositions (`Eq`, `HEq`, `Nat.le`, `Acc`), and
eliminating a proposition into Prop is semantically trivial: proofs
denote bottom (`prop_denot_bot`), so both sides of such an Iota denote
bottom whatever the indices.

Facts the plan rests on:

- The model already interprets a Prop inductive's constructors and
  recursor as bottom: `code_ok` interprets constructors only under
  `canon_ok` (which asks `never_prop`) and recursors only under
  `rec_hyps`. Their types are propositions (impredicativity), so bottom
  is their whole denotation.
- `has_canon` is syntactic (`rec_canon`, which already allows indices
  and any sort), so the relation's parameter clause (`pconv`) and
  injectivity (`ind_inj_args`) already cover Prop inductives' parameters.
- A Prop-only recursor is one with no extra motive universe
  (`uparams == lps`, `elim_level == Zero`).
- Proof irrelevance is sound and adequate from a premise `t : Sort l`
  with `is_zero(l)` (`sound_irr`, `adeq_irr`).

Steps:

- **P1a: Iota carries its type's sort (done).** Rule `Iota(l)` gains the
  premise `t : Sort(l)` (third, before the parameter premises) and the
  side condition `iota_prop(sig, m) ==> is_zero(l)` (`iota_prop`, opaque:
  the redex's recursor has `elim_level == Zero`). The level is the rule's
  own, not the recursor's elimination level at its instance: with extra
  arguments after the major, `t` is the motive's result applied further,
  not the motive at the major. Producers: the relation's Iota conversion
  (`t` the motive at the major, sorted by `motive_at`) and subject
  reduction (`l` from validity, `d_ty`); both have `iota_prop` false
  because `rec_frag` now asks `rec_large` (opaque: a motive universe
  exists) until P1b admits Prop-only recursors. Renaming, substitution,
  local swap/close, level instantiation (`ls_is_zero`), signature
  extension carry the premise and `iota_prop`. (`rec_large` left
  `rec_frag` again in P1b.)
- **P1b: Prop-only recursors of non-indexed Prop inductives (done).**
  `rec_frag` no longer asks `rec_large`; `rec_model` asks `never_prop`
  only of a recursor eliminating into any universe, and `rec_hyps` (what
  interprets a recursor, `code_ok`) asks `rec_large`, so a Prop-only
  recursor denotes bottom. Soundness and adequacy of its Iota are proof
  irrelevance on the P1a premise (`sound_irr`; `adeq_irr` also takes an
  Iota node with `iota_prop`, its type premise at index 2); `sound_iota`
  asks `!iota_prop`. Large eliminators of Prop inductives stay out
  (`rec_model`'s `never_prop`), see "Open: large elimination out of Prop".
- **P1c: subject reduction for them (done, before P1b).** `iota_sr`'s
  lemmas ask `canon_sr`, the tables' syntactic half without `never_prop`.
  Subject reduction and the relation build the Iota node on the bare
  redex (`bare`: the spine up to the major) at the motive at the major
  (`iota_end`), whose sort is the motive's level (`motive_at`: `Zero` for
  a Prop-only recursor), then extend over the extra arguments
  (`reconv_spine`). So the P1a side condition holds without sort
  uniqueness along conversion chains.
- **P2: indexed Prop families.** Found 2026-10-05: almost every indexed
  Prop family in core also has value parameters (`Eq`'s `a : α`,
  `Nat.le`'s `n`, `Acc`'s `r`, `HEq`'s), so P2 needs value parameters
  too. The model side is free for both: a Prop-only recursor's inductive
  has no tables (`canon_ok` asks `never_prop`) and its Iota is
  irrelevance. What they need is subject reduction, which needs the
  major's indices and value parameters convertible with the recursor's
  (injectivity). Today `pconv` records conversions only for parameters
  typed by a sort (`peq`): a value argument's domain depends on the
  earlier arguments, and recording a typed equality there would make the
  relation's symmetry and transitivity need substitution congruence over
  the telescope inside the fundamental lemma.
  Design: **term chains.** `mchain(g, x, y)`: a sequence from `x` to `y`
  whose consecutive entries are derivably equal at *some* type.
  Reflexive, symmetric and transitive by construction, and weakening
  carries it. Subject reduction (outside the model) turns a chain into an
  equality at the declared domain, step by step with `uniq`
  (`mchain_typed`: `x : T` and `mchain(x, y)` give `x ≡ y : T`).
  - **V1 (done): `pconv` records a term chain for every parameter, and
    for every index unless the inductive is always a type** (`never_prop`:
    there the model is index-blind and a recursive field's type relates to
    the result type at other index terms, `direct_pconv`). Establishing sites: the type former's relation
    (`tf_pconv`: each argument's conversion at its domain is one step),
    closed field types (`closed_pconv`: arguments are closed types,
    `sargs_typed`, related across the two level instances by
    `closed_conv`), field types over the parameters (`ps_pconv`), direct
    occurrences (`direct_pconv`), the recursor's inductive (`dom_rec_end`).
    `ind_inj_args` reads the chains back (and the argument counts agree);
    `ti_sr::mchain_typed` types them.
  - **V2 (done 2026-10-06): Prop-only recursors with value parameters
    and indices.** `rec_frag` asks `rec_scope_g` (no `ni == 0`) of every
    recursor and `rec_frag_l` (`rec_scope`, type parameters) of one with a
    motive universe. `iota_pjs` is empty for a Prop-only redex. `sig_rec`
    asks `rec_model` of a large recursor and `rec_model_p` of a Prop-only
    one: its rules typed in the general form (`iota_gen::rule_typed_g`,
    `rule_body_g` with the recursive calls' index terms), its
    constructors' types closed, its inductive semantic, and index chains
    (`ni == 0 || !never_prop`). Subject reduction dispatches: `iota_sr`
    for a large recursor, `iota_gen::iota_sr_g` for a Prop-only one. The
    generic route inspects no field kind: injectivity's term chains give
    the major's instance, parameters and indices (`srg_inj`); a telescope
    pair over the constructor's telescope (`srg_tpair`, `tpair_spair`)
    moves the fields to the recursor's parameters, the constructor
    application and the index terms (`srg_move`); the rule's spine types
    the reduct (`srg_rule`), and spine congruence at the motive converts
    its type (`srg_end`).
    **Correction:** `Eq`, `HEq` and `Acc` are subsingletons, so their
    recursors eliminate into every universe: they are large recursors of
    Prop inductives, still outside (`rec_model` asks `never_prop`; see
    "Open: large elimination out of Prop"). V2 admits the indexed Prop
    families with Prop-only elimination (`Nat.le`, `List.Mem`-like
    families with several constructors).
  - **V3 (done 2026-10-06): large recursors of Prop inductives into
    Prop.** `rec_interp` (a large recursor of an inductive that is a type
    at every instance) is what the model interprets (`rec_hyps`,
    `sig_rec`'s `rec_model`, `rec_frag_l`); every other recursor gets
    `rec_model_p`, no parameter premises, and generic subject reduction.
    `iota_prop` is per instance: the redex's motive level (`iota_lm`, the
    elimination level at the instance, opaque) is zero. `rec_fire` asks
    `fire_inst` (opaque): an interpreted recursor, or a proposition motive.
    So `Eq.rec`/`HEq.rec` reduce exactly at instances with a Prop motive,
    and their Iota is irrelevance; into Type they are stuck in the typed
    judgment (S6.6 must treat the kernel's such reductions as outside the
    fragment). The rule's level is pinned, `Iota(l)` with
    `l == iota_lm(m)`: level instantiation transports it by `lvl_compose`
    (`iota_lm_ls`), which `iota_prop ==> is_zero(l)` could not survive once
    `iota_prop` depends on the instance. A zero instance of an interpreted
    recursor (`Nat.rec.{0}`) is irrelevance too, its subject reduction
    still `iota_sr`'s. `Acc` stays out: its accessibility field is a
    function into `Acc` (not a field kind of `rec_canon`).

### Structures stage plan (2026-10-06)

Chosen next (2026-10-06) after the Prop stage. The kernel's facts
(`tc.rs`): a projection `Proj(i, s)` infers `s`'s type, reduces it to
`S.{us} ps` with `S` a structure (`get_structure`: one constructor, no
indices; recursive allowed for projections), and types the projection at
the constructor's field `i` at `us`, instantiated at the parameters and
the earlier projections `Proj(0, s) .. Proj(i-1, s)`; when `S` may be a
proposition, the field must be a proposition too. Head reduction:
`Proj(i, c ps fs) ~> fs[i]`, else reduce `s`. Definitional equality adds
structure eta (`t ≡ c ps fs` when `Proj(j, t) ≡ fs[j]` for every `j`),
unit eta (two terms of a type with one constructor without fields are
equal) and K-like reduction (a recursor of a Prop inductive with one
constructor without fields fires on any major whose type has the
constructor's indices).

The judgment has none of it and the model gives `Proj` only bottom. Each
rule lands dead first, gated by a signature condition the model can
discharge vacuously (the S6.3 pattern), then goes live with its model
case:

- **T1: projection typing and reduction, syntax.** `struct_of(sig, S)`
  (a canonical inductive with one constructor and no indices, its
  fields' telescope); rules `ProjCong` (`x ≡ x2 : S.{us} ps` gives
  `Proj(i, x) ≡ Proj(i, x2)` at field `i` over `ps` and `x`'s earlier
  projections) and `ProjIota` (the projection of a constructor
  application converts with its field, both typed); `hstep` reduces
  projections. Renaming, substitution, local swap/close, level
  instantiation, extension, validity, generation, scoping and subject
  reduction cover them; the model's cases are vacuous behind
  `proj_ok(sig)` ("no structures") until T2.
- **T2a (done, 39f3e33): `hstep` reduces projections** (a constructor
  application's to its field, else the subject).
- **T2, in steps** (found 2026-10-06: canonical field types never mention
  earlier fields, `field_kind`, so a projection's type is the field's type
  over the parameters alone; covered: `Prod`, `PProd`, `MProd`, `And`;
  dependent fields, `Sigma`/`Subtype`/`Iff`, need more field kinds):
  T2b the syntactic facts (a projection's type in the parameters only,
  closed under substitution, renaming, local swap/close, level
  instantiation, extension; the redex likewise) in `ti_proj`; T2c the
  rules' transports wired into the derivation transformations; T2d
  generation and subject reduction (a projection of a constructor
  application: injectivity's chains for the parameters, as in
  `iota_gen`); T2e the model and soundness; T2f adequacy; T2g the flip of
  `proj_ok` to a real condition (structures in scope, their facts in the
  model's hypothesis).
  Done through T2d's generation (`gen_proj`): substitution, renaming,
  local swap/close, level instantiation and pairs, validity, scoping,
  constants, generation are real. Still dismissed by the gate
  (`proj_dead`, `gen_proj_dead`): signature extension, uniqueness and
  subject reduction (their projection cases need injectivity at the
  structure, i.e. the flipped `proj_ok` carrying per-structure facts such
  as `sem_const` and the constructor's closed type), the kernel port's
  "projections are typed nowhere" (`kclaims::gen_proj`,
  `untypable_untyped`, `jkernel::sr_pstep`/`lveq_conv`: S6.6 at the flip).
  **Soundness and adequacy are real (2026-10-06, T2e/T2f)**, under
  `dom_proj_sound::proj_sem` (each structure and its constructor
  interpreted at every instance, its canonical recursor in scope, its
  tables' syntactic facts), which the gate still gives vacuously
  (`proj_ok_sem`); the flip must derive it. ProjIota gained two premises
  for them: the field typed at its declared type `proj_fty` (the ⊇
  direction builds the one-field constructor node, `dom_iota::con_major`)
  and the subject's type headed by the constructor's structure (so the
  Prop test on the subject's type speaks of the projected structure).
  `struct_of` now asks every field to be a type parameter, and a
  structure that may be a proposition always to be one, or else its sort
  parameters never to be propositions (so `Prod`, `MProd` and `And` are in,
  `PProd`, whose parameters are `Sort u`, is not yet).
  **T2g, the flip (2026-10-06): the projection rules are live.** The
  rules' gate is gone; the model's structure facts (`proj_sem`) are a
  conjunct of `sig_sr` (and so of `rec_hyps`), the hypothesis soundness,
  adequacy, uniqueness and subject reduction already take. Uniqueness
  reads the subjects' structure off the chain between their types
  (`dom_fund::ind_head_chain`, cycle-free); subject reduction builds
  ProjIota for a firing projection (`ti_sr::sr_proj_fire`). The kernel
  port's structures came with S6.6 (below). The flip exposed that
  the rule transports had verified vacuously under the gate; they now
  carry the subject heads through the operations. Adequacy: ProjIota is the Iota
  pattern; ProjCong (`dom_adeq_proj`) takes the subjects' relation at a
  constructor value above the witness, moves the projected arguments'
  relation at the field's table entry to the witness (`arg_adeq`), and
  expands along `Proj(i, x) ~> Proj(i, c ps fs) ~> fs[i]` with the
  ProjCong and ProjIota derivations built at the substituted terms.
  **First slice (2026-10-06):** `struct_of` admits structures whose fields
  are type parameters or recursive occurrences (`Prod`, `PProd`, `MProd`,
  `And`). Soundness of a projection needs the field's table entry to be a
  member of the field type's denotation; for a parameter the entry is the
  parameter's own code (a member of the parameter term, `tf_spine`), for
  a recursive field the structure's code. Closed or nested field types
  need a general lemma that a simple type's code (`ceval`) is a member of
  its denotation, which the model does not have yet.
- **T2: the model.** `mem_w` gives `Proj(i, x)` the `i`-th field value of
  `x`'s constructor values (bottom otherwise); soundness of both rules
  (a constructor application's members are constructor nodes whose
  fields are members of its arguments, down-closed; projections of a
  join-closed denotation). Adequacy: the relation at a structure code
  already relates terms reducing to constructor applications fieldwise
  (`con_tm`); a projection head-reduces to the related field
  (`expand_tm`). Prop structures: projections of proofs are proofs
  (irrelevance).
- **Found 2026-10-06, before T3: structure and unit eta are unsound in
  the current model.** Constructor nodes are lazy: `Con(S, 0, [⊥, ⊥])` is
  well-formed and distinct from `⊥` (unlike `Lam`, whose `wf` asks a
  non-bottom output, which is what makes function eta sound), and every
  constructor application contains it (`dom_iota::con_major` with
  all-bottom fields). Axioms and locals denote only `⊥`. So for an axiom
  `ax : Prod A B`, eta relates `{⊥}` to a denotation containing
  `Con(Prod, 0, [⊥, ⊥])`; likewise `ax : Unit` and `Unit.unit`. Smashing
  all-bottom nodes into `⊥` is no fix (zero-field constructors such as
  `Nat.zero` must stay distinct for the recursors). T3/T4 need a model
  change first (e.g. type-directed bottoms: at a structure type, bottom
  is the all-bottom constructor node), or stay out of the judgment.
- **The eta redesign (chosen 2026-10-06): smash structures, irrefutable
  structure recursors.** A structure's constructor node with every field
  bottom is not well-formed, so a structure value is `⊥` or has a
  non-bottom field (functions already work this way: `wf(Lam)` asks a
  non-bottom output). Multi-constructor types stay lazy (`Nat.zero`,
  `succ ⊥` must stay apart from `⊥` for their recursors). Then
  `ax ≡ c ps (π0 ax) .. (πn ax)` holds in the model (both `{⊥}` at an
  axiom), unit eta too (a zero-field structure has no well-formed node,
  so all its terms denote `{⊥}`). The price: Iota at a constructor
  application with bottom fields must still hold, so the model's
  recursor at a structure applies the minor to bottom fields when the
  major is `⊥` (irrefutable match); adequacy then needs the judgment's
  head reduction to fire a structure recursor on any major, eta-expanding
  it (`rec M x ~> M-rule (π0 x) .. (πn x)`, the kernel's
  `toCtorWhenStructure`), which is untyped: the recursor names its
  inductive. Stages:
  E1 keys: `NdKey::Con` and `NdKey::Ty` carry a structure flag;
  `has_type` ties a value's flag to its code's; `wf` asks a flagged node
  for a non-bottom field; every producer passes `false` (no semantic
  change). E2 smash on: codes and constructor values take the flag from
  `struct_of`; the constructor's code function at bottom fields is `⊥`;
  `recval` is irrefutable at structures; the model's lemmas re-proven.
  E3 judgment: the structure-eta conversion rule (E3a, `StructEta`,
  extensional: equal projections) with its transports; then the
  recursor-eta head step (E3b). That step needs no rule of its own: its
  subject reduction is StructEta under application congruence
  (`x ≡ c ps (π0 x) .. (πn x)`, the projections' premises by ProjIota)
  followed by ordinary Iota at the constructor application.
  E4 soundness and adequacy of StructEta (done), and the recursor's
  adequacy at the irrefutable match (through the head step).
  **Revision (E4c, 2026-10-06): a smashed structure's recursor never
  takes Iota; its eta step is a rule (`RecEta`).** The recursor's end in
  adequacy can read typing facts only off the logical relation: every
  inversion lemma (`uniq`, `spine_ty`, `dom_fund`'s injectivity, and so
  `iota_sr` and the projection's subject reduction) is proven from
  adequacy, so calling one there is circular. A major that is the
  constructor's application with a bottom value then has untyped fields:
  typing them at the recursor's parameters needs the constructor's
  parameters to be the recursor's (injectivity) and the spine's
  arguments typed at its head's declared domains (Pi injectivity), and
  the relation at bottom says nothing. Restricting Iota to the
  constructor at the redex's own parameters does not help (the spine
  still needs inverting), and keeping Iota as a rule while the head step
  eta-expands breaks Iota's adequacy (the minor at the projections and
  at the fields would have to be related without the minor's own
  relation). So `rec_fire` excludes smashed structures: their redexes
  always take the eta step, the end route only ever meets the major's
  projections (typed by ProjCong from the major's own typing), and the
  step gets its own rule `RecEta` (`m ≡ rec_eta_result(m)`, both sides
  typed), adequate by one head step like Iota, sound by the irrefutable
  recursor (a projection of a constructor value is its field, of
  anything else bottom). The kernel's Iota at a structure's constructor
  application becomes RecEta followed by ProjIota at each field, derived
  outside adequacy where inversion is available. RecEta also asks the
  major to convert with its expansion and the redex there to be typed,
  so its soundness is Iota's at the expansion (E4c-5). Landed through
  E4c-6: the smashed end goes through the major's projections
  (src/dom_rec_eta.rs). E6, the flip: the staging switch is gone, every
  structure (whose field count fits a projection index) is smashed, so
  StructEta (structure and unit eta) and RecEta hold in the judgment.
- **T3: structure eta.** Rule `x ≡ c ps (Proj(0, x)) .. (Proj(n-1, x)) :
  S ps`. Soundness by the join-closure of `x`'s denotation; adequacy
  because a related `x` reduces to a constructor application whose
  fields its projections reduce to.
- **T4: unit eta.** Rule for types with one constructor without fields:
  any two terms are equal. Soundness: members are bottom or the single
  constructor node; adequacy: both reduce to it or are related at
  bottom.
- **T5: K-like reduction** for Prop recursors (one constructor, no
  fields): the major replaced by the constructor at the major's type's
  indices when they convert with the constructor's. Into Prop it is
  irrelevance; subject reduction by the generic route with the index
  premise.

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

**Found 2026-10-12: no interpretation exists in this architecture.** The
fundamental lemma relates every context to itself over the bottom
environment, and the relation asks a term with a non-bottom member to
head-reduce to a canonical form. Take `T := Eq.rec (motive := fun _ _ =>
Type) Nat h`. In `(a : Nat) (h : a = a)`, `h ≡ Eq.refl a` by
irrelevance and Iota fires (the kernel's K-like step), so soundness gives
`T` the code of `Nat`. In `(a b : Nat) (h : a = b)`, `T` is stuck, so
adequacy forces it to denote bottom. Over the bottom environment both
applications of `Eq.rec` receive the same arguments (`a`, `b`, `h` all
bottom), so no choice of `Eq.rec`'s denotation meets both. A
proof-relevant `Eq.refl` (`ref w`, as the paper's identity type) does not
help: irrelevance (`h ≡ Eq.refl a` at `h : a = a`) is then unsound over
the bottom environment, and with it the contradiction returns. Lifting it
needs a model where variables are not bottom (neutral elements). `And`-
and `True`-like large eliminators are not affected: they are structures,
and their stuck redexes take the eta step (`RecEta`). Measured: Lean's
Core reaches `Eq` at its 16th declaration, so the fragment covers no
longer Core prefix in this model; Eq's large elimination is metatheory
the full judgment's hypotheses carry.

### Sub-stages

| | content |
|---|---|
| S6.1 | compacts: one data node `Nd(key, comps)` for type codes and constructor values, compared pointwise; order, join, compatibility, coherence, well-formedness (done) |
| S6.2 | semantic typing for them; the stage and join properties (Props 2.16-2.18) (done) |
| S6.3 | syntax: the signature carries the kernel's recursor tables (`Sig.ienv`); rule `Iota` relates a ready recursor application (`rec_ready`) to its rule instance (`rec_result`) where both sides are typed; renaming, substitution, local swap/close, level instantiation, validity, generation and signature extension cover it (done). `Iota` also asks `iota_ok(sig)`, the signature condition the model will need: for now "no recursors", so the rule is dead in the model until S6.4 states the real condition |
| S6.4 | interpretation of inductive constants, constructors, recursor applications; ideal properties; soundness incl. `Iota` |
| S6.5 | logical relation clauses; their properties; adequacy incl. `Iota`; injectivity re-proven |
| S6.6 | kernel side: `jsig` from the environment's inductive tables, SR for the kernel's recursor iota, `frag_env` relaxed; literals through `Nat` (plan below) |
| S6.7 | projections, structure and unit eta, K-like reduction |

### S6.6 plan (2026-10-07)

The kernel claims (`kclaims`, `jkernel`) hold today for environments
without inductive tables (`frag_env`), where every recursor, projection
and eta step is vacuous (about thirty sites use that). Stages:

- **S6.6a, the kernel's steps with inductive tables, under hypotheses**
  on `jsig` (`iota_ok`, `sig_sr`; every recursor interpreted or Prop-only;
  every structure the kernel eta-expands in the `struct_of` slice): a
  typed recursor redex fits its rule (the kernel checks neither the
  major's arity nor its levels: typing gives both); subject reduction for
  the kernel's iota (unsmashed: Iota; smashed: RecEta, then ProjIota at
  each field under application congruence); projection steps (ProjIota);
  structure and unit eta (StructEta). Proven first as separate lemmas,
  then the flip: `frag_env` allows inductive tables and the fragment's
  vacuous cases become these proofs.
  The flip is staged. Stage 1 (landed): recursors are live. `frag_env`
  keeps the kernel's structure tables empty (`struct_ctor`, `ctor_nf`:
  no projections, structure or unit eta) and asks, at every locals map,
  `kclaims::ind_ok`: `iota_ok`, `sig_sr`, every recursor interpreted, no
  judgment structures, each constructor one of its inductive's canonical
  recursor; and constructor entries declared, not definitions, not
  recursors. The model never reads locals, but the hypotheses are stated
  at every locals map because the verifier cannot see that across
  signatures. Signature extension (`ti_valid::sig_ext`) carries every
  rule, structures included: an old canonical recursor stays canonical
  with the same shape, and the larger signature's `iota_ok` makes it the
  only one (`canon_grow`, `struct_iff`). The kernel's iota is the
  judgment's (`jkernel::sr_iota_at`), and K-like reduction converts by
  proof irrelevance with the constructor typed at the major's parameters
  (`kiota::ctor_params_typed`). Stage 2 (landed): the kernel's
  structures. `frag_env` no longer empties `struct_ctor` and `ctor_nf`;
  `ind_ok` asks that each structure the kernel eta-expands is a smashed
  judgment structure whose canonical constructor is the kernel's, and
  that the field counts are the canonical shape's (Sigma, Subtype and
  other structures outside the `struct_of` slice stay out). A typed
  projection of a constructor application fires (`kiota::kproj_fire`,
  through `ctor_arity_at`: a constructor application typed at a
  canonical inductive's application is that inductive's, at its exact
  arity); projection congruence and the kernel's projection step are
  derivations (`proj_cong_d`, `proj_step_d`). Structure and unit eta are
  StructEta over `kstruct`'s facts: a structure application typed at a
  sort has exactly its parameters (`struct_type_arity`), projections are
  typed at the parameters their fields name (`struct_proj_typed`), and
  the eta expansion is typed (`struct_cx_typed`). The projection's
  inference claim follows the kernel's walk down the constructor's type
  (`proj_reg::walk_ty`): each stage converts to the telescope
  instantiated as far, and Pi-injectivity moves each argument's typing
  to the next stage.
- **S6.6b**: the hypotheses from the verified inductive module, at every
  export prefix (`export_kh`). Direction (2026-10-07): prove nanoda's own
  recursor generator. Today the checker reads recursors from the export
  and compares them with its generated ones by `def_eq` in a temporary
  extension, and no contract carries anything out; its only guarantee is
  `declar_cert_at`. The generator builds exactly the canonical form over
  locals: `mk_recursor_ty` is `Π params motives minors indices major,
  motive indices major`, `mk_rec_rule_val` is `λ params motives minors
  fields, minor fields ihs`. Phases:
  - **B1** abstraction algebra: abstracting an opened telescope's locals
    (`abstr_pi_telescope_model`) is the de Bruijn telescope (`binds`).
  - **B2** the locals' types: parameters and indices from the
    inductive's type, the motive (`motive_ty`), each minor (`minor_ty`,
    fields and induction hypotheses), the major.
  - **B3** `mk_recursor_ty` is `rec_ty`, `mk_rec_rule_val` is `rule_rhs`.
    B3a (`kminor.rs`): a minor premise built from opened locals is
    `minor_ty(j)` opened at the parameters, the motive and the earlier
    minors (`minor_canon`), given the constructor type's canonical form
    and the recursive positions; indices included. `tel_canon` is the
    general step: abstracting locals that opened a substituted telescope.
    B3b (`kminor.rs`): the recursor type built from opened parameters,
    motive, minors, indices and major is `rec_ty(lm)` (`rec_ty_canon`),
    and a rule value is `rule_rhs` (`rule_canon`, hypotheses `rr_ih`),
    given each local's opened declared type. What is left of B3 is the
    bridge from the generator's witnesses to these lemmas' inputs.
    B3c–i: the bridge for the type. The minor witnesses carry the earlier
    minors (`prev`) and the tested fact that non-Pi fields are recursive
    exactly when syntactically the inductive at the parameters
    (`recs_syn`, B3f, corpus clean), so a canonical constructor's
    positions are `rposj` (`wit_positions`). `check_inductive_declar`
    records the creation windows and proves, for every shape the block
    has (`gen_shape_ok`: single inductive, canonical type and constructor
    forms, admitted field kinds), that its recursor's type is that
    shape's `rec_ty` (`declar_rec_glue`). B3j–l: the rules. Each rule's
    hypotheses call one recursor name (hash-consed names), its re-opened
    fields are the constructor's at `rposj` (`fields_canon`), and its
    value is `rule_rhs` with that recursor (`rule_bridge`,
    `rules_declar_canon`); `declar_rec_glue` carries both. B3 is
    complete for a single inductive; B4 ties the rules' recursor to the
    declared one and compares with the export.
    B4a–b: strings and names are hash-consed (proved), so the rules'
    recursor is the declared one. B4c: the comparison with the export is
    observed, not enforced: `assert_nonnested_recursors_def_eq` returns
    whether every exported recursor is syntactically the generated one at
    its universe parameters (`rec_old`). FINDING: Lean's exported
    recursors strip `outParam`/`optParam`/`autoParam` from binder types
    while the declared inductive and constructor types keep them, so the
    literal canonical form misses those inductives (Init: 97 of the
    recursor types, 118 rules -- the `H*` classes, `GetElem`,
    `Membership`, `Rat`, `Std.Format`, ...). They stay outside the
    fragment; an annotation-stripping canonical form is the widening.
    B4d: the target is nanoda's behaviour, and nanoda accepts an exported
    recursor when it CONVERTS to the generated one (`assert_def_eq`). The
    comparison functions now ensure exactly that (`rec_conv_old`: the
    exported type at the generated universe parameters converts to the
    generated type, each exported rule to the generated rule), for every
    recursor, annotated or not. The syntactic flag (`rec_old`) stays as
    an observation; the difference it exposes -- Lean's export strips
    binder annotations, so exported recursors are canonical only up to
    conversion -- is documented here rather than built into the claim.
  - **B5 direction: `rec_canon` up to conversion, aligned with nanoda.**
    nanoda decides an exported recursor by conversion with the one it
    generates, so the canonical recursor becomes one whose declared type
    and rules CONVERT to `rec_ty`/`rule_rhs`, not one equal to them.
    Staged: (1) shape facts the equality used to supply are their own
    conjuncts; (2) the four split lemmas (`rec_ty_split[_g]`,
    `rule_split[_g]`) give conversion; (3) typing side: one conversion
    step after the recursor constant is typed; (4) semantic side: the
    model reads a recursor at its canonical type, with one agreement
    lemma; (5) rule side: reduction facts become conversion facts.
    TRADEOFF, recorded as the work goes:
    - Gained: every recursor nanoda accepts by conversion is covered,
      including the annotated inductives Lean exports stripped (`HAdd`,
      `GetElem`, `Rat`, ...); no stricter check than nanoda's.
    - Paid: the metatheory reads the recursor's type and rules only up to
      conversion -- typing goes through a conversion step, the semantic
      model through an agreement lemma, and iota's right-hand side is a
      conversion, not a reduction.
    - Stays an assumption (not checked by nanoda): a rule's value has no
      string literals and is a lambda (`rule_shape`; nanoda checks only
      that it is closed). The recursor's inductive is still read off its
      declared type syntactically (`rec_ind`), as nanoda reads it
      (`get_major_induct`).
    FINDING (5b): `rec_canon` cannot itself be relaxed to typed conversion
    -- the typed judgment (`derivable`, `tconvd`/`chain_ok`, `iota_ok`,
    `rec_fire`) is defined through `rec_canon`, so the definition is
    circular. `rec_canon_c` stays as a standalone predicate.
  - **B5 design: the canonical twin signature** (user's choice over an
    untyped δβ notion, because it keeps nanoda's own relation).
    `rec_canon` stays syntactic. `twin(sig)` is `sig` with each recursor
    whose inductive side is canonical (`rec_canon` minus its two
    equalities) given the canonical type `rec_ty` and rules `rule_rhs`;
    `rec_canon(twin(sig), rid)` then holds by construction. The kernel's
    claims are proved in the twin and TRANSFERRED back: the twin and
    `sig` differ only at those recursors, whose declared type and rules
    convert (in `sig`) to the twin's -- exactly what nanoda's `def_eq`
    certifies (B4d). Layers:
    T1 `twin` and `rec_canon(twin(sig), rid)`.
    T2 transfer of derivations: a constant's typing step uses the twin's
       type, then one conversion to the declared one; an iota step's
       right-hand side differs by conversion.
    T3 the certificate: `declar_cert_at` for the inductive carries the
       conversions (kconv), bridged to the typed ones the transfer needs.
    T4 `kh_hyp` assumes `ind_ok` of the twin instead of `sig`.
    Trade-off: closest to nanoda's relation (def_eq, incl. eta and proof
    irrelevance) at the cost of a judgment-transfer layer; the untyped
    alternative would have been smaller but narrower than nanoda.
    T2 as built: the claims are stated in the twin
    (`jsig := twin(jsig_raw)`), rather than transferred back. The twin's
    obligations are named assumptions, to be certified in T3:
    - `kclaims::twin_ok` (part of `frag_env`, per cutoff): the
      environment's rules are string-free lambdas; and for each
      twinned recursor, at every level instance the declared type converts to the canonical one in
      the twin (nanoda's `def_eq`, B4d); and each exported rule converts
      to its canonical rule at any type the canonical rule has
      (`rule_conv`, nanoda's per-rule `def_eq` in `rec_conv`). The twin
      fires the canonical rule; `jkernel::sr_iota_at` returns to nanoda's
      rule instance through `spine_conv` (converting heads convert their
      spines).
    - `export_sound::twins_stable`: along the export, a later cutoff's
      twin decides an earlier cutoff's recursors the same way, with the
      same canonical type and rules (`env_weaken::twin_le`, now required
      by every weakening lemma).
    - `export_sound::twin_types`: a twinned recursor's canonical type is
      a type in the environment of its certificate (nanoda types the
      generated recursor before the recursor itself is added).
    FINDING (T3): two of these obligations cannot be certified from
    nanoda's checks, and stay named hypotheses (user's decision, 2026-10-08):
    - `twin_types`: nanoda, like Lean, never type-checks the recursor it
      generates; that the canonical type is a type is metatheory (the
      generated recursor is well typed when the inductive and
      constructors are), not a check nanoda makes.
    - the conversions in `twin_ok` (declared type, `rule_conv`): nanoda
      compares by `def_eq` in the environment holding the whole block,
      recursors included. The typed half of that claim (`cw`) holds
      under `kh` of that environment, which already assumes `twin_ok` of
      the same recursors -- circular -- and needs both sides typed
      (`twin_types` again). The untyped half (`kconv`) is not circular,
      but `kconv` to typed conversion is the research-level step
      (unique typing, inversion; see METATHEORY.md). A strengthening
      lemma (the comparison holds in the environment before the block's
      recursors) would also break the cycle; not attempted.
    Certified instead: `twins_stable` and the level facts, which follow
    from the environment's growth and the declarations' own checks.
    T3a: a recursor's rule constructors are declared before it (a
    tested-input check beside nanoda's own `recursor_before_inductive`;
    Init.Core and Init clean), and its certificate records it. With the
    inductive (in the recursor's checked type) and the constructors'
    field types (in their checked types) also earlier, everything the
    twin's decision reads is fixed when the recursor is declared.
    T3b-c: `twins_stable` is no longer assumed. `twin::rec_core_grow`:
    in a growing signature (`grows`: constants and tables kept, no
    earlier constant becomes a recursor or constructor --
    `env_model::tables_stable_at`), the twin decides a recursor, and
    builds its canonical type and rules, as before, when its type, its
    constructors and theirs mention only earlier constants.
    `export_sound::twin_le_at` supplies that inside the `export_kh`
    induction, from the certificates (types are types at their cutoffs,
    `ti_level::d_consts`; the constructors from T3a). `rec_core` now also
    asks the major premise to exist with a constant head, so the
    inductive it reads is a real one.
    T3d: the level facts are no longer assumed. `twin::canon_elp`: the
    canonical type and rules mention only the recursor's level
    parameters when the inductive's and constructors' types mention only
    the inductive's (piece by piece: telescope parts, `lift`, motive,
    minor premises, major premise, rule bodies). `export_sound::inst_decl`
    takes those from the declarations' certificates (`dty_lp_ok`). What
    `twin_ok` still assumes: the rules' shape (`rule_rhs_ok`), the
    canonical type closed, and the two conversions; plus `twin_types`.
    T3e: the canonical type closed is no longer assumed
    (`twin::canon_nofv`, the same assembly as `canon_elp`, from every
    declared type closed, `fv_free`). Left in `rule_rhs_ok`, of what
    nanoda does not establish: no loose bound variable (`check_rec_rules`
    states only closedness and levels), no string literal, a lambda; its
    constructor is a declared constructor (T3a's lookup), certifiable
    once the first is.
    T3f: done. nanoda's own `assert_closed` already rejects loose bound
    variables; its contract now says so (`nlbv == 0`), `check_rec_rules`
    carries it, and the recursor's certificate records it with T3a's
    constructor lookup (`ctor_np`). `export_kh` derives both;
    `twin_ok`'s rule conjunct is now exactly what nanoda never checks: a
    rule value has no string literal and is a lambda.
    Trade-off as built: a constant's typing in the twin is at the
    canonical type, and `typed_const` recovers the declared type through
    `twin_ok`'s conversion. So the claims follow nanoda's `def_eq`. The
    rules' shape (string-free lambdas) stays an assumption. `rec_ind` is
    still read syntactically, as nanoda's `get_major_induct` does.
  - **B4** the comparison: a verified structural (model) equality check
    of the exported recursor against the generated one (a tested-input
    check, registered), with the tables' data fields.
  - **B5** the certificate: `declar_cert_at` for a recursor carries its
    canonical form at the cutoff.
  - **B6** the rest of `rec_canon` and `ind_ok`'s tables (the inductive's
    and constructors' type forms, field kinds, constructor tables,
    uniqueness), from the constructor and positivity certificates.
    B6-0: the hypothesis/claim split. `kclaims::frag_env` (what `kh`
    claims) is `frag_hyp` (what `kh_hyp` assumes) plus `tables_ok`, the
    constructor tables, plus `ind_ok` derived (`frag_env_of`). `tables_ok`
    -- a constructor is declared, no definition or recursor, and has an
    inductive (also a constructor with a field count) -- is certified at
    every cutoff by the export model (`env_model::tables_ok_at`): each
    entry is a constructor declaration's. `ind_ok_hyp` is `ind_ok`
    without those. Later B6 steps move more of `ind_ok_hyp` into
    certified facts the same way.
    B6a design: what remains of `ind_ok_hyp` turns on `has_canon` -- an
    inductive's recursor being twinned (`twin::rec_core`). nanoda's
    generator proofs already show the generated recursor is canonical
    for any shape `sh` with `gen_shape_ok(st, sh, lm)` (the declared
    inductive and constructor types in canonical form, admitted field
    kinds), but only conditionally: nothing yet shows nanoda's checks
    establish such a shape. Measured on Init (808 constructors of single
    non-nested inductives): every constructor restates its inductive's
    parameters syntactically (nanoda checks them only by `def_eq`) and
    ends in the inductive at the parameters (nanoda checks this
    syntactically, `is_valid_ind_app`); 422 fields have a function type,
    which `fkind_ok` does not admit -- the fragment's boundary, as before.
    Steps: B6a-1 a tested-input check that each parameter's type is the
    inductive's (`model_eq`, before nanoda's `assert_def_eq`; Init and
    Init.Core clean; stricter than nanoda's `def_eq`, recorded in
    VERUS_REWRITES.md), carried by `ctor_cert_ok`; B6a-2 the existence
    of `gen_shape_ok` from the checker's walks, given admitted field
    kinds; B6a-3 the inductive's certificate records it, with nanoda's
    recursor data comparison (`aux_data_ck`); B6a-4 `rec_core` at the
    export from the certificate, so `has_canon` and the tables follow
    and `kh_hyp` keeps only the fragment's boundary.
    B6a-2 done as a lemma (`inductive::shape_exists`): for a single
    inductive whose fields are of an admitted kind, the declared types
    give `gen_shape_ok(st, decl_shape(st), lm)`. `decl_shape` reads the
    shape off the declared types as `rec_canon::shape_of` does (fields
    up to the constructor's arity). Pieces: the constructor's parameters
    are the inductive's (`ctor_pdoms`: B6a-1's check, `kgen::tel_eq`);
    its result is the inductive at the block's universe parameters
    (second tested check, `levels_ptr_eq`; Init 808/808) applied to the
    parameters as variables (`ctor_result`: distinct walk locals,
    `kgen::vsub_is_free`); bounds and closedness of the assembled motive
    and minor premises (`twin::motive_nlbv`, `minor_nlbv`, `head_nofv`);
    the block's constants (`ind_const_at`).
    B6a-2g: `shape_exists` is reached inside `check_inductive_declar`.
    Three more tested checks (each registered, Init/Init.Core clean): the
    inductive's literal walk covers its parameters; the checked
    constructors and the checked inductive are the exported ones
    structurally (`model_eq` in `assert_nonnested_ctors_def_eq` /
    `assert_nonnested_tys_def_eq`, giving `ctor_old` / `ind_old` and the
    declared types' closedness). The state's facts are bundled where
    they are fresh (opaque `shape_pre`, after the constructor checks),
    carried past the recursors' construction (`shape_pre_frame`), and
    `shape_end` gives `gen_shape_ok` at the end of the non-nested branch
    for a single inductive with admitted fields (`fields_admitted`).
    B6a-3/4 plan (what `twin::rec_core` at the export needs, and from
    where): the declared inductive and constructor types in canonical
    form (`shape_end`, `ind_old`, `ctor_old` -- done); the recursor's
    table data (parameters, one motive, minors, major index, rules'
    constructors and field counts, level parameters) from nanoda's
    `aux_data_ck` of the exported recursor against the generated one,
    with the generator's facts; `rec_ind`, the head of the exported
    recursor type's major premise, a syntactic reading nanoda checks
    only by `def_eq` (a tested check); the constructor tables and level
    parameters from the export model and the constructor arm's checks;
    the indices and the inductive's type not mentioning the inductive
    (`ind_app_ok`; declaration order); the canonical rules string-free
    lambdas (`frag_term` of the declarations, the motive binder). The
    field kinds `rec_core` reads (`psimple`/`direct_occ`, stricter than
    `fkind_ok`) stay the fragment's boundary in `kh_hyp`.
    Done since: B6a-3a (`a4b1ca4`) a tested check that the exported
    recursor's major premise has the generated one's head (`rec_major_head`
    in `rec_conv`); B6a-3b (`b627683`) `rec_conv` records the exported
    recursor's counts and per-rule constructors and telescope sizes
    against the generated ones (the counts restated after the unverified
    `aux_data_ck`).
    B6a-3c design (the block certificate): the constructors `rec_core`
    reads come from the recursor's rule table, so the certificate is keyed
    on the block's exported recursor, not on the inductive's constructor
    list -- its rules' constructors are the generated rules' (`rec_conv`),
    those are the header's (`mk_recursors`), whose types are the exported
    constructors' (`ctor_old`). The certificate states, for a block in the
    fragment (one inductive, non-nested, fields admitted), that some
    exported recursor named the inductive's `.rec` has the shape's counts,
    rules and major head, and that the exported inductive and constructor
    types have that shape. B6a-4 then needs every recursor of the
    environment to be such a block's recursor: nanoda compares each
    block's exported recursor names with the generated ones
    (`ck_recursor_names_simple`, against the parser's
    `ind_name_to_recursor_names`). That table is built from every
    recursor declaration (`ExportBuilder::recursor_names`: each listed
    under each inductive of its `all_inductives`), and the recursor arm of
    `check_declar` checks its first inductive is a declared inductive. So
    every recursor of the export is, by name, some block's generated
    recursor: the link is certifiable (contracts on `recursor_names` and
    `ck_recursor_names_simple`), not a new hypothesis.
    B6a-3 done: `inductive::block_cert(ef, i)` -- for an exported
    single, non-nested inductive, the exported inductive, constructors
    and a recursor have a canonical shape (`block_ok`: types, closedness,
    bounds, the recursor's counts, rules' constructors and field counts,
    universe parameters and its major premise -- the latter now tested
    against the block's inductive itself, not only the generated one's).
    `check_inductive_declar` ensures it (`block_ind_part`,
    `block_rec_part`, `block_cert_end`), `check_declar` passes it on, and
    the serial driver collects `export_sound::all_block_certified`.
    Facts it rests on, beyond the earlier tested checks: the recursor's
    universe parameters are its inductive's (`rec_uparams_ok`); the
    exported constructors' inductive and parameter count are the block's;
    the generated recursor's rules have the constructors' arities
    (`pi_telescope_size` states the arity); and three checks tying the
    export's `is_nested`, block size and first type to nanoda's branch.
    B6a-4 plan. (1) Linking an environment recursor to its block: the
    parser's table covers every recursor declaration (contract on
    `ExportBuilder::recursor_names`, part of `export_rec_names_ok`);
    `ck_recursor_names_simple` makes a non-nested block's entry exactly the
    generated names (`rec_names_set` states its set), and `rec_conv` makes
    the generated name the exported one's; the recursor arm's checks give
    the recursor's first inductive, declared before it. So a recursor
    whose block is single and non-nested is that block's `od_r`. (2)
    `rec_core(raw_cc, rid)` from `block_ok` and the export model's entries
    (types, tables, `rec_entry`), with the field kinds (`field_kind`) the
    one fragment condition left. (3) What it buys: with `twin_canon`,
    `rec_canon` of the twin for every such recursor; then `iota_ok`'s
    syntactic parts (`rec_scope_g`: distinct constructors and universe
    parameters, one canonical recursor per inductive, `rec_elp`; rules'
    shape) are certifiable, leaving `sig_sr` and `rec_interp` -- the model
    facts, B7 -- and the boundary (single, non-nested, field kinds) as
    hypotheses.
    B6a-4 (1)+(2) done: `export_sound::rec_core_at(ef, cc, rid)` -- under
    `below_ok` and the driver's collections (`all_block_certified`,
    `all_rec_checked`) with the parser's name table, every recursor at a
    cutoff whose block is single and non-nested (`rec_simple`, export
    side) and whose fields have admitted kinds (`rec_fields_ok`, model
    side) satisfies `twin::rec_core` of the raw signature. The pieces: the
    shape the signature reads off is the certificate's (`shape_read`); the
    constructors are the signature's (`ctor_facts`, their universe
    parameters from `ctor_e2_cert`); the inductive's type misses the
    inductive because it is typed before it (`ty_self_free`); the
    constructors' index arguments miss it (a tested check's consequence,
    `block_ok`); the canonical rules are closed, string-free lambdas with
    no loose bound variable (`twin::rule_shape_canon`; string-freedom of
    the pieces from `kh_hyp`'s `frag_term`). `field_kind` stays a boundary
    hypothesis: it is the model's simple-field predicate, which nanoda's
    positivity check approximates but does not state.
    B6a-4 (3) groundwork: two tested checks for `rec_scope_g`'s
    uniqueness parts. A single-motive recursor's major premise is headed
    by one of its own inductives (`rec_arm_ok`; a nested block's auxiliary
    recursors eliminate e.g. `List T` with more motives, and are exempt).
    The exported constructor's index is its position (`ctor_idx_old`),
    so `block_ok` has distinct constructors. OBSERVED DIFFERENCE: nanoda
    alone accepts a block whose header lists one constructor twice
    (`aux_data_ck` compares against the temporary map's last entry);
    Lean's kernel rejects it. The check aligns nanoda with Lean; no Lean
    export is affected (Init: 57424 declarations).
    B6a-4 (3) done for the syntactic part: `export_sound::twin_scope_at`
    -- for a recursor at a cutoff whose block is simple, the twin has it
    in scope (`rec_scope_g`: canonical, distinct constructors, the only
    canonical recursor of its inductive -- `twin_unique_at`, from the
    major-head check and the parser's table --, the inductive no
    constructor or recursor, distinct universe parameters and `rec_elp`
    from the declarations' certificates), its constructors are no
    recursors, and its rules are well formed (`rule_rhs_ok`). What
    `iota_ok`'s `rec_frag` still asks of such a recursor is the
    interpreted clause (`rec_interp ==> rec_frag_l`: no indices, sort
    parameters) -- a model fact, B7 -- and nothing of the others, which
    stay under `ind_ok_hyp` (B8 splits it by `rec_simple`).
    B8 step 1 done: `iota_ok`'s syntactic part left the hypotheses.
    `ind_ok_hyp` keeps of it only `rec_small` (no indices, sort
    parameters -- the fragment's shape); `frag_env_of` takes
    `kclaims::iota_syn` as it takes `tables_ok`, and the export
    certifies it at every cutoff and locals (`iota_syn_at`). The cost is
    the boundary, now explicit: `export_sound::ex_bound` (every
    recursor's block simple, and the driver's collections with the
    parser's recursor table) in `below_ok`/`export_kh`, and
    `rec_fields_ok` (field kinds) in `kh_hyp`. No scope is lost: a mutual
    or nested block's recursors have several motives, which `rec_canon`
    excludes, so `ind_ok_hyp` already failed for such exports; `ex_bound`
    states that boundary at the export.
    FINDING (2026-10-10), KH IS FALSE INSIDE A BLOCK: the parser inserts a
    block's inductives, then its constructors, then its recursors
    (`parser.rs`), so at a cutoff between a block's first constructor and
    its recursor, `ctor_ind` has the constructors and `recs` lacks the
    recursor; `ind_ok`'s constructor clause (`has_canon` of the
    constructor's inductive) is false there, so `kh` and `kh_hyp` are.
    `export_kh` assumes `kh_hyp` at every cutoff, so its hypotheses are
    unsatisfiable for any export with a constructor: the end-to-end
    statement is vacuous on real exports. Every proof is still valid; it
    is the theorem's scope that is empty.
    FIX CHOSEN: MATCH NANODA, NOT THE EXPORT ORDER'S IDEAL. nanoda checks
    each constructor's and recursor's type in the environment up to it --
    mid-block, constructors without their recursor -- and treats an
    inductive as a structure from its declaration alone (`get_structure`:
    one constructor, no indices). So the theory, not nanoda, gives way:
    (1) `ind_ok`'s constructor, structure and field-count clauses hold
    once the inductive's shape is known, not unconditionally; a probe
    (full verify with the weakened clauses) broke 7 of 3588 proofs: three
    where a recursor is present (iota, `cr_env_of`) and four structure
    steps (unit eta, structure eta, projection typing). (2) STRUCTURES
    REBASED: the judgment sees a structure from its declaration tables,
    as nanoda does. Stages: S1 `has_canon` (a canonical recursor exists)
    renamed `has_rec`; S2 `struct_decl` -- the structure's shape read off
    `struct_ctor`, `ctor_np`, `ctor_nf` and the constructor's declared
    type -- and `has_canon := has_rec || struct_decl`, `canon_shape` the
    recursor's shape when there is one and the tables' otherwise (equal
    when both are); S3 the structure soundness proofs read declaration
    facts, not recursor facts; S4 the weakened clauses, the three
    recursor-present fixes, and the export's certification. Mid-block,
    between a structure and its constructor, nanoda's structure steps
    read the constructor's tables (`ctor_num_fields`), which are absent,
    so no structure fact is needed there.
    S2/S3 DONE (structures rebased). `dom_code::struct_decl(sig, s)`: an
    entry in the structure table whose constructor is declared with its
    parameter and field counts, the structure's and constructor's types in
    canonical form over the shape the tables give (`struct_rd`,
    `ind_core`), fields typed by parameters -- read off the declaration,
    no recursor. `has_canon := struct_decl || has_rec`; `canon_shape` is
    the canonical recursor's shape where there is one, else the tables'
    (opaque, with `canon_shape_rec` / `canon_shape_struct`). Where both
    exist they agree: `rec_scope_g` states it, certified at the export
    from `ind_ok_hyp`'s structure and field-count clauses
    (`kclaims::struct_agree`, `twin_scope_at`). The constructor machinery
    is indexed by a shape in scope, not a recursor
    (`dom_rec_ty::ind_scope`; `dom_iota::*_s`, `iota_sr::*_s`,
    `kiota::ctor_params_typed_s`/`ctor_arity_at_s`; the recursor versions
    wrap them), and the kernel's structure steps read the structure's
    facts from `dom_proj_sound::struct_sem` (`kstruct::struct_facts`,
    `canon_scope`), which now states them of the structure: in scope,
    never a proposition, its and its constructor's types closed types. The
    recursor-stripped signature (`ti_strip::strip`) also hides the
    structure table, so its derivations still have no structure rule.
    Model hypothesis change: `struct_sem` (part of `sig_sr`) gains
    `never_prop` and the two closed-type facts, which the recursor's
    interpretation (`rec_model`) used to supply.
    S4 (remaining): weaken `ind_ok`'s constructor/structure/field-count
    clauses to hold once the shape is known. A probe leaves the kernel's
    K step and projection step, which reach a constructor's inductive by
    typing: K through nanoda's own check that the major premise's head is
    the recursor's inductive (to thread into `cwh_k`); the projection
    through a head-injectivity argument for an inductive of unknown shape
    (nanoda's `reduce_proj` checks only that the head is a constructor);
    and the structure steps through a clause that a structure with a
    declared constructor has a known shape.
    S4 DONE (the vacuity is gone from the statement): `ind_ok`'s
    constructor and field-count clauses hold once the inductive's shape is
    known (`has_canon`), its structure clause once the structure's
    constructor is declared -- when nanoda's kernel can use the structure.
    Mid-block, an inductive without its recursor (not a structure) is
    constrained by none of them. Two kernel steps reached a constructor's
    inductive by typing and are justified without its shape: K, through
    nanoda's own check that the major premise's head is the K recursor's
    major inductive (`expr::get_major_induct` now states what it reads;
    `kclaims::k_rec`, `k_rec_canon`: that recursor is in the fragment, so
    the inductive has a canonical recursor); the projection, as nanoda's
    `reduce_proj` does (the head is any constructor): a constructor of an
    inductive of unknown shape is no term of a structure's application
    (`kiota::foreign_ctor_absurd`, over `dom_fund::tf_head_red` -- a type
    former's full application reduces only to its own applications, its
    shape unknown). New per-constructor facts in `ind_ok` (and so in
    `ind_ok_hyp`): `ctor_form` (its declared type a telescope ending in its
    inductive at its level parameters, fully applied; the inductive a type
    former) -- what nanoda's block check establishes, certified for simple
    blocks by `block_ok` (to certify at the export next) -- and
    `ctor_sem` (its inductive a semantic constant: the rank bound
    `rec_model` states for an inductive with a recursor; a model
    hypothesis, B7).
    `ctor_form` CERTIFIED: a tested-input check in the constructor arm
    (`inductive::ctor_form_ok`: the declared type, read literally, is a
    telescope over its inductive at the constructor's universe parameters,
    fully applied; the inductive's type ends in a sort), recorded in
    `ctor_e2_cert` with the inductive's tables there; the export lifts it
    to every cutoff (`export_sound::ctor_forms_at`), and `frag_env_of`
    takes it as it takes `iota_syn`. `ind_ok_hyp` keeps `ctor_sem` only.
    OBSERVED DIFFERENCE: nanoda's constructor arm checks a constructor's
    inductive exists and its parameters, not that its type ends in that
    inductive; a constructor declaration outside its inductive's block
    (not among the block's constructors, which the block check rebuilds)
    would otherwise go unchecked in form. Lean exports never have one
    (Init: 57424 declarations).
    CONSTRUCTOR CLAUSES CERTIFIED (`kclaims::ctor_clause`: a constructor
    of an inductive of known shape is among its constructors, with its
    field count). Two tested-input checks (a53cfde): the constructor arm
    checks its inductive lists it at its index (`ctor_listed`, collected as
    `all_ctors_listed` in `ex_bound`); a single-motive recursor's rules are
    its major premise's inductive's constructors in order, with their field
    counts (`rules_listed`, in `rec_arm_ok`). The export certifies the
    clause at every cutoff and locals (`export_sound::ctor_clauses_at`: with
    a canonical recursor, `ctor_clause_rec` -- the twin keeps the rules'
    constructors and counts; a structure known from its declaration,
    `ctor_clause_struct`), and `frag_env_of` takes it as an input.
    `ind_ok_hyp` is now: `rec_small`, `sig_sr`, every recursor interpreted,
    `ctor_sem`, and the structure clause (a structure with a declared
    constructor is a smashed structure of the model: field kinds and the
    proposition conditions of the `struct_of` slice -- the boundary).
    RANKS ORDER EVERY TYPE: `metatheory::jrank` now also requires that,
    in the twin, every constant's type mentions only lower-ranked
    constants (`types_ranked`, `dom_model::consts_ranked`); the export's
    position ranks witness it (`export_sound::ranked_at`: a type at its
    declaration's certificate, a recursor's canonical one by `twin_types`,
    mentions only earlier declarations -- `type_crank`). So every declared
    axiom-like constant is semantic (`dom_model::sem_const_of`), and
    `ctor_sem` left `ind_ok_hyp` (`frag_env_of` derives it). `ind_ok_hyp`
    is now `rec_small`, `sig_sr`, every recursor interpreted, and the
    structure clause.
    THE MODEL'S SEMANTIC CONSTANTS FROM THE RANKS: `sig_sr`'s semantic
    constants -- each recursor, its inductive and constructors, each
    structure and its constructor (`rec_model`, `rec_model_p`,
    `struct_sem`) -- are declared constants, so the ranks give them
    (`kclaims::sig_sr_of`, from `iota_syn`'s scope and the inductive's
    side). `ind_ok_hyp` takes `sig_sr_h`: `sig_sr` without them
    (`rec_model_h`, `rec_model_p_h`, `struct_sem_h`). One table fact joins
    `tables_ok`, certified as the others (`env_model::tables_ok_at`): no
    recursor is in the constructor tables (a declaration is one kind).
    A SECOND VACUITY, FOUND AND FIXED: `sig_sr`'s level facts
    (`dom_levels::sig_lps`, in `rec_model` and `rec_model_p`) asked that
    every local of the stripped signature be fixed by every level
    substitution, and `frag_hyp` asks `ind_ok_hyp` at every locals map --
    so a local `Sort u` refuted it, and `kh_hyp` was unsatisfiable for any
    export with a recursor (the claims held vacuously there). `ti_strip::strip`
    now drops the locals too: it types closed terms only (rule bodies,
    constructor and recursor types), and its derivations still weaken to
    the full signature. No proof used the stripped signature's locals.
    THE LEVEL FACTS CERTIFIED: with no locals, `sig_lps` is what the
    certificates say -- each constant's type and value over its own
    universe parameters (a twinned recursor's canonical type,
    `twin::canon_elp_sig`), and no recursor rules to check
    (`export_sound::lps_at`, cycle-free: it reads the certificates, not
    the fragment). It left `rec_model_h` and `rec_model_p_h`;
    `frag_env_of` takes it as an input.
  - **B7** the model's facts (`rec_model_h`, `struct_sem_h`): typed rules,
    fields typed and blind, closed types, from the canonical form and the
    certificates (the semantic constants are done, above).
  - **B8** `kh_hyp` loses `ind_ok`; what is left is the fragment's
    boundary (single-motive, field kinds, interpreted recursors,
    structures in the slice), to be widened after.
- **S6.6c**: literals through `Nat`.

Out of the fragment until the model grows: large eliminators of Prop
inductives at non-Prop instances (`Eq.rec` into Type) and the kernel's
structure eta at structures outside the `struct_of` slice (dependent
fields: `Sigma`, `Subtype`); the slice's widening is its own arc.

### Rank-stratified strip (2026-10-10, R1-R3 done)

FOUND: the model's typing facts (`ty_closed`, `rule_typed`,
`fields_typed`, `rule_typed_g`) are stated in `ti_strip::strip(sig)`, with
no recursor or structure at all: an inductive's, constructor's or
recursor's type, and a rule body, must be typed without any iota,
projection or structure eta. nanoda checks a declaration in the
environment before it, where every earlier recursor and structure
reduces. So the facts cannot be certified as stated; a type whose
checking needs an earlier recursor's iota is accepted by nanoda and
outside the model. Direction (the user, 2026-10-10): align with nanoda.

Why the strip exists: soundness's Iota case calls soundness on the rule
body's derivation, which must be smaller -- it was `inode` (0 without
Iota/RecEta nodes, 1 with), decreasing because the stripped signature
fires none. R1 DONE: soundness decreases on `irank` (1ef011d);
`ti_strip::strip_below` with `strip_below_zero` (it is `strip` below rank
0) and `strip_below_valid` (a derivation below rank `r` is one of the
signature, `irank <= r + 1`, given `iota_ok`); `ti_valid::sig_ext` admits
the same constants and ranks in place of `def_ok` (2dc5495).
R2a: `dom_levels::sig_lps` holds below every rank (`sig_lps_below`) --
the kept recursors' rules over their own parameters too -- certified as
before (`export_sound::lps_at`, with `rules_at`) (1a379a9).
R2 base: below a rank the recursor conditions hold
(`ti_strip::iota_ok_below`: a kept recursor stays canonical --
`canon_below`, fewer recursors leave its fields' kinds, `psimple_shrink`
-- and unique, any other kept one being the signature's); so a
derivation below a rank is one below any higher rank
(`derivable_below_mono`) and of the signature (`derivable_below`)
(3541958).
R2b-1: a rule's body is typed below its recursor's rank
(`dom_rec_end::rule_typed` in `strip_below(sig, rk(c))`): it may use
every lower-ranked recursor and structure, as nanoda's check of the
recursor has them. Soundness's Iota case hands the oracle of that level
(`strip_below_valid`: those derivations measure at most `rk + 1`, the
redex `rk + 2`); `dom_iota_sound::sound_iota` and the telescope lemmas
take it; the field facts still at rank 0 reach it by
`dom_sound::oracle_down` (ee19629).
R2b-2a: a recursor's closed types -- its own, its inductive's and
constructors' (`rec_model*`) -- and a Prop-only recursor's rules
(`iota_gen::rule_typed_g`) are typed below the recursor's rank too.
Helpers take the level (`dom_levels::closed_conv(sig, rr, ..)`,
`iota_sr::const_lv`) with `iota_ok(sig) || rr <= 0`
(`ti_strip::derivable_up`); subject reduction's `sr_ok`/`srg_ok` carry
`iota_ok`; `kstruct::canon_scope` returns the level its facts hold at
(7270ccf).
R2b-2b: an inductive's field types are typed below the inductive's rank
(`dom_code::styped`, `dom_psimple::ptyped` and their parts take the
level; `ftyped`, `pfield_ok`, `fbnd` use `rk(ind)`; the field lemmas of
`dom_lift`/`dom_psimple` read it off their inductive). A recursor
reaches them from its own rank: its inductive ranks below it
(`dom_rec_ty::ind_below_rec`, from its type's major premise and the rank
bound of a semantic constant). Lifting a fact typed above rank 0 to the
signature needs its recursor conditions, so `sig_sr`, `canon_ok` and
`canon_sr` carry `iota_ok` -- not a new hypothesis: the kernel's
signature has it, and `sig_sr_of` takes the one `frag_env_of` derives
(6d203bf).
R2b-2c: a structure's and its constructor's closed types are typed below
the structure's rank (`dom_proj_sound::struct_sem`, `struct_sem_h`;
`kstruct::struct_facts`, `canon_scope` -- now always at the inductive's
or its recursor's rank). R2 DONE: no model fact asks typing without the
lower-ranked recursors and structures; each is at the rank of the
declaration nanoda checks it with.

The plan:

- **R1** `strip_below(sig, r)`: recursors and structures of rank below
  `r`, no locals (`strip(sig) == strip_below(sig, 0)`). Soundness
  decreases on `irank(sig, d)`, one more than the highest rank of a
  recursor an Iota/RecEta node of `d` fires (0 without); a derivation of
  `strip_below(sig, r)` is one of `sig` with `irank <= r`
  (`strip_below_valid`, as `ti_valid::d_ext` with equal ranks in place of
  `def_ok`; it needs `iota_ok(sig)`, which an Iota node gives).
- **R2** each fact at its own level: recursor `c`'s in
  `strip_below(sig, rank(c))`, a structure's at its rank; the Iota case
  hands the oracle of that level.
- **R3** certified at the export: the declaration's typing at its
  certificate's cutoff extends to `strip_below(jsig, rank)` (`derivable_ext`;
  everything before it in position is below it in rank).
  DESIGN POINT (found 2026-10-10, after R2): the judgment's ranks are
  CHOSEN (`metatheory::jrank`: any ranks with `rank_ok` and
  `types_ranked`), not the export's positions, so "before in position,
  below in rank" does not hold of them. The way through is the one
  `types_ranked` took: put the model's typing facts, stated of the
  ranks, into `jrank`'s choice; the export proves the position ranks
  meet them (`export_sound::ranked_at`), so the chosen ranks do too, and
  the facts leave `ind_ok_hyp`. The work is that existence proof: each
  declaration's certified typing at its cutoff (`types_at`, the twin's
  canonical rules) lifted into `strip_below(jsig, position)`
  (`ti_valid::derivable_ext`; `ti_strip::iota_ok_below`).
- **R3a** the closed types. `jrank`'s choice adds `types_typed`: where
  the recursors are in the fragment, every constant's type is typed with
  only the recursors and structures ranked below it
  (`dom_rec_end::types_below`). It is conditional on `iota_ok` because
  the judgment's `iota_ok` comes from the fragment (`kclaims::frag_env_of`),
  which now consumes these facts; the export proves the implication at
  the positions, the claims use it once `frag_env_of` has `iota_ok`
  (`frag_congr` moves `iota_ok` across ranks). The witness
  (`export_sound::typed_below_at`): each declaration's certified type at
  its cutoff, its canonical one for a twinned recursor, extends into
  `strip_below(twin at positions, position)` (`cut_ext`: the cutoff's
  recursors and structures are table keys, so declarations before it,
  `table_declared`). The closed-type facts leave `rec_model_h`,
  `rec_model_p_h` and `struct_sem_h`; `kclaims::sig_sr_of` derives them
  (`ty_closed_at`, level instances by `ti_level::d_ls`), with a recursor's
  constructors and inductive below it because its type has them in its
  minors and major (`dom_rec_minor::ctor_below_rec`, `ind_below_rec_g`).
  TRADEOFF: a structure's constructor's type is now typed below the
  constructor's rank, not the structure's. That is what nanoda checked:
  the constructor after the structure, whose structure-eta entry is
  then in scope (it comes with the inductive's declaration,
  `env_model::struct_ctor_entry`). `kstruct::canon_scope` returns the larger of
  the two ranks; `struct_cx_typed` lifts at the constructor's.
- **R3b** the fields. Two findings. (1) No strengthening: nanoda
  types each field on its own (`inductive::ctor_cert_ok`,
  `kinfer_claim` of the binder type), with the parameters and earlier
  fields as locals; the model wants a closed field typed in the empty
  context. Plan (R3b-2): rebuild that derivation structurally (head
  from R3a, arguments by induction, sort matches by type uniqueness and
  sort injectivity in the certified typing), no consumer rework.
  (2) Ranks: the model evaluates a field's code at its inductive's rank,
  so its constants must rank below the inductive. nanoda checks
  constructors with only the block's inductives added, but over a block
  bound the parser supplies (`mutual_block_sizes`), and a constructor's
  own certificate is at its own position, after the earlier
  constructors -- nothing certified it. TRADEOFF (user's choice): a
  tested-input check, `check_inductive_declar` tests each constructor
  against the environment before its inductive (`TcCtx::consts_known`;
  a single block's own name, `inductive::block_names`), never failing
  on Lean exports (Init.Core, Init). R3b-1 (done): certified as
  `inductive::ctors_known` inside `block_cert`; `jrank`'s choice gains
  `ctors_ranked` (`dom_rec_end::ctors_below`), witnessed at the
  positions (`export_sound::ctors_below_at`, `ctor_known_at`); the
  hypothesis keeps only the fields' shapes (`dom_canon::capp`, `pcapp`;
  `dom_code::fields_typed_h`), and `kclaims::fields_of` gives the ranks
  (`dom_canon::field_consts`, `ranked_of`, `fields_typed_of`). The shape
  (an application of constants, none the inductive, a constructor or a
  recursor) stays a fragment-boundary hypothesis.
  R3b-2 (done for closed fields): `dom_field_ty::simple_rebuild` types a
  closed simple type nanoda typed inside a constructor's telescope in the
  empty context below a rank -- head from R3a, arguments by induction,
  each retyped at its domain's sort by the level equality type
  uniqueness and sort injectivity give in the certificate's signature
  (`ti_spine::spine_ty`, `ti_sr::uniq`, `dom_fund::sort_inj_chain`).
  `jrank`'s choice gains `fields_typed_r` (`dom_canon::fields_ty`),
  witnessed at the positions (`export_sound::fields_ty_at`:
  `field_cert` inverts the constructor's certified type to the field,
  `dom_field_ty::tel_inv`; `field_ty_one` instantiates its levels and
  rebuilds; `twin_facts`, `cert_sig_facts`). TRADEOFF: the rebuild needs
  the heads of a closed field's type to take sorts syntactically
  (`dom_field_ty::sort_doms`), else the sorts' match lives under the
  telescope's binders and is strengthening again; it replaces the closed
  fields' typing in the hypothesis (`fields_typed_h`). Lean's type
  formers (`Prod`, `List`, ...) take sorts. R3b-2c (done): the fields
  over the parameters, the same rebuild in the parameters' context
  (`dom_field_ty::prebuild`: the parameters' variables are leaves typed
  at their sorts, the field lowered past the earlier fields,
  `rec_canon::plow`; the context well formed from the inductive's type
  below its rank, `ti_beta::pi_tele_wf`), certified at the positions
  (`export_sound::pfield_ty_one`) as `fields_ty`'s second clause
  (`dom_canon::pftyped`); the boundary over the parameters is
  `dom_field_ty::psd`. `fields_typed` now holds of a canonical inductive
  from the certificates and the boundary alone; what stays assumed of
  the fields is their shape (`capp`, `pcapp`) and that their heads take
  sorts (`sort_doms`, `psd`).
- **R3c** `rule_typed`: nanoda never types rule bodies, it converts the
  declared rules to the ones it generates, so this is the theorem that
  canonical recursor rules are well typed, not a certificate lift.
  R3c-1 (done, interpreted recursors): `dom_rule_ty::rule_typed_of`, from
  the recursor's and constructors' types below their ranks (R3a) alone,
  so no new export witness: the rule's binders are well formed (the
  recursor's head binders, `pi_tele_wf`; each field binder the
  constructor's, renamed past the motive and minors, `ti_meta::d_ren`),
  the minor's variable is applied to the field variables and the
  recursive calls (each the recursor at the binders' variables and the
  field, `spine_build`), at the identities of the substitution calculus
  (`fld_dom_id`, `vsub_vars_lift`), and its type is the minor's end
  (`dom_rec_minor::minor_end`). `rule_typed` leaves `rec_model_h`;
  `kclaims::sig_sr_of` derives it. R3c-2 (done): `rule_typed_g` for the
  other recursors (indices), in `rec_model_p_h`. The R3c-1 construction
  carries over except at the recursive calls' index arguments: arbitrary
  terms (not simple types, so not rebuilt as in R3b) to be typed at the
  recursor's index domains, which needs inversion of the recursive
  field's type (`ti_spine::spine_ty`), hence `sig_sr` -- held at the
  constructor's certificate's cutoff (its `kh`), not below the
  recursor's rank. Plan: invert there, extend into the position-ranked
  twin below the recursor's position (`export_sound::cut_ext`; the
  constructor precedes the recursor), certify as a further `jrank`
  choice conjunct (R3b's pattern), and generalise `dom_rule_ty` over
  the indices (general analogues of `dom_rec_minor::minor_split`,
  `minor_end`, `msds_ih`). Done as planned: `dom_rule_g::rule_typed_g_of`
  given `idx_typed`; `idx_typed_of_ctor` from the constructor-side fact
  (`ctor_ctx_to_rule`: `ren_field`'s renaming, then weakening past the
  later fields; `idx_dom_id`); certified at the positions
  (`export_sound::ctor_field_s0`, `ctor_idx_s0`, `ctor_idx_cert`) as the
  `jrank` choice conjunct `idx_typed_r` (`dom_rule_g::idx_all`).
  `rule_typed` and `rule_typed_g` are now theorems: the rule typings
  leave the model's hypothesis entirely.
- **`twin_ok` stays a hypothesis (decision 2026-10-11).** nanoda accepts an
  exported recursor when its type and rules `def_eq` the generated ones
  (`inductive::rec_conv_old`), but that conversion is untyped (the
  exported rules are never typed, so `def_eq_claim`'s typed half `cw`
  says nothing of them) and runs in the block check's temporary
  environment, where `kh` is not established. Structural equality is not
  an option either: Lean's export strips `outParam`/`optParam`/`autoParam`
  from recursor binders (S6.6b B4c: Init 97 types, 118 rules). The gap
  to nanoda: an exported rule that is an ill-typed expansion of the
  generated one passes nanoda's check; the judgment assumes it converts
  as a typed term. Options declined for now: re-checking (inferring the
  exported rules, re-running `def_eq`) in the recursor's own
  environment, or an annotation-aware equality test.

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

### Widening to real exports: projections first (planned 2026-10-11)

MEASURED: Lean's Core export leaves the fragment at its 13th declaration
(`MonadReaderOf.read`: a projection in its value), then `Eq` (indexed,
`rec_small`) at 16 and `Quot` (built-ins, `frag_hyp`) at 41. `export_kh`
now concludes at a cutoff from the hypotheses at the cutoffs up to it
(538d755), so a prefix inside the fragment is covered; widening the
fragment is what extends it. Order chosen: projections, then indexed
families with Prop large elimination, then `Nat`/literals/`Quot`.

Projections need three steps; `MonadReaderOf.read` (`m ρ` with
`m : Type u → Type v`) needs all three, because its recursor already leaves
the fragment (`m` is not Sort-typed: `rec_small`, `rec_frag_l`,
`pfield_ok`; `m ρ` is no `field_kind`, so no `rec_canon`, so no `iota_ok`).

- **K, the kernel step (on today's slice) -- DONE.** `frag_term` admits
  `Proj(i, x)` for a fragment `x`; `proj_reg::cc_proj` (empty until now,
  since the claim was vacuous) is proved by typing the projection with
  `kstruct::struct_proj_typed` and reusing `ci_proj` for the kernel's
  field type. Projections of structures outside the slice stay out
  through `ind_ok_hyp`'s structure clause, not through `frag_term`.
  Originally: `Proj` leaves `frag_term`'s
  exclusions; `infer_proj`'s `kcc` (now vacuous) is derived: the subject's
  `cc` by induction, its type converted to `S.{us} ps`, the structure
  clause gives `struct_of`, the field walk gives `proj_ty`, `never_prop`
  gives `!proj_prop`, then a `ProjCong` node (`kiota::proj_cong_d`).
- **Slice 1: closed and `psimple` structure fields.** `struct_of` asks
  `psimple` instead of `pvar_field`. New: `ceval_mem` (a field type's code
  at typed parameter codes is a member of its denotation; via
  `dom_canon::tf_step`, `dom_adeq::mem_app_intro`), the ⊇ inversion (a
  member of `F[ps]` at some typed parameter codes) for `proj_iota_sup`,
  and field types independent of earlier projections (from `plow_vsub`).
  Re-proofs in dom_proj_sound, dom_adeq_proj, ti_sr, kstruct.
- **Slice 2: parameters that are not sorts, fields headed by a parameter
  (`m ρ`).** `ceval` gains the applied-variable case, `psimple`/
  `field_kind` the applied parameter, the Sort-only gates go, and the
  logical relation relates Pi-typed parameters. On both the recursor and
  structure sides.
- **Later: dependent fields** (`Sigma.snd`, `Subtype.property`): table
  entries that depend on earlier fields (Σ-codes).

**Coverage by dependency closure (measured 2026-10-12).** Lean's
Core reaches `Eq` at its 16th declaration, so no long Core prefix is in
the fragment (see "Open: large elimination out of Prop"). The theorem
holds of any export nanoda accepts, and a declaration's dependency
closure is an export, so a declaration whose closure is in the fragment
is covered by checking that closure. Measured on Core's 3875 declarations
(scratchpad script approximating the gates): 235 today (54 before the
correction below); 1208 with every
shape gate widened (structure fields over the parameters, function-typed
fields, `outParam`/type-former/value parameters, `And`-like large
elimination, `Sort u` inductives, Prop-only recursors at the kernel side);
1557 with literals and the Nat built-ins too. Removing one gate from the
widened set costs: structure fields 774, non-dependent field types 640,
`outParam` 322, type-former parameters 248, polymorphic fields 241,
`And`-like elimination 218, `Sort u` 173, Prop-only recursors 52, value
parameters 35. Polymorphic fields (`Bind.bind : {α β} → ...`) have no
finite canonical code (a dependent Pi over a sort), so the table design
excludes them.

**Slice: structure fields over the parameters (started 2026-10-12).**
`struct_of` admits `psimple` fields (then arrows). Groundwork:
`dom_canon::ceval_mem` (a simple field's code is a member of its type,
a former's application through its code function); the field kinds ask
of a nested former that its parameters are types (`rec_canon::tparams`),
its level arity, and that it is no constructor; `sig_ext`/`env_le` carry
the tables' stability. Typed parameter codes: a former's type over
sorts lies below the arrow chain of its sorts (`dom_canon::sbound_mem`),
so the codes projected onto its typed approximation's inputs are types
(`proj_chain_t`, `tf_spine_t`); with them a field over the parameters
has its entry as a member (`field_entry_mem`, `proj_entry_ps`).
**Rule ProjIota takes the constructor's parameters typed** (user's
choice, 2026-10-13, as Iota's in P4b-2j): a field mentioning a parameter
twice needs that parameter's members joined, so its denotation
join-closed, which only its typing's soundness gives; the soundness
induction has no other route to it (generation yields `derivable`
facts, not derivations to recurse on). `ti_syntax::proj_pjs`; producers
from the telescope (subject reduction) or the relation's parameter
equations (`pjs_peq`, `pargs_at_cl`); the transformers carry them.
Projection side done (493f213): a field not a parameter is equal at a
sort at two parameter lists equal at their sorts and two equivalent
instances (`dom_adeq_proj::sfield_conv`), which serves uniqueness of
types, subject reduction, projection adequacy and struct eta; the model
side dispatches on the field's kind. Open: the recursor's eta for
smashed structures (`dom_rec_eta` reads parameter fields), then the flip.

**Correction (2026-10-13): parameter-typed fields were refuted.**
`rec_model` asked every non-recursive field `ranked` and `rec_model_h`
asked it `capp`, both false on a variable. So for an interpreted
recursor (large elimination, an inductive never a proposition: `List`,
`Prod`, `Option`, every type class) whose inductive has a
parameter-typed field, `rec_hyps` and the fragment hypothesis were
unsatisfiable (`rec_hyps` with `pvar_at` proved `false`). The P3b
parameter machinery verified but never applied there, and the coverage
script, which admitted `psimple` fields everywhere, overstated the
fragment: 54 of Core's 3875 declarations by dependency closure, not
235. Fixed: `pranked`/`pcapp` (a parameter's variable allowed) in
`rec_model`/`rec_model_h`; `dom_iota::r2l_ok` asks `ranked` of closed
fields only (`dom_psimple::pranked_simple`). The refutation no longer
goes through, nor does the one through the eta step's hypotheses.

### The conditional theorem (started 2026-10-12)

Goal: the end-to-end theorem for EVERY export, conditional on named
metatheory hypotheses `H_meta` about Lean's type theory (Pi/sort
injectivity, type-former injectivity, unique typing, subject reduction for
the kernel's reductions), which are open for full Lean. Inside the
fragment the domain model still discharges them; outside, they are
assumptions, stated once.

Design: the environment carries a ghost flag `EnvSpec.full`, which the
kernel's own relations ignore. Lean's rules that the model does not
interpret (`RedG`, `LitTy`, `ProjG` below) fire only when
`sig.ienv.full` holds; `iota_ok` (what the model needs) includes
`!full`, so every model proof sees them as vacuous. The kernel's model
environments keep `full: false`, so every existing result is unchanged.
The flag rides in the environment rather than the signature so that
every signature operation (`strip_below`, `sig_with`, `sig_swap`, `twin`)
and `EnvSpec::sub` (which asks equal flags) preserve it, and the
structural lemmas carry the new rules directly.

The claims stay per mode: the fragment's at `jsig` under `kh`, the full
judgment's at `jsig` over the flagged environment under the hypotheses
`khF`. Mode is fixed per export, not per prefix: switching `jsig` to the
full judgment exactly where `frag_env` fails was tried and dropped
(target/work/jsig_switch_experiment.patch), since weakening a derivation
from an earlier prefix then needs the fragment to be closed under
prefixes, which nothing proves.

- **`RedG` -- DONE.** One rule for the kernel's contractions beyond
  beta/delta/zeta, `full_red::full_red`: iota by the environment's own
  rule (`rec_ready`/`rec_result`), Nat folding, quotient reduction,
  projection of a constructor application, Nat-literal unfolding, String
  expansion -- `pstep`'s redexes. Both sides typed at `t`, `t` a type.
  K-like reduction needs no rule: the kernel swaps the major for a
  constructor by proof irrelevance, then iota fires. `full_red`'s lemmas
  carry it through substitution, swap, close, level instances and
  environment extension, one proof per operation.
- **`LitTy` -- DONE.** A literal at `Nat`/`String` (`full_red::lit_ty`,
  the kernel's inference), the type typed as a premise; shaped like
  `Local`, and `gen_ok` gains the literal case (under `full`, so the
  fragment's untypability of literals is unchanged).
- **The hypotheses -- `meta_hyp::meta_ok`.** Uniqueness of types, Pi and
  Sort injectivity, Pi not a sort; `meta_of` proves them from the model
  for the fragment. Generic lemmas move to `meta_ok` (`ti_spine`'s `_m`
  forms so far). Subject reduction for `RedG` is the remaining hypothesis
  to state.
- **Structure and unit eta -- DONE.** `RedG`'s side condition is
  `full_conv`: a reduction, or `eta_g` (the other side is a structure's
  constructor applied to parameters and this side's projections), or a
  unit-like type (a structure without fields). Levels and parameters are
  left free: both sides typed alike pins them, as in Lean.
- **`ProjG` -- DONE.** `ProjCong` at any structure (`gstruct`: a
  structure-table entry whose constructor shares its level parameters,
  closed type): the field is the constructor type's binder at the
  instance, over the parameters and the subject's earlier projections
  (`gproj_ty`, the kernel's `infer_proj` walk), with Lean's Prop
  restriction (`proj_prop ==> is_zero`). Generation records a subject
  convertible to the projected term, since a dependent field's type
  mentions the subject.
- **Two disjoint worlds -- DONE.** The fragment's structure rules
  (`ProjCong`, `ProjIota`, `StructEta`; `Iota`/`RecEta` through `iota_ok`)
  fire only in non-full environments, `ProjG`/`RedG`/`LitTy` only in full
  ones; `sig_ext` and `env_weaken::env_le` ask equal flags, so weakening
  stays in one world. In full mode `jsig` is `jsig_raw` -- Lean's
  declarations as they are, without the canonical twin the model needs,
  so no `twin_ok`.
- **The full hypotheses -- `kclaims::kh_full`.** `meta_ok`, `h_sr_red`
  (subject reduction for `full_red`) and `h_str` (strengthening for
  closed terms) at every locals, with the
  environment facts the checker certifies (`fv_free`, `env_wf`, `sig_wf`,
  `lev_ok`, level-parameter facts, closed rules); no Church-Rosser
  (`cr_env`'s confluence is false for real exports) and no twin.
- **`kh = kh_frag || kh_full` -- DONE.** The claim library (`kclaims`,
  `jkernel`, `kbind`, `kiota`) holds in both worlds: subject reduction for
  parallel reduction (`jkernel::sr_pstep` under `sr_ok`) gets full-mode
  leaves (`redg_d`: a `RedG` node from `h_sr_red`; `delta_d`, generic;
  literals unfold), projection congruence goes through `gproj_cong` /
  `kiota::proj_cong_m`, unit eta is a `RedG` node, and uniqueness and
  Pi injectivity come from `kh_meta` (the model's in the fragment, the
  hypotheses in full). The kernel's contracts are unchanged: they
  instantiate non-full environments, where `kh` is `kh_frag`.
- **Fragment-only claim lemmas (the gaps for full-mode certificates).**
  Once restricted to `!denv.full`, since their arguments were the
  fragment's (untypable literals, canonical recursors, the model's
  structures). The kernel's literal comparisons are untyped conversions in
  both judgments (`nat_unary`: a numeral and its literal reduce to the
  same unary numeral), so the vacuity lemmas they used are gone.
  `cwh_to_lit` (a `Nat.succ` numeral folded back to its literal):
  `kh_full` asks `nat_decl_ok` (an export declaring `Nat.succ` declares
  `Nat` at a sort, with no universe parameters -- checkable on the
  declarations; nanoda folds by name and checks neither). A typed numeral
  has its head declared (generation), so the literal is typed at `Nat`,
  subject reduction types the numeral there, and uniqueness chains its
  other types (`kclaims::to_lit_full`). Closed in both worlds since: `cw_of_step`/`cw_of_ceq` (Church-Rosser: `kh_full` asks
  `nat_ext::cr_ext` -- the fold-free environment's syntactic
  confluence conditions and `h_nat_ext`, the Nat-extension agreement
  Lean's kernel rests on -- so untyped conversion joins with folding off
  and lifts back), `cwh_quot_leaf` (a parallel step, typed by subject
  reduction), `ci_lit` (a `LitTy` node at the declared `Nat`/`String`).
  `cw_eta` (structure eta, `full_eta`): along the certified constructor
  telescope (`ctor_typing::struct_ok`, `ctor_form`, both in `kh_full`)
  `x`'s projections are typed in turn, so its eta expansion is typed,
  converts with `x` (`RedG`) and field by field with `y`; for a
  structure always in `Prop`, proof irrelevance. Open: a
  universe-polymorphic structure whose sort may but need not be `Prop`
  (`eta_sort_ok`) -- nanoda types no data projection of it, so its
  expansion is not typed in this judgment.
- **Constructor typing at the inductive's parameters -- DONE
  (`full_e2`, `kclaims::ctor_at_params`).** Lean checks a constructor's
  parameter binders against its inductive's only up to conversion; the
  kernel certifies it through E2' (`tc::ctor_e2_cert`: `λ (f : C's type)
  (S's parameter binders), f params` typed). `kh_full` asks it at every
  constructor (`e2_ok`; certified per constructor -- in fragment mode
  today, the full-mode certificate comes with the dual contracts); the
  lambdas inverted and `C`, the parameters substituted type `C ps`
  wherever `S ps` is typed. Used by `cwh_eta_exp` (the kernel's eta
  expansion, which nanoda performs only on never-`Prop` structures:
  `never_prop_at`) and by `cwh_k` (K-like reduction: the constructor the
  kernel puts for the major is typed -- its parameters fit the
  inductive's arity because past it a type former's application is a
  sort and no sort is a Pi, `full_e2::spine_arity` -- so proof
  irrelevance applies) and by `proj_reg` (the kernel's projection walk:
  its stages convert to the constructor's telescope as before, the
  parameters typed by E2', the earlier projections by
  `full_eta::projs_typed`).
- **Structure eta's sort condition -- a named export fact.** A fieldless
  structure needs no projections; for the rest `kh_full` asks
  `structs_sorted` (each structure with fields is never or always a
  proposition; checkable on the declarations, and Lean's `structure`
  command rejects the others).
- **The kernel's own `Prop` test.** `may_be_prop` now carries its claim
  (the inferred sort, never zero when it answers no); the eta expansion
  and the projection claims take their full-mode condition from it.
- **Projections out of possibly-`Prop` structures** (`And.left` is one)
  **-- DONE, under strengthening.** nanoda checks only the earlier fields
  the rest of the walk mentions (`infer_proj prop`), so a non-dependent
  earlier data field has no typed projection. The constructor's type is
  a Pi telescope, so each stage of the walk is its own `whnf`
  (`keeps_bind`, recorded in `proj_reg::pwalk_ok`) and the stages are the
  telescope's syntactically. Then each stage is a type
  (`proj_reg::walk_prop_ty`): a mentioned field is a proposition by the
  kernel's check (`pprop_ok`, recorded in `infer_proj`), so its
  projection is typed (`ProjG`) and instantiates the stage; an unmentioned
  field leaves a closed body, a type without the binder by `h_str` --
  strengthening for closed terms, a metatheory hypothesis in `kh_full`
  next to `h_sr_red`. The projected field is a proposition too, so the
  projection rule types it at the kernel's field type (`walk_prop_at`).
- **Dual kernel contracts -- DONE.** `tc::kcw`/`kcwh`/`kcc`/`kci`/
  `kcprop` are each the claim at the kernel's environment and at
  `kclaims::flag` of it (the same tables, the flag set); `kdual` wraps the
  claim lemmas the kernel uses, calling each in both worlds. The check
  claim's guard is `kclaims::cterm`: the fragment's terms in the
  fragment, every term but the model's non-term `Closed` in the full
  judgment (so literals are covered there).
- **Full-mode certificates and the export theorem -- DONE.**
  `declar_cert_at` and `ctor_e2_cert` carry the full judgment's clauses
  next to the fragment's (`tc::type_cert_full`, `tc::val_cert_full`, the
  parameter term at `flag`), from the dual contracts.
  `export_full::export_kh_full` gives `kh` at every cutoff's flagged
  environment: the fragment's induction (`export_sound::export_kh`) with
  no twin, no `iota_ok` and no fragment conditions. Full-mode ranks need
  only the definitions ordered (`metatheory::jrank` chooses by mode), and
  weakening (`env_weaken::ew_*`) needs the twin only in the fragment.
  Certified: the declarations' types and values typed, `sig_wf`,
  `lev_ok`, the free-variable and level facts, `struct_ok`, `ctor_forms`,
  `e2_ok`. Named (`export_full::full_hyp`): the metatheory (`meta_ok`,
  `h_sr_red`, `h_str`), Church-Rosser with the Nat extension (`cr_ext`),
  `structs_sorted`, `nat_decl_ok`. The declarations denote no `Closed`
  (needed for the full-mode certificates' `full_term` guards): the
  parser guarantees `export_full::export_placed` (`ExportBuilder::finish`:
  the arena's stored nodes are placed, by the dag's invariant, and every
  declaration's type and value is one of them), so `export_full::placed_full`
  makes them terms; a constructor's parameter term is one because
  `ctor_param_term` walks its inductive's parameter binders
  (`e2_lift::pi_prefix`, recorded in `ctor_e2_cert`).
- **Next:** widen the fragment.
