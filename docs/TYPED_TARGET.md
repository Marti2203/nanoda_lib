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
- **Soundness is well-founded** by Iota-freeness first:
  `sound` decreases on `(inode(d), d)`. In the Iota case, derivations of
  the stripped signature have no Iota node (`ti_strip::strip_valid`), so
  soundness can use them. The telescope lemmas take a syntax signature
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
  - **B4** the comparison: a verified structural (model) equality check
    of the exported recursor against the generated one (a tested-input
    check, registered), with the tables' data fields.
  - **B5** the certificate: `declar_cert_at` for a recursor carries its
    canonical form at the cutoff.
  - **B6** the rest of `rec_canon` and `ind_ok`'s tables (the inductive's
    and constructors' type forms, field kinds, constructor tables,
    uniqueness), from the constructor and positivity certificates.
  - **B7** the model's facts (`rec_model`, `struct_sem`): typed rules,
    fields typed and blind, semantic constants, from the canonical form
    and the certificates.
  - **B8** `kh_hyp` loses `ind_ok`; what is left is the fragment's
    boundary (single-motive, field kinds, interpreted recursors,
    structures in the slice), to be widened after.
- **S6.6c**: literals through `Nat`.

Out of the fragment until the model grows: large eliminators of Prop
inductives at non-Prop instances (`Eq.rec` into Type) and the kernel's
structure eta at structures outside the `struct_of` slice (dependent
fields: `Sigma`, `Subtype`); the slice's widening is its own arc.

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
