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
- **P3, the lemmas.** PER, monotonicity, stability, head expansion,
  conversion, and the lifting lemma (a parameter related at `A` lifts to a
  field's simple type), then `tf_rel`, `cf_end`, constructor adequacy.
- **P4, the recursor with parameters.** The recursor stage generalized
  from `np == 0`: parameters in the telescope induction, the walk, the IH
  instances, the Iota cores. Subject reduction for Iota with parameters
  needs `I P ≡ I P'` to give `P ≡ P'`, which the parametric relation's
  parameter clause provides through the fundamental theorem.

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
