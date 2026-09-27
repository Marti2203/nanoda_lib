# Metatheory: from the kernel's conversion to real conversion

## Where we are

`whnf` and `def_eq` are proven against `kconv` (`src/tc.rs`): typed
definitional equality `deq_p_any` in `InferOnly` mode (`io == true`), whose
typed leaves (proof irrelevance, unit types, structure eta) consult types the
kernel infers WITHOUT checking application arguments.

`tconv` is the same relation with `io == false`: the leaves consult real,
fully checked typing. The target theorem is

> on well-typed terms, `kconv(x, y)` implies `tconv(x, y)`.

`kconv` and `tconv` share every untyped step (reduction, eta, quotient and
recursor steps, congruence). They differ only in the three typed leaves and in
the typing/conversion those leaves consult. So the theorem is: a typed leaf that
fires under `InferOnly` typing also fires under real typing, on well-typed
terms.

## Status and what is missing (2026-09-27, branch `metatheory`)

**Proven.**
- The kernel side: `whnf`/`def_eq` against `kconv`; `kconv_wt ⟹ tconv` on
  well-typed terms; the export theorem, under `kh_hyp` (`export_sound.rs`).
- Layer 1, Church-Rosser: parallel reduction is confluent (`confluence.rs`);
  eta-free conversion (`ceq`) is joinable up to universe-level equivalence
  (`conv_frag.rs`), in a real environment under `h_nat_ext` (`nat_ext.rs`).
- Layer 2 on the fragment: Pi/Sort injectivity for `ceq`
  (`injectivity.rs`), and the kernel's injectivity hypotheses with eta-free
  premises (`frag_hyps.rs`).
- Typed inversion for a typed conversion judgment (option A, see below):
  Pi injectivity, Sort injectivity and Pi/Sort disjointness for every
  derivable conversion of `ti_syntax` -- with eta, proof irrelevance,
  impredicative `Prop` and Lean's levels (`dom_fund.rs`).

**Missing.** Everything below is assumed, not proven. `kh_hyp` =
`hyps_all` + `h_sr` + `h_sr_leaf` is what the export theorem still takes.

| gap | what is assumed | why it is open | plan |
|---|---|---|---|
| full injectivity | `h_pi_inj_app`, `h_pi_inj_dom`, `h_sort_inj` over `tconv` | `tconv` has eta and typed leaves (proof irrelevance, unit-eta, struct-eta); untyped Church-Rosser cannot see them | A's typed half is DONE for `ti_syntax` (Pi, lambda, application, beta, eta, sorts with levels, proof irrelevance); open: translate `tconv`/`kconv_wt` derivations into `ti_syntax` derivations (constants, inductives, projections, literals, `let` are not in `ti_syntax` yet); B afterwards: interpret nanoda's untyped terms directly |
| uniqueness of typing | `h_unique_in` | a Lean4Lean conjecture; not a corollary of the paper's method | none yet |
| subject reduction | `h_sr`, `h_sr_leaf` (iota/quotient steps keep types) | needs injectivity and a substitution lemma for typing; recursor rules need the inductive checker's guarantees | the paper derives SR for its fragment; extend per feature |
| Nat extension | `h_nat_ext`: each built-in Nat fold is joinable, without folding, with the op application | a named trust assumption, as in Lean's kernel | plausible for Init by inspection, not proven (export of Lean 4.30.0-rc2): every folded op is structural -- `add`/`sub`/`mul`/`pow`/`beq`/`ble` by `Nat.brecOn`, `div`/`mod` by fuel helpers (`Nat.div.go`, `Nat.modCore.go`), `gcd` by `WellFounded.Nat.fix`, which runs `Nat.rec` on fuel -- so each reduces by delta/beta/iota. Not checked: whether nanoda validates these bodies when they are declared |
| features outside the paper | — | the paper covers Pi, Sigma, unit, Nat, Id, Prop with irrelevance, type-in-type | Lean's universe levels (`imax`, impredicative Prop), inductive families and recursors, K-like reduction, quotients, general structure eta, projections, Nat/String literals, `let` |
| well-typed chains | the theorem is about `kconv_wt`, not `kconv` | `kconv ⟹ tconv` for arbitrary chains is FALSE (`option1_refuted`) | the kernel's derivations as `InferWt` derivations (S4) |

## Typed inversion, option A (branch `metatheory`, 2026-09-27)

Following arXiv 2607.13662 (blueprint and errata: `docs/typed-inversion/blueprint.md`).

| stage | modules | content |
|---|---|---|
| 1-2 | `dom_compact`, `dom_typing` | compacts (a CUSL), application, stage-indexed semantic typing |
| 3 | `ti_syntax`, `ti_subst`, `ti_meta`, `ti_sub`, `ti_hred`, `ti_chain` | the typed judgment (derivation trees), renaming, substitution, head reduction, type-conversion chains |
| 4 | `dom_model`, `dom_sound` | the domain model and its soundness (Thm 2.31) |
| 5 | `dom_rel*`, `dom_proj` | the logical relation: PER, monotonicity, head expansion, stability (joint projection) |
| 6 | `dom_adeq_base`, `dom_adeq_syn`, `dom_adeq`, `dom_fund` | related substitutions, adequacy (Thm 2.35), the fundamental lemma (Thm 2.36), `pi_inj`, `sort_inj`, `pi_not_sort` (Cor 2.37) |

Differences from the paper:
- Lean levels: `Sort l : Sort (succ l)`, Pi at `imax`, `Prop` = a level
  equivalent to zero. Single type conversions do not compose across levels,
  so the relation and `pi_inj` use chains of type conversions (`tchain`),
  each link at its own sort. `sort_inj` gives level equivalence.
- Rules carry their presuppositions: congruences under both contexts, beta
  with both sides typed, eta with its domain's AND codomain's typing
  (`Eta(l, l2)`; adequacy needs the codomain's denotation join-closed at the
  argument, which only a typing derivation of the codomain supplies).
- Proof irrelevance (`Irr`) as in nanoda: any two proofs of a proposition
  convert.

## The plan the user chose (2026-09-26)

1. **A conditional theorem.** Prove `kconv ⟹ tconv` on well-typed terms from
   NAMED hypotheses — stated as spec predicates the theorem `requires`, never
   as axioms — for the properties that are research-open for Lean's theory:
   - uniqueness of typing up to `tconv`;
   - Pi-injectivity (definitional inversion for Π);
   - whatever form of subject reduction the leaves' intermediate terms need.
2. **Then a fragment.** Discharge the hypotheses for a sub-theory, following
   *Definitional Inversion, Without Normalisation* (Carneiro, Coquand,
   Frabetti Mathieu, Lennon-Bertrand, Mellies, Weirich; arXiv 2607.13662,
   July 2026), which proves inversion for MLTT with eta, Σ/unit eta, Nat, Id
   and `Prop` with definitional irrelevance — not full inductives, not K.

## Phase 1 finding: the hypotheses must be TRUE of the model first

A conditional theorem is only worth something if its hypotheses hold of the
model; if one is false, the theorem is vacuously true. Auditing `types_to`
(`src/tc_model.rs`) against uniqueness of typing found the model looser than
Lean's theory in these places:

| | defect | consequence | fix size |
|---|---|---|---|
| A | `Pi` and `Lambda` both map to `ExprSpec::Bind` | `λx:A.b` and `Πx:A.b` are the same model term; it has a Pi type (lambda rule) AND a `Sort` (pi rule), not convertible — **uniqueness of typing is false**; conversion also equates a lambda with a pi | large: 330 `ExprSpec::Bind` sites, beta/eta/typing/congruence rules and the confluence proofs |
| B | `NatLit` / `StringLit` type as `Nat`/`String` at ANY universe-level list | two non-convertible types | small |
| C | `Let` rule ignores the annotation (`val : ty0` unchecked, `ty0` not checked to be a type), even with `io == false` | ill-typed lets are "well-typed" | small (io = false only) |
| D | lambda rule does not check the binder type is a type (a `Sort`), even with `io == false` | as C | small (io = false only) |
| E | `Const` rule does not check the universe-level arity | ill-arity constants typed | small |
| H | binder rules (lambda/Pi typing, `deq_p_c`'s fresh-local congruence) only require the opening local to be absent from the body, not unreachable through the types of the body's locals | an outer local's id can be reused as the bound variable. With `a : A` and `j : P a`, `λx:A. j` got type `Πx:A. P x`; the conversion rule could likewise equate lambdas whose bodies have different types | small in the model (`unreach`); kernel side discharged from the existing scope discipline (`dbj_deep_unreach`) |
| G | binder congruence in `deq_p_c` opens with a fresh local whose type in `lctx` is unconstrained (need not be the binder type) | a typed leaf under a binder may use the wrong type for the bound variable | small (the exec side already opens with the binder's type) |

**Done (2026-09-26):** B (`8a5082c`), E (`91bb1fa`), C and D (`1fcc781`), G
(this commit's successor). For G, the fresh local has EITHER binder type (they
are convertible), which keeps the relation symmetric.

**A done (2026-09-26, branch `pi-lambda-split`):** `ExprSpec::Bind` carries a
`BinderKind` (`Pi` / `Lam`). Beta, eta and head spines match `Lam`; the lambda
typing rule types a `Lam` with a `Pi`; the pi rule types a `Pi`; application
needs a `Pi`; congruence and level substitution relate only binders of the same
kind. Telescopes are kind-indexed (`telescope_size_spec(k, ..)`,
`abstr_telescope_model(k, ..)`); Pi-peeling uses `pi_spine`. No kernel change:
the exec side already distinguished the two, and the def_eq binder walk only
gained a ghost `bks: Seq<BinderKind>`.

**H done (2026-09-26, found while planning option 3):** the rules require
`unreach(lctx, k, _)` (`expr_model::deep_absent` to some depth) for the
binder type(s) and body(ies). The kernel always opens with a level-local
one level above everything in scope, and `dbj_deep_unreach` turns the
existing deep-scope facts into unreachability, so no kernel code changed.

B–E and G are spec tightenings. The kernel already behaves this way (literals
are `Nat` with no levels, Check mode checks binders and let annotations,
`infer_const` checks arity), so they cost proof work, not kernel changes. A is
the large one. The model has to distinguish Π from λ before the metatheory can
say anything, and that touches the foundations every proof rests on.

## The hypotheses, stated (`src/metatheory.rs`)

All are spec predicates, none assumed:

| predicate | says |
|---|---|
| `typed`, `tconv`, `kconv`, `well_typed`, `is_type` | real typing; real / kernel conversion |
| `lctx_wf` | every local's type is a type |
| `env_wf` | every constant's type is a closed type; every definition's value has its declared type (delta needs it) |
| `h_unique` | two real types of one term are `tconv` (in a well-formed context) |
| `h_pi_inj_app` | `tconv(Π a1 b1, Π a2 b2)`, `arg : targ`, `tconv(targ, a2)` give `tconv(b1[arg], b2[arg])` |
| `h_sort_inj` | `tconv(Sort l1, Sort l2)` gives `l1 ≡ l2` under every assignment |
| `h_sr` | a `pstep` keeps a term's real type (given `env_wf`, `lctx_wf`) |
| `kconv_implies_tconv` | the phase-2 target: on well-typed `x`, `y` in a well-formed context, `kconv ⟹ tconv` |

Checked by hand against the model after defect A:

- `h_unique`: every typing rule is functional up to conversion. The lambda
  rule takes the body type up to conversion, which `tconv` congruence absorbs.
- `h_pi_inj`: no typed leaf can relate two Pi types. A Pi's type is a
  `Sort`, which is never a proposition (so no proof irrelevance), a unit-like
  structure, or a structure. Eta is `Lam`-only.
- `h_sr` for iota rests on the recursor rules the inductive checker
  generates; that is the classic hard case, and the reason SR stays a
  hypothesis.

### Open design question: which chains the theorem is about

`kconv` is a chain relation, and a chain between two well-typed terms can pass
through terms that are ill-typed under real typing. For example, the
expansion `x ← (λ_:A. x) bad` is `InferOnly`-typed, because `InferOnly` never
checks the argument. A typed leaf between two such terms has no real-typing
counterpart. There are two options:

1. **Arbitrary chains** (the statement above). This is the strongest
   theorem and needs nothing from the exec side. The proof has to show that
   detours through ill-typed terms add nothing, which is a
   chain-normalisation argument of research size.
2. **Well-typed chains.** Restate the target over chains whose every element
   is really well-typed. The proof becomes a straightforward induction (leaf
   transfer plus congruence). The cost is on the exec side: `def_eq` must
   produce such chains. It already visits only forward reducts of well-typed
   inputs (which are well-typed by `h_sr`) and their subterms (which are
   well-typed by generation). The eta case is the exception: it builds
   `λ(x:t2). f x` with `t2` taken from the other side, and its typing needs
   `h_unique` + `h_pi_inj`.

## Option 2 in progress (user choice 2026-09-26: option 2 first, then option 1)

**Modes.** `io` is now `IoMode`: `Real` (was `false`), `Infer` (was `true`,
what `def_eq` is proven against, unchanged) and `InferWt`. `InferWt` is
`Infer` whose typed leaves also require really typed terms: both sides
(`leaf_wt`), the proof-irrelevance witness, and the structure-eta
constructor application (`wt1`). `metatheory::kconv_wt` is `deq_p_any` at
`InferWt`.

**B: the congruence skeleton, PROVEN.** `kconv_wt_implies_tconv`: given
`leaf_transfer` (every `InferWt` typed leaf relates `tconv`-equal terms),
`kconv_wt ⟹ tconv`. It is an induction over `deq_p_c`/`deq_p`. Untyped steps
are shared, congruence (including the binder rule's fresh-local form, and a
new `deq_p_any_let_congr`) and chains transfer directly, and leaves use the
premise.

**C: leaf transfer. Here the global local context bites.** Each leaf
transfers from one core lemma, "InferOnly soundness": if `e` has `InferWt`
type `t` and real type `T`, then `tconv(t, T)`. It does NOT need uniqueness
of typing. It does need:

- Pi-injectivity in substitution form (the application case);
- injectivity of inductive-type applications (the projection case);
- **a renaming lemma** (the lambda and Pi cases). The two derivations may open
  the binder with different locals `lid` and `lid'`. Relating them means
  renaming one derivation's local to the other's, together with every local
  opened below it.

The model's local context is the arena's global ambient map, whose later
locals' types mention earlier ones. So renaming there is a simulation between
derivations under a renaming of all locals opened inside the term, with
freshness side conditions on every existential witness. The lemma is not
research-open, but it spans the whole typed family (typing, the three
leaves, chains, and the untyped rules under free-variable renaming).

**Option 3, model step (2026-09-26).** Real typing's lambda and Pi rules
are now cofinite: for EVERY local `k` unreachable from the binder, the body
opened with `k` is typed in `lctx.insert(k, A)`, with one codomain (lambda)
or one codomain level (Pi) shared by all `k`, plus a non-vacuity witness.
The `InferOnly` rules still pick one local. Instantiated at that local
(where `lctx[k]` already is `A`, so the insert changes nothing), the real
rule speaks about the same term in the same context, so the soundness lemma
needs no renaming. `InferWt`'s lambda rule also asks the abstracted codomain
not to reach the opening local: the kernel's in-scope inferred types satisfy
this, and it is what the fresh-local congruence at that local needs. The
renaming lemma moves to where it is standard: turning one real derivation
into the cofinite form when real typings are produced.

**Option 2 theorem, PROVEN (2026-09-26).**
`metatheory::kconv_wt_implies_tconv` requires `hyps` = `h_pi_inj_app`
(Pi-injectivity in the application form) ∧ `h_sort_inj` (Sort-injectivity)
∧ `h_unique_in` (uniqueness of real typing). One mutually recursive group
proves it:

- `s_sound`: the `InferWt` type of a really typed term converts to its real
  type. Case lemmas `s_app` (Pi-injectivity), `s_let`, `s_lam` (the real
  rule instantiated at the kernel's own local), `s_pi` (Sort-injectivity),
  constants via `rel_pair_deq_c`, and `s_proj`: the `InferWt` derivation of a
  projection transfers step by step (`walk_transfer`) to a real derivation
  of the same type, which uniqueness relates to the other real type. This
  avoids inductive-type injectivity.
- `leaf_transfer`: proof irrelevance, unit, and structure eta, each
  re-derived under real typing (`proof_type_transfer`,
  `unit_like_transfer`, `eta_transfer`).
- `transfer_c` / `transfer_p`: the congruence skeleton.

Uniqueness is used only for projections. Subject reduction is not needed
here; it comes back for option 1 and for the kernel producing `InferWt`
derivations.

**Binder conversion in context-extension form (2026-09-26).** Real typing
extends the context at binders, so real conversion must too. Otherwise, in a
context with no local of the binder's type, two real types of one lambda
could fail to convert, making `h_unique_in` false and the theorem vacuous
there. The binder rule now picks a local `k` and one of the two binder types
`ty`, and relates the opened bodies in `lctx.insert(k, ty)`. The kernel modes
also require `lctx[k] == ty`, where the extension is the identity, so
nothing about `def_eq`'s proofs changed.

## Option 1 is false (2026-09-26, `metatheory::option1_refuted`)

`kconv ⟹ tconv` over arbitrary chains fails even between well-typed terms in
a well-formed context. The setting: propositions `A`, `B`, axioms `p : A`
and `bad : B`, and one local of type `A`.

- `m = (λz:A. z) bad` has `InferOnly` type `A`, because arguments are not
  checked.
- Proof irrelevance gives `m ~ p`, and beta gives `m ~ bad`.
- So `kconv(bad, p)` holds, and it is PROVEN outright (`cx_kconv`), as are
  both ends' real typings and `lctx_wf` (`cx_well_formed`).
- `option1_refuted`: `kconv_implies_tconv` contradicts `h_conv_typed`
  (conversion relates only terms of convertible types) together with
  `h_axioms_distinct` (distinct axioms do not convert).

Those two are standard properties of the real theory, so they're the only
premises. Proving them for this environment outright is a consistency
argument, fragment work.

Nanoda is unaffected: the kernel only compares terms it has already checked,
and its proof-irrelevance test compares inferred types (`B` vs `A`), so it
never builds `m`. The finding is about the SPEC. `kconv` forgets the
kernel's invariant that compared terms are well typed, and option 2
(`kconv_wt`) is the statement that keeps it. The remaining obligation is
the kernel side: `def_eq` only produces `InferWt` derivations.

## Kernel side: scoped real contexts (design, user choice 2026-09-26)

**Why.** To show `def_eq` only produces `InferWt` derivations, the kernel
must produce REAL typings, and turning its one-local derivations into the
cofinite form needs a renaming lemma. In the global arena context, renaming
a local `x` breaks. Existential witnesses may mention later locals whose
global types mention `x`, and typed leaves on those terms stop matching. In
a SCOPED context (only in-scope locals, each entry mentioning only earlier
ones, the opening local outside the domain), no entry mentions `x`, and
renaming is the standard locally nameless lemma.

**The model change (S1).** `Infer`, the kernel's spec, keeps the global
context and its rules, so `def_eq`'s proofs are untouched. `InferWt` and
`Real` become scoped. Their binder rules open with a local NOT in the
context's domain (plus `unreach`) and extend the context with it:

| rule | `InferWt` | `Real` |
|---|---|---|
| lambda / Pi typing | ∃ `k ∉ dom Γ`, body typed in `Γ.insert(k, A)` | ∀ such `k` (cofinite), plus one exists |
| binder congruence | ∃ `k ∉ dom Γ`, `ty`, bodies related in `Γ.insert(k, ty)` | same (∃) |

**S1 DONE.** Option 2's proof carries over with the context threaded
through the recursion. The lambda case instantiates the real rule at `InferWt`'s own
local, and congruence reuses the same `k`. The hypotheses become
all-contexts statements (`hyps_all`), unconditionally over every map. They
are inversion and uniqueness properties, and a context's well-formedness
plays no part in them.

**S2 DONE (equivariance).** `swap_model.rs` (untyped: `pstep`,
`pstep_star`, `defeq`, the four untyped leaves, `deq_c`/`deq`) and
`swap_typed.rs` (`types_to` in all three modes, `deq_p`/`deq_p_c`, the typed
leaves and helpers, the projection walk, `wt1`/`leaf_wt`) prove that
swapping two locals `x ↔ y` in the terms and the context preserves every
derivation. It needs one premise: stored environment terms and declaration
types mention no local (`env_fv_free`, `dty_fv_free`). A swap is a
bijection, so it never collides with a local a derivation picked, and no
rule needed a side condition. Renaming is the special case where the swap
fixes everything but the renamed local.

**S3 DONE.** `real_lam_intro` / `real_pi_intro` (`swap_typed.rs`) take a
real derivation at ONE local outside a well-formed scoped context
(`ctx_ok`: no outside local is reachable from any entry) and conclude the
cofinite rule, by swapping that local with each fresh one. The context is
fixed by the swap (`cswap_fixed`), and the binder type, body and codomain are
fixed because their locals are in the context (`fv_in`, `scoped_unreach`).

**S4 foundation (2026-09-26).** The kernel's scope is now a well-formed
scoped context:
- `live_ok` also records that each live local's type is closed and in scope
  over the locals opened before it (`live_types_ok`), maintained at the
  three binder pushes and the pops.
- `kscope(tc)` restricts the arena's local context to the live
  level-locals and the unique locals.
- `kscope_ok`: `kscope(tc)` is `ctx_ok`.
- `in_scope_fv_in`: anything in scope mentions only `kscope` locals.
- `real_gen::rt_fv_in`: really typed terms are scoped.

**The cache problem, and the chosen route (2026-09-26).** The kernel
caches claims and reuses them at other depths, and the arena hash-conses
locals. So "the kernel's binder local is outside the live scope" holds when a
claim is made but not when a cached claim is reused, and scope-relative
kernel claims would need STRENGTHENING, which junk witnesses defeat. Two
options were weighed: scope-keyed caches (a kernel change), or tight claims.
The user chose to try tight claims first:

- **Tight claims.** State every kernel claim in the MINIMAL context of its
  subject, `rctx(G, e)`: the global context restricted to what `e`
  reaches. It does not depend on the live scope, so it is cache-stable.
  The kernel's binder local is unreachable from the binder, hence outside
  `rctx` of it, and `rctx(body[lid]) ⊆ rctx(binder).insert(lid, A)`, so claims
  compose by WEAKENING alone.
- **Cofinite rules everywhere in the scoped modes** (the standard locally
  nameless method). `InferWt` typing, and the binder congruence of `InferWt`
  and `Real`, quantify over every fresh local. Weakening then needs no
  renaming, only a fresh non-vacuity witness (pigeonhole over finite
  contexts). The kernel's single-local derivations become cofinite by
  equivariance (S2), as in S3.

**M1 + M3 DONE.** `InferWt` typing and both scoped modes' binder
congruence are cofinite. Their fresh locals are outside the context, unused
by any entry (`ctx_fresh`), and unreachable from the binder. Option 2
re-verifies, now also requiring environment terms to mention no local
(`fv_free`). The lambda and Pi cases instantiate both sides at `InferWt`'s
non-vacuity local and spread the codomain conversion to every fresh local
by swapping (`conv_all_fresh`), so no height bound was needed.

**Local ids are `nat` (2026-09-26).** Weakening needs a local fresh for any
finite context at every binder. With `u32` ids that supply is finite while
derivation heights are unbounded, so weakening was unprovable. `ExprSpec::Free`,
the context maps, fresh-local parameters, id sequences and sets are now `nat`.
The arena side keeps `u32`: `expr_id` casts to `nat`, and `raw_node` returns
nothing for ids at or above 2^32. Spec-level only; no exec code changed, and
every existing proof re-verified untouched.

**M2 + M4 DONE.** With `ctx_fresh`, the scoped rules' freshness is
`fv_absent`, which doesn't depend on the context (`Infer` keeps `unreach`
for the global context). `swap_typed::fresh_local` gives a local outside
any finite context, unused by its entries, and free in the given terms.
`weaken.rs` proves weakening for both scoped modes, renaming-free: each
cofinite instance in the larger context is one in the smaller, and the
non-vacuity witness comes from `fresh_local`.

**M6 DONE.** `swap_typed::scoped_lam_intro` / `scoped_pi_intro` (typing)
and `metatheory::conv_all_fresh` (conversion) take one fresh local to every
fresh local in either scoped mode. This is what the kernel side needs,
since the kernel opens exactly one local per binder.

**M5 DONE.** `rctx.rs`: `rctx(G, e)` restricts `G` to the locals `e`
reaches (`reach_n`, an inductive path through free locals and their types).
Three lemmas:
- `rctx_mono`: a term's free locals include another's, so its `rctx` does too.
- `rctx_open`: `rctx(body[lid]) ⊆ rctx(binder).insert(lid, A)` when
  `G[lid] = A`.
- `rctx_fresh`: a local unreachable from `e` (the kernel's `unreach` fact)
  is outside `rctx(G, e)` and mentioned by none of its entries.

**M7 roadmap (the kernel port).** Typed leaves are produced at exactly five
kernel sites: `proof_irrel_eq`, `def_eq_unit`, `try_eta_struct_aux`, and
inside `whnf`'s iota `to_ctor_when_k` (K-like recursors) and
`expand_eta_struct_aux`. Everything else is reduction, congruence and
untyped leaves, which translate structurally from `Infer` in `G` to
`InferWt` in `rctx`. The leaf sites need real typings of their operands (from
the inputs' real typedness by generation and subject reduction) and of their
witness, the kernel's own inferred type. That in turn needs:
- (a) a SUBSTITUTION LEMMA for the scoped modes: typing and conversion
  survive replacing a local by a term of its type, because inferred
  application types are instantiated codomains;
- (b) the five leaf sites;
- (c) the structural translation of the remaining contracts and the cache
  invariants.

Subject reduction stays a named hypothesis.

**M7(a) DONE.** `subst_model.rs` (untyped): `fsubst(e, k, m)` for closed
`m` commutes with shifting, opening, spines and the iota/nat/quot/eta
leaves. `pstep`, `pstep_star`, `defeq`, `deq_c` and `deq` are preserved.
The binder rule's local is renamed off `k` and `m` by `fswap_deq` when
they clash. `subst_typed.rs` (typed, scoped modes): `st_types_to` and
`st_deq_p`, with every typed leaf. The context becomes `sctx(G, k, m)`:
`k` removed, `m` substituted into the other entries. Every height grows by
`m`'s typing height, which keeps each rule's relative height side
conditions. A cofinite instance at `k` itself comes from one at a far
local, renamed by equivariance.

**The obstacle M7(b) meets: regularity.** An `InferWt` irrelevance leaf
needs its proof type `A` (`is_proof_type_m`) to be really typed (`wt1`).
The kernel's witness is its own inferred type. For `x = f a` that is the
instantiated codomain `B[a]`, where `Pi(A, B)` is `whnf` of `f`'s type.
So the site needs REGULARITY: the type of a really typed term is itself
really typed. In this model that holds only UP TO CONVERSION. The real
application rule takes any `Pi(A, B)` convertible to the function's type,
so `B` may hold a beta-redex whose argument is arbitrary (junk that
reduction discards): `Pi(Nat, (fun _ : X => Nat) junk)` converts to
`Pi(Nat, Nat)`, and the rule then assigns the type `(fun _ => Nat) junk`.
Regularity up to conversion needs:
- (i) the substitution lemma closed under conversion: `m : T'` with
  `T' ~ G[k]`, result types up to conversion. `subst_typed` is the
  `T' = G[k]` special case.
- (ii) Pi-inversion on the function's typed conversion `ft ~ Pi(A, B)`.
  It may pass through typed leaves, so confluence alone does not give it.
  This is the `h_pi_inj_app` family.
- (iii) level instantiation of declaration types (the `Const` case).

Two ways forward: state regularity up to conversion as a named hypothesis
next to subject reduction, or prove it from (i)-(iii) plus the existing
inversion hypotheses. **Chosen: prove it.**

**Regularity status.**
- (i) DONE, `subst_conv.rs`: `sc_types_to` / `sc_deq_p`. `m : tm` with
  `tm ~ G[k]`; each result type is returned with its conversion to the
  substituted type, at a fixed height `dd`.
- (iii) DONE, `level_inst.rs` (untyped) and `level_typed.rs` (typed):
  instantiating universe parameters preserves `pstep`, `defeq`, `deq_c`,
  typing and conversion at the same height. `lt_closed` is the `Const`
  case: a declaration type is typed at any instance. It assumes
  `env_lp_ok` / `dty_lp_ok`: each declaration mentions only its own
  universe parameters, which the kernel checks. The trusted
  string-expansion fact now also says the expansion has no universe
  parameter.
- `regularity.rs::reg_app` DONE: `Pi(A, B)` really typed, and `m` typed
  at a type convertible to `A`, give `B[m]` typed at a type convertible to
  the codomain sort. This is the application step.
- (ii) What remains is at the kernel, not in the model. Regularity is a
  property of the KERNEL's inference: its application type is the
  codomain of `whnf` of the function type, a reduct of a typed term, so
  subject reduction makes it typed. It is proven site by site in `infer`'s
  contract during the port (M7c). The application site feeds `reg_app` the
  conversion `aty2 ~ A`. That comes from the real derivation's `aty2 ~ aty_r`,
  plus `Pi(A, B) ~ ft ~ ft_r ~ Pi(aty_r, bt_r)` and Pi DOMAIN injectivity:
  a sibling of `h_pi_inj_app` that will be stated with the port.

**M7 claim shape (settled 2026-09-26).** Stating each kernel claim in
exactly `rctx(G, operands)` fails: a subterm's claim would need its typing
moved from the parent's context down to the subterm's own `rctx`. That is
STRENGTHENING, and model conversions can pass through junk terms that
mention unrelated locals, so strengthening is a deep metatheorem at best.
Instead every claim is quantified over contexts:

    claim(x, y)  :=  forall D.  rctx(G, x) <= D  &&  rctx(G, y) <= D
                                && x, y really typed in D
                       ==>  deq_p_any(D, InferWt, x, y)

(and likewise for `whnf` and `infer`).
- Generation and subject reduction stay in the same `D`, so no
  strengthening is ever needed.
- Cache-stable: `rctx(G, e)` of an existing term does not change as the
  arena grows, and the claim names no context.
- Binders: in `D` the kernel's local `lid` may collide with junk. Pick a
  far local `j` for `D`, use the body claim at `swap(D, j, lid) + {lid : A}`,
  swap back to `j`, and M6 gives the cofinite rule.
- Transitivity: needs the middle term's locals reached from the endpoints
  (the kernel's `scope_pres` facts) and the middle term typed in `D`
  (subject reduction, regularity).
- Leaf sites get `x, y` typed in `D` from the claim's own antecedent. The
  inferred types come from `infer`'s claim together with regularity.

**Structure eta leaf, one-sided (2026-09-26).** The `InferWt` eta leaf used
to need both sides really typed (`leaf_wt`). One side is the kernel's
operand; the other is its expansion `C params x.0 .. x.n`, whose typing
would take structure-typing metatheory. Option 2's `eta_transfer` only ever
used the unexpanded side's real typing. So `eta_struct_expand` now carries
`wt1` of that side, and the `deq_p_c` eta disjunct no longer asks for
`leaf_wt`. This only weakens what `InferWt` demands, and option 2 is
re-proved unchanged in substance.

**M7 progress and remaining plan (2026-09-26).** `kclaims.rs` holds the
claim algebra:
- claim shapes: `cw` (conversion), `ci` (inference, with regularity and
  reach), `tt_to` (typing transfer);
- structural lemmas: `cw_refl` / `cw_symm` / `cw_trans`, `cw_app` /
  `cw_proj` / `cw_bind` (binder via swap and narrowing),
  `cw_of_deq_any`;
- leaves: `cw_irrel`, `cw_unit`.

What remains before `tc.rs` can switch its claims:
1. INDUCTIVE TYPING FACTS. The environment says what a structure
   constructor's type looks like: a Pi telescope of `np + nf` binders whose
   parameter binders are the inductive's, ending in the inductive applied to
   those parameters. This is a kernel-checked environment condition, like
   `env_lp_ok`. From it:
   - a constructor application's real type converts to `I params ...`
     (`h_pi_inj_app` once per argument);
   - `x.k` is really typed when `x`'s type converts to `I params ...`;
   - `C params fields` is really typed when each field has its instantiated
     field type. This covers the eta expansion `C params (e.0) .. (e.n)`
     and the K-like `C params`.
   These unlock the remaining leaf sites (`try_eta_struct`,
   `expand_eta_struct_aux`, `to_ctor_when_k`) and projection regularity.
2. Regularity per `infer` site: App (`reg_app` plus Pi domain
   injectivity), Proj (from 1), Const (`lt_closed` plus weakening), Lam,
   Pi, Let, Sort and literals.
3. Subject reduction for `whnf`'s outputs (`h_sr`, restated per context).
4. The switch: `def_eq_claim` / `whnf_claim` / `kinfer_claim` and the cache
   invariants restated as `cw` / `ci` / `tt_to` claims.

**M7 model side COMPLETE (2026-09-26, through 6d5310c).** `kclaims.rs` has
every claim and every step lemma the port needs:
- claim shapes: `cw` (conversion), `ci` (inference), `cwh` (reduction:
  conversion, type-preserving transfer `tp_to`, reach containment), `cprop`;
- algebra: refl/symm/trans, app/proj/bind congruence (`cw_bind`: swap plus
  narrowing), spine congruence;
- typed leaves: `cw_irrel`, `cw_unit`, `cw_eta`;
- `whnf` steps: reduction chains, K-like (`cwh_k`), eta before iota
  (`cwh_eta_exp`), major replacement (`cwh_replace`), uncapped iota and
  quotient (`cwh_rec_leaf`, `cwh_quot_leaf`).

Supporting modules:
- `ctor_typing.rs`: spine typing, constructor-application types, projection
  typing, expansion typing;
- `replace.rs`: substitutivity, argument replacement;
- `reduce_fv.rs`: reduction adds no local;
- `telescope.rs`.

Every claim assumes `kh`:
- the named hypotheses (`hyps_all`, and subject reduction `h_sr` with its
  companion `h_sr_leaf` for the uncapped iota and quotient steps);
- closed, well-typed declarations (`fv_free`, `env_wf`);
- the constructor conditions `struct_ok` and `ctor_params_ok`, environment
  invariants the ported inductive checker is to establish.

Admissible contexts are well formed (`lctx_wf`). The model's `InferWt` eta
leaf is one-sided (71d63a3). Next: the `tc.rs` switch, then the checker port.

Steps: M1 cofinite scoped rules; M2 freshness (`fvs`, pigeonhole); M3
option 2 re-proved; M4 weakening; M5 `rctx` and its reachability lemmas;
M6 one local ⟹ cofinite for `InferWt` typing and conversion; M7 kernel
port.

**Then:**
- S4, the kernel's derivations as `InferWt` derivations in the live scope.
  This re-proves `whnf`/`def_eq`/`infer` against `InferWt` (the existing
  `dbj_deep_in` scope discipline supplies the scoping) and needs subject
  reduction as a named hypothesis.

## Proof plan for phase 2 (after phase 1)

Mutual induction on derivation height over `types_to` and `deq_p`, `io`
true → false:

- **InferOnly soundness:** a well-typed term's `InferOnly` type converts
  (`tconv`) to a real type of it. The application case is the crux. It uses
  uniqueness (the function's real type) and Pi-injectivity (the codomain).
- **Leaf transfer:** each typed leaf's premises move from `io == true` to
  `io == false` through InferOnly soundness plus conversion transfer on the
  (well-typed) types involved.
- **Congruence/chain transfer:** needs every visited term to be well-typed.
  Either the theorem is stated over derivations through well-typed terms
  (and the exec proofs supply that), or subject reduction is a hypothesis.
  Settled when phase 1 ends.

Plus an environment well-formedness hypothesis: every declaration's type (and
value) is well-typed. The kernel checked it for earlier declarations.

## Church-Rosser and the Nat-literal extension (branch `metatheory`)

Layer 1 (`confluence.rs`, `conv_cr.rs`, `conv_frag.rs`) proves parallel
reduction confluent and eta-free conversion (`ceq`, a sub-relation of `deq`)
joinable up to universe-level equivalence; layer 2 (`injectivity.rs`) derives
Pi and Sort injectivity for `ceq`. Confluence needs the redex kinds not to
overlap (`env_conf`).

The kernel's Nat-literal extension overlaps with delta: `Nat.add 2 3` folds
to `5` by built-in arithmetic, and `Nat.add` is also a definition. Nothing
ties the two for an arbitrary export (`Nat.add a b := 0` makes reduction
non-confluent), so a real environment is handled under a named hypothesis:

| predicate | says |
|---|---|
| `EnvSpec.nat_fold` | whether folding is a reduction rule (always `true` for the kernel) |
| `nofold(env)` | `env` with folding off: the Nat operations are plain definitions |
| `h_nat_ext` (`nat_ext.rs`) | every foldable op application is `defeq` in `nofold(env)` to the value the built-in arithmetic returns |
| `cr_ext` | `env_conf(nofold(env))`, closed environment terms, well-formed recursor rules, `h_nat_ext` |

Under `cr_ext`, every reduction step of `env` is a conversion of
`nofold(env)` (`pstep_ext_jn`), so `ceq` in `env` lands in joinability there
(`ceq_jn_ext`), and injectivity holds in `env` (`ceq_bind_inj`,
`ceq_sort_inj` with `ne = nofold(env)`). `h_nat_ext` is the trust Lean's own
kernel places in its extension.

### The injectivity hypotheses on the eta-free fragment (`frag_hyps.rs`)

`jn_tconv`: joinability modulo level equivalence is real conversion. With it,
`frag_hyps_ext` proves, in a real environment under `cr_ext`, the fragment
forms of the kernel's hypotheses in every context: `h_sort_inj_frag`,
`h_pi_inj_dom_frag`, `h_pi_inj_app_frag`. They are `h_sort_inj`,
`h_pi_inj_dom` and `h_pi_inj_app` with the premise conversion restricted to
`ceq` (no eta, no typed leaves). The application form needs no `tconv(targ,
a2)` premise: a really typed argument is closed, and instantiation respects
joinability. The full hypotheses need typed inversion (proof irrelevance,
eta), the next stage.
