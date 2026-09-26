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
