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
| G | binder congruence in `deq_p_c` opens with a fresh local whose type in `lctx` is unconstrained (need not be the binder type) | a typed leaf under a binder may use the wrong type for the bound variable | small (the exec side already opens with the binder's type) |

B–E and G are spec tightenings. The kernel already behaves this way (literals
are `Nat` with no levels, Check mode checks binders and let annotations,
`infer_const` checks arity), so they cost proof work, not kernel changes. A is
the large one. The model has to distinguish Π from λ before the metatheory can
say anything, and that touches the foundations every proof rests on.

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
