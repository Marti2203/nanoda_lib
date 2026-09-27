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
