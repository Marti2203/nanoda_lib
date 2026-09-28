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
certified export from `kh_hyp`, which now names: the fragment
(`frag_env`, and every declared type and value a fragment term),
`cr_env`, and the signature's well-formedness at every level instance
(`sig_wf`, `lev_ok`). The certificates give the rest (closedness, own
universe levels, declared types that are types, values typed at them).
Discharging `sig_wf`/`lev_ok` needs level instantiation for derivations
and ranks from declaration order; `cr_env` is about the export's names.

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
