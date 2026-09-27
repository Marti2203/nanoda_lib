# Blueprint: "Definitional Inversion, Without Normalisation" (arXiv 2607.13662), Section 2 + Prop (Section 3.6)

Target: mechanise in Verus over de Bruijn terms
`Var(nat) | Sort(level) | Pi(A,B) | Lam(A,b) | App(f,a)`.

How to read this document:

- **[PAPER]** marks statements taken from the paper (formulas restated in plain notation).
- **[RECON]** marks my reconstruction. Either the paper does not state it (for example the order on
  compacts, joins, well-formedness, and most proofs), or the extracted LaTeX is garbled. Every
  [RECON] item is my best reading and should be sanity-checked while mechanising.
- **[NOTE]** marks my own analysis of subtleties.

Notation: `⊥` is bottom; `U` is the universe code; `λ(f)`, `Π(a,g)` are compact codes; `≤` is the
information order; `u ↑ v` means compatible; `u ∨ v` is the join; `≡` on compacts means `≤` both
ways (the setoid equality). Syntactic universe `𝒰`; syntactic `Π_{x:A} B`, `λ_{x:A} M`, `M N`.
`B[N]` substitutes the last variable (de Bruijn index 0) by N.

---------------------------------------------------------------------------------------------------

## 0. Map of the proof (dependency order)

```
S0  syntax: terms, substitution algebra, typing/conversion (Fig 3, presupposition-carrying form),
    syntactic weakening / substitution / context-conversion lemmas, generation (inversion) lemmas,
    head reduction (deterministic), typed head reduction
C0  compacts: datatype, rank, wf, le / apply (mutual), join, compat, ≡            (§1.1–1.5)
C1  order lemmas: preorder, apply monotone (both args), join is lub, compat ⇔ ∃ub,
    apply distributes over join, rank bounds, "projection" lemma              (§1.6)
T0  semantic typing  u :_n a  (Fig 2, intensional form of Prop 2.15)           (§2)
T1  Prop 2.16 + 2.17 (mutual, induction on n); Prop 2.18 (stability); inversion lemmas;
    stage-free typing; (optional) Prop 2.15 extensional⇔intensional
M0  interpretation ⟦M⟧ρ as a predicate on compacts (Fig 4 left)                (§4)
M1  ⟦·⟧ is an ideal (contains ⊥, down-closed, join-closed); monotone in ρ;
    weakening; Lemma 2.29 semantic substitution
M2  Thm 2.31 soundness (typing ⇒ semantic typing; conversion ⇒ equal ideals)
    Thm 2.32 disjointness (optional warm-up)
R0  logical relation (Definition of §2.6), stage-indexed                        (§6)
R1  §2.7 properties, in mutual groups by induction on n:
      G1 IsType, ToType (definitional)
      G2 {SymmTy, Symm, TransTy, Trans, Trans', Conv, Bot}  (one mutual induction on n)
      G3 {MonoTypeDecrTy, MonoTerm, MonoTypeIncr, MonoTypeDecr}
      G4 {JoinTy, Join}
      Cor 2.33 stability (needs G3 at all stages)
      Lemma 2.34 head reduction/expansion (+ type-level analogue)
R2  substitution relation; Thm 2.35 adequacy (induction on the conversion derivation; uses 2.31)
R3  identity substitution related over ⊥ (induction on context) ⇒ Thm 2.36 fundamental lemma
R4  Cor 2.37 Π-injectivity (and sort injectivity with levels); Thm 2.38 subject reduction
P   Prop extension: threads through C0, T0/T1, M0–M2, R0–R2 (§9)
```

---------------------------------------------------------------------------------------------------

## 1. The domain and its compact elements (Section 2.1)

### 1.1 Domain equation [PAPER]

    (dom)   D ≅ [D ⇒ D]  +  ↑(D × [D ⇒ D])  +  ↑1
                 (λ)          (Π)              (U)

The sum is **coalesced** (all components share one bottom). `↑` adds a new bottom (lifting).
The function space (λ) is **not** lifted, so the ⊥ of `[D⇒D]` (the everywhere-⊥ function)
is identified with the global ⊥: **λ(⊥) = ⊥**. In contrast `Π(⊥,⊥) ≠ ⊥`, because knowing that
something is a Π-type is an observation. The paper motivates this: η requires that `⊥` and `λx.⊥`
cannot be told apart.

The corresponding functor on CUSLs [PAPER]:

    (func)  F(X) := (X ⇒ X) + ↑(X × (X ⇒ X)) + ↑1        (coalesced)
    C_0 := {⊥},   C_{n+1} := F(C_n),   C := ⋃_n C_n,   D := ideals(C)

`C_n` is finite for this theory. The paper warns that this fails for extensions, so proofs must
not rely on it.

### 1.2 Elements of C_{n+1} [PAPER]

- `⊥`
- `U`
- `λ(f)` for `f` a step function in `C_n ⇒ C_n`
- `Π(a, b)` for `a ∈ C_n` and `b ∈ C_n ⇒ C_n`
- subject to `λ(⊥) = ⊥`

The paper describes C as essentially a quotient inductive type. The quotient identifies `λ(⊥)`
with `⊥`, and identifies different presentations of the same step function. Every mechanisation
(Section 4) uses an **unquotiented** representation. It partially enforces canonicity (a λ body may
not represent ⊥) and treats C as a **setoid** whose equivalence is the one induced by the preorder.

### 1.3 Domain-theory primer used [PAPER, Defs 2.1–2.7, 2.9, Prop 2.8, Thm 2.10]

- **Def 2.1 Compatibility.** `u ↑_P v` iff there is `w ∈ P` with `u ≤ w` and `v ≤ w`.
- **Def 2.2.** A *directed* set is non-empty, and any two of its elements have an upper bound in
  the set. A *bounded* set has an upper bound in P.
- **Def 2.3.** P is *directed complete* if every directed set has a sup, and *bounded complete* if
  every bounded set has a sup. `⋁X` is the sup and `u ∨ v := ⋁{u,v}`.
- **Def 2.4 Compact.** u is compact iff `u ≤ ⋁X` for directed X implies `u ≤ v` for some `v ∈ X`.
- **Def 2.5 Scott domain.** A bounded- and directed-complete poset in which
  `u = ⋁{v ∈ compacts(D) | v ≤ u}` for every u.
- **Def 2.6 CUSL.** A poset with least element ⊥ in which every compatible pair has a sup.
- **Def 2.7 Ideals.** A subset that is downward closed and closed under finite sups (so if
  `u,v ∈ I` then `u∨v` exists and lies in I). `ideals(P)` is ordered by ⊆. The principal ideal is
  `↓u = {v | v ≤ u}`.
- **Prop 2.8.** `ideals(P)` is a Scott domain iff P is a CUSL.
- **Def 2.9 Embedding** `f : C → C'` between CUSLs:
  - `f(⊥) = ⊥`;
  - if `x ↑ y` then `f x ↑ f y` and `f(x∨y) = f x ∨ f y`;
  - `f x ≤ f y ⇒ x ≤ y`;
  - `f x ↑ f y ⇒ x ↑ y`.
- **Thm 2.10.** Dom^◁ (Scott domains with e-p pairs) ≃ CUSL (with embeddings), via compacts/ideals.

### 1.4 Step functions [PAPER, Def 2.11, Props 2.12–2.14]

- **Def 2.11.** A step function `f : X → Y` is a monotone function with
  `f(u) = ⋁{ v_i | u_i ≤ u }` for a finite set of pairs `{u_1↦v_1, …, u_k↦v_k} ∈ P_fin(X×Y)`,
  called a *presentation*.
- Presentations are not unique: adding `(u ↦ ⊥)` never changes the function.
- A finite set of pairs presents a function **iff** `u_i ↑ u_j ⇒ v_i ↑ v_j` for all i, j. This
  makes the sup well defined.
- **Prop 2.12.** Step functions ordered pointwise form a CUSL `X ⇒ Y`, and
  `compacts([D⇒E]) ≅ compacts(D) ⇒ compacts(E)`, `ideals(X⇒Y) ≅ [ideals X ⇒ ideals Y]`.
- **Prop 2.13.** `⇒` is a functor CUSL × CUSL → CUSL, **covariant in both arguments**, and it
  preserves directed colimits.
- **Prop 2.14.** The inclusion `C_n ⊆ C_{n+1}` is an embedding.
  - [NOTE] In a single global datatype with stage-independent order/join/compat (§1.5), this is
    free: all four clauses of Def 2.9 hold by definition. Only typing is stage-sensitive (Prop 2.18).

**Application on compacts** [PAPER]:
`app(λ f, u) := f(u)`, and `app(v, u) := ⊥` for v not a λ. The paper notes this is *not* a step
function. D-level: `app̄(v̄, ū) := { app(v,u) | v ∈ v̄, u ∈ ū }`.

D-level lifts [PAPER]: `Ū := {⊥, U}` and `λ̄(f) := { λ(u) | u ∈ f }` for `f ∈ ideals(C ⇒ C)`.

### 1.5 Order, apply, join, compatibility, well-formedness [RECON]

The paper does not spell these out. The following is the standard reading of the coalesced sum
with a pointwise order on step functions, made intensional so it can be computed.

Representation: `f = [(u_1,v_1), …, (u_k,v_k)]`, a list of pairs.

**apply** (application of a step function):

    apply(f, x) := join-fold of { v_i | le(u_i, x) }     (⊥ if there are none)

**le (≤)**, defined by cases:

    le(⊥, y)                  := true
    le(U, y)                  := y == U
    le(Π(a,g), y)             := y == Π(a',g') ∧ le(a,a') ∧ le_fun(g, g')
    le(λ(f), y)               := y == λ(f') ∧ le_fun(f, f')
    le_fun(f, f')             := ∀ i < |f|.  le(v_i, apply(f', u_i))

`le_fun` is the pointwise order, stated intensionally:
`f ≤ f'  ⟺  ∀x. f x ≤ f' x  ⟺  ∀i. v_i ≤ f'(u_i)`.

- (⇒) `v_i ≤ f(u_i) ≤ f'(u_i)`.
- (⇐) `f(x) = ⋁{v_i | u_i ≤ x} ≤ ⋁{f'(u_i) | u_i ≤ x} ≤ f'(x)` by monotonicity of f'.

Also note `λ(f) ≤ ⊥` only when f presents ⊥. That case is excluded by wf (see below). So on wf
elements, `le(λ f, ⊥)` = false is correct.

**join (∨)** is structural and only meaningful when the arguments are compatible:

    join(⊥, y) = y;  join(x, ⊥) = x;  join(U, U) = U
    join(Π(a,g), Π(a',g')) = Π(join(a,a'), g ++ g')
    join(λ f, λ f')        = λ(f ++ f')
    otherwise: junk (for example return the first argument); only used under compat

**compat (↑)**:

    compat(⊥, y) = compat(x, ⊥) = true;   compat(U, U) = true
    compat(Π(a,g), Π(a',g')) = compat(a,a') ∧ compat_fun(g, g')
    compat(λ f, λ f')        = compat_fun(f, f')
    otherwise false
    compat_fun(f, f') := fun_ok(f ++ f')
    fun_ok(h) := ∀ i j. compat(h.in_i, h.in_j) ⇒ compat(h.out_i, h.out_j)

This is the presentation condition of Def 2.11. Justification: two wf step functions have an
upper bound iff their union is a valid presentation.

**wf** (well-formedness; the paper, Section 4, says: in functions, compatible inputs must give
compatible outputs, and λ terms must not be ⊥):

    wf(⊥), wf(U)
    wf(Π(a,g)) := wf(a) ∧ wf_fun(g)
    wf(λ f)    := wf_fun(f) ∧ ∃ i. f.out_i ≠ ⊥      (λ must not present ⊥)
    wf_fun(f)  := (∀ i. wf(f.in_i) ∧ wf(f.out_i)) ∧ fun_ok(f)

- [NOTE] With wf, "v ≡ ⊥" holds iff `v == Bot` syntactically. This is why the non-⊥ check for λ
  can be syntactic.
- [NOTE] `Π(a, [])` is allowed and represents `Π(a, ⊥)`, which is observable.

**Smart constructor** [RECON]: `mk_lam(f) := if ∀i. f.out_i == ⊥ then ⊥ else λ(f)`. Use it
whenever a λ is built from a function that might present ⊥. This implements the coalescing
`λ(⊥) = ⊥`.

**≡**: `eqv(u,v) := le(u,v) ∧ le(v,u)`. Every "=" between compacts in the paper (for example
`f(u) = f(v)` in `dom`, or `(u,v)` after joins) means `≡`, **never** Verus `==`.

**Rank and stage** [RECON]:

    rank(⊥)=0,  rank(U)=1,  rank(Prop)=1 (Prop extension)
    rank(λ f)    = 1 + max_i max(rank u_i, rank v_i)
    rank(Π(a,g)) = 1 + max(rank a, max_i max(rank u_i, rank v_i))
    in_stage(n,u) := wf(u) ∧ rank(u) ≤ n        (sufficient for "u ∈ C_n")

- [NOTE] The rank of a *representation* is not ≡-invariant. For example, a junk pair `(x ↦ ⊥)`
  with a high-rank `x` raises the rank. So `rank(u) ≤ n` is sufficient but not necessary for
  membership of the class in `C_n`. This is harmless thanks to Prop 2.18 and Cor 2.33 (stages can
  always be raised).
- [NOTE] `C_n` is **not** downward closed in `C`: an element below a `C_n` element may need higher
  rank. Never assume `x ≤ y ∈ C_n ⇒ x ∈ C_n`.

### 1.6 Order lemmas to prove first [RECON]

Prove these by strong induction on rank sums:

1. `le` is reflexive and transitive on wf elements.
2. `apply` is monotone in the argument (`x ≤ y ⇒ f x ≤ f y`) and in the function
   (`f ≤ f' ⇒ f x ≤ f' x`).
3. `rank(apply(f,x)) ≤ max_i rank(v_i)`, so `rank(app(λ f, x)) < rank(λ f)`.
4. For wf and compat arguments:
   - `u ≤ u∨v` and `v ≤ u∨v`;
   - `u ≤ w ∧ v ≤ w ⇒ u∨v ≤ w`;
   - `wf(u∨v)`;
   - `compat(u,v) ⇔ ∃ wf w. u ≤ w ∧ v ≤ w`;
   - `u ≤ w ∧ v ≤ w ⇒ compat(u,v)`.
5. `apply(f ++ f', x) ≡ apply(f,x) ∨ apply(f',x)`. Also `app(u1∨u2, w) ≡ app(u1,w) ∨ app(u2,w)`.
6. Values of a wf step function at compatible arguments are compatible.
7. The **projection lemma** [RECON; the compact-level replacement for finitary projectors]. For a
   presentation g and any x, let `π_g(x) := ⋁{ g.in_i | g.in_i ≤ x }` (⊥ if there are none). Then:
   - `π_g(x) ≤ x`;
   - `g(π_g x) ≡ g(x)`;
   - `rank(π_g x) ≤ max rank of g's inputs`;
   - if every `g.in_i : a` and `a : U`, then `π_g(x) : a` (by Prop 2.16 plus the Bot rule).

   The same works for a union of presentations (for example the inputs of both f and g).

---------------------------------------------------------------------------------------------------

## 2. Semantic typing (Section 2.2, Figure 2, Prop 2.15)

### 2.1 Figure 2, extensional form [PAPER]

`u :_n a` means "u has type a", with `u, a ∈ C_n`. The rules case-split on the type:

    Bot:   a :_n U                                   ⟹  ⊥ :_n a
    Univ:                                             ⟹  U :_{n+1} U
    Lam:   a :_n U,  dom(f,a),  ∀u∈C_n. f(u) :_n g(u)  ⟹  λ(f) :_{n+1} Π(a,g)
    Pi:    a :_n U,  dom(g,a),  ∀u∈C_n. g(u) :_n U     ⟹  Π(a,g) :_{n+1} U

    dom(f,a) := ∀u∈C_n. ∃v∈C_n. v ≤ u ∧ v :_n a ∧ f(u) = f(v)

`dom(f,a)` says that f is completely determined by its values on elements of type a.

[NOTE] Lam does **not** require `dom(g,a)` or `g(u) : U`. So `u :_n a` does **not** imply
`a :_n U`. The logical relation therefore presupposes `a :_n U` separately.

### 2.2 Prop 2.15, intensional form [PAPER]

For `f ∈ C_n ⇒ C_n` and `a ∈ C_n`:

- `dom(f,a)` holds iff some presentation `{u_i ↦ v_i}` of f has `u_i :_n a` for all i.
- If moreover `g :_n Π(a, _ ↦ U)`, then `∀u∈C_n. f(u) :_n g(u)` holds iff some presentation of f
  has `v_i :_n g(u_i)` for all i.

This holds only for a *well-chosen* representation: a junk pair `(u ↦ ⊥)` with untyped u breaks
it. The paper mentions that a canonical representation exists but does not use it.

All three mechanisations (Section 4) state Lam and Pi **in this intensional form**, quantifying
over the entries of the given representation (a finite conjunction), and recover the extensional
form of Figure 2 as a derived equivalence.

### 2.3 Recommended definition for Verus [RECON; intensional, representation-based]

    has_type(n, u, a) :=
      in_stage(n,u) ∧ in_stage(n,a) ∧ match (u, a):
        (⊥, _)                        ⇒ has_type(n, a, U)                                   [Bot]
        (U, U)                        ⇒ n ≥ 1                                               [Univ]
        (Π(b,g), U)                   ⇒ n ≥ 1 ∧ has_type(n-1, b, U)
                                         ∧ ∀i. has_type(n-1, g.in_i, b)
                                         ∧ ∀i. has_type(n-1, g.out_i, U)                    [Pi]
        (λ(f), Π(b,g))                ⇒ n ≥ 1 ∧ has_type(n-1, b, U)
                                         ∧ ∀i. has_type(n-1, f.in_i, b)
                                         ∧ ∀i. has_type(n-1, f.out_i, apply(g, f.in_i))    [Lam]
        _                             ⇒ false
    decreases (n, [u == ⊥] + [a == ⊥])     // lexicographic

- Bot calls `has_type(n, a, U)` at the same n. The measure still drops:
  `(⊥,⊥) → (⊥,U) → (U,U)` goes 2 → 1 → 0.
- Consequences to prove: `u :_n ⊥ ⇒ u = ⊥`; `⊥ :_n U ⇔ n ≥ 1`; `⊥ :_0 a` is false for every a.

**Stage-free typing:**

    stage(u,a) := max(rank u, rank a, 1)
    typed(u,a) := has_type(stage(u,a), u, a)

The `1` is needed because `⊥ : ⊥` only holds from stage 1. By Prop 2.18 this is equivalent to
`∃n. u :_n a`, and then `u :_m a` for every `m ≥ stage`.

[PAPER] Stage-free typing is `u : a := ∃n. u :_n a`. The D-level lift is

    ū : ā  :=  ∀u∈ū. ∃v∈ū. ∃a∈ā. u ≤ v ∧ v : a

Optional derived lemma [RECON], a representation-independent finite form of dom:

    dom(f,a) ⇔ ∀i. ∃w. w ≤ u_i ∧ w :_n a ∧ v_i ≤ f(w)      (given a :_n U)

- (⇒) Instantiate dom at `u_i`.
- (⇐) For a given u, take `w = ⋁` of the witnesses for the `u_i ≤ u`. They are pairwise
  compatible because all are ≤ u. The join is typed by 2.16 (and by Bot if empty). Then
  `f(w) ≥ f(u) ≥ f(w)`.

### 2.4 Closure properties [PAPER statements; RECON proofs]

- **Prop 2.16 (joins).** `u ↑ v`, `u :_n a`, `v :_n a` ⟹ `u∨v :_n a`.
- **Prop 2.17 (weakening the type).** `u :_n a` and `a ≤ a'` ⟹ `u :_n a'`.
  - [RECON] This needs the extra hypothesis `a' :_n U`. Without it, take `a = ⊥`, `u = ⊥` and `a'` a
    non-type: then `⊥ :_n a'` fails. Add `a' :_n U` (or `a' ∈` some typed ideal) as a premise.
- **Prop 2.18 (stability).** For `u, a ∈ C_n`: `u :_n a ⇔ u :_{n+1} a`.
- [PAPER] "For all u, a ∈ C there is a least n (computable) with u, a ∈ C_n, and `u : a ⇔ u :_n a`;
  if `u : a` then `u :_m a` for all `m ≥ n`."

Proof outlines [RECON]:

- **2.16 and 2.17 together** by induction on n (2.16 at n uses 2.17 at n−1).
  - 2.16: case on a.
    - ⊥ subjects are trivial.
    - a = U: `Π(b,g) ∨ Π(b',g') = Π(b∨b', g++g')`. Then `b∨b' : U` (IH 2.16). Inputs of `g++g'`
      are typed `b∨b'` (IH 2.17 with `b ≤ b∨b'`). Outputs are `: U`.
    - a = Π: `λ f ∨ λ f' = λ(f++f')`. The entries are already typed.
  - 2.17: case on a.
    - a = ⊥ ⇒ u = ⊥; use Bot with `a' : U`.
    - a = U ⇒ `a' ≡ U`.
    - a = Π(b,g) ⇒ `a' = Π(b',g')` with `b ≤ b'` and `g ≤ g'`. For u = λ f: inputs `u_i : b ⇒ u_i : b'`
      (IH, with `b' : U` taken from `a' : U`). Outputs `v_i : g(u_i) ⇒ v_i : g'(u_i)` (IH;
      `g(u_i) ≤ g'(u_i)` by apply monotonicity; `g'(u_i) : U` because g' outputs are `: U`, joined
      by 2.16 at n−1).
- **2.18** by induction on n.
  - (⇒) Each rule lifts, since premises at n−1 lift by IH.
  - (⇐) The `in_stage(n, ·)` conjuncts force entries into `C_{n−1}`; then apply IH.
- **Invariance under ≡ in the *type* argument** (needed for MonoTypeDecrTy in both directions):
  follows from 2.17 applied both ways.
- The representation-based `has_type` is **not** invariant under ≡ in the *subject*, and typing is
  **not downward closed in the subject**. Every lemma therefore carries typing of each subject
  witness as a premise (the paper's grey premises).
- **Inversions to have handy:**
  - `λ f :_n a ⇒ a = Π(…)`;
  - `Π(b,g) :_n a ⇒ a = U` (or `a = Prop` in the extension);
  - `U :_n a ⇒ a = U`;
  - `⊥ :_n a ⇒ a :_n U`.

---------------------------------------------------------------------------------------------------

## 3. Finitary projectors (Sections 2.3–2.4): what is needed

[PAPER] Definitions, recorded for completeness:

- **Def 2.19.** A finitary projector is a continuous `p : D → D` with `p α ≤ α`, `p(p α) = p α`,
  and whose image is a Scott domain.
- **Thm 2.20.** `Fp D` is a Scott domain.
- Notation: `D|p` is the image of p, and `C|p = {u ∈ C | p u = u}`.
- **Props 2.21–2.24.**
  - `C|p` = the compacts of `D|p`.
  - Every fixed point is a limit of compact fixed points.
  - `C|p` is closed under finite sups.
  - Conversely, every sup-closed `E ⊆ C` defines `p(α) = {u ∈ E | u ≤ α}` with `E = C|p`.
- **§2.4.** `p_n(α) := {u ∈ C_n | ∃a∈α. u :_n a}`. **Prop 2.25**: this is well defined and
  continuous. The proof: the set is closed under compatible sups, using 2.17 on `a1 ≤ a1∨a2` and
  then 2.16. **Prop 2.26 / 2.27** relate `p_n` and a global `p`.
- The equations of p:

      p Ū Ū           = Ū
      p Ū (Π̄(α,β))    = Π̄(p Ū α, u ↦ p Ū (β(p α u)))
      p (Π̄(α,β)) f    = u ↦ p (β (p α u)) (app̄(f, p α u))
      p α β           = ⊥ otherwise

**Needed for the mechanisation: none of it directly.** The compact-level route (Fig. 4 left,
typing on compacts) avoids D and Fp entirely; the paper itself notes an elementary proof exists.
Only two ideas carry over:

- the sup-closure argument of Prop 2.25, used to show ⟦·⟧ ideals are join-closed;
- the compact-level projection `π_g(x)` of §1.6 item 7. This replaces "`p α u`" wherever an
  argument v must be pushed down to a typed argument with the same image.

---------------------------------------------------------------------------------------------------

## 4. Syntax: MLTTη (Figure 3 and the Section 4 presupposition-carrying form)

### 4.1 Figure 3 as printed [PAPER] (named variables, "selected rules")

    Univ:  ⊢Γ  ⟹  Γ ⊢ 𝒰 : 𝒰
    Pi:    Γ ⊢ A : 𝒰,  Γ,x:A ⊢ B : 𝒰  ⟹  Γ ⊢ Π_{x:A} B : 𝒰
    Lam:   Γ ⊢ A : 𝒰,  Γ,x:A ⊢ M : B  ⟹  Γ ⊢ λ_{x:A} M : Π_{x:A} B
    App:   Γ ⊢ M : Π_{x:A} B,  Γ ⊢ N : A  ⟹  Γ ⊢ M N : B[N]
    β:     Γ ⊢ A : 𝒰,  Γ,x:A ⊢ M : B,  Γ ⊢ N : A  ⟹  Γ ⊢ (λ_{x:A} M) N ≡ M[N] : B[N]
    η:     Γ,x:A ⊢ M x ≡ N x : B  ⟹  Γ ⊢ M ≡ N : Π_{x:A} B

Types are terms of 𝒰 (Russell-style, type-in-type). The paper omits substitution, the congruence
rules, and (implicitly) context formation, variables, conversion, and the equivalence rules.

### 4.2 Full rule set to mechanise [RECON, following Section 4's description]

Section 4 [PAPER, paraphrased]: the conversion rules carry the presuppositions of their conclusion
as extra premises. The Π and λ congruences require the codomain/body equation under **both**
domains A and A'. β and η require both sides to be well-typed at the common type. This is
equivalent to the economical system (Lean: `IsDefEq.iff`). Lean additionally defines typing as the
**diagonal** of conversion.

Recommended for Verus: one judgement `Γ ⊢ M ≡ N : A`, and `Γ ⊢ M : A := Γ ⊢ M ≡ M : A`.
Contexts are lists of types, where entry i lives in the context of the entries below it. In de
Bruijn form:

    ctx:     ⊢ ·            ⊢Γ,  Γ ⊢ A : 𝒰  ⟹  ⊢ Γ.A
    Var:     ⊢Γ,  Γ(i) = A  ⟹  Γ ⊢ Var i ≡ Var i : A↑^{i+1}
    Univ:    ⊢Γ  ⟹  Γ ⊢ 𝒰 ≡ 𝒰 : 𝒰
    Sym:     Γ ⊢ M ≡ N : A  ⟹  Γ ⊢ N ≡ M : A
    Trans:   Γ ⊢ M ≡ N : A,  Γ ⊢ N ≡ P : A  ⟹  Γ ⊢ M ≡ P : A
    Conv:    Γ ⊢ M ≡ N : A,  Γ ⊢ A ≡ B : 𝒰  ⟹  Γ ⊢ M ≡ N : B
    PiCong:  Γ ⊢ A ≡ A' : 𝒰,  Γ.A ⊢ B ≡ B' : 𝒰,  Γ.A' ⊢ B ≡ B' : 𝒰
               ⟹  Γ ⊢ Pi(A,B) ≡ Pi(A',B') : 𝒰
    LamCong: Γ ⊢ A ≡ A' : 𝒰,  Γ.A ⊢ B : 𝒰,  Γ.A ⊢ M ≡ M' : B,  Γ.A' ⊢ M ≡ M' : B
               ⟹  Γ ⊢ Lam(A,M) ≡ Lam(A',M') : Pi(A,B)
    AppCong: Γ ⊢ M ≡ M' : Pi(A,B),  Γ ⊢ N ≡ N' : A,  (Γ ⊢ A : 𝒰,  Γ.A ⊢ B : 𝒰)
               ⟹  Γ ⊢ App(M,N) ≡ App(M',N') : B[N]
    Beta:    Γ ⊢ A : 𝒰,  Γ.A ⊢ M : B,  Γ ⊢ N : A,  (Γ ⊢ App(Lam(A,M),N) : B[N],  Γ ⊢ M[N] : B[N])
               ⟹  Γ ⊢ App(Lam(A,M),N) ≡ M[N] : B[N]
    Eta:     Γ ⊢ M : Pi(A,B),  Γ ⊢ N : Pi(A,B),  Γ.A ⊢ App(M↑,Var 0) ≡ App(N↑,Var 0) : B
               ⟹  Γ ⊢ M ≡ N : Pi(A,B)

With `Sort(level)`, 𝒰 becomes `Sort(l)`. See §8.3 for levels.

Syntactic metatheory needed before §6 [RECON; standard]:

- weakening;
- substitution: `Γ.A ⊢ J`, `Γ ⊢ N ≡ N' : A` ⟹ `Γ ⊢ J[N] ≡ J[N']`, plus the general
  parallel-substitution form `Δ ⊢ σ ≡ σ' : Γ`;
- context conversion (`Γ ⊢ A ≡ A'` ⟹ judgements in `Γ.A` hold in `Γ.A'`);
- presupposition / validity: from `Γ ⊢ M ≡ N : A` get `⊢ Γ`, `Γ ⊢ A : 𝒰`, `Γ ⊢ M : A`,
  `Γ ⊢ N : A`;
- generation (inversion of typing), each up to conversion of the type:
  - `Γ ⊢ Lam(A,b) : T ⇒ ∃B. Γ.A ⊢ b : B ∧ Γ ⊢ T ≡ Pi(A,B) : 𝒰`;
  - `Γ ⊢ App(M,N) : T ⇒ ∃A B. Γ ⊢ M : Pi(A,B) ∧ Γ ⊢ N : A ∧ Γ ⊢ T ≡ B[N] : 𝒰`;
  - similarly for Pi.

### 4.3 Head reduction [PAPER]

    (λ_{x:A} M) N  ⇝  M[N]              M ⇝ M'  ⟹  M N ⇝ M' N

`⇝*` is the reflexive-transitive closure. **Typed head reduction**:

    Γ ⊢ M ⇝* M' : A   :=   M ⇝* M'  ∧  Γ ⊢ M ≡ M' : A

The paper builds the conversion into the definition because subject reduction is not yet
available, so it cannot be derived from `M ⇝* M'` and `Γ ⊢ M : A`.

[RECON] Encode as a deterministic `hstep(t) : Option<Term>` and `hiter(t,k)`, with
`hred(t,t') := ∃k. hiter(t,k) == t'`. Lemmas:

- **determinism**: if `t ⇝* w` with w stuck (no hstep) and `t ⇝* t'`, then `t' ⇝* w`;
- Pi, Sort and Lam are stuck;
- head reduction commutes with renaming and substitution (needed in adequacy);
- the congruence `M ⇝* M' ⇒ M N ⇝* M' N`.

---------------------------------------------------------------------------------------------------

## 5. The domain model (Section 2.5, Figure 4, Defs 2.28 and 2.30, Lemma 2.29, Thm 2.31)

### 5.1 Environments [PAPER, Def 2.28]

- A domain environment `ρ ∈ Env_D` maps variables to D; a compact environment `ρ ∈ Env_C` maps
  variables to C.
- `(ρ, x ↦ a)` extends ρ.
- Environments are ordered pointwise, with least element `⊥ := _ ↦ ⊥`.

[RECON] Use compact environments `Seq<Compact>`, index 0 = innermost. Order them pointwise by `le`.

### 5.2 Figure 4 [PAPER, with one garble fixed]

Left column (sets of compacts, compact env ρ):

    ⟦x⟧ρ        := { u ∈ C | u ≤ ρ(x) }
    ⟦𝒰⟧ρ        := { ⊥, U }
    ⟦Π_{x:A}B⟧ρ := { Π(a,b) | a ∈ ⟦A⟧ρ ∧ dom(b,a) ∧ ∀_{u:a} b(u) ∈ ⟦B⟧_{ρ,x↦u} } ∪ {⊥}
    ⟦λ_{x:A}M⟧ρ := { λ(f)   | ∃ a ∈ ⟦A⟧ρ. dom(f,a) ∧ ∀_{u:a} f(u) ∈ ⟦M⟧_{ρ,x↦u} }
    ⟦M N⟧ρ      := { app(u,v) | u ∈ ⟦M⟧ρ ∧ v ∈ ⟦N⟧ρ }

- **GARBLE.** The extracted text prints the variable case as `{u | ρ(x) ≤ u}` (upward closed). That
  is wrong. The proof of Thm 3.1 uses `⟦h⟧ρ = {u | u ≤ ref ⊥}`, so the correct case is
  `u ≤ ρ(x)`, the principal ideal.
- The garbled line for Π reads "`{Π(a,b) | a ∈ ⟦A⟧ρ ∧ dom(b,a) ∧ ∀_{u:a} b u ∈ ⟦B⟧_{ρ,x↦u}} ∪ {⊥}`";
  I am confident of this reading.
- `∀_{u:a}` quantifies over compacts u with `u : a` (stage-free).

Right column (D-level):

    ⟦x⟧ρ = ρ(x);  ⟦𝒰⟧ρ = Ū;
    ⟦Π_{x:A}B⟧ρ = Π̄(⟦A⟧ρ, u ↦ ⟦B⟧_{ρ, x↦p ⟦A⟧ρ u})
    ⟦λ_{x:A}M⟧ρ = λ̄(u ↦ ⟦M⟧_{ρ, x↦p ⟦A⟧ρ u})
    ⟦M N⟧ρ      = app̄(⟦M⟧ρ, ⟦N⟧ρ)

The two agree via `⋃_{ρ' ∈ Env_C, ρ' ≤ ρ} ⟦t⟧_{ρ'} = ⟦t⟧_ρ` [PAPER].

[NOTE] **Ill-typed terms** are simply interpreted, often by ⊥.

[NOTE] **Down-closure gap (my analysis; please check).** The λ and Π clauses of the left column
are not literally downward closed when read as sets of representations. Example:

- take `f = {⊥ ↦ v}` (constant) and `f' = {U ↦ v}`;
- then `f' ≤ f` pointwise, so `λ f' ≤ λ f`;
- but `dom(f', a)` can fail at `u = U` unless `U : a` for some `a ∈ ⟦A⟧ρ`.

The right-column semantics does contain `λ f'`. So read each left-column clause as the down-closure
of the displayed generator set. Recommended Verus definition [RECON]:

    mem(Var i, ρ, u)     := le(u, ρ[i])
    mem(Sort _, ρ, u)    := u == ⊥ ∨ u == U
    mem(Pi(A,B), ρ, u)   := u == ⊥ ∨ ∃ a g. le(u, Π(a,g)) ∧ mem(A,ρ,a)
                                     ∧ ∀i. typed(g.in_i, a) ∧ mem(B, ρ·g.in_i, g.out_i)
    mem(Lam(A,M), ρ, u)  := u == ⊥ ∨ ∃ a f. le(u, λ f) ∧ mem(A,ρ,a)
                                     ∧ ∀i. typed(f.in_i, a) ∧ mem(M, ρ·f.in_i, f.out_i)
    mem(App(M,N), ρ, u)  := ∃ w v. mem(M,ρ,w) ∧ mem(N,ρ,v) ∧ le(u, app(w,v))
    decreases M (structural)

The generators use the intensional (entry-wise) form. This is equivalent to the extensional form
given down-closure and join-closure:

- intensional ⇒ extensional: `f(u) = ⋁{v_i | u_i ≤ u}`. Each `v_i ∈ ⟦M⟧_{ρ·u_i} ⊆ ⟦M⟧_{ρ·u}`, and
  ideals are join-closed.
- extensional ⇒ intensional: replace f by the saturated presentation `{w_i ↦ f(w_i)}`, where `w_i`
  is the dom-witness for `u_i`. Then f is below it.

The quantifier inside is finite (over the entries), which is much easier to handle than `∀_{u:a}`
over all compacts.

### 5.3 Ideal lemmas [RECON]

By structural induction on M:

- **(I1)** `mem(M,ρ,⊥)`;
- **(I2)** down-closed: `u' ≤ u ∧ mem(M,ρ,u) ⇒ mem(M,ρ,u')`. This is free with the down-closure
  form, except for App: use `app(w,v)` monotone and the fact that `u' ≤ app(λf, v)` gives
  `u' = app(mk_lam{v ↦ u'}, v)` with `mk_lam{v↦u'} ≤ λ f`;
- **(I3)** join-closed: `mem(M,ρ,u1) ∧ mem(M,ρ,u2) ⇒ compat(u1,u2) ∧ mem(M,ρ,u1∨u2)`;
- **(I4)** monotone in ρ: `ρ ≤ ρ'` ⇒ `mem(M,ρ,u) ⇒ mem(M,ρ',u)`;
- **(I5)** weakening/renaming: `mem(M↑, ρ·w, u) ⇔ mem(M, ρ, u)`, and general renamings.

Notes:

- (I3) is the Prop 2.25 argument: generators with domain types a1, a2 join into a generator at
  `a1 ∨ a2` (which is in the ideal ⟦A⟧ by IH). Entries stay typed by 2.17. Compatibility of the
  outputs comes from both lying in `⟦M⟧_{ρ·(u_i ∨ u'_j)}`.
- (I3) needs 2.17 with `a1∨a2 : U`. Either carry "`⟦A⟧ρ : U`" or use the hypotheses available in
  soundness. **Caveat:** for ill-typed A the ideal may fail join-closure. The paper only claims
  ideals; you may need to restrict (I3) to the typed setting, or state it per construction.

### 5.4 Lemma 2.29 semantic substitution [PAPER]

For compact ρ: `⟦M[N/x]⟧ρ = ⟦M⟧_{ρ, x ↦ ⟦N⟧ρ}` (extension by an *ideal*). Proof: structural
induction on M.

Compact-env form for Verus [RECON]:

    mem(M[N], ρ, u)  ⇔  ∃v. mem(N, ρ, v) ∧ mem(M, ρ·v, u)

Generalise to substitution at depth k with lifting, and to parallel substitutions σ:
`mem(M[σ], ρ, u) ⇔ ∃ compact env ρ'. (∀x. mem(σ(x), ρ, ρ'(x))) ∧ mem(M, ρ', u)`.

- The ⇐ direction uses (I4).
- The ⇒ direction uses (I3) to join the finitely many witnesses. For App this is the join of two
  witnesses; for λ it is one per entry.

### 5.5 Fitting and soundness [PAPER, Def 2.30, Thm 2.31]

- **Def 2.30.** ρ fits Γ iff for all `(x:A) ∈ Γ`: `⟦A⟧ρ : U` and `ρ(x) : ⟦A⟧ρ`.
- **Thm 2.31.** Assume ρ fits Γ.
  - `Γ ⊢ M : A` ⟹ `⟦M⟧ρ : ⟦A⟧ρ`.
  - `Γ ⊢ M ≡ N : A` ⟹ `⟦M⟧ρ = ⟦N⟧ρ`.
- [PAPER] The coalesced sum makes the model validate `λ̄(⊥) = ⊥`, which is critical for η.

[RECON] Verus forms:

- `ideal_typed(M, ρ, A) := ∀u. mem(M,ρ,u) ⇒ ∃v a. mem(M,ρ,v) ∧ le(u,v) ∧ mem(A,ρ,a) ∧ typed(v,a)`.
- `fits(Γ, ρ) := ∀i. ideal_typed(A_i↑, ρ, Sort) ∧ ∃a. mem(A_i↑, ρ, a) ∧ typed(ρ[i], a)`. The
  second conjunct states the D-level `↓ρ(x) : ⟦A⟧` in compact form.
- `sem_eq(M,N,ρ) := ∀u. mem(M,ρ,u) ⇔ mem(N,ρ,u)`.

Proof outline [RECON]: induction on the derivation, proving both parts together. Key cases:

- **Var** from fits. **Univ** trivial (`U : U`, `⊥ : ⊥`).
- **Pi/Lam (typing).** Given a generator `λ f` (entries `u_i : a`, `v_i ∈ ⟦M⟧_{ρ·u_i}`), the IH
  under the extended env `ρ·u_i` (which fits `Γ.A` since `a ∈ ⟦A⟧`) gives `v_i ≤ w_i : b_i` with
  `w_i ∈ ⟦M⟧_{ρ·u_i}` and `b_i ∈ ⟦B⟧_{ρ·u_i}`.
  - Build `f'' = {u_i ↦ w_i}` and `g = {u_i ↦ b_i}`. They are wf: compatible inputs give outputs
    lying in a common ideal `⟦·⟧_{ρ·(u_i∨u_j)}` via (I4) and (I3).
  - Then `λ f ≤ λ f'' : Π(a', g)`, with `a'` a U-typed element of `⟦A⟧` above a (use `⟦A⟧ : U`).
  - Need 2.16/2.17 and `apply(g, u_i) ≥ b_i`.
- **App.** Combine the witnesses for M (a λ typed at some Π) and N (typed at some a'), join the
  domain types in the ideal, and use 2.17. Then use Lemma 2.29 for `⟦B[N]⟧ = ⟦B⟧_{ρ·⟦N⟧}`.
- **β.** Both inclusions go through Lemma 2.29.
  - ⊆: `app(λ f, v) = f(v) = f(v')` for a dom-witness `v' ≤ v`, `v' : a`, and
    `f(v') ∈ ⟦M⟧_{ρ·v'} ⊆ ⟦M⟧_{ρ·v}`.
  - ⊇: given `u ∈ ⟦M⟧_{ρ·v}` with `v ∈ ⟦N⟧`, raise v to a typed `v''` (soundness of `N : A`) and
    form `mk_lam{v'' ↦ u}` ∈ ⟦λM⟧; its app at v'' is u.
- **η.** Uses that `⟦M⟧ρ : ⟦Π A B⟧ρ`: every element lies below a `λ f` whose presentation has typed
  inputs, so it is determined by its values on typed arguments. With the IH at the extended envs,
  `⟦M⟧ = ⟦N⟧`. The coalescing `λ(⊥) = ⊥` is used when M's values are all ⊥ (for example M a
  variable interpreted by ⊥). **This is where the presupposition premises of Eta (both sides typed
  at Π) are needed.**
- **Sym, Trans, Conv, congruences:** direct.

### 5.6 Thm 2.32 disjointness [PAPER]

For well-formed Γ with `Γ ⊢ A : 𝒰` and `Γ,x:A ⊢ B : 𝒰`: `Γ ⊢ Π_{x:A}B ≢ 𝒰 : 𝒰`.

Proof: the ⊥ environment fits every context. By 2.31 the interpretations are equal. But
`Π(⊥,⊥) ∈ ⟦Π…⟧` while `⟦𝒰⟧ = {⊥, U}`, and the Π̄ and Ū constructors are disjoint.

---------------------------------------------------------------------------------------------------

## 6. The logical relation (Section 2.6)

### 6.1 Shape [PAPER]

There are two stage-indexed relations with `a, u ∈ C_n`:

    Γ ⊨_n A ≡ A' type |_a
    Γ ⊨_n M ≡ M' : A |_{u:a}

Diagonals:

- `Γ ⊨_n A type |_a := Γ ⊨_n A ≡ A type |_a`
- `Γ ⊨_n M : A |_{u:a} := Γ ⊨_n M ≡ M : A |_{u:a}`

The four relations refine the judgements `Γ ⊢ A : 𝒰`, `Γ ⊢ A ≡ A' : 𝒰`, `Γ ⊢ M : A` and
`Γ ⊢ M ≡ M' : A`.

**Presuppositions:**

- `u :_n a` and `a :_n U`;
- `a ≤ ⟦A⟧_⊥` (and similarly for the other terms), `u ≤ ⟦M⟧_⊥`.

The definition is **by induction on the stage n, then by case analysis on the semantic type a**.
Variables of Γ are all interpreted by ⊥, so neutrals are interpreted by ⊥ too. There is no Kripke
quantification over context extensions, and the relation gives no inversion for neutrals.

### 6.2 Clauses [PAPER]

**⊥ (degenerate; compared in the paper to step-indexing):**

    Γ ⊨_n A ≡ A' type |_⊥          := ⊤
    Γ ⊨_n M ≡ M' : A |_{u:⊥}       := ⊤

**Π, type clause:**

    Γ ⊨_{n+1} T ≡ T' type |_{Π(a,b)}  :=
        Γ ⊢ T  ⇝* Π_{x:A}  B  : 𝒰
        Γ ⊢ T' ⇝* Π_{x:A'} B' : 𝒰
        Γ ⊢ A ≡ A' : 𝒰
        Γ, x:A ⊢ B ≡ B' : 𝒰
        Γ ⊨_n A ≡ A' type |_a
        ∀ M M' v.  [ v :_n a ]  [ Γ ⊢ M ≡ M' : A ]  Γ ⊨_n M ≡ M' : A |_{v:a}
             ⟹  Γ ⊨_n B[M]  ≡ B[M']  type |_{b(v)}
              ∧  Γ ⊨_n B'[M] ≡ B'[M'] type |_{b(v)}
              ∧  Γ ⊨_n B[M]  ≡ B'[M'] type |_{b(v)}

(`[·]` marks the paper's grey premises. They are hypotheses of the implication.) A, B, A', B' are
existentially bound by the reductions. They are unique by determinism, since Π is stuck.

**Π, term clause:**

    Γ ⊨_{n+1} M ≡ M' : T |_{u : Π(a,b)}  :=
        [ Γ ⊨_{n+1} T type |_{Π(a,b)} ]
        Γ ⊢ T ⇝* Π_{x:A} B : 𝒰
        ∀ N N' w.  [ w :_n a ]  [ Γ ⊢ N ≡ N' : A ]  Γ ⊨_n N ≡ N' : A |_{w:a}
             ⟹  Γ ⊨_n M N  ≡ M N'  : B[N] |_{app(u,w) : b(w)}
              ∧  Γ ⊨_n M' N ≡ M' N' : B[N] |_{app(u,w) : b(w)}
              ∧  Γ ⊨_n M N  ≡ M' N' : B[N] |_{app(u,w) : b(w)}

The grey conjunct `Γ ⊨_{n+1} T type |_{Π(a,b)}` **is part of the definition** in the
mechanisations; Section 2.7 says grey premises are spelled out because the mechanisations
manipulate them. The term relation does **not** contain `Γ ⊢ M ≡ M' : T`; syntactic conversion
of the related terms is always a separate premise.

**U, type clause:**

    Γ ⊨_n A ≡ A' type |_U  :=  Γ ⊢ A ⇝* 𝒰 : 𝒰  ∧  Γ ⊢ A' ⇝* 𝒰 : 𝒰

**U, term clause:**

    Γ ⊨_{n+1} M ≡ M' : A |_{u:U}  :=  Γ ⊢ A ⇝* 𝒰 : 𝒰  ∧  Γ ⊨_{n+1} M ≡ M' type |_u

The type relation is called at the **same stage** n+1.

**Other cases** [RECON]: witness shapes that cannot occur under the presupposition (type witness
`λ(f)`, …) are defined as `false`.

### 6.3 Recursion structure [RECON]

- The type relation at `(n+1, Π)` calls the term relation at stage n.
- The term relation at `(n+1, Π)` calls the type relation at stage n+1 (grey conjunct) and the term
  relation at stage n.
- The term relation at `(n+1, U)` calls the type relation at stage n+1.
- The type relation never calls the term relation at the same stage.

So the measure is lexicographic `(n, tag)` with `tag(type) = 0 < tag(term) = 1`. The recursive
calls appear in negative positions (under `∀ … ⟹`). That is fine because this is recursion, not an
inductive definition, which is why the paper needs only induction on ℕ.

### 6.4 Stage-free relation [PAPER, Cor 2.33]

For `u, a ∈ C`, write `Γ ⊨ …` for the relation at any stage containing u and a. Cor 2.33 makes this
independent of the stage. In Verus, use a canonical stage such as `max(rank u, rank a, 1)`, or
`∃n` together with the corollary.

---------------------------------------------------------------------------------------------------

## 7. Properties of the logical relation (Section 2.7) [PAPER statements; RECON proofs]

All statements are for the two-sided relations; the diagonals are special cases.

- `Γ ⊨_n M ≡ N : A |_{u:a}` presupposes `u :_n a` and `a :_n U`.
- `Γ ⊨_n A ≡ A' type |_a` presupposes `a :_n U`.
- Grey premises (marked `[·]`) are redundant presuppositions. **State all of them as `requires`**,
  as the mechanisations do.

### 7.1 Statements

    (IsType)   Γ ⊨_n M ≡ N : A |_{u:a}  ⟹  Γ ⊨_n A type |_a
    (ToType)   Γ ⊨_n M ≡ N : A |_{u:U}  ⟹  Γ ⊨_n M ≡ N type |_u
    (Bot)      [a :_n U] [Γ ⊨_n A type |_a]  ⟹  Γ ⊨_n M ≡ N : A |_{⊥:a}      (any M, N)
    (Symm)     [Γ ⊢ M ≡ N : A]  Γ ⊨_n M ≡ N : A |_{u:a}  ⟹  Γ ⊨_n N ≡ M : A |_{u:a}
    (SymmTy)   Γ ⊨_n A1 ≡ A2 type |_a  ⟹  Γ ⊨_n A2 ≡ A1 type |_a
    (Trans)    [Γ ⊢ M1 ≡ M2 : A] [Γ ⊢ M2 ≡ M3 : A]
               Γ ⊨_n M1 ≡ M2 : A |_{u:a}   Γ ⊨_n M2 ≡ M3 : A |_{u:a}
                 ⟹  Γ ⊨_n M1 ≡ M3 : A |_{u:a}
    (TransTy)  Γ ⊨_n A1 ≡ A2 type |_a   Γ ⊨_n A2 ≡ A3 type |_a  ⟹  Γ ⊨_n A1 ≡ A3 type |_a
    (Trans')   Γ ⊨_n A1 ≡ A2 : 𝒰 |_{a:s}   Γ ⊨_n A2 ≡ A3 : 𝒰 |_{a:U}
                 ⟹  Γ ⊨_n A1 ≡ A3 : 𝒰 |_{a:s}
    (Conv)     Γ ⊨_n A ≡ B type |_a   Γ ⊨_n M ≡ N : A |_{u:a}  ⟹  Γ ⊨_n M ≡ N : B |_{u:a}
    (MonoTypeIncr)  [u :_n a] [u :_n a'] [Γ ⊨_n A type |_{a'}]  a ≤ a'
                    Γ ⊨_n M ≡ N : A |_{u:a}  ⟹  Γ ⊨_n M ≡ N : A |_{u:a'}
    (MonoTypeDecr)  a ≤ a'  [u :_n a] [a' :_n U]  Γ ⊨_n M ≡ N : A |_{u:a'}
                      ⟹  Γ ⊨_n M ≡ N : A |_{u:a}
    (MonoTypeDecrTy) a ≤ a'  [a :_n U] [a' :_n U]  Γ ⊨_n A ≡ B type |_{a'}
                      ⟹  Γ ⊨_n A ≡ B type |_a
    (MonoTerm) u ≤ u'  [u :_n a] [u' :_n a]  Γ ⊨_n M ≡ N : A |_{u':a}
                 ⟹  Γ ⊨_n M ≡ N : A |_{u:a}
    (JoinTy)   [a1 ↑ a2] [a1 :_n U] [a2 :_n U]
               Γ ⊨_n A ≡ B type |_{a1}   Γ ⊨_n A ≡ B type |_{a2}  ⟹  Γ ⊨_n A ≡ B type |_{a1∨a2}
    (Join)     [u1 ↑ u2] [u1 :_n a] [u2 :_n a]
               Γ ⊨_n M ≡ N : A |_{u1:a}   Γ ⊨_n M ≡ N : A |_{u2:a}  ⟹  Γ ⊨_n M ≡ N : A |_{u1∨u2:a}

The monotonicity rules go both ways: the relation can be lowered and raised along the witnesses.

[RECON] Add `a :_n U` to MonoTypeDecr, since the relation at `u:a` presupposes it. It follows from
`a ≤ a'`, `a' : U` and the inversions only in special cases.

**Cor 2.33 (Stability).** For `u, a ∈ C_n ⊆ C_{n+1}`:

    Γ ⊨_n A ≡ A' type |_a   ⇔  Γ ⊨_{n+1} A ≡ A' type |_a
    Γ ⊨_n M ≡ M' : A |_{u:a} ⇔ Γ ⊨_{n+1} M ≡ M' : A |_{u:a}

Consequently the stage can be dropped.

**Lemma 2.34 (Head reduction).** Assume `Γ ⊢ M ⇝* M' : A`, `Γ ⊢ N ⇝* N' : A` and
`Γ ⊢ M ≡ N : A`. Then

    Γ ⊨ M ≡ N : A |_{u:a}  ⇔  Γ ⊨ M' ≡ N' : A |_{u:a}

Since this is an equivalence, it gives head expansion as well as head reduction.

### 7.2 Proof outlines and mutual groups [RECON]

The paper says only that the properties are proved "by recursion on rank/stage, in several mutual
groups". The grouping below is mine, derived by checking which property each case needs.

**G1: IsType, ToType.** Immediate from the clauses.

- IsType at Π: the grey conjunct. At U: the first conjunct is exactly the U type clause. At ⊥: ⊤.
- ToType: the second conjunct of the U term clause.

**G2: {SymmTy, TransTy, Symm, Trans, Trans', Conv, Bot}**, one induction on n, each case split on
the type witness a. Needs determinism of head reduction and syntactic lemmas (Conv rule, context
conversion, substitution).

- **SymmTy at Π(a,b)**, swapping T and T':
  - Domain: SymmTy_n.
  - The swapped clause quantifies over terms related at `A'`. Transport them to `A` with Conv_n,
    using `A' ≡ A` from SymmTy_n; transport the syntactic conversion with the Conv rule.
  - Apply the hypothesis. For the cross conclusion `B'[M] ≡ B[M']`: apply the hypothesis to
    `(M', M)` (related by Symm_n) to get `B[M'] ≡ B'[M]`, then SymmTy_n.
  - Syntactic side: `Γ,x:A' ⊢ B' ≡ B` needs context conversion.
- **TransTy at Π.**
  - By determinism, both clauses mention the same reduct of `T2`, which identifies `A2, B2`.
  - Domain: TransTy_n.
  - Codomain `B1[M] ≡ B3[M']`: hypothesis 1 at `(M, M')` gives `B1[M] ≡ B2[M']`. Hypothesis 2 at
    `(M', M')` gives `B2[M'] ≡ B3[M']`. The pair `M' ≡ M'` is obtained by the PER argument
    (Symm_n, Trans_n) and Conv_n from `A1` to `A2`. Then TransTy_n.
- **Symm at Π** (term):
  - For `M' N ≡ M N'`: apply the hypothesis to `(N', N)` (Symm_n) to get `M N' ≡ M' N : B[N']`.
  - Symm_n gives `M' N ≡ M N' : B[N']`.
  - Conv_n from `B[N']` to `B[N]`, using the type clause's `B[N] ≡ B[N']` (plus SymmTy_n).
- **Trans at Π:** as TransTy, with the intermediate application `M2 N'`.
- **Symm/Trans at U:** reduce to SymmTy/TransTy at the same stage (the U term clause calls the type
  relation at the same n). Order within stage n+1: type properties first, then term properties.
- **Trans':** case on s. `s = ⊥` is trivial. `s = U` is Trans. Other s cannot type a (a is a code
  typed in U).
- **Conv at U:** transport "`A ⇝* 𝒰`" using the type relation `A ≡ B |_U`.
- **Conv at Π:**
  - B reduces to `Π A'' B''`.
  - The new clause quantifies over terms at `A''`. Move them to `A` with Conv_n, using the domain
    relation plus SymmTy_n.
  - Transport the results from `B_A[N]` to `B''[N]` using the codomain part of the type relation.
  - The grey conjunct `B type |_{Π}` comes from SymmTy and TransTy on `A ≡ B`.
- **Bot at Π:**
  - `app(⊥, w) = ⊥`, then Bot_n.
  - Needs `b(w) :_n U` (from `a : U`: Pi-rule outputs are U-typed, joined by 2.16) and
    `B[N] type |_{b(w)}`. The latter comes from the type clause (`B[N] ≡ B[N']`) and the PER
    properties.
  - At U: `M ≡ N type |_⊥ = ⊤`.

**G3: {MonoTypeDecrTy, MonoTerm, MonoTypeIncr, MonoTypeDecr}**, one induction on n. Within stage
n+1 the order is DecrTy, then MonoTerm, then Incr and Decr.

- **DecrTy_{n+1} at Π:**
  - `a = Π(b,g) ≤ a' = Π(b',g')`.
  - Domain by DecrTy_n.
  - For `v : b` related at `v:b`: `v : b'` by 2.17. MonoTypeIncr_n lifts to `v : b'`. The
    hypothesis gives relations at `g'(v)`. DecrTy_n lowers to `g(v) ≤ g'(v)`.
- **MonoTerm_{n+1}:**
  - At U: DecrTy_{n+1} on the witness `u ≤ u'`.
  - At Π: `app(u,w) ≤ app(u',w)`, then MonoTerm_n.
- **Incr_{n+1} at Π:** given `w : b'`, possibly not `: b`.
  - Let `w0 := π(w)`, the join of the entries of f's inputs that are `≤ w`. These are typed `b`, so
    `w0 : b` and `w0 : b'`, `w0 ≤ w`, and `f(w0) ≡ f(w)` (projection lemma §1.6(7)).
  - Lower the related arguments to `w0 : b'` (MonoTerm_n), then to `w0 : b` (Decr_n).
  - Apply the hypothesis, getting relations at `f(w0) : g(w0)`.
  - Incr_n to `g'(w)` (since `g(w0) ≤ g(w) ≤ g'(w)`). Then move `f(w0) ≡ f(w)` with MonoTerm_n both
    ways.
  - This is where the "well-chosen representation" (typed inputs) matters.
- **Decr_{n+1} at Π:** related args at `w : b` are at `w : b'` by 2.17 and Incr_n. Apply the
  hypothesis at `g'(w)`, then Decr_n to `g(w)`.

**G4: {JoinTy, Join}**, one induction on n. Needs G3.

- JoinTy at Π: `Π(b1,g1) ∨ Π(b2,g2) = Π(b1∨b2, g1++g2)`.
  - Domain by JoinTy_n.
  - For the codomain at `v : b1∨b2`: project v to `v1 = π_{g1}(v) : b1`, lower the related arguments
    (MonoTerm_n, Decr_n), apply hypothesis 1, and move `g1(v1) ≡ g1(v)`. Do the same for g2.
  - Then JoinTy_n at `g1(v) ∨ g2(v) ≡ (g1++g2)(v)`.
- Join at Π: similar, with `app(u1∨u2, w) ≡ app(u1,w) ∨ app(u2,w)`.

**Cor 2.33, Stability** [RECON proof]: induction on n.

- (⇐, from n+1 to n): lift `v :_n a` to `v :_{n+1} a` (2.18). Use IH(⇒) for the hypotheses and
  IH(⇐) for the conclusions.
- (⇒, from n to n+1): the new clause quantifies over `v ∈ C_{n+1}` with `v :_{n+1} a`, and v may
  not be in `C_n`.
  - Project `w := π(v)`, the join of the inputs of b (and of f for the term clause) that are `≤ v`.
    Then `w ∈ C_n`, `w :_n a`, `b(w) ≡ b(v)`, `f(w) ≡ f(v)`.
  - Lower the arguments with MonoTerm and IH(⇐).
  - Use the old clause at w, lift with IH(⇒), and move `b(w) ≡ b(v)` with DecrTy both ways (and
    MonoTerm for apps).
- The paper: "a main consequence of the monotonicity and stability laws".

**Lemma 2.34** [RECON proof]: induction on n, case on a.

- ⊥: trivial.
- U: the term relation is "`A ⇝* 𝒰` ∧ the type relation at u". The type relation is invariant under
  typed head reduction of its terms: its clauses only ask "`⇝*` some stuck head", and determinism
  gives `T ⇝* T'`, `T ⇝* P` stuck ⇒ `T' ⇝* P`. Conversions compose by Trans. Prove this type-level
  analogue first.
- Π: `M ⇝* M'` gives `M N ⇝* M' N` (congruence), typed by AppCong. Then the IH at stage n.

---------------------------------------------------------------------------------------------------

## 8. Adequacy, fundamental lemma, consequences

### 8.1 Substitution relation [PAPER, garbled; RECON]

The paper says `σ, σ' : Δ → Γ` are related over ρ (fitting Γ) when for every `(x:A) ∈ Γ`:

    Δ ⊨ σ(x) ≡ σ'(x) : A σ |_{ρ : ⟦A⟧ρ}

As printed this is ill-typed: `ρ` stands where `ρ(x)` should be, and `⟦A⟧ρ` is an ideal, not a
compact. Recommended reconstruction:

    related(Δ, σ, σ', Γ, ρ) :=
        fits(Γ, ρ)
      ∧ ∀x ∈ Γ.  Δ ⊢ σ(x) ≡ σ'(x) : A_x[σ]                                  (syntactic)
      ∧ ∀x ∈ Γ, ∀ a u.  mem(A_x, ρ, a) ∧ typed(a, U) ∧ le(u, ρ(x)) ∧ typed(u, a)
             ⟹  Δ ⊨ σ(x) ≡ σ'(x) : A_x[σ] |_{u:a}
      ∧ (recommended) ∀x ∈ Γ, ∀a. mem(A_x,ρ,a) ∧ typed(a,U)  ⟹  Δ ⊨ A_x[σ] ≡ A_x[σ'] type |_a

- The last conjunct is not in the paper. It avoids circularity when σ' must be related to itself:
  `σ' ≡ σ'` at `A_x[σ']` needs Conv along `A_x[σ] ≡ A_x[σ']`.
- The paper remarks that the ⊥ environment suffices only for closed instances. Interpreting a Π
  already forces the codomain to be considered under arbitrary arguments, so adequacy genuinely
  needs a general fitting environment.

### 8.2 Theorem 2.35 (Adequacy) [PAPER]

Let ρ fit Γ, and let `σ, σ' : Δ → Γ` be related over ρ. Then for `a ≤ ⟦A⟧ρ` with `a : U`, and
`u ≤ ⟦M⟧ρ` with `u : a`:

    Γ ⊢ A ≡ A' : 𝒰   ⟹  Δ ⊨ A[σ] ≡ A'[σ'] type |_a
    Γ ⊢ M ≡ M' : A   ⟹  Δ ⊨ M[σ] ≡ M'[σ'] : A[σ] |_{u:a}

Here "`a ≤ ⟦A⟧ρ`" means `mem(A, ρ, a)`.

Proof outline [RECON]. The paper says only "induction on the syntactic typing/conversion
judgement". It suffices to prove the term statement: the type statement is the term statement at
type 𝒰 with witness `a : U`, followed by ToType. Cases:

- **Var:** from `related`. Adjust the witnesses with MonoTerm, MonoTypeIncr/Decr and joins inside
  the ideal ⟦A⟧ρ.
- **Univ:** `a ∈ {⊥, U}` and `u ∈ {⊥, U}`. Reductions are 0 steps.
- **PiCong:** `u = ⊥` (Bot) or `u = Π(a1, g)`, a generator of `⟦Π A B⟧ρ`.
  - Domain: IH on `A ≡ A'`.
  - Codomain: for related `M ≡ M'` at `v : a1`, extend `(σ,M) ~ (σ',M')` over `ρ·v`. `ρ·v` fits
    `Γ.A` since `a1 ∈ ⟦A⟧ρ`. `g(v) ∈ ⟦B⟧_{ρ·v}` via the ideal lemmas and the projection.
  - The three conclusions `B[σ,M] ≡ B[σ,M']`, `B'[σ',M] ≡ B'[σ',M']`, `B[σ,M] ≡ B'[σ',M']` come
    from the IH on the three presupposition premises (`Γ.A ⊢ B : 𝒰`, `Γ.A' ⊢ B' : 𝒰`, and
    `B ≡ B'` under both contexts), with suitable substitution pairs: `(σ,σ)` and `(σ',σ')` via the
    PER properties.
  - Use Stability to put witnesses at the right stage, and substitution algebra
    `(B[σ↑])[M] = B[σ,M]`.
- **LamCong:** witness `a = Π(a1,g)`. `u = ⊥` is Bot. Otherwise `u = λ f`.
  - For related `N ≡ N'` at `w : a1`: `app(λ f, w) = f(w)`, and `f(w) ≡ f(π w)` with `π w : a2`
    (the λ generator's domain type). Also `f(w) ∈ ⟦M⟧_{ρ·w}`.
  - IH on `M ≡ M'` in `Γ.A`, with `ρ·w` and `(σ,N) ~ (σ',N')`, gives
    `M[σ,N] ≡ M'[σ',N'] : B[σ,N] |_{f(w) : g(w)}`.
  - Head-expand to `(λM[σ↑]) N` with Lemma 2.34. The typed reduction comes from the β rule.
  - The other two conclusions use the IH on the two presupposition copies.
- **AppCong:**
  - The goal witness is `u ≤ app(u1, v1)` with `u1 ∈ ⟦M⟧`, `v1 ∈ ⟦N⟧`, and `a ≤ ⟦B[N]⟧ρ`.
  - By soundness, raise `u1` to a λ typed at some `Π(a1,g) ∈ ⟦Π A B⟧`, and raise `v1` to `w : a1`
    (joining domain types inside `⟦A⟧`).
  - The IH on M gives the Π clause, instantiated with the IH on N.
  - Adjust the witnesses: `a` and `g(w)` are both in the ideal `⟦B⟧_{ρ·⟦N⟧}`, so they are
    compatible. Go up with MonoTypeIncr to the join and down with MonoTypeDecr to a. Lower u with
    MonoTerm.
  - Syntactic types: `B[σ↑][N[σ]] = B[N][σ]`.
- **Beta:** Lemma 2.34 (head reduction on the left side), then the IH on `M[N]`.
- **Eta:**
  - `a = Π(a1,g)`. By Thm 2.31, `u ≤ ⟦M⟧ρ = ⟦N⟧ρ`. This is where soundness enters adequacy: witness
    sets of the two sides agree.
  - For related W, W' at `w : a1`: the IH on `(M↑ 0) ≡ (N↑ 0)` over `ρ·w` with `(σ,W) ~ (σ',W')`,
    and `(M↑ 0)[σ,W] = M[σ] W`.
  - The witness is `app(u,w) ∈ ⟦M↑ 0⟧_{ρ·w}`.
  - The diagonal conclusions come from the IH on the typing premises.
- **Sym / Trans:** Symm/Trans, with witness transfer via soundness (`⟦M⟧ = ⟦N⟧`).
- **Conv:** the IH on `A ≡ B : 𝒰` at witness `a ∈ ⟦B⟧ = ⟦A⟧` (soundness), then Conv.

### 8.3 Theorem 2.36 (Fundamental lemma) [PAPER]

For `a ≤ ⟦A⟧_⊥` with `a : U`, and `u ≤ ⟦M⟧_⊥` with `u : a`:

    Γ ⊢ A ≡ A' : 𝒰  ⟹  Γ ⊨ A ≡ A' type |_a
    Γ ⊢ M ≡ M' : A  ⟹  Γ ⊨ M ≡ M' : A |_{u:a}

The paper: this is the special case `Δ = Γ`, `σ = σ' = id`, `ρ = ⊥`.

[RECON] The paper does not show that `id` is related to itself over ⊥. With the reconstructed
relation this needs, for each `(x:A) ∈ Γ`, `Γ ⊨ x ≡ x : A |_{⊥:a}` (Bot, which needs
`Γ ⊨ A type |_a`) and the type conjunct.

Obtain these by induction on Γ, quantifying over all extensions: for every `⊢ Γ.Θ`, the weakening
`↑^{|Θ|} : Γ.Θ → Γ` is related to itself over ⊥.

- Step `Γ.A`: for the new variable, apply adequacy (Thm 2.35) to `Γ ⊢ A : 𝒰` with substitution
  `↑^{|Θ|+1}`. It is related by the IH for Γ with extension `A.Θ`.
- This uses 2.35 only at shorter contexts.
- The ⊥ environment fits every context: `⊥ : a` for every U-typed `a ∈ ⟦A⟧_⊥`, and `⟦A⟧_⊥ : U`
  by soundness on the prefix.

### 8.4 Cor 2.37 (Injectivity of Π) [PAPER]

If `Γ ⊢ Π_{x:A}B ≡ Π_{x:A'}B' : 𝒰` then `Γ ⊢ A ≡ A' : 𝒰` and `Γ, x:A ⊢ B ≡ B' : 𝒰`.

Proof [PAPER]: the fundamental lemma gives `Γ ⊨ Π_{x:A}B ≡ Π_{x:A'}B' type |_{Π(⊥,⊥)}`. Unfold
the clause.

Details [RECON]:

- `Π(⊥, [])` is `: U` at stage 1, because `⊥ :_0 U` fails but `⊥ :_1 U` holds, and the Pi rule
  premises are at stage n−1. It is in `⟦Π A B⟧_⊥`: `⊥ ∈ ⟦A⟧`, and the empty presentation satisfies
  the generator condition vacuously.
- The reducts of the two Π-terms are themselves (0 steps; Π is stuck, determinism), so the clause's
  conversions are exactly the goal.

**Sort injectivity with levels** [PAPER, Section 3 "Universe hierarchies"]:

- Interpret every `𝒰_i` as U, erasing levels.
- Sharpen the U type clause to
  `Γ ⊨_n A ≡ A' type |_U := ∃i. Γ ⊢ A ⇝* 𝒰_i ∧ Γ ⊢ A' ⇝* 𝒰_i`.
- The fundamental lemma then gives `Γ ⊢ 𝒰_i ≡ 𝒰_j ⇒ i = j`.
- The Π clause records `Γ ⊢ A ≡ A' : 𝒰_i`, `Γ,x:A ⊢ B ≡ B' : 𝒰_j`.
- This works for cumulative and non-cumulative hierarchies.
- For `Sort(level)`: `∃ l'. A ⇝* Sort(l) ∧ A' ⇝* Sort(l')` with `l ≃ l'` (level equivalence).

### 8.5 Thm 2.38 (Subject reduction) [PAPER]

If `Γ ⊢ M : A` and `M ⇝* M'` then `Γ ⊢ M' : A`. The paper says only that Π-injectivity supplies
exactly the inversion needed.

[RECON] Induction on the length of `⇝*`, then induction on the head step.

- **Root β:** `(λ_{A0} b) N : T`. Generation gives `M = λ_{A0} b : Π A B`, `N : A`, `T ≡ B[N]`.
  Generation on λ gives `Γ.A0 ⊢ b : B0` with `Π A0 B0 ≡ Π A B`. Cor 2.37 gives `A0 ≡ A` and
  `B0 ≡ B`. Then `N : A0` (Conv), `b[N] : B0[N]` (substitution lemma), and
  `B0[N] ≡ B[N] ≡ T` (substitution into conversion), so `b[N] : T`.
- **Congruence `M N ⇝ M' N`:** generation, then the IH, then App and Conv.

(Thm 2.39 Progress, not needed: a closed well-typed term is a λ, a Π, a 𝒰, or head-reduces.)

---------------------------------------------------------------------------------------------------

## 9. The Prop extension (Section 3.6)

### 9.1 Syntax [PAPER]

    Prop:      ⊢Γ  ⟹  Γ ⊢ Prop : 𝒰
    Prop-U:    Γ ⊢ A : Prop  ⟹  Γ ⊢ A : 𝒰
    Fun-Prop:  Γ ⊢ A : 𝒰,  Γ,x:A ⊢ B : Prop  ⟹  Γ ⊢ Π_{x:A}B : Prop
    Irr:       Γ ⊢ A : Prop,  Γ ⊢ M : A,  Γ ⊢ N : A  ⟹  Γ ⊢ M ≡ N : A
    Prop-Uβ:   Γ ⊢ M ≡ N : Prop  ⟹  Γ ⊢ M ≡ N : 𝒰

- Prop is a sub-universe of 𝒰 and is closed under Π with codomain in Prop (impredicative in the
  domain).
- Irr is definitional proof irrelevance. Prop-Uβ propagates the resulting equalities from Prop to 𝒰.
- **Reduction is unchanged:** proof irrelevance is only an extensionality rule.

In the presupposition-carrying form [RECON]: Prop-U is the diagonal of Prop-Uβ. Fun-Prop becomes a
congruence with both-context premises, like PiCong but at Prop.

### 9.2 Domain model [PAPER]

- The only new compact is a code `Prop :_{n+1} U`, which the paper describes as lying below U.
- Proof irrelevance adds no elements. It imposes a **constraint**: prove that
  `u :_n a :_n Prop ⇒ u = ⊥`. Every proposition, interpreted as a type, is the singleton `{⊥}`.
- For Π: any inhabitant has the form `λ(f)`, and for each x, `f(x) :_{n−1} b(x) :_{n−1} Prop`
  gives `f(x) = ⊥` recursively. So `λ(f) = λ(⊥) = ⊥`.
- Other constructors (for example `⊤ : Prop` with unit-like rules) may be added if this property is
  maintained.

[RECON] Precise changes. The paper gives only the prose above.

- **Compacts:** add `Prop` to the enum, with rank 1.
  - `le(Prop, y) := y == Prop`; `join(Prop, Prop) = Prop`; `compat(Prop, Prop)`.
  - Prop is incompatible with U, Π and λ.
  - **Interpretation of "lying below U":** I read it as "Prop is a code *in* U" (`Prop : U`), not as
    `Prop ≤ U` in the information order. With `Prop ≤ U`, MonoTypeDecrTy would force the U type
    clause ("`A ⇝* 𝒰`") to imply the Prop type clause ("`A ⇝* Prop`"), which is false. The
    information-order reading is therefore incompatible with a sensible logical relation.
- **Semantic typing:** add three rules.

      PropU:   n ≥ 1                                            ⟹  Prop :_n U
      PiProp:  n ≥ 1,  b :_{n-1} U,  ∀i. g.in_i :_{n-1} b,  ∀i. g.out_i :_{n-1} Prop
                                                                ⟹  Π(b,g) :_n Prop
      Bot:     unchanged (⊥ :_n Prop because Prop :_n U)

  - The `(λ f, Π(b,g))` rule is unchanged. If `Π(b,g)` is a proposition, the constraint lemma
    shows its only typed inhabitant is ⊥.
  - Lemmas to add:
    - (a) `a :_n Prop ⇒ a :_n U` (induction on n; semantic Prop-U);
    - (b) **the constraint** `u :_n a ∧ a :_n Prop ⇒ u == ⊥`. Induction on n, case on a:
      - a = ⊥ ⇒ u = ⊥;
      - a = Π(b,g) ⇒ u = ⊥ or `u = λ f` with each `f.out_i :_{n−1} g(f.in_i)`, and
        `g(f.in_i) :_{n−1} Prop` (Prop outputs joined; needs 2.16 for Prop). By IH every output is
        ⊥, which contradicts `wf(λ f)` (some output ≠ ⊥);
      - a = U or a = Prop are not `: Prop`.
    - (b') the ≤-closed form: `u :_n a`, `a ≤ a'`, `a' :_n Prop` ⇒ `u = ⊥` (2.17, then (b));
    - extend 2.16, 2.17, 2.18 and the inversions to the new rules.
- **Interpretation:** `⟦Prop⟧ρ := {⊥, Prop}`. The Π clause is unchanged: `⟦Π A B⟧` does not depend
  on whether B is in Prop.
- **Soundness additions** (2.31):
  - Prop: `{⊥,Prop} : {⊥,U}`.
  - Fun-Prop: as the Pi case with Prop outputs.
  - Prop-U / Prop-Uβ: by (a); equality is unchanged.
  - **Irr:** `⟦A⟧ρ : ⟦Prop⟧`. Every `v ∈ ⟦M⟧` lies below some `v' : a'` with `a'` below an element
    typed `⊥` or `Prop` in ⟦A⟧. By (b') and `u : ⊥ ⇒ u = ⊥`, `v' = ⊥`. So `⟦M⟧ρ = {⊥} = ⟦N⟧ρ`.
- **Logical relation (additional clauses; the paper gives none for Prop):**

      Γ ⊨_n A ≡ A' type |_Prop        :=  Γ ⊢ A ⇝* Prop : 𝒰  ∧  Γ ⊢ A' ⇝* Prop : 𝒰
      Γ ⊨_{n+1} M ≡ M' : A |_{u:Prop} :=  Γ ⊢ A ⇝* Prop : 𝒰  ∧  Γ ⊨_{n+1} M ≡ M' type |_u

  - Terms at a type witness a with `a : Prop` use the existing clauses (Π). Since `u : a` forces
    `u = ⊥`, only the Bot property is ever needed there.
  - ToType generalises to the Prop witness.
  - The G2–G4 cases at Prop mirror those at U. Mono cases: `Prop ≤ a'` forces `a' = Prop`.
- **Adequacy additions:**
  - **Irr:** the goal witness `u : a` with `a ∈ ⟦A⟧ρ`, and `⟦A⟧ρ : ⟦Prop⟧` by soundness. By (b'),
    `u = ⊥`. Conclude by Bot, which needs `Δ ⊨ A[σ] type |_a` from the IH on the premise
    `Γ ⊢ M : A` via IsType.
  - **Prop-Uβ:** the goal witness has type `a ∈ {⊥,U}`. For `a = U`: `u : U` and `u ∈ ⟦M⟧`. By
    soundness, `⟦M⟧ : ⟦Prop⟧`, so `u ≤ v ∈ ⟦M⟧` with `v : Prop` (or `v : ⊥`, hence `v = u = ⊥`).
    The IH at `v : Prop` gives "`M ≡ N type |_v`". MonoTypeDecrTy (`u ≤ v`, both `: U`) gives it
    at u. Assemble the U term clause (`𝒰 ⇝* 𝒰`).
  - **Fun-Prop:** as PiCong with the outer witness `Prop`.
  - **Prop formation:** 0-step reductions.
- **Injectivity:** a Π-equation at Prop reaches 𝒰 by Prop-Uβ and then falls under Cor 2.37.
  Disjointness of Prop and 𝒰 (and of Prop and Π) follows from the model or the relation.

[NOTE, Lean alignment] Lean's `Sort 0` is impredicative Prop and `Sort (l+1)` is a universe. Erase
`Sort(l)` to Prop if `l ≃ 0` and to U otherwise. The fragment must then decide "is this level
zero" for every Sort that occurs. With level parameters and `imax` this may be undetermined, so
restrict to closed levels or add a level valuation to the environment. The sharpened U clause then
compares levels up to equivalence.

---------------------------------------------------------------------------------------------------

## 10. Pitfalls

1. **⊥ vs λ⊥ coalescing.**
   - `λ(⊥) = ⊥`, but `Π(⊥,⊥) ≠ ⊥`.
   - In the unquotiented representation, wf forbids a λ whose outputs are all ⊥, and ⊥ must be added
     explicitly wherever a λ could degenerate. Use `mk_lam` everywhere a λ is built.
   - This is also what makes the η case of soundness and the Prop constraint go through.
2. **Non-unique presentations; setoid.**
   - All paper "=" on compacts is `≡`. Never use `==` for semantic equality of compacts.
   - Junk pairs `(u ↦ ⊥)` do not change the function but break intensional typing. The intensional
     rules hold only for a well-chosen representation.
   - Rank is not ≡-invariant, so in-stage is only a sufficient condition.
3. **Typing is not downward closed in the subject**, and `u : a` does not imply `a : U`. Hence the
   grey premises (`u :_n a`, `a :_n U`) on every property. Keep them as explicit `requires`.
4. **Prop 2.17 needs `a' : U`.** Otherwise it is false at `a = ⊥`.
5. **Stage 0 is empty for typing.** `⊥ :_0 a` is false, so the canonical stage must be ≥ 1.
6. **Figure 4 transcription issues.**
   - The variable case is garbled (it must be `u ≤ ρ(x)`).
   - The λ/Π clauses must be read as down-closures to form ideals (my analysis).
   - ⊥ is added explicitly to Π, and to λ in the canonical representation.
7. **The relation at ⊥ is ⊤.** It carries no syntactic information: Bot holds for arbitrary M, N.
   Syntactic conversions are therefore separate premises (grey `Γ ⊢ M ≡ N : A` in Symm and Trans),
   and the Π clauses record them.
8. **Mixed-stage recursion.** The U term clause calls the type relation at the **same** stage, and
   the Π term clause calls the type relation at the same stage (grey conjunct). Use the measure
   `(n, tag)`. Within a stage, prove type-level properties before term-level ones.
9. **Determinism of head reduction** is essential: it identifies the reducts in TransTy, Trans and
   SymmTy (the middle term's reduct), and it drives Lemma 2.34. Typed head reduction must bundle
   the conversion, because SR is proved only at the end.
10. **Presupposition-carrying rules** (Section 4): congruences under both contexts, β/η with both
    sides typed. Without them the adequacy cases lack the IHs for the diagonal and cross
    conclusions. Prove the equivalence with the economical rules separately, if at all.
11. **Soundness is used inside adequacy.** It transfers witnesses between sides that have equal
    interpretations (η, Sym, Trans, Conv).
12. **The substitution relation is garbled** (§8.1). Getting `id` related over ⊥ needs a context
    induction that the paper does not describe.
13. **Mutual groups** (§7.2): G2 and G3 each need their own simultaneous induction on n.
    Stability (2.33) needs G3 at stage n+1.
14. **Measures:**
    - compacts: rank (not structural size), because `apply` builds new terms by joins;
    - typing: `(n, #bots)`;
    - relation: `(n, tag)`;
    - ⟦·⟧ and Lemma 2.29: structural recursion on the term;
    - soundness and adequacy: derivation height (or structural on a derivation tree);
    - fundamental lemma: additionally the context length.
15. **No inversion for neutrals.** Variables and neutrals are all ⊥, so the relation never says
    anything about `x M ≡ y N`.
16. **"Prop lies below U"** must mean `Prop : U`, not `Prop ≤ U` (§9.2).
17. **Finite C_n is not to be relied on** (the paper warns that extensions break it). Avoid
    enumerating C_n; quantify over in-stage compacts instead.
18. **The model is coarse by design.** All inversions come from the syntactic conversions recorded
    in the relation, never from the model alone. Only disjointness-type results (Thm 2.32) come
    from the model directly.

---------------------------------------------------------------------------------------------------

## 11. Verus encoding notes (concrete suggestions)

### 11.1 Compacts

```rust
pub enum Compact {
    Bot,
    U,
    Prop,                                      // Prop extension
    Lam(Box<Steps>),                           // step function; wf => some output != Bot
    Pi(Box<Compact>, Box<Steps>),              // domain, codomain step function
}
pub enum Steps { Nil, Cons(Box<Compact>, Box<Compact>, Box<Steps>) }  // (input, output) list
```

A hand-rolled cons list gives free structural `decreases` and avoids the question of whether
`decreases` passes through `Seq` inside a datatype. If `Seq<(Compact, Compact)>` is preferred,
probe the height/decreases mechanism in a scratch file first.

Spec fns:

- `rank(c): nat` and `rank_steps(s): nat` (structural).
- `wf(c)`, `wf_steps(s)`, `fun_ok(s)` (structural plus calls to `compat`).
- `le(u, v)`, `le_fun(f, g)`, `apply(f, x)`, `apply_acc(...)`: **mutual**, with
  `decreases rank(u) + rank(v)` (apply: `rank_steps(f) + rank(x)`). Check each edge:
  - `le(λf, λf')` → `apply(f', u_i)`: `rank(f') + rank(u_i) < rank(λf) + rank(λf')`;
  - `apply(f, x)` → `le(u_i, x)`;
  - `le(v_i, apply(f',u_i))` uses `rank(apply(f',u_i)) ≤ rank_steps(f')`. This needs a rank lemma
    inside the decreases proof (`decreases_by` or `via`), or make apply's result rank syntactically
    evident. The alternative is `le_fun(f, f') := ∀i. ∃`-free "`le(v_i, join-of-selected)`"
    unfolded via a helper that walks f' and calls `le(u'_j, u_i)`.
  - This mutual recursion follows the memory note on fuel: every edge must decrease.
- `join(u, v)` (structural, total, junk on incompatible) and `compat(u, v)` (decreases rank sum).
- `app(u, w) := match u { Lam(f) => apply(f, w), _ => Bot }`.
- `mk_lam(f)`.
- `proj(s, x)`: the join of s's inputs that are `≤ x`.

### 11.2 Semantic typing

```text
spec fn has_type(n: nat, u: Compact, a: Compact) -> bool
  decreases n, (if u is Bot {1} else {0}) + (if a is Bot {1} else {0})
```

- Use the intensional rules of §2.3 (plus Prop rules). The finite `∀ i` over entries can be written
  as `forall|i| 0 <= i < len ==> has_type(n-1, nth_in(s,i), b)`, or as a structural helper
  `all_typed_in(n, s, b)` recursing on `Steps`. The helper avoids quantifiers entirely, is closest
  to Lean's Boolean-valued definition, and is easier to trigger.
- Stage-free: `typed(u,a) := has_type(max(rank u, rank a, 1), u, a)`.

### 11.3 Syntax and judgements

- `enum Term { Var(nat), Sort(Level), Pi(Box<Term>, Box<Term>), Lam(Box<Term>, Box<Term>), App(Box<Term>, Box<Term>) }`
  plus lift/subst with the usual algebra. The repo's `subst_algebra.rs` may be reusable.
- **Judgements as explicit derivation trees:**
  `enum Deriv { Var{..}, Univ{..}, Sym(Box<Deriv>), Trans(Box<Deriv>, Box<Deriv>), Conv(..), PiCong(..), LamCong(..), AppCong(..), Beta(..), Eta(..), Prop.., Irr(..), PropUb(..) }`
  with `concl(d) -> (Ctx, Term, Term, Term)` and a structural checker `valid(d)`. Then
  `conv(Γ,M,N,A) := ∃d. valid(d) ∧ concl(d) == (Γ,M,N,A)`, as a non-recursive wrapper.
- This avoids existentials (middle terms of Trans, types in Conv) inside a recursive spec fn. Per
  the project's memory, such existentials are unprovable from outside and should be replaced by
  explicit chains behind a non-recursive wrapper. Soundness and adequacy become `proof fn`s with
  `decreases d`.
- Head reduction: `hstep(t) -> Option<Term>` (deterministic), `hiter(t, k)`, and
  `hred(t,t') := ∃k. hiter(t,k) == t'` wrapped as a named (possibly opaque) predicate.
  `hred_typed(Γ,t,t',A) := hred(t,t') ∧ conv(Γ,t,t',A)`.
- For the relation's "`T ⇝* Π A B`" define `pi_reduct(T) := hiter(T, choose|k| is_pi(hiter(T,k)))`
  and use its fields. Determinism makes the choice irrelevant (prove a lemma).

### 11.4 Interpretation

`mem(M: Term, rho: Seq<Compact>, u: Compact) -> bool`, `decreases M`, as in §5.2 (down-closure of
intensional generators).

- The existentials (`∃ a f` for λ/Π, `∃ w v` for App) live inside a structurally recursive spec fn.
  If introducing them from outside is painful, use the marker-predicate trigger technique from the
  project memory (match-arm exists trigger law), or split each arm into a non-recursive named
  predicate that takes the recursive call results as arguments.
- Ideal equality: `sem_eq(M, N, rho) := forall|u| mem(M,rho,u) <==> mem(N,rho,u)`. Never compare
  closures with `==`.

### 11.5 Logical relation, by recursion on the stage

```text
spec fn rel_ty(n: nat, g: Ctx, t: Term, t2: Term, a: Compact) -> bool
  decreases n, 0nat
{
  match a {
    Bot  => true,
    U    => hred_typed(g, t, Sort(u), Sort(u)) && hred_typed(g, t2, ...),   // (level-sharpened: same level)
    Prop => ... reduces to Prop ...,
    Pi(b, gs) => n >= 1 && reduces_to_pi(g,t) && reduces_to_pi(g,t2)
        && conv(g, dom(t), dom(t2), U) && conv(g.push(dom(t)), cod(t), cod(t2), U)
        && rel_ty(n-1, g, dom(t), dom(t2), *b)
        && forall|m: Term, m2: Term, v: Compact|
             #![trigger rel_tm(n-1, g, m, m2, dom(t), v, *b)]
             has_type(n-1, v, *b) && conv(g, m, m2, dom(t)) && rel_tm(n-1, g, m, m2, dom(t), v, *b)
               ==> rel_ty(n-1, g, subst0(cod(t), m),  subst0(cod(t),  m2), apply(gs, v))
                && rel_ty(n-1, g, subst0(cod(t2), m), subst0(cod(t2), m2), apply(gs, v))
                && rel_ty(n-1, g, subst0(cod(t), m),  subst0(cod(t2), m2), apply(gs, v)),
    _ => false,
  }
}
spec fn rel_tm(n: nat, g: Ctx, m: Term, m2: Term, ty: Term, u: Compact, a: Compact) -> bool
  decreases n, 1nat
{
  match a {
    Bot  => true,
    U    => n >= 1 && reduces_to_U(g, ty) && rel_ty(n, g, m, m2, u),      // same n, tag drops
    Prop => n >= 1 && reduces_to_Prop(g, ty) && rel_ty(n, g, m, m2, u),
    Pi(b, gs) => n >= 1 && rel_ty(n, g, ty, ty, a) && reduces_to_pi(g, ty)
        && forall|nn, nn2, w| has_type(n-1, w, *b) && conv(g, nn, nn2, dom(ty))
                               && rel_tm(n-1, g, nn, nn2, dom(ty), w, *b)
             ==> rel_tm(n-1, g, App(m,nn),  App(m,nn2),  subst0(cod(ty), nn), app(u, w), apply(gs, w))
              && rel_tm(n-1, g, App(m2,nn), App(m2,nn2), subst0(cod(ty), nn), app(u, w), apply(gs, w))
              && rel_tm(n-1, g, App(m,nn),  App(m2,nn2), subst0(cod(ty), nn), app(u, w), apply(gs, w)),
    _ => false,
  }
}
```

- The two spec fns are mutually recursive with lexicographic `decreases n, tag`. Recursive calls
  inside `forall` bodies are allowed if the decreases check passes. **Probe this first** in a
  scratch file (mutual recursion + lexicographic measure + call under a quantifier in a negative
  position).
- `rel_ty` at the `U` case ignores n. The `U` term clause needs `n >= 1` because `U ∉ C_0`.
- Triggers: the Π clause's `forall` needs a trigger mentioning all three bound variables.
  `rel_tm(n-1, g, m, m2, dom(t), v, *b)` works. Consumers instantiate by asserting the hypothesis
  terms. Given the project's experience with multi-var quantifiers, consider wrapping the whole
  forall as a named predicate `pi_codomain_ok(n, g, t, t2, b, gs)` defined by the same forall.
- Stage-free wrappers: `rel_ty_sf(g,t,t2,a) := rel_ty(stage_of(a), ...)` and
  `rel_tm_sf(..., u, a) := rel_tm(max(rank u, rank a, 1), ...)`, with Cor 2.33 as the bridge.
- The §7 properties are `proof fn`s with `decreases n` (and a secondary tag where same-stage calls
  occur). Each takes the grey premises as `requires`. One proof fn per property per group; the
  mutual groups become mutually recursive proof fns with a shared `decreases n, k`, where k orders
  the properties within a stage.

### 11.6 Adequacy data

- `related(Δ, σ, σ', Γ, ρ)` as in §8.1, with `σ: Seq<Term>` (a parallel substitution for de
  Bruijn variables).
- `fits(Γ, ρ)` as in §5.5.
- Adequacy: `proof fn adequacy(d: Deriv, ρ, Δ, σ, σ', a, u) requires valid(d), fits, related, mem(A,ρ,a), typed(a,U), mem(M,ρ,u), typed(u,a) ensures rel_tm_sf(...) decreases d`.

### 11.7 Suggested staging of the Verus work

1. Compacts plus order lemmas (§1.6), including the projection lemma. This is the riskiest
   termination proof (`le` and `apply` mutual on rank).
2. `has_type` plus 2.16, 2.17, 2.18, the inversions, and (Prop) the constraint lemma.
3. Syntax: derivation trees, substitution/weakening/context-conversion lemmas, generation, head
   reduction determinism.
4. `mem` plus the ideal lemmas plus Lemma 2.29, then soundness (2.31).
5. `rel_ty`/`rel_tm` plus groups G1–G4, Stability, and Lemma 2.34.
6. Adequacy, the context induction for `id`, the fundamental lemma, injectivity, then SR.
