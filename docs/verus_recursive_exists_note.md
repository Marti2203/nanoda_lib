# Verus note: an `exists` inside a recursive spec fn cannot be witnessed from outside

Status: reproduced on this repo's Verus fork (see `verus_recursive_exists_repro.rs`
in this directory — `verus verus_recursive_exists_repro.rs --crate-type lib` gives
**6 verified, 2 errors**, and the two failures are exactly the two lemmas that try
to witness the embedded existential). Discovered 2026-08-30 while building
`tc_model.rs::deq`; this note is written to be upstream-issue-ready.

## Behavior

Given a **recursive** `open spec fn` whose body embeds an existential — the
natural way to write a transitive closure with a height index:

```rust
pub open spec fn r(x: int, y: int, h: nat) -> bool
    decreases h
{
    ||| x == y
    ||| (h > 0 && exists |z: int| #[trigger] r(x, z, (h - 1) as nat) && #[trigger] r(z, y, (h - 1) as nat))
}
```

the *introduction* direction is unprovable, even in the most favorable form,
with the witness's trigger terms literally present as `requires`:

```rust
proof fn intro_rec(x: int, y: int, w: int, h: nat)
    requires r(x, w, (h - 1) as nat), r(w, y, (h - 1) as nat), h > 0
    ensures r(x, y, h)      // FAILS: postcondition not satisfied
{ }
```

Re-asserting an identical `exists` in the proof body does not help — the assert
itself *passes*, but the postcondition still fails:

```rust
    assert(exists |z: int| #[trigger] r(x, z, (h - 1) as nat) && #[trigger] r(z, y, (h - 1) as nat));  // passes
    // ensures r(x, y, h)  -- still fails
```

Meanwhile all of the following verify, so the failure is *specifically* the
witnessing of the embedded existential from outside the definition:

- the same `exists` in a **non-recursive** `open spec fn` (empty-body intro passes);
- *unfolding* the recursive fn through its quantifier-free disjuncts;
- *folding* into the recursive fn through a quantifier-free disjunct.

## What we ruled out

Everything below was tried on the real relation (`deq` in `tc_model.rs`) before
concluding the behavior is structural, not a formulation bug:

1. **`reveal_with_fuel(r, 2/3)`** — no effect.
2. **Trigger hygiene** — the arithmetic term `(h - 1) as nat` inside the annotated
   trigger does get silently degraded (Verus prints "automatically chose triggers"
   notes instead of erroring), but removing the arithmetic did not fix it:
3. **Naming the existential as a mutually recursive helper** spec fn
   (`deq_trans_at(env, x, y, hm)` with lexicographic `decreases h, 0int` /
   `decreases hm, 1int`), so the quantifier's trigger arguments are plain
   parameters — introduction and elimination lemmas for the helper *still* fail,
   because the helper is a member of the recursive clique and therefore also
   fuel-guarded.
4. **Pure-variable intro/elim wrapper lemmas** around that helper — same failure.

## Why (our best understanding)

Two independently-written alpha-equivalent quantifiers are distinct closures in
the encoding; nothing ever identifies them (the same fact underlies the known
`Seq::new`-closure-identity gotcha). A **non-recursive** `open spec fn`'s body is
effectively inlined at use sites, so the definition's `exists` and a caller's
`assert`/`choose` land on the *same* formula instance and everything works. A
**recursive** fn's body instead sits behind a fuel-guarded definitional axiom —
it is never inlined — so proving the definition's `exists` requires the SMT
solver to bridge from the caller's separately-encoded quantifier (or from ground
facts through the definition-side quantifier's triggers), and in practice this
instantiation does not happen, even when the exact trigger terms exist as ground
facts in the context.

If this is intended behavior, it deserves a diagnostic: today the definition
compiles cleanly and the failure surfaces far away as an unprovable
postcondition, which pattern-matches to (and cost us several rounds of) trigger
debugging.

## The reliable pattern (workaround)

Split the relation: keep the recursive fn **quantifier-free per disjunct** (a
"one step" relation — congruence arms via `match`), and put the *only*
existential in a **non-recursive wrapper** as an explicit chain:

```rust
pub open spec fn chain_valid(ch: Seq<int>, h: nat) -> bool {
    forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 ==> r(ch[i], ch[i + 1], h)
}

pub open spec fn r_star(x: int, y: int, h: nat) -> bool {
    exists |ch: Seq<int>| ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && chain_valid(ch, h)
}
```

Both directions verify (see the repro's `intro_star`/`elim_star`). Transitivity
becomes chain concatenation (free), symmetry chain reversal, congruence
`Seq::new` chain-mapping — this is exactly the architecture `beta_model.rs`'s
`pstep`/`pstep_chain_valid`/`pstep_star` and `tc_model.rs`'s `deq_c`/`deq` use,
and a standard normalization argument shows chains lose no generality against an
inline transitivity constructor.
