use vstd::prelude::*;

verus! {

// ============================================================
// CASE A: exists inside a NON-recursive open spec fn -- works.
// ============================================================

pub open spec fn step(x: int, y: int) -> bool {
    y == x + 1
}

pub open spec fn joined_nr(x: int, y: int) -> bool {
    exists |z: int| #[trigger] step(x, z) && #[trigger] step(y, z)
}

proof fn intro_nr(x: int, y: int, w: int)
    requires step(x, w), step(y, w)
    ensures joined_nr(x, y)
{
    // passes with an empty body: the non-recursive body is inlined,
    // the ground trigger terms fire, the witness is found.
}

// ============================================================
// CASE B: the SAME exists inside a RECURSIVE open spec fn -- the
// introduction (witnessing) direction fails.
// ============================================================

pub open spec fn r(x: int, y: int, h: nat) -> bool
    decreases h
{
    ||| x == y
    ||| (h > 0 && exists |z: int| #[trigger] r(x, z, (h - 1) as nat) && #[trigger] r(z, y, (h - 1) as nat))
}

proof fn intro_rec(x: int, y: int, w: int, h: nat)
    requires r(x, w, (h - 1) as nat), r(w, y, (h - 1) as nat), h > 0
    ensures r(x, y, h)      // FAILS: postcondition not satisfied
{
}

proof fn intro_rec_with_assert(x: int, y: int, w: int, h: nat)
    requires r(x, w, (h - 1) as nat), r(w, y, (h - 1) as nat), h > 0
    ensures r(x, y, h)      // STILL FAILS
{
    // re-writing the quantifier does not help: a separately-written
    // alpha-equivalent exists is a distinct closure and never bridges
    // to the one inside r's fuel-guarded definition axiom.
    assert(exists |z: int| #[trigger] r(x, z, (h - 1) as nat) && #[trigger] r(z, y, (h - 1) as nat));
    // (the assert itself passes; the postcondition still fails)
}

// The other directions DO work, so the failure is specifically the
// witnessing of the embedded existential from outside:

proof fn unfold_rec(x: int, y: int, h: nat)
    requires r(x, y, 0), x != y
    ensures false
{
    // passes: unfolding through the quantifier-free disjunct works.
}

proof fn fold_rec(x: int, y: int, h: nat)
    requires x == y
    ensures r(x, y, h)
{
    // passes: folding through the quantifier-free disjunct works.
}

// ============================================================
// CASE C: the workaround -- keep the step relation recursive and
// quantifier-free, and put the ONLY existential in a non-recursive
// wrapper (chain form). Both directions work.
// ============================================================

pub open spec fn chain_valid(ch: Seq<int>, h: nat) -> bool {
    forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 ==> r(ch[i], ch[i + 1], h)
}

pub open spec fn r_star(x: int, y: int, h: nat) -> bool {
    exists |ch: Seq<int>| ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && chain_valid(ch, h)
}

proof fn intro_star(x: int, y: int, w: int, h: nat)
    requires r(x, w, h), r(w, y, h)
    ensures r_star(x, y, h)
{
    let ch = seq![x, w, y];
    assert(ch.len() == 3 && ch[0] == x && ch[ch.len() - 1] == y);
    assert(chain_valid(ch, h)) by {
        assert forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies r(ch[i], ch[i + 1], h) by {
            if i == 0 { assert(ch[0] == x && ch[1] == w); } else { assert(ch[1] == w && ch[2] == y); }
        }
    }
}

proof fn elim_star(x: int, y: int, h: nat)
    requires r_star(x, y, h)
    ensures exists |ch: Seq<int>| ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && chain_valid(ch, h)
{
    // passes: choose/exists against a non-recursive wrapper works.
}

} // verus!

fn main() {}
