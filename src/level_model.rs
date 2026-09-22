//! Exploratory Verus model of universe-level arithmetic (`Level` in `level.rs`).
//!
//! `level.rs`'s functions operate on `LevelPtr<'t>`, an index into `TcCtx`'s
//! interning arena, so proving anything about them directly requires modeling
//! the arena itself. To make progress on the *algorithm* first, this module
//! defines a standalone, arena-free recursive mirror of `Level` (`LevelSpec`,
//! using `Box` instead of arena pointers) together with a semantic
//! interpretation `interp` (level + parameter assignment -> the natural
//! number it denotes). We then prove executable functions ported from
//! `level.rs` respect that semantics.
//!
//! This is scaffolding, not a finished verification of `level.rs`: connecting
//! these theorems back to the real arena-based code requires showing the
//! arena's `read_level`/interning maintains a simulation with `LevelSpec`,
//! which is future work.
use vstd::prelude::*;

verus! {

/// Arena-free mirror of `crate::level::Level`. `Param` carries a raw `u64` id
/// rather than an interned `Name`, since name identity plays no role in the
/// semantics below (only equality) — and unlike a ghost `nat`, `u64` is a
/// real runtime value, so exec code can actually compare two params' ids
/// (needed by `leq_core_partial` below).
#[derive(Debug, PartialEq)]
pub enum LevelSpec {
    Zero,
    Succ(Box<LevelSpec>),
    Max(Box<LevelSpec>, Box<LevelSpec>),
    IMax(Box<LevelSpec>, Box<LevelSpec>),
    Param(u64),
}

pub open spec fn max_nat(a: nat, b: nat) -> nat {
    if a >= b {
        a
    } else {
        b
    }
}

/// `lw` deliberately ignores `Succ`: `lw(Succ a) == lw(a)`. Those arms are
/// the ones that move `diff`, and they shrink the term, so they are paid
/// for by `level_depth` rather than by `lw`.
/// The value a level denotes under a parameter assignment `rho`. Unassigned
/// params default to 0, matching Lean's convention that missing substitutions
/// leave the level unconstrained-but-well-defined for our purposes here.
/// The SIMPLIFIED-FORM invariant: hereditarily, no `IMax`'s second argument
/// is a `Zero` or a `Succ`.
///
/// This is what makes `leq_core`'s final catch-all `panic!()` unreachable.
/// Enumerating that function's arms, the pairs left uncovered are exactly
/// those whose `IMax` has a `Zero` or `Succ` in second position -- every
/// other shape is caught by an earlier arm, by `is_param(b)`, or by
/// `is_any_max(b)`. `simplify` establishes the invariant: those two cases are
/// precisely the ones its `IMax` arm collapses (to `r_simp`, and through
/// `combining`) instead of building an `IMax` node.
/// Candidate termination weight for `leq_core`, the missing piece behind the
/// `diff` overflow obligation.
///
/// The two hard arms are the ones that REWRITE rather than descend, and they
/// grow the term, so no size or subterm measure works:
///
///     IMax(a, IMax(x, y))  ->  Max(IMax(a, y), IMax(x, y))     (y duplicated)
///     IMax(a, Max(x, y))   ->  Max(IMax(a, x), IMax(a, y))     (a duplicated)
///
/// A multiset of second-argument sizes handles the first and fails on the
/// second; a max over them fails on both, since duplication is invisible to a
/// max and `a` may carry a heavier `IMax` than the one being rewritten.
///
/// This weight charges an `IMax`'s SECOND argument double and a `Max` a
/// constant. Doubling makes pushing an `IMax`/`Max` out of second position
/// strictly cheaper, and the `Max` constant pays for the duplication.
///
/// `leq_core`'s `diff - 1` is an `isize` overflow
/// obligation, and bounding `diff` means bounding how many `Succ` strips a
/// call can perform -- i.e. `leq_core`'s termination argument, which is what
/// `exec_allows_no_decreases_clause` gives up. The intended measure is
/// lexicographic:
///
///     (lw(l) + lw(r),  params_in_imax(l) + params_in_imax(r),  size(l) + size(r))
///
/// with each arm paid for by exactly one component:
///
///   - `Max` descent, and both `IMax` rewrites  -> first  (proven above)
///   - `leq_imax_by_cases`                      -> second (a `Param` in
///     second position is substituted by `0`/`succ p`, and `simplify` then
///     collapses that `IMax` node away; `lw` alone is only non-increasing
///     there, since `lw(Succ p) == lw(p) == 0`)
///   - `Succ` strip, which is where `diff` moves -> third
///
/// The first half of the second component is DONE: `simplify` now proves
/// `lw(result) <= lw(ptr)` (and `combining` the bound that induction needs),
/// both on the kernel's own code.
///
/// The other half is blocked, and worth recording because the blocker is not
/// where it looks. `leq_imax_by_cases` substitutes through `subst_simp` =
/// `subst_level` then `simplify`, so the second component needs
/// `subst_level`'s semantics -- that substituting a `Param` by `0`/`succ p`
/// leaves `lw` alone and drops that param from second position. But
/// `subst_level` cannot be migrated into `verus!` at all: its `Param` arm
/// walks `.iter().copied().zip(..)`, and Verus has no spec for
/// `Iterator::copied`. So this arc and the upstream `copied` gap are the same
/// blocker, not two.
///
/// Giving `subst_level` a trusted `assume_specification` would unblock it at
/// the cost of an assumption on the very function the measure rests on.
pub open spec fn lw(l: LevelSpec) -> nat
    decreases l,
{
    match l {
        LevelSpec::Zero => 0,
        LevelSpec::Param(_) => 0,
        LevelSpec::Succ(a) => lw(*a),
        LevelSpec::Max(a, b) => 1 + max_nat(lw(*a), lw(*b)),
        LevelSpec::IMax(a, b) => lw(*a) + 2 * lw(*b) + 1,
    }
}

/// `IMax(a, IMax(x, y))  ->  Max(IMax(a, y), IMax(x, y))` strictly decreases.
pub proof fn lw_decreases_imax_imax(a: LevelSpec, x: LevelSpec, y: LevelSpec)
    ensures
        lw(
            LevelSpec::Max(
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
                Box::new(LevelSpec::IMax(Box::new(x), Box::new(y))),
            ),
        ) < lw(LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::IMax(Box::new(x), Box::new(y))))),
{
    let n1 = LevelSpec::IMax(Box::new(a), Box::new(y));
    let n2 = LevelSpec::IMax(Box::new(x), Box::new(y));
    assert(lw(n1) == lw(a) + 2 * lw(y) + 1);
    assert(lw(n2) == lw(x) + 2 * lw(y) + 1);
    assert(lw(LevelSpec::Max(Box::new(n1), Box::new(n2))) == 1 + max_nat(lw(n1), lw(n2)));
    assert(lw(LevelSpec::IMax(Box::new(a), Box::new(n2))) == lw(a) + 2 * lw(n2) + 1);
    // max(A, B) <= A + B when both are nats, which is all the slack needed
    assert(max_nat(lw(n1), lw(n2)) <= lw(a) + lw(x) + 2 * lw(y) + 1);
}

/// `IMax(a, Max(x, y))  ->  Max(IMax(a, x), IMax(a, y))` strictly decreases.
/// This is the arm that duplicates `a`, and the one every simpler measure
/// fails on.
pub proof fn lw_decreases_imax_max(a: LevelSpec, x: LevelSpec, y: LevelSpec)
    ensures
        lw(
            LevelSpec::Max(
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(x))),
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
            ),
        ) < lw(LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::Max(Box::new(x), Box::new(y))))),
{
    let m1 = LevelSpec::IMax(Box::new(a), Box::new(x));
    let m2 = LevelSpec::IMax(Box::new(a), Box::new(y));
    assert(lw(m1) == lw(a) + 2 * lw(x) + 1);
    assert(lw(m2) == lw(a) + 2 * lw(y) + 1);
    assert(lw(LevelSpec::Max(Box::new(m1), Box::new(m2))) == 1 + max_nat(lw(m1), lw(m2)));
    let mx = LevelSpec::Max(Box::new(x), Box::new(y));
    assert(lw(mx) == 1 + max_nat(lw(x), lw(y)));
    assert(lw(LevelSpec::IMax(Box::new(a), Box::new(mx))) == lw(a) + 2 * lw(mx) + 1);
    // both branches carry the same `lw(a)`, so the Max constant is the margin
    assert(max_nat(lw(m1), lw(m2)) == lw(a) + 2 * max_nat(lw(x), lw(y)) + 1);
}

/// Second component of `leq_core`'s measure: how many `IMax` nodes carry a
/// `Param` in second position. Those are the ones `leq_imax_by_cases`
/// eliminates -- it substitutes the param by `0`/`succ p`, and `simplify`
/// then collapses the `IMax` away (its `IMax` arm returns `r_simp` for a
/// `Zero` second argument, and folds through `combining` for a `Succ` one).
pub open spec fn params_in_imax(l: LevelSpec) -> nat
    decreases l,
{
    match l {
        LevelSpec::Zero => 0,
        LevelSpec::Param(_) => 0,
        LevelSpec::Succ(a) => params_in_imax(*a),
        LevelSpec::Max(a, b) => params_in_imax(*a) + params_in_imax(*b),
        LevelSpec::IMax(a, b) => params_in_imax(*a) + params_in_imax(*b) + (
        if matches!(*b, LevelSpec::Param(_)) {
            1nat
        } else {
            0nat
        }),
    }
}

/// NOT monotone under `simplify`, which is a trap worth recording. Take
/// `IMax(l, Max(Zero, Param p))`: the second argument is a `Max`, so it
/// contributes 0. `simplify` turns `Max(Zero, Param p)` into `Param p` (via
/// `combining`'s `(Zero, _)` arm), and the node then contributes 1 -- the
/// count went UP.
///
/// So the lexicographic argument cannot lean on this component alone across
/// a `simplify`. In that example `lw` strictly decreases (`lw(Max(Zero, p))`
/// is 1 and `lw(Param p)` is 0, so the `IMax` drops from `lw(l)+3` to at
/// most `lw(l)+1`), which is what saves it -- but that has to be PROVEN as a
/// relation between the two components, not assumed.
pub proof fn params_in_imax_not_monotone_under_simplify()
    ensures
        params_in_imax(
            LevelSpec::IMax(
                Box::new(LevelSpec::Zero),
                Box::new(LevelSpec::Max(Box::new(LevelSpec::Zero), Box::new(LevelSpec::Param(0)))),
            ),
        ) == 0,
        params_in_imax(LevelSpec::IMax(Box::new(LevelSpec::Zero), Box::new(LevelSpec::Param(0))))
            == 1,
        // and the weight moves the other way, which is the saving grace
        lw(LevelSpec::IMax(Box::new(LevelSpec::Zero), Box::new(LevelSpec::Param(0)))) < lw(
            LevelSpec::IMax(
                Box::new(LevelSpec::Zero),
                Box::new(LevelSpec::Max(Box::new(LevelSpec::Zero), Box::new(LevelSpec::Param(0)))),
            ),
        ),
{
    assert(params_in_imax(LevelSpec::Zero) == 0);
    assert(params_in_imax(LevelSpec::Param(0)) == 0);
    assert(params_in_imax(LevelSpec::Max(Box::new(LevelSpec::Zero), Box::new(LevelSpec::Param(0))))
        == 0) by {
        reveal_with_fuel(params_in_imax, 3);
    }
    assert(lw(LevelSpec::Max(Box::new(LevelSpec::Zero), Box::new(LevelSpec::Param(0)))) == 1) by {
        reveal_with_fuel(lw, 3);
    }
}

/// The parameters appearing DIRECTLY as an `IMax`'s second argument.
///
/// Written as a candidate third component of `leq_core`'s termination measure
/// and **refuted** -- it does not strictly decrease at `leq_imax_by_cases`,
/// because `simplify` can collapse a `Max` that was hiding a parameter and so
/// move a NEW one into second position. `docs/LEQ_CORE_TERMINATION.md` carries
/// the witness.
///
/// Kept because the statements below are correct and are the natural building
/// blocks if a combined measure is ever found. They are not, on their own, the
/// answer, and nothing depends on them yet.
/// The clique measure's first component is a SET, but `decreases` needs a
/// well-founded value, so what it actually uses is the cardinality. These two
/// turn the subset facts proven above into the `len` facts the `decreases`
/// clauses will need, once, instead of at all seventeen edges.
pub proof fn undet_len_mono(a: Set<u64>, b: Set<u64>)
    requires
        a.subset_of(b),
    ensures
        a.len() <= b.len(),
{
    vstd::set_lib::lemma_len_subset(a, b);
}

/// The `by_cases` edge: "the parameter left, and nothing else arrived" becomes
/// a STRICT drop in cardinality. This is the step that makes the measure's
/// first component actually decrease rather than merely not grow.
pub proof fn undet_len_strict(a: Set<u64>, b: Set<u64>, x: u64)
    requires
        a.subset_of(b),
        b.contains(x),
        !a.contains(x),
    ensures
        a.len() < b.len(),
{
    assert(a.subset_of(b.remove(x))) by {
        assert forall|n: u64| a.contains(n) implies b.remove(x).contains(n) by {
            assert(n != x);
        }
    }
    vstd::set_lib::lemma_len_subset(a, b.remove(x));
    assert(b.remove(x).len() == b.len() - 1);
}

/// THE SCALAR MEASURE for `leq_core` (docs/LEQ_CORE_TERMINATION.md). A single
/// `nat`, so it can be summed with `|diff|` -- which is what the lexicographic
/// form could not do, and what the overflow bound actually needs.
///
/// The weights are FORCED, not chosen:
///
/// - `lw` gets **2**: the `IMax` rewrites drop `lw` by at least one while
///   `level_depth` grows by at most one, on the one side being rewritten.
/// - `undet` gets **3**: `by_cases` substitutes into BOTH sides, so
///   `level_depth` can grow by one *each*, +2 in total, against a drop of at
///   least one in `undet`.
///
/// That +2 is the easy thing to get wrong -- a first draft used weight 2 here
/// and the `by_cases` arm came out non-strict.
///
/// Nothing grows by more than one per side, which is `level_depth` being a
/// `max` rather than a sum.
pub open spec fn leq_measure(l: LevelSpec, r: LevelSpec) -> nat {
    3 * undet_imax_params(l).union(undet_imax_params(r)).len() + 2 * (lw(l) + lw(r)) + level_depth(
        l,
    ) + level_depth(r)
}

/// Peeling a `Succ` off the left drops the measure by EXACTLY one -- `undet`
/// and `lw` are both blind to `Succ`, and `level_depth` counts it. This is the
/// arm where `diff` moves, so the exact figure is what makes `|diff| + M`
/// non-increasing rather than merely bounded.
pub proof fn leq_measure_succ_left(sub: LevelSpec, r: LevelSpec)
    ensures
        leq_measure(LevelSpec::Succ(Box::new(sub)), r) == leq_measure(sub, r) + 1,
{
    undet_imax_params_succ(sub);
    assert(undet_imax_params(LevelSpec::Succ(Box::new(sub))).union(undet_imax_params(r))
        =~= undet_imax_params(sub).union(undet_imax_params(r)));
}

/// The mirror image, for the arm that moves `diff` the other way.
pub proof fn leq_measure_succ_right(l: LevelSpec, sub: LevelSpec)
    ensures
        leq_measure(l, LevelSpec::Succ(Box::new(sub))) == leq_measure(l, sub) + 1,
{
    undet_imax_params_succ(sub);
    assert(undet_imax_params(l).union(undet_imax_params(LevelSpec::Succ(Box::new(sub))))
        =~= undet_imax_params(l).union(undet_imax_params(sub)));
}

/// The `Max` arms: `leq_core` recurses into one side at a time, and `lw` alone
/// pays for it (`lw(Max(a,b)) = 1 + max(..)` is strictly above either branch).
pub proof fn leq_measure_max_left(a: LevelSpec, b: LevelSpec, r: LevelSpec)
    ensures
        leq_measure(a, r) < leq_measure(LevelSpec::Max(Box::new(a), Box::new(b)), r),
{
    let mx = LevelSpec::Max(Box::new(a), Box::new(b));
    undet_imax_params_max_sub(a, b);
    undet_len_mono(
        undet_imax_params(a).union(undet_imax_params(r)),
        undet_imax_params(mx).union(undet_imax_params(r)),
    );
    assert(undet_imax_params(a).union(undet_imax_params(r)).subset_of(
        undet_imax_params(mx).union(undet_imax_params(r)),
    ));
    lw_max_gt(a, b);
}

/// The mirror of `leq_measure_max_left`, for the arms that recurse into the
/// RIGHT side's `Max` branches.
pub proof fn leq_measure_max_right(l: LevelSpec, x: LevelSpec, y: LevelSpec)
    ensures
        leq_measure(l, x) < leq_measure(l, LevelSpec::Max(Box::new(x), Box::new(y))),
{
    let mx = LevelSpec::Max(Box::new(x), Box::new(y));
    undet_imax_params_max_sub(x, y);
    undet_len_mono(
        undet_imax_params(l).union(undet_imax_params(x)),
        undet_imax_params(l).union(undet_imax_params(mx)),
    );
    assert(undet_imax_params(l).union(undet_imax_params(x)).subset_of(
        undet_imax_params(l).union(undet_imax_params(mx)),
    ));
    lw_max_gt(x, y);
}

/// The right-hand mirrors of the two `IMax` rewrite lemmas and of
/// `leq_measure_mono_left`. `leq_core` rewrites whichever side carries the
/// nested `IMax`, so both directions are needed.
pub proof fn leq_measure_imax_imax_right(l: LevelSpec, a: LevelSpec, x: LevelSpec, y: LevelSpec)
    ensures
        leq_measure(
            l,
            LevelSpec::Max(
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
                Box::new(LevelSpec::IMax(Box::new(x), Box::new(y))),
            ),
        ) < leq_measure(
            l,
            LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::IMax(Box::new(x), Box::new(y)))),
        ),
{
    let lhs = LevelSpec::Max(
        Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
        Box::new(LevelSpec::IMax(Box::new(x), Box::new(y))),
    );
    let rhs = LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::IMax(Box::new(x), Box::new(y))));
    undet_imax_params_imax_imax(a, x, y);
    undet_len_mono(
        undet_imax_params(l).union(undet_imax_params(lhs)),
        undet_imax_params(l).union(undet_imax_params(rhs)),
    );
    assert(undet_imax_params(l).union(undet_imax_params(lhs)).subset_of(
        undet_imax_params(l).union(undet_imax_params(rhs)),
    ));
    lw_decreases_imax_imax(a, x, y);
    level_depth_imax_imax_le(a, x, y);
}

pub proof fn leq_measure_imax_max_right(l: LevelSpec, a: LevelSpec, x: LevelSpec, y: LevelSpec)
    ensures
        leq_measure(
            l,
            LevelSpec::Max(
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(x))),
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
            ),
        ) < leq_measure(
            l,
            LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::Max(Box::new(x), Box::new(y)))),
        ),
{
    undet_imax_params_imax_max(a, x, y);
    lw_decreases_imax_max(a, x, y);
    level_depth_imax_max_le(a, x, y);
}

pub proof fn leq_measure_mono_right(l: LevelSpec, r: LevelSpec, r2: LevelSpec)
    requires
        undet_imax_params(r2).subset_of(undet_imax_params(r)),
        lw(r2) <= lw(r),
        level_depth(r2) <= level_depth(r),
    ensures
        leq_measure(l, r2) <= leq_measure(l, r),
{
    assert(undet_imax_params(l).union(undet_imax_params(r2)).subset_of(
        undet_imax_params(l).union(undet_imax_params(r)),
    ));
    undet_len_mono(
        undet_imax_params(l).union(undet_imax_params(r2)),
        undet_imax_params(l).union(undet_imax_params(r)),
    );
}

/// `leq_measure` is monotone in a left-hand replacement that does not grow any
/// component. `leq_core`'s `IMax`/`Max` arm runs `simplify` before recursing,
/// and `simplify` promises exactly these three bounds -- this assembles them.
pub proof fn leq_measure_mono_left(l: LevelSpec, l2: LevelSpec, r: LevelSpec)
    requires
        undet_imax_params(l2).subset_of(undet_imax_params(l)),
        lw(l2) <= lw(l),
        level_depth(l2) <= level_depth(l),
    ensures
        leq_measure(l2, r) <= leq_measure(l, r),
{
    assert(undet_imax_params(l2).union(undet_imax_params(r)).subset_of(
        undet_imax_params(l).union(undet_imax_params(r)),
    ));
    undet_len_mono(
        undet_imax_params(l2).union(undet_imax_params(r)),
        undet_imax_params(l).union(undet_imax_params(r)),
    );
}

/// The SECOND branch of a left `Max` -- `Max(a,b)` is not `Max(b,a)` as a
/// `LevelSpec`, so the first lemma does not cover it.
pub proof fn leq_measure_max_left2(a: LevelSpec, b: LevelSpec, r: LevelSpec)
    ensures
        leq_measure(b, r) < leq_measure(LevelSpec::Max(Box::new(a), Box::new(b)), r),
{
    let mx = LevelSpec::Max(Box::new(a), Box::new(b));
    undet_imax_params_max_sub(a, b);
    undet_len_mono(
        undet_imax_params(b).union(undet_imax_params(r)),
        undet_imax_params(mx).union(undet_imax_params(r)),
    );
    assert(undet_imax_params(b).union(undet_imax_params(r)).subset_of(
        undet_imax_params(mx).union(undet_imax_params(r)),
    ));
    lw_max_gt(a, b);
}

/// The second branch of a right `Max`.
pub proof fn leq_measure_max_right2(l: LevelSpec, x: LevelSpec, y: LevelSpec)
    ensures
        leq_measure(l, y) < leq_measure(l, LevelSpec::Max(Box::new(x), Box::new(y))),
{
    let mx = LevelSpec::Max(Box::new(x), Box::new(y));
    undet_imax_params_max_sub(x, y);
    undet_len_mono(
        undet_imax_params(l).union(undet_imax_params(y)),
        undet_imax_params(l).union(undet_imax_params(mx)),
    );
    assert(undet_imax_params(l).union(undet_imax_params(y)).subset_of(
        undet_imax_params(l).union(undet_imax_params(mx)),
    ));
    lw_max_gt(x, y);
}

/// The first `IMax` rewrite: `lw` drops by at least one (weight 2) against a
/// `level_depth` growth of at most one. Net at most -1.
pub proof fn leq_measure_imax_imax(a: LevelSpec, x: LevelSpec, y: LevelSpec, r: LevelSpec)
    ensures
        leq_measure(
            LevelSpec::Max(
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
                Box::new(LevelSpec::IMax(Box::new(x), Box::new(y))),
            ),
            r,
        ) < leq_measure(
            LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::IMax(Box::new(x), Box::new(y)))),
            r,
        ),
{
    let lhs = LevelSpec::Max(
        Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
        Box::new(LevelSpec::IMax(Box::new(x), Box::new(y))),
    );
    let rhs = LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::IMax(Box::new(x), Box::new(y))));
    undet_imax_params_imax_imax(a, x, y);
    undet_len_mono(
        undet_imax_params(lhs).union(undet_imax_params(r)),
        undet_imax_params(rhs).union(undet_imax_params(r)),
    );
    assert(undet_imax_params(lhs).union(undet_imax_params(r)).subset_of(
        undet_imax_params(rhs).union(undet_imax_params(r)),
    ));
    lw_decreases_imax_imax(a, x, y);
    level_depth_imax_imax_le(a, x, y);
}

/// The second `IMax` rewrite, same shape -- and here `undet` is exactly equal
/// rather than merely non-increasing.
pub proof fn leq_measure_imax_max(a: LevelSpec, x: LevelSpec, y: LevelSpec, r: LevelSpec)
    ensures
        leq_measure(
            LevelSpec::Max(
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(x))),
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
            ),
            r,
        ) < leq_measure(
            LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::Max(Box::new(x), Box::new(y)))),
            r,
        ),
{
    undet_imax_params_imax_max(a, x, y);
    lw_decreases_imax_max(a, x, y);
    level_depth_imax_max_le(a, x, y);
}

/// The arena-wide bound on `leq_measure`. `leq_core`'s callers cannot thread a
/// measure bound upward -- `leq`, `is_zero` and `simplify` are mutually
/// recursive -- so it has to be an invariant of the arena, in the same style as
/// `local_type_cap()`.
///
/// What it assumes: universe levels appearing in a real export file have
/// bounded measure. That is a far weaker claim than the `leq` axiom it is meant
/// to replace ("the universe-ordering decision procedure is sound"), and it is
/// the same shape this crate already trusts elsewhere.
pub uninterp spec fn leq_measure_cap() -> nat;

#[verifier::external_body]
pub proof fn leq_measure_bounded(l: LevelSpec, r: LevelSpec)
    ensures
        leq_measure(l, r) <= leq_measure_cap(),
        leq_measure_cap() <= 500_000_000,
{
}

/// `by_cases` fires exactly when an `IMax`'s second argument is a bare `Param`,
/// and that parameter IS in the set. Without this the departure proven above
/// would be a no-op rather than a decrease.
pub proof fn undet_imax_params_contains_imax_param(a: LevelSpec, p: u64)
    ensures
        undet_imax_params(LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::Param(p)))).contains(p),
{
}

// PROBE, run and removed: two mutually recursive EXEC functions, one keeping
// its argument and dropping a phase constant, the other raising the phase and
// dropping the argument -- exactly the clique measure's shape. It VERIFIES, so
// the phase component is sound machinery and not wishful thinking. Recorded
// here rather than left in the tree, like the contradiction detectors.
/// The `subst_simp -> simplify` edge's `lw` column. Substituting a parameter by
/// a WEIGHTLESS value leaves `lw` exactly unchanged -- and both of `by_cases`'
/// values are weightless (`lw(Zero) == 0`, and `lw(Succ(Param p)) ==
/// lw(Param p) == 0`, since `lw` ignores `Succ` by design).
///
/// This is what lets that edge fall through to the phase component. It cannot
/// fall through to `level_depth`, which GROWS there -- see the ordering note in
/// docs/LEQ_CORE_TERMINATION.md.
pub proof fn lw_subst_preserved(l: LevelSpec, p: u64, v: LevelSpec)
    requires
        lw(v) == 0,
    ensures
        lw(subst_level_spec(l, seq![p], seq![v])) == lw(l),
    decreases l,
{
    match l {
        LevelSpec::Zero => {},
        LevelSpec::Param(q) => {
            if q == p {
                assert(find_level_idx(seq![p], q) == Some(0nat));
            } else {
                assert forall|j: int| 0 <= j < seq![p].len() implies seq![p][j] != q by {
                    assert(seq![p][j] == p);
                }
                find_level_idx_no_match(seq![p], q);
            }
        },
        LevelSpec::Succ(a) => {
            lw_subst_preserved(*a, p, v);
        },
        LevelSpec::Max(a, b) => {
            lw_subst_preserved(*a, p, v);
            lw_subst_preserved(*b, p, v);
        },
        LevelSpec::IMax(a, b) => {
            lw_subst_preserved(*a, p, v);
            lw_subst_preserved(*b, p, v);
        },
    }
}

/// Structural height of a level. The THIRD component of the clique measure in
/// docs/LEQ_CORE_TERMINATION.md -- it is what covers the two edges where both
/// `undet_imax_params` and `lw` are flat: `leq_core`'s `Succ` peels and
/// `simplify`'s own `Succ` arm. (`lw` deliberately ignores `Succ`, which is
/// exactly why those edges need something else.)
pub open spec fn level_depth(l: LevelSpec) -> nat
    decreases l,
{
    match l {
        LevelSpec::Zero => 0,
        LevelSpec::Param(_) => 0,
        LevelSpec::Succ(a) => 1 + level_depth(*a),
        LevelSpec::Max(a, b) => 1 + max_nat(level_depth(*a), level_depth(*b)),
        LevelSpec::IMax(a, b) => 1 + max_nat(level_depth(*a), level_depth(*b)),
    }
}

/// Substituting a SHALLOW value raises the HEIGHT by at most one, however many
/// occurrences there are. `level_depth` is a `max`, not a sum -- that is the
/// whole point, and it is what makes a SCALAR measure possible with no
/// term-size ceiling.
pub proof fn level_depth_subst_le(l: LevelSpec, p: u64, v: LevelSpec)
    requires
        level_depth(v) <= 1,
    ensures
        level_depth(subst_level_spec(l, seq![p], seq![v])) <= level_depth(l) + 1,
    decreases l,
{
    match l {
        LevelSpec::Zero => {},
        LevelSpec::Param(q) => {
            if q == p {
                assert(find_level_idx(seq![p], q) == Some(0nat));
            } else {
                assert forall|j: int| 0 <= j < seq![p].len() implies seq![p][j] != q by {
                    assert(seq![p][j] == p);
                }
                find_level_idx_no_match(seq![p], q);
            }
        },
        LevelSpec::Succ(a) => {
            level_depth_subst_le(*a, p, v);
        },
        LevelSpec::Max(a, b) => {
            level_depth_subst_le(*a, p, v);
            level_depth_subst_le(*b, p, v);
        },
        LevelSpec::IMax(a, b) => {
            level_depth_subst_le(*a, p, v);
            level_depth_subst_le(*b, p, v);
        },
    }
}

/// `IMax(a, IMax(x,y)) -> Max(IMax(a,y), IMax(x,y))` raises the height by at
/// most one -- again because `level_depth` maxes rather than sums, so
/// duplicating `y` costs nothing.
pub proof fn level_depth_imax_imax_le(a: LevelSpec, x: LevelSpec, y: LevelSpec)
    ensures
        level_depth(
            LevelSpec::Max(
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
                Box::new(LevelSpec::IMax(Box::new(x), Box::new(y))),
            ),
        ) <= level_depth(
            LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::IMax(Box::new(x), Box::new(y)))),
        ) + 1,
{
    let da = level_depth(a);
    let dx = level_depth(x);
    let dy = level_depth(y);
    reveal_with_fuel(level_depth, 3);
    assert(level_depth(LevelSpec::IMax(Box::new(x), Box::new(y))) == 1 + max_nat(dx, dy));
    assert(level_depth(LevelSpec::IMax(Box::new(a), Box::new(y))) == 1 + max_nat(da, dy));
    assert(level_depth(
        LevelSpec::Max(
            Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
            Box::new(LevelSpec::IMax(Box::new(x), Box::new(y))),
        ),
    ) == 1 + max_nat(1 + max_nat(da, dy), 1 + max_nat(dx, dy)));
    assert(level_depth(
        LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::IMax(Box::new(x), Box::new(y)))),
    ) == 1 + max_nat(da, 1 + max_nat(dx, dy)));
}

/// `IMax(a, Max(x,y)) -> Max(IMax(a,x), IMax(a,y))`, same bound, same reason.
pub proof fn level_depth_imax_max_le(a: LevelSpec, x: LevelSpec, y: LevelSpec)
    ensures
        level_depth(
            LevelSpec::Max(
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(x))),
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
            ),
        ) <= level_depth(
            LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::Max(Box::new(x), Box::new(y)))),
        ) + 1,
{
    let da = level_depth(a);
    let dx = level_depth(x);
    let dy = level_depth(y);
    reveal_with_fuel(level_depth, 3);
    assert(level_depth(LevelSpec::Max(Box::new(x), Box::new(y))) == 1 + max_nat(dx, dy));
    assert(level_depth(LevelSpec::IMax(Box::new(a), Box::new(x))) == 1 + max_nat(da, dx));
    assert(level_depth(LevelSpec::IMax(Box::new(a), Box::new(y))) == 1 + max_nat(da, dy));
    assert(level_depth(
        LevelSpec::Max(
            Box::new(LevelSpec::IMax(Box::new(a), Box::new(x))),
            Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
        ),
    ) == 1 + max_nat(1 + max_nat(da, dx), 1 + max_nat(da, dy)));
    assert(level_depth(
        LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::Max(Box::new(x), Box::new(y)))),
    ) == 1 + max_nat(da, 1 + max_nat(dx, dy)));
}

/// `lw` strictly drops into either `Max` branch -- `leq_core`'s `Max` arms and
/// `simplify`'s `Max` arm.
pub proof fn lw_max_gt(a: LevelSpec, b: LevelSpec)
    ensures
        lw(LevelSpec::Max(Box::new(a), Box::new(b))) > lw(a),
        lw(LevelSpec::Max(Box::new(a), Box::new(b))) > lw(b),
{
}

/// Parameters occurring at a position NOT underneath any `Succ`. A `Succ`
/// wrapper is the syntactic marker for "known nonzero", so everything beneath
/// one is decided and does not count.
pub open spec fn params_outside_succ(l: LevelSpec) -> Set<u64>
    decreases l,
{
    match l {
        LevelSpec::Zero => Set::empty(),
        LevelSpec::Param(n) => Set::empty().insert(n),
        LevelSpec::Succ(_) => Set::empty(),
        LevelSpec::Max(a, b) => params_outside_succ(*a).union(params_outside_succ(*b)),
        LevelSpec::IMax(a, b) => params_outside_succ(*a).union(params_outside_succ(*b)),
    }
}

/// The FOURTH measure candidate for `leq_core` (docs/LEQ_CORE_TERMINATION.md
/// §4): parameters whose zero-ness is still undecided AND that sit in an
/// `IMax`'s second subtree, where that undecidedness is what blocks reduction.
///
/// It threads between the two refuted variants. `imax_params` counts only
/// DIRECT second-position occurrences and fails `by_cases`' `Zero` branch (a
/// parameter can enter when `simplify` collapses a `Max` that was hiding it);
/// counting the whole second subtree fails the `Succ` branch (the parameter is
/// still in the subtree afterwards). Counting the subtree MINUS what sits under
/// a `Succ` survives both: `p := Succ(Param p)` puts every occurrence of `p`
/// under a `Succ`, so `p` leaves; and a parameter hidden under a `Max` was
/// already counted before the collapse, so it never "enters".
///
/// NOT yet proven to be a measure -- see the note for what remains, of which
/// the `simplify` non-growth lemma is the real work.
pub open spec fn undet_imax_params(l: LevelSpec) -> Set<u64>
    decreases l,
{
    match l {
        LevelSpec::Zero => Set::empty(),
        LevelSpec::Param(_) => Set::empty(),
        LevelSpec::Succ(a) => undet_imax_params(*a),
        LevelSpec::Max(a, b) => undet_imax_params(*a).union(undet_imax_params(*b)),
        LevelSpec::IMax(a, b) => undet_imax_params(*a).union(undet_imax_params(*b)).union(
            params_outside_succ(*b),
        ),
    }
}

/// Peeling an outer `Succ` changes nothing: it hides no `IMax`.
pub proof fn undet_imax_params_succ(a: LevelSpec)
    ensures
        undet_imax_params(LevelSpec::Succ(Box::new(a))) == undet_imax_params(a),
{
}

/// Each `Max` branch contributes a subset -- the `Max` arms of `leq_core`
/// recurse into one side at a time.
pub proof fn undet_imax_params_max_sub(a: LevelSpec, b: LevelSpec)
    ensures
        undet_imax_params(a).subset_of(undet_imax_params(LevelSpec::Max(Box::new(a), Box::new(b)))),
        undet_imax_params(b).subset_of(undet_imax_params(LevelSpec::Max(Box::new(a), Box::new(b)))),
{
}

/// First `IMax` rewrite: `IMax(a, IMax(x,y)) -> Max(IMax(a,y), IMax(x,y))`.
/// NON-INCREASING -- `x`'s undecided parameters leave, because `x` moves out of
/// second position into first.
pub proof fn undet_imax_params_imax_imax(a: LevelSpec, x: LevelSpec, y: LevelSpec)
    ensures
        undet_imax_params(
            LevelSpec::Max(
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
                Box::new(LevelSpec::IMax(Box::new(x), Box::new(y))),
            ),
        ).subset_of(
            undet_imax_params(
                LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::IMax(Box::new(x), Box::new(y)))),
            ),
        ),
{
    reveal_with_fuel(undet_imax_params, 3);
    // Both sides unfold to unions of the same five pieces; the right has one
    // more (`params_outside_succ(x)`), which is exactly what `x` leaving second
    // position gives up.
    let ua = undet_imax_params(a);
    let ux = undet_imax_params(x);
    let uy = undet_imax_params(y);
    let px = params_outside_succ(x);
    let py = params_outside_succ(y);
    let lhs = undet_imax_params(
        LevelSpec::Max(
            Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
            Box::new(LevelSpec::IMax(Box::new(x), Box::new(y))),
        ),
    );
    let rhs = undet_imax_params(
        LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::IMax(Box::new(x), Box::new(y)))),
    );
    assert(lhs =~= ua.union(uy).union(py).union(ux.union(uy).union(py)));
    assert(rhs =~= ua.union(ux.union(uy).union(py)).union(px.union(py)));
    assert forall|n: u64| lhs.contains(n) implies rhs.contains(n) by {
        assert(ua.contains(n) || ux.contains(n) || uy.contains(n) || py.contains(n));
    }
}

/// Second `IMax` rewrite: `IMax(a, Max(x,y)) -> Max(IMax(a,x), IMax(a,y))`.
/// FLAT -- exactly equal, which is why the count may lead the lexicographic
/// order here where `imax_params` could not.
pub proof fn undet_imax_params_imax_max(a: LevelSpec, x: LevelSpec, y: LevelSpec)
    ensures
        undet_imax_params(
            LevelSpec::Max(
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(x))),
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
            ),
        ) =~= undet_imax_params(
            LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::Max(Box::new(x), Box::new(y)))),
        ),
{
    reveal_with_fuel(undet_imax_params, 3);
    let ua = undet_imax_params(a);
    let ux = undet_imax_params(x);
    let uy = undet_imax_params(y);
    let px = params_outside_succ(x);
    let py = params_outside_succ(y);
    let lhs = undet_imax_params(
        LevelSpec::Max(
            Box::new(LevelSpec::IMax(Box::new(a), Box::new(x))),
            Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
        ),
    );
    let rhs = undet_imax_params(
        LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::Max(Box::new(x), Box::new(y)))),
    );
    assert(lhs =~= ua.union(ux).union(px).union(ua.union(uy).union(py)));
    assert(rhs =~= ua.union(ux.union(uy)).union(px.union(py)));
    assert forall|n: u64| lhs.contains(n) == rhs.contains(n) by {}
    assert(lhs =~= rhs);
}

/// THE `by_cases` STEP, first half. Substituting `p := v` throughout, where `v`
/// itself has no `p` outside a `Succ`, leaves no `p` outside a `Succ`.
pub proof fn params_outside_succ_subst_single(l: LevelSpec, p: u64, v: LevelSpec)
    requires
        !params_outside_succ(v).contains(p),
    ensures
        !params_outside_succ(subst_level_spec(l, seq![p], seq![v])).contains(p),
    decreases l,
{
    match l {
        LevelSpec::Zero => {},
        LevelSpec::Succ(_) => {},
        LevelSpec::Param(q) => {
            if q == p {
                assert(find_level_idx(seq![p], q) == Some(0nat));
            } else {
                assert forall|j: int| 0 <= j < seq![p].len() implies seq![p][j] != q by {
                    assert(seq![p][j] == p);
                }
                find_level_idx_no_match(seq![p], q);
            }
        },
        LevelSpec::Max(a, b) => {
            params_outside_succ_subst_single(*a, p, v);
            params_outside_succ_subst_single(*b, p, v);
        },
        LevelSpec::IMax(a, b) => {
            params_outside_succ_subst_single(*a, p, v);
            params_outside_succ_subst_single(*b, p, v);
        },
    }
}

/// THE `by_cases` STEP, second half -- and the reason this candidate exists.
///
/// After `by_cases` substitutes its parameter, that parameter is GONE from the
/// measure's first component. Both of the values it substitutes satisfy the
/// hypotheses trivially, and for the same structural reason:
///
///   `p := Zero`            -- erases every occurrence
///   `p := Succ(Param p)`   -- keeps them, but every one is now under a `Succ`,
///                             and both predicates are blind underneath one
///
/// The corollary below instantiates exactly those two.
pub proof fn undet_imax_params_subst_single(l: LevelSpec, p: u64, v: LevelSpec)
    requires
        !params_outside_succ(v).contains(p),
        !undet_imax_params(v).contains(p),
    ensures
        !undet_imax_params(subst_level_spec(l, seq![p], seq![v])).contains(p),
    decreases l,
{
    match l {
        LevelSpec::Zero => {},
        LevelSpec::Param(q) => {
            if q == p {
                assert(find_level_idx(seq![p], q) == Some(0nat));
            } else {
                assert forall|j: int| 0 <= j < seq![p].len() implies seq![p][j] != q by {
                    assert(seq![p][j] == p);
                }
                find_level_idx_no_match(seq![p], q);
            }
        },
        LevelSpec::Succ(a) => {
            undet_imax_params_subst_single(*a, p, v);
        },
        LevelSpec::Max(a, b) => {
            undet_imax_params_subst_single(*a, p, v);
            undet_imax_params_subst_single(*b, p, v);
        },
        LevelSpec::IMax(a, b) => {
            undet_imax_params_subst_single(*a, p, v);
            undet_imax_params_subst_single(*b, p, v);
            // the third union member, which is where `params_outside_succ` --
            // and therefore the whole candidate -- does its work
            params_outside_succ_subst_single(*b, p, v);
        },
    }
}

/// The other half of a STRICT decrease: `p` leaving is only progress if nothing
/// else arrives. Substitution is structural -- it rewrites `Param p` leaves and
/// moves no other parameter -- so the set can only shrink.
pub proof fn undet_imax_params_subst_no_growth(l: LevelSpec, p: u64, v: LevelSpec)
    requires
        params_outside_succ(v) =~= Set::<u64>::empty(),
        undet_imax_params(v) =~= Set::<u64>::empty(),
    ensures
        undet_imax_params(subst_level_spec(l, seq![p], seq![v])).subset_of(undet_imax_params(l)),
        params_outside_succ(subst_level_spec(l, seq![p], seq![v])).subset_of(
            params_outside_succ(l),
        ),
    decreases l,
{
    match l {
        LevelSpec::Zero => {},
        LevelSpec::Param(q) => {
            if q == p {
                assert(find_level_idx(seq![p], q) == Some(0nat));
            } else {
                assert forall|j: int| 0 <= j < seq![p].len() implies seq![p][j] != q by {
                    assert(seq![p][j] == p);
                }
                find_level_idx_no_match(seq![p], q);
            }
        },
        LevelSpec::Succ(a) => {
            undet_imax_params_subst_no_growth(*a, p, v);
        },
        LevelSpec::Max(a, b) => {
            undet_imax_params_subst_no_growth(*a, p, v);
            undet_imax_params_subst_no_growth(*b, p, v);
        },
        LevelSpec::IMax(a, b) => {
            undet_imax_params_subst_no_growth(*a, p, v);
            undet_imax_params_subst_no_growth(*b, p, v);
        },
    }
}

/// Every parameter name occurring anywhere in a level. Distinct from
/// `imax_params` below, which counts only those in an `IMax`'s SECOND
/// position -- that one exists for a termination measure, this one for
/// `all_uparams_defined`'s "every parameter is declared" property.
pub open spec fn param_names(l: LevelSpec) -> Set<u64>
    decreases l,
{
    match l {
        LevelSpec::Zero => Set::empty(),
        LevelSpec::Param(n) => Set::empty().insert(n),
        LevelSpec::Succ(a) => param_names(*a),
        LevelSpec::Max(a, b) => param_names(*a).union(param_names(*b)),
        LevelSpec::IMax(a, b) => param_names(*a).union(param_names(*b)),
    }
}

pub open spec fn imax_params(l: LevelSpec) -> Set<u64>
    decreases l,
{
    match l {
        LevelSpec::Zero => Set::empty(),
        LevelSpec::Param(_) => Set::empty(),
        LevelSpec::Succ(a) => imax_params(*a),
        LevelSpec::Max(a, b) => imax_params(*a).union(imax_params(*b)),
        LevelSpec::IMax(a, b) => {
            let here = match *b {
                LevelSpec::Param(q) => Set::empty().insert(q),
                _ => Set::empty(),
            };
            imax_params(*a).union(imax_params(*b)).union(here)
        },
    }
}

/// The set is finite, so `.len()` is meaningful -- needed before it can be a
/// measure component at all.
pub proof fn imax_params_finite(l: LevelSpec)
    ensures
        imax_params(l).finite(),
    decreases l,
{
    match l {
        LevelSpec::Succ(a) => {
            imax_params_finite(*a);
        },
        LevelSpec::Max(a, b) => {
            imax_params_finite(*a);
            imax_params_finite(*b);
        },
        LevelSpec::IMax(a, b) => {
            imax_params_finite(*a);
            imax_params_finite(*b);
        },
        _ => {},
    }
}

pub open spec fn imax_normal(l: LevelSpec) -> bool
    decreases l,
{
    match l {
        LevelSpec::Zero => true,
        LevelSpec::Param(_) => true,
        LevelSpec::Succ(a) => imax_normal(*a),
        LevelSpec::Max(a, b) => imax_normal(*a) && imax_normal(*b),
        LevelSpec::IMax(a, b) => imax_normal(*a) && imax_normal(*b) && match *b {
            LevelSpec::Zero => false,
            LevelSpec::Succ(_) => false,
            _ => true,
        },
    }
}

pub open spec fn ls_is_zero(l: LevelSpec) -> bool {
    matches!(l, LevelSpec::Zero)
}

pub open spec fn ls_is_param(l: LevelSpec) -> bool {
    matches!(l, LevelSpec::Param(_))
}

pub open spec fn ls_is_succ(l: LevelSpec) -> bool {
    matches!(l, LevelSpec::Succ(_))
}

pub open spec fn ls_is_max(l: LevelSpec) -> bool {
    matches!(l, LevelSpec::Max(_, _))
}

pub open spec fn ls_is_imax(l: LevelSpec) -> bool {
    matches!(l, LevelSpec::IMax(_, _))
}

pub open spec fn ls_is_any_max(l: LevelSpec) -> bool {
    matches!(l, LevelSpec::Max(_, _) | LevelSpec::IMax(_, _))
}

/// The second argument of an `IMax` (`Zero` elsewhere -- never consulted).
pub open spec fn ls_imax_snd(l: LevelSpec) -> LevelSpec {
    match l {
        LevelSpec::IMax(_, b) => *b,
        _ => LevelSpec::Zero,
    }
}

/// The disjunction of `leq_core`'s arm guards, in the order the function
/// tests them. Its final `_ => panic!()` is reached exactly when this is
/// false.
pub open spec fn leq_core_covered(l: LevelSpec, r: LevelSpec, diff: int) -> bool {
    ||| (ls_is_zero(l) && diff >= 0)
    ||| (ls_is_zero(r) && diff < 0)
    ||| (ls_is_param(l) && ls_is_param(r))
    ||| (ls_is_param(l) && ls_is_zero(r))
    ||| (ls_is_zero(l) && ls_is_param(r))
    ||| ls_is_succ(l)
    ||| ls_is_succ(r)
    ||| ls_is_max(l)
    ||| (ls_is_param(l) && ls_is_max(r))
    ||| (ls_is_zero(l) && ls_is_max(r))
    ||| (ls_is_imax(l) && ls_is_param(ls_imax_snd(l)))
    ||| (ls_is_imax(r) && ls_is_param(ls_imax_snd(r)))
    ||| (ls_is_imax(l) && ls_is_any_max(ls_imax_snd(l)))
    ||| (ls_is_imax(r) && ls_is_any_max(ls_imax_snd(r)))
}

/// Non-vacuity check for the lemma above (a conditional lemma that happens
/// to have an always-true conclusion would prove nothing). `IMax(p, 0)`
/// against `Zero` at `diff = 0` falls through every one of `leq_core`'s
/// arms -- so the catch-all IS reachable in general -- and it is exactly the
/// shape `imax_normal` forbids. The invariant is therefore load-bearing
/// rather than decorative.
pub proof fn leq_core_covered_is_not_vacuous()
    ensures
        !leq_core_covered(
            LevelSpec::IMax(Box::new(LevelSpec::Param(0)), Box::new(LevelSpec::Zero)),
            LevelSpec::Zero,
            0,
        ),
        !imax_normal(LevelSpec::IMax(Box::new(LevelSpec::Param(0)), Box::new(LevelSpec::Zero))),
{
}

pub open spec fn interp(l: LevelSpec, rho: Map<nat, nat>) -> nat
    decreases l,
{
    match l {
        LevelSpec::Zero => 0,
        LevelSpec::Succ(a) => interp(*a, rho) + 1,
        LevelSpec::Max(a, b) => max_nat(interp(*a, rho), interp(*b, rho)),
        LevelSpec::IMax(a, b) => {
            if interp(*b, rho) == 0 {
                0
            } else {
                max_nat(interp(*a, rho), interp(*b, rho))
            }
        },
        LevelSpec::Param(p) => if rho.contains_key(p as nat) {
            rho[p as nat]
        } else {
            0
        },
    }
}

pub open spec fn is_succ(l: LevelSpec) -> bool {
    match l {
        LevelSpec::Succ(_) => true,
        _ => false,
    }
}

pub open spec fn is_imax(l: LevelSpec) -> bool {
    match l {
        LevelSpec::IMax(_, _) => true,
        _ => false,
    }
}

/// Mirrors `TcCtx::combining` (the worker behind `simplify`'s `Max` case):
/// pushes a `max` down through matching `Succ`s instead of leaving nested
/// `Max` nodes around, e.g. `combining(Succ(a), Succ(b)) = Succ(combining(a,b))`
/// rather than `Max(Succ(a), Succ(b))`.
///
/// The second `ensures` clause is the structural fact `simplify_imax_step`
/// below needs: when the right-hand side is `Succ`-shaped, `combining` can
/// never produce an `IMax` node. (It's not true in general — e.g.
/// `combining(IMax(x,y), Zero) == IMax(x,y)`, passed straight through by the
/// `(l, Zero) => l` arm — but that passthrough arm requires `r == Zero`,
/// which `is_succ(r)` rules out.)
pub fn combining(l: LevelSpec, r: LevelSpec) -> (result: LevelSpec)
    ensures
        forall|rho: Map<nat, nat>| #[trigger]
            interp(result, rho) == max_nat(interp(l, rho), interp(r, rho)),
        is_succ(r) ==> !is_imax(result),
    decreases l,
{
    match (l, r) {
        (LevelSpec::Zero, r) => r,
        (l, LevelSpec::Zero) => l,
        (LevelSpec::Succ(l2), LevelSpec::Succ(r2)) => {
            let sub = combining(*l2, *r2);
            // The automatic trigger doesn't chain the recursive call's forall
            // postcondition through `interp`'s own recursion on its own; restating
            // these three facts (the IH, and how `interp` unfolds on the result and
            // on the two original scrutinees) is what it takes to close the goal.
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(sub, rho) == max_nat(interp(*l2, rho), interp(*r2, rho)));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(LevelSpec::Succ(Box::new(sub)), rho) == interp(sub, rho) + 1);
            assert(forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) == interp(*l2, rho) + 1);
            assert(forall|rho: Map<nat, nat>| #[trigger] interp(r, rho) == interp(*r2, rho) + 1);
            LevelSpec::Succ(Box::new(sub))
        },
        (l, r) => LevelSpec::Max(Box::new(l), Box::new(r)),
    }
}

/// A conservative, structural-only fragment of `TcCtx::leq_core`
/// (`level.rs`'s decision procedure for "is `l + diff <= r` valid for every
/// assignment of the universe parameters"). It's faithful to the real
/// `leq_core` for every case that doesn't require the "IMax case split"
/// (`leq_imax_by_cases`) — and for everything else it just returns `false`,
/// which is always a safe (if incomplete) answer.
///
/// `leq_core(l, r, diff)` in `level.rs` maintains the invariant that it
/// decides `interp(l) <= interp(r) + diff`, not `interp(l) + diff <=
/// interp(r)` — `diff` is added to the *right*, which is why peeling a
/// `Succ` off `l` decrements `diff` (`l = Succ(s)`: `s + 1 <= r + diff` iff
/// `s <= r + (diff - 1)`) while peeling one off `r` increments it.
///
/// The real `leq_core`'s hard case (IMax-by-cases) is left unimplemented
/// here because its termination isn't structural: substituting a param `p`
/// with `Succ(p)` to test the "`p` is nonzero" branch makes the substituted
/// term *larger*, not smaller, so a plain structural `decreases` doesn't
/// apply. The actual reason it terminates is that the substitution
/// eliminates every `IMax(_, p)` occurrence of that specific `p` (`subst`
/// replaces all of them, and `simplify` rewrites the resulting
/// `IMax(_, Succ(_))`/`IMax(_, Zero)` shapes into `Max`/`Succ`/`Zero`, none
/// of which can trigger a further case split on `p`) — so the number of
/// *distinct params that could still trigger a case split* is what
/// decreases, not term size. Formalizing that requires first proving
/// `subst`+`simplify` actually has that "no more case-split shapes for
/// `p`" property, which is real work for a follow-up.
pub fn leq_core_partial(l: &LevelSpec, r: &LevelSpec, diff: i64) -> (result: bool)
    ensures
        result ==> forall|rho: Map<nat, nat>| #[trigger]
            interp(*l, rho) as int <= interp(*r, rho) as int + diff as int,
    decreases l, r,
{
    match (l, r) {
        (LevelSpec::Zero, _) if diff >= 0 => true,
        (_, LevelSpec::Zero) if diff < 0 => false,
        (LevelSpec::Param(a), LevelSpec::Param(x)) => *a == *x && diff >= 0,
        (LevelSpec::Param(_), LevelSpec::Zero) => false,
        (LevelSpec::Zero, LevelSpec::Param(_)) => diff >= 0,
        (LevelSpec::Succ(s), _) => {
            match diff.checked_sub(1) {
                Some(d) => {
                    let sub = leq_core_partial(&**s, r, d);
                    assert(sub ==> forall|rho: Map<nat, nat>| #[trigger]
                        interp(**s, rho) as int <= interp(*r, rho) as int + d as int);
                    assert(forall|rho: Map<nat, nat>| #[trigger]
                        interp(*l, rho) == interp(**s, rho) + 1);
                    sub
                }
                // `diff - 1` would overflow `i64`: astronomically unreachable in
                // practice (it needs ~2^63 nested `Succ`s), but since we only need
                // to return a sound answer, not a complete one, `false` is free.
                ,
                None => false,
            }
        },
        (_, LevelSpec::Succ(s)) => {
            match diff.checked_add(1) {
                Some(d) => {
                    let sub = leq_core_partial(l, &**s, d);
                    assert(sub ==> forall|rho: Map<nat, nat>| #[trigger]
                        interp(*l, rho) as int <= interp(**s, rho) as int + d as int);
                    assert(forall|rho: Map<nat, nat>| #[trigger]
                        interp(*r, rho) == interp(**s, rho) + 1);
                    sub
                },
                None => false,
            }
        },
        (LevelSpec::Max(a, b), _) => {
            let ra = leq_core_partial(&**a, r, diff);
            let rb = leq_core_partial(&**b, r, diff);
            assert(ra ==> forall|rho: Map<nat, nat>| #[trigger]
                interp(**a, rho) as int <= interp(*r, rho) as int + diff as int);
            assert(rb ==> forall|rho: Map<nat, nat>| #[trigger]
                interp(**b, rho) as int <= interp(*r, rho) as int + diff as int);
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(*l, rho) == max_nat(interp(**a, rho), interp(**b, rho)));
            ra && rb
        },
        (LevelSpec::Param(_), LevelSpec::Max(x, y)) => {
            let rx = leq_core_partial(l, &**x, diff);
            let ry = leq_core_partial(l, &**y, diff);
            assert(rx ==> forall|rho: Map<nat, nat>| #[trigger]
                interp(*l, rho) as int <= interp(**x, rho) as int + diff as int);
            assert(ry ==> forall|rho: Map<nat, nat>| #[trigger]
                interp(*l, rho) as int <= interp(**y, rho) as int + diff as int);
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(*r, rho) == max_nat(interp(**x, rho), interp(**y, rho)));
            rx || ry
        },
        (LevelSpec::Zero, LevelSpec::Max(x, y)) => {
            let rx = leq_core_partial(l, &**x, diff);
            let ry = leq_core_partial(l, &**y, diff);
            assert(rx ==> forall|rho: Map<nat, nat>| #[trigger]
                interp(*l, rho) as int <= interp(**x, rho) as int + diff as int);
            assert(ry ==> forall|rho: Map<nat, nat>| #[trigger]
                interp(*l, rho) as int <= interp(**y, rho) as int + diff as int);
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(*r, rho) == max_nat(interp(**x, rho), interp(**y, rho)));
            rx || ry
        }
        // Any pair involving `IMax` that isn't caught above: not attempted (see
        // doc comment). Returning `false` unconditionally keeps this sound.
        ,
        _ => false,
    }
}

/// Structural duplicate of a `LevelSpec` reached via `&`, proven to denote
/// the same value. Needed because substitution may need to copy its
/// replacement value at more than one occurrence site, and `LevelSpec` isn't
/// (and, being `Box`-recursive, can't cheaply be) `Copy`. Plain
/// `#[derive(Clone)]` doesn't work here either: Verus rejects it with
/// "cyclic self-reference" on a recursive `Box` enum, so this is written out
/// by hand.
pub fn dup(l: &LevelSpec) -> (result: LevelSpec)
    ensures
        result == *l,
    decreases l,
{
    match l {
        LevelSpec::Zero => LevelSpec::Zero,
        LevelSpec::Param(p) => LevelSpec::Param(*p),
        LevelSpec::Succ(a) => {
            let sub = dup(a);
            assert(sub == **a);
            LevelSpec::Succ(Box::new(sub))
        },
        LevelSpec::Max(a, b) => {
            let sa = dup(a);
            let sb = dup(b);
            assert(sa == **a);
            assert(sb == **b);
            LevelSpec::Max(Box::new(sa), Box::new(sb))
        },
        LevelSpec::IMax(a, b) => {
            let sa = dup(a);
            let sb = dup(b);
            assert(sa == **a);
            assert(sb == **b);
            LevelSpec::IMax(Box::new(sa), Box::new(sb))
        },
    }
}

/// Mirrors `TcCtx::subst_level` specialized to a single parameter (which is
/// all `leq_imax_by_cases` ever needs: it always substitutes exactly the one
/// param it's case-splitting on). Proven to mean exactly what substitution
/// should mean: interpreting the substituted term under `rho` is the same as
/// interpreting the original term under `rho` with `p`'s assignment
/// overridden to whatever `v` denotes under `rho`.
pub fn subst1(l: LevelSpec, p: u64, v: &LevelSpec) -> (result: LevelSpec)
    ensures
        forall|rho: Map<nat, nat>| #[trigger]
            interp(result, rho) == interp(l, rho.insert(p as nat, interp(*v, rho))),
    decreases l,
{
    match l {
        LevelSpec::Zero => LevelSpec::Zero,
        LevelSpec::Param(q) => {
            if q == p {
                let result = dup(v);
                assert(forall|rho: Map<nat, nat>| #[trigger]
                    interp(result, rho) == interp(*v, rho));
                result
            } else {
                LevelSpec::Param(q)
            }
        },
        LevelSpec::Succ(a) => {
            let sub = subst1(*a, p, v);
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(sub, rho) == interp(*a, rho.insert(p as nat, interp(*v, rho))));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(LevelSpec::Succ(Box::new(sub)), rho) == interp(sub, rho) + 1);
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(l, rho.insert(p as nat, interp(*v, rho))) == interp(
                    *a,
                    rho.insert(p as nat, interp(*v, rho)),
                ) + 1);
            LevelSpec::Succ(Box::new(sub))
        },
        LevelSpec::Max(a, b) => {
            let sa = subst1(*a, p, v);
            let sb = subst1(*b, p, v);
            let result = combining(sa, sb);
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(sa, rho) == interp(*a, rho.insert(p as nat, interp(*v, rho))));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(sb, rho) == interp(*b, rho.insert(p as nat, interp(*v, rho))));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(result, rho) == max_nat(interp(sa, rho), interp(sb, rho)));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(l, rho.insert(p as nat, interp(*v, rho))) == max_nat(
                    interp(*a, rho.insert(p as nat, interp(*v, rho))),
                    interp(*b, rho.insert(p as nat, interp(*v, rho))),
                ));
            result
        },
        LevelSpec::IMax(a, b) => {
            let sa = subst1(*a, p, v);
            let sb = subst1(*b, p, v);
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(sa, rho) == interp(*a, rho.insert(p as nat, interp(*v, rho))));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(sb, rho) == interp(*b, rho.insert(p as nat, interp(*v, rho))));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(LevelSpec::IMax(Box::new(sa), Box::new(sb)), rho) == if interp(sb, rho)
                    == 0 {
                    0
                } else {
                    max_nat(interp(sa, rho), interp(sb, rho))
                });
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(l, rho.insert(p as nat, interp(*v, rho))) == if interp(
                    *b,
                    rho.insert(p as nat, interp(*v, rho)),
                ) == 0 {
                    0
                } else {
                    max_nat(
                        interp(*a, rho.insert(p as nat, interp(*v, rho))),
                        interp(*b, rho.insert(p as nat, interp(*v, rho))),
                    )
                });
            LevelSpec::IMax(Box::new(sa), Box::new(sb))
        },
    }
}

/// Mirrors `TcCtx::subst_level`'s linear scan (`for (k, v) in
/// ks.iter().zip(vs.iter()) { if level == k { return v } }`): the index of
/// the FIRST position in `ks` equal to `q`, or `None` if `q` doesn't occur
/// -- scanning from the front, unlike `find_from_end` in `expr_model.rs`
/// (which scans backward for a different real-code loop).
pub open spec fn find_level_idx(ks: Seq<u64>, q: u64) -> Option<nat>
    decreases ks.len(),
{
    if ks.len() == 0 {
        None
    } else if ks[0] == q {
        Some(0)
    } else {
        match find_level_idx(ks.subrange(1, ks.len() as int), q) {
            Some(p) => Some((p + 1) as nat),
            None => None,
        }
    }
}

/// `find_level_idx`'s in-bounds guarantee, split out as its own lemma
/// (mirroring `find_pos_from_end`'s ensures in `expr_model.rs`, which
/// bundles this fact directly into an `pub fn`'s contract -- `find_level_idx`
/// is a `spec fn`, so the same fact needs a companion `proof fn` instead).
pub proof fn find_level_idx_bound(ks: Seq<u64>, q: u64)
    ensures
        match find_level_idx(ks, q) {
            Some(i) => i < ks.len(),
            None => true,
        },
    decreases ks.len(),
{
    if ks.len() == 0 || ks[0] == q {
    } else {
        find_level_idx_bound(ks.subrange(1, ks.len() as int), q);
    }
}

/// Converse direction of `find_level_idx`'s definition: if index `i` is a
/// match and every earlier index isn't, `i` IS the (first, hence unique)
/// match `find_level_idx` reports. Needed by `verified_subst_level`'s
/// real-arena scan, which discovers a match by pointer equality one index
/// at a time and needs to connect "this specific index matched, and I've
/// already ruled out everything before it" back to `find_level_idx`'s own
/// definition (which recurses front-to-back over the whole sequence).
pub proof fn find_level_idx_first_match(ks: Seq<u64>, q: u64, i: nat)
    requires
        i < ks.len(),
        ks[i as int] == q,
        forall|j: int| 0 <= j < i ==> ks[j] != q,
    ensures
        find_level_idx(ks, q) == Some(i),
    decreases i,
{
    if i == 0 {
    } else {
        assert(ks[0] != q);
        find_level_idx_first_match(ks.subrange(1, ks.len() as int), q, (i - 1) as nat);
    }
}

/// `find_level_idx`'s other converse: if NO index matches, the search
/// reports `None`. Needed by `verified_subst_level` for the "scanned the
/// whole list, no pointer match" case.
pub proof fn find_level_idx_no_match(ks: Seq<u64>, q: u64)
    requires
        forall|j: int| 0 <= j < ks.len() ==> ks[j] != q,
    ensures
        find_level_idx(ks, q) is None,
    decreases ks.len(),
{
    if ks.len() == 0 {
    } else {
        assert(ks[0] != q);
        find_level_idx_no_match(ks.subrange(1, ks.len() as int), q);
    }
}

/// The parameter environment `subst_levels` implicitly substitutes into:
/// every param `p` found (via `find_level_idx`) in `ks` is replaced by
/// whatever `vs` denotes at that SAME index, interpreted under the
/// ORIGINAL `rho` (simultaneous substitution -- mirrors `subst1`'s
/// `rho.insert(p, interp(*v, rho))`, generalized from one override to a
/// whole list); every other param keeps its original `rho` assignment
/// untouched. Built by recursing to the END of `ks`/`vs` first (base case
/// `rho` itself) and inserting front-to-back on the way back OUT of the
/// recursion, so an EARLIER entry's insert (applied LAST) always wins over
/// a later one for a repeated key -- matching `find_level_idx`'s
/// first-match semantics exactly. (`Set::new`/`Set::full` in this Verus's
/// `vstd` return `Option<Set<A>>`, `None` unless the predicate is
/// provably finite -- awkward for an unbounded `nat` domain, so this
/// builds the map via plain `insert` instead of `Map::new` with a
/// predicate-defined domain.)
pub open spec fn level_spec_param_name(l: LevelSpec) -> u64 {
    match l {
        LevelSpec::Param(q) => q,
        _ => 0,
    }
}

/// Extracts the parameter name of every (assumed-`Param`-shaped) element of
/// a level list -- the bridge between a real `LevelsPtr` uparams list's
/// `to_model_of_levels` (a `Seq<LevelSpec>`) and `subst_env`/`find_level_idx`
/// (which operate on the raw `Seq<u64>` names). `level_spec_param_name`'s
/// arbitrary `0` fallback for non-`Param` shapes is never actually reached
/// for a genuine uparams list (every real declaration parameter IS a
/// `Param` level), so it's never observed by any proof that uses this.
pub open spec fn level_names(ls: Seq<LevelSpec>) -> Seq<u64> {
    Seq::new(ls.len(), |i: int| level_spec_param_name(ls[i]))
}

pub open spec fn subst_env(rho: Map<nat, nat>, ks: Seq<u64>, vs: Seq<LevelSpec>) -> Map<nat, nat>
    decreases ks.len(),
{
    if ks.len() == 0 {
        rho
    } else {
        subst_env(rho, ks.subrange(1, ks.len() as int), vs.subrange(1, vs.len() as int)).insert(
            ks[0] as nat,
            interp(vs[0], rho),
        )
    }
}

/// SYNTACTIC level substitution -- the spec mirror of the real
/// `level.rs::subst_level` (zero/succ/max/imax rebuilt structurally, a
/// `Param` looked up in `ks` and replaced by the matching `vs` entry,
/// else left alone). Exists so delta-unfolding's model target can be a
/// FUNCTION of the definition body and the constant's levels (the
/// delta-lift arc): `subst_env` below is the SEMANTIC view of the same
/// operation, and `subst_level_spec_interp` ties the two.
pub open spec fn subst_level_spec(l: LevelSpec, ks: Seq<u64>, vs: Seq<LevelSpec>) -> LevelSpec
    decreases l,
{
    match l {
        LevelSpec::Zero => LevelSpec::Zero,
        LevelSpec::Succ(a) => LevelSpec::Succ(Box::new(subst_level_spec(*a, ks, vs))),
        LevelSpec::Max(a, b) => LevelSpec::Max(
            Box::new(subst_level_spec(*a, ks, vs)),
            Box::new(subst_level_spec(*b, ks, vs)),
        ),
        LevelSpec::IMax(a, b) => LevelSpec::IMax(
            Box::new(subst_level_spec(*a, ks, vs)),
            Box::new(subst_level_spec(*b, ks, vs)),
        ),
        LevelSpec::Param(q) => match find_level_idx(ks, q) {
            Some(i) => if i < vs.len() {
                vs[i as int]
            } else {
                l
            },
            None => l,
        },
    }
}

/// Elementwise `subst_level_spec` over a level list.
pub open spec fn subst_levels_spec(ls: Seq<LevelSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>) -> Seq<
    LevelSpec,
> {
    Seq::new(ls.len(), |i: int| subst_level_spec(ls[i], ks, vs))
}

/// `find_level_idx` never indexes past `ks`.
pub proof fn find_level_idx_in_range(ks: Seq<u64>, q: u64)
    ensures
        find_level_idx(ks, q) matches Some(i) ==> i < ks.len(),
    decreases ks.len(),
{
    if ks.len() == 0 {
    } else if ks[0] == q {
    } else {
        find_level_idx_in_range(ks.subrange(1, ks.len() as int), q);
    }
}

/// The syntactic mirror agrees with the semantic environment view.
/// `interp` depends on the environment ONLY through what it says about
/// parameters. Two maps that give every parameter the same value give every
/// level the same value.
///
/// `leq_imax_by_cases` needs this: its two branches evaluate under
/// `rho.insert(p, ..)`, and the case analysis has to get back to `rho` itself.
pub proof fn interp_congr(l: LevelSpec, rho1: Map<nat, nat>, rho2: Map<nat, nat>)
    requires
        forall|q: u64| #[trigger]
            interp(LevelSpec::Param(q), rho1) == interp(LevelSpec::Param(q), rho2),
    ensures
        interp(l, rho1) == interp(l, rho2),
    decreases l,
{
    match l {
        LevelSpec::Zero => {},
        LevelSpec::Param(q) => {
            assert(interp(LevelSpec::Param(q), rho1) == interp(LevelSpec::Param(q), rho2));
        },
        LevelSpec::Succ(a) => {
            interp_congr(*a, rho1, rho2);
        },
        LevelSpec::Max(a, b) => {
            interp_congr(*a, rho1, rho2);
            interp_congr(*b, rho1, rho2);
        },
        LevelSpec::IMax(a, b) => {
            interp_congr(*a, rho1, rho2);
            interp_congr(*b, rho1, rho2);
        },
    }
}

/// The `forall rho` form, which is the shape `subst_expr_levels_rel`'s `Sort`
/// arm is written in.
pub proof fn subst_level_spec_interp_forall(l: LevelSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        ks.len() == vs.len(),
    ensures
        forall|rho: Map<nat, nat>| #[trigger]
            interp(subst_level_spec(l, ks, vs), rho) == interp(l, subst_env(rho, ks, vs)),
{
    assert forall|rho: Map<nat, nat>| #[trigger]
        interp(subst_level_spec(l, ks, vs), rho) == interp(l, subst_env(rho, ks, vs)) by {
        subst_level_spec_interp(l, ks, vs, rho);
    }
}

pub proof fn subst_level_spec_interp(
    l: LevelSpec,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
    rho: Map<nat, nat>,
)
    requires
        ks.len() == vs.len(),
    ensures
        interp(subst_level_spec(l, ks, vs), rho) == interp(l, subst_env(rho, ks, vs)),
    decreases l,
{
    match l {
        LevelSpec::Zero => {},
        LevelSpec::Succ(a) => {
            subst_level_spec_interp(*a, ks, vs, rho);
        },
        LevelSpec::Max(a, b) => {
            subst_level_spec_interp(*a, ks, vs, rho);
            subst_level_spec_interp(*b, ks, vs, rho);
        },
        LevelSpec::IMax(a, b) => {
            subst_level_spec_interp(*a, ks, vs, rho);
            subst_level_spec_interp(*b, ks, vs, rho);
        },
        LevelSpec::Param(q) => {
            subst_env_param(rho, ks, vs, q);
            find_level_idx_in_range(ks, q);
        },
    }
}

/// `subst_env`'s defining correctness property, for exactly the query
/// `interp` itself performs at a `Param` node: substituted param `q`
/// denotes whatever `vs` says at `find_level_idx`'s matching index
/// (interpreted under the ORIGINAL `rho`); every other param denotes
/// exactly what it denoted under `rho` before the substitution.
pub proof fn subst_env_param(rho: Map<nat, nat>, ks: Seq<u64>, vs: Seq<LevelSpec>, q: u64)
    requires
        ks.len() == vs.len(),
    ensures
        interp(LevelSpec::Param(q), subst_env(rho, ks, vs)) == match find_level_idx(ks, q) {
            Some(i) => interp(vs[i as int], rho),
            None => interp(LevelSpec::Param(q), rho),
        },
    decreases ks.len(),
{
    find_level_idx_bound(ks, q);
    if ks.len() == 0 {
        assert(subst_env(rho, ks, vs) == rho);
        assert(find_level_idx(ks, q) is None);
        assert(interp(LevelSpec::Param(q), subst_env(rho, ks, vs)) == interp(
            LevelSpec::Param(q),
            rho,
        ));
    } else {
        let tail_ks = ks.subrange(1, ks.len() as int);
        let tail_vs = vs.subrange(1, vs.len() as int);
        subst_env_param(rho, tail_ks, tail_vs, q);
        let tail_env = subst_env(rho, tail_ks, tail_vs);
        let v0 = interp(vs[0], rho);
        vstd::map::lemma_map_insert_domain(tail_env, ks[0] as nat, v0);
        assert(subst_env(rho, ks, vs) == tail_env.insert(ks[0] as nat, v0));
        assert(subst_env(rho, ks, vs).dom() == tail_env.dom().insert(ks[0] as nat));
        if ks[0] == q {
            vstd::map::lemma_map_insert_same(tail_env, ks[0] as nat, v0);
            assert(subst_env(rho, ks, vs)[q as nat] == v0);
            assert(subst_env(rho, ks, vs).contains_key(q as nat));
            assert(interp(LevelSpec::Param(q), subst_env(rho, ks, vs)) == v0);
            assert(find_level_idx(ks, q) == Some(0nat));
        } else {
            assert(subst_env(rho, ks, vs).contains_key(q as nat) == tail_env.contains_key(
                q as nat,
            ));
            if tail_env.contains_key(q as nat) {
                vstd::map::axiom_map_insert_different(tail_env, q as nat, ks[0] as nat, v0);
                assert(subst_env(rho, ks, vs)[q as nat] == tail_env[q as nat]);
                assert(interp(LevelSpec::Param(q), subst_env(rho, ks, vs)) == interp(
                    LevelSpec::Param(q),
                    tail_env,
                ));
            } else {
                assert(interp(LevelSpec::Param(q), subst_env(rho, ks, vs)) == 0);
                assert(interp(LevelSpec::Param(q), tail_env) == 0);
                assert(interp(LevelSpec::Param(q), subst_env(rho, ks, vs)) == interp(
                    LevelSpec::Param(q),
                    tail_env,
                ));
            }
            assert(find_level_idx(ks, q) == match find_level_idx(tail_ks, q) {
                Some(p) => Some((p + 1) as nat),
                None => None::<nat>,
            });
        }
    }
}

/// Exec counterpart of `find_level_idx`, mirroring `TcCtx::subst_level`'s
/// real loop directly (recursion over the slice instead of a `for` loop,
/// matching this file's existing `find_pos_from_end`-style convention in
/// `expr_model.rs`).
pub fn find_level(ks: &[u64], q: u64) -> (result: Option<usize>)
    requires
        ks.len() <= 1_000_000_000,
    ensures
        match result {
            Some(i) => find_level_idx(ks@, q) == Some(i as nat) && (i as nat) < ks.len(),
            None => find_level_idx(ks@, q) is None,
        },
    decreases ks.len(),
{
    if ks.len() == 0 {
        None
    } else if ks[0] == q {
        Some(0)
    } else {
        let sub = &ks[1..ks.len()];
        assert(sub@ =~= ks@.subrange(1, ks@.len() as int));
        match find_level(sub, q) {
            Some(p) => Some(p + 1),
            None => None,
        }
    }
}

/// Mirrors `TcCtx::subst_level`/`subst_levels`: simultaneous, list-indexed
/// level substitution -- the multi-parameter generalization of `subst1`
/// (which `leq_imax_by_cases` only ever needed for a single param).
/// Structurally identical to `subst1` case-by-case; the only real
/// difference is the `Param` case, which does a linear scan (`find_level`)
/// instead of a single equality check.
pub fn subst_levels(l: LevelSpec, ks: &[u64], vs: &[LevelSpec]) -> (result: LevelSpec)
    requires
        ks.len() == vs.len(),
        ks.len() <= 1_000_000_000,
    ensures
        forall|rho: Map<nat, nat>| #[trigger]
            interp(result, rho) == interp(l, subst_env(rho, ks@, vs@)),
    decreases l,
{
    match l {
        LevelSpec::Zero => LevelSpec::Zero,
        LevelSpec::Param(q) => {
            match find_level(ks, q) {
                Some(i) => {
                    let result = dup(&vs[i]);
                    assert(result == vs@[i as int]);
                    assert forall|rho: Map<nat, nat>| #[trigger]
                        interp(result, rho) == interp(
                            LevelSpec::Param(q),
                            subst_env(rho, ks@, vs@),
                        ) by {
                        subst_env_param(rho, ks@, vs@, q);
                    }
                    result
                },
                None => {
                    assert forall|rho: Map<nat, nat>| #[trigger]
                        interp(LevelSpec::Param(q), rho) == interp(
                            LevelSpec::Param(q),
                            subst_env(rho, ks@, vs@),
                        ) by {
                        subst_env_param(rho, ks@, vs@, q);
                    }
                    LevelSpec::Param(q)
                },
            }
        },
        LevelSpec::Succ(a) => {
            let sub = subst_levels(*a, ks, vs);
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(sub, rho) == interp(*a, subst_env(rho, ks@, vs@)));
            let result = LevelSpec::Succ(Box::new(sub));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(result, rho) == interp(sub, rho) + 1);
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(l, subst_env(rho, ks@, vs@)) == interp(*a, subst_env(rho, ks@, vs@)) + 1);
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(result, rho) == interp(l, subst_env(rho, ks@, vs@)));
            result
        },
        LevelSpec::Max(a, b) => {
            let sa = subst_levels(*a, ks, vs);
            let sb = subst_levels(*b, ks, vs);
            let result = combining(sa, sb);
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(sa, rho) == interp(*a, subst_env(rho, ks@, vs@)));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(sb, rho) == interp(*b, subst_env(rho, ks@, vs@)));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(result, rho) == max_nat(interp(sa, rho), interp(sb, rho)));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(l, subst_env(rho, ks@, vs@)) == max_nat(
                    interp(*a, subst_env(rho, ks@, vs@)),
                    interp(*b, subst_env(rho, ks@, vs@)),
                ));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(result, rho) == interp(l, subst_env(rho, ks@, vs@)));
            result
        },
        LevelSpec::IMax(a, b) => {
            let sa = subst_levels(*a, ks, vs);
            let sb = subst_levels(*b, ks, vs);
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(sa, rho) == interp(*a, subst_env(rho, ks@, vs@)));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(sb, rho) == interp(*b, subst_env(rho, ks@, vs@)));
            let result = LevelSpec::IMax(Box::new(sa), Box::new(sb));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(result, rho) == if interp(sb, rho) == 0 {
                    0
                } else {
                    max_nat(interp(sa, rho), interp(sb, rho))
                });
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(l, subst_env(rho, ks@, vs@)) == if interp(*b, subst_env(rho, ks@, vs@))
                    == 0 {
                    0
                } else {
                    max_nat(
                        interp(*a, subst_env(rho, ks@, vs@)),
                        interp(*b, subst_env(rho, ks@, vs@)),
                    )
                });
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(result, rho) == interp(l, subst_env(rho, ks@, vs@)));
            result
        },
    }
}

pub open spec fn is_zero_or_succ(l: LevelSpec) -> bool {
    match l {
        LevelSpec::Zero => true,
        LevelSpec::Succ(_) => true,
        _ => false,
    }
}

/// Mirrors the body of `TcCtx::simplify`'s `IMax` case, given already-
/// simplified children. Takes the "is `l_simp` semantically zero-or-one"
/// decision (`is_zero(l_simp) || is_one(l_simp)` in the real code) as an
/// opaque `flag` rather than computing it: that requires `is_zero`/`is_one`,
/// which bottom out in `leq`, which is mutually recursive with `simplify`
/// itself, so wiring that up is future work.
///
/// The key fact — that the result is never `IMax`-shaped when `r_simp` is
/// `Zero` or `Succ`-shaped — doesn't depend on which way `flag` goes: taking
/// `flag` as a parameter rather than computing it lets us prove that fact
/// now, without waiting on the harder mutual-recursion work.
pub fn simplify_imax_step(l_simp: LevelSpec, r_simp: LevelSpec, flag: bool) -> (result: LevelSpec)
    requires
        is_zero_or_succ(r_simp),
    ensures
        !is_imax(result),
{
    if flag {
        r_simp
    } else {
        match r_simp {
            LevelSpec::Zero => LevelSpec::Zero,
            LevelSpec::Succ(s) => combining(l_simp, LevelSpec::Succ(s)),
            _ => LevelSpec::IMax(Box::new(l_simp), Box::new(r_simp)),
        }
    }
}

/// The concrete fact that makes `leq_imax_by_cases`'s recursion terminate:
/// substituting the parameter being case-split on (`p`) into the exact
/// `IMax(a, Param(p))` node that triggered the split — with a replacement
/// `v` that's `Zero` or `Succ`-shaped, exactly what `leq_imax_by_cases`
/// plugs in — and then running one step of `simplify`'s `IMax` handling,
/// can never produce another `IMax` node. So this specific parameter can
/// never trigger a further case split at this position, regardless of how
/// deep `a` itself is or what it contains.
///
/// (This mirrors `subst1`'s own `IMax` arm without calling it: `subst1` on
/// `IMax(a, Param(p))` always reconstructs `IMax(subst1(a,...), dup(v))`
/// since `p` trivially matches itself, so inlining that one step here avoids
/// needing a separate structural — as opposed to semantic — correctness
/// lemma about `subst1` in general.)
pub fn case_split_resolves(a: LevelSpec, p: u64, v: &LevelSpec, flag: bool) -> (result: LevelSpec)
    requires
        is_zero_or_succ(*v),
    ensures
        !is_imax(result),
{
    let l_child = subst1(a, p, v);
    let r_child = dup(v);
    assert(r_child == *v);
    simplify_imax_step(l_child, r_child, flag)
}

/// `leq_imax_by_cases`'s first substitution target: `p := Zero`.
pub fn case_split_resolves_zero(a: LevelSpec, p: u64, flag: bool) -> (result: LevelSpec)
    ensures
        !is_imax(result),
{
    case_split_resolves(a, p, &LevelSpec::Zero, flag)
}

/// `leq_imax_by_cases`'s second substitution target: `p := Succ(Param(p))`.
/// Note `p` still occurs in the replacement — substitution doesn't erase
/// `p` from the term, it only erases this specific `IMax(_, p)` shape (see
/// the module-level discussion in `leq_core_partial`'s doc comment).
pub fn case_split_resolves_succ(a: LevelSpec, p: u64, flag: bool) -> (result: LevelSpec)
    ensures
        !is_imax(result),
{
    let v = LevelSpec::Succ(Box::new(LevelSpec::Param(p)));
    case_split_resolves(a, p, &v, flag)
}

pub open spec fn eff(rho: Map<nat, nat>, p: nat) -> nat {
    if rho.contains_key(p) {
        rho[p]
    } else {
        0
    }
}

/// Inserting `p`'s own current effective value back into `rho` never changes
/// what any term denotes under `rho`. This is the fact that makes the
/// universe-level case-split proof technique work (see `case_split_sound`
/// below): whichever of `p`'s two cases (zero, or some successor) actually
/// holds for a given `rho`, substituting that case's witness for `p` and
/// re-evaluating under `rho` gives back exactly `interp(t, rho)`.
pub proof fn noop_insert(t: LevelSpec, rho: Map<nat, nat>, p: nat)
    ensures
        interp(t, rho.insert(p, eff(rho, p))) == interp(t, rho),
    decreases t,
{
    match t {
        LevelSpec::Zero => {},
        LevelSpec::Param(q) => {
            assert(interp(LevelSpec::Param(q), rho.insert(p, eff(rho, p))) == eff(
                rho.insert(p, eff(rho, p)),
                q as nat,
            ));
            assert(interp(LevelSpec::Param(q), rho) == eff(rho, q as nat));
            if q as nat == p {
                assert(eff(rho.insert(p, eff(rho, p)), q as nat) == eff(rho, q as nat));
            } else {
                assert(eff(rho.insert(p, eff(rho, p)), q as nat) == eff(rho, q as nat));
            }
        },
        LevelSpec::Succ(a) => {
            noop_insert(*a, rho, p);
        },
        LevelSpec::Max(a, b) => {
            noop_insert(*a, rho, p);
            noop_insert(*b, rho, p);
        },
        LevelSpec::IMax(a, b) => {
            noop_insert(*a, rho, p);
            noop_insert(*b, rho, p);
        },
    }
}

/// The actual mathematical justification for `leq_imax_by_cases`: since
/// every `nat` is either `0` or `succ(y)` for some `y`, checking the goal
/// once with `p := 0` substituted in and once with `p := succ(p)`
/// substituted in — and getting `true` both times — proves the goal for
/// *every* possible assignment to `p`, not just those two. `lhs_0`/`rhs_0`
/// and `lhs_s`/`rhs_s` are left abstract (characterized only by what
/// `subst1` guarantees they denote) rather than literally computed by
/// calling `subst1`, since `proof fn` can't call the `exec fn` `subst1` —
/// the actual gluing happens at the `exec` call site, which has both the
/// real substituted terms (from calling `subst1`) and this lemma's
/// conclusion available.
pub proof fn case_split_sound(
    l: LevelSpec,
    r: LevelSpec,
    p: u64,
    diff: int,
    lhs_0: LevelSpec,
    rhs_0: LevelSpec,
    lhs_s: LevelSpec,
    rhs_s: LevelSpec,
)
    requires
        forall|rho: Map<nat, nat>| #[trigger]
            interp(lhs_0, rho) == interp(l, rho.insert(p as nat, 0nat)),
        forall|rho: Map<nat, nat>| #[trigger]
            interp(rhs_0, rho) == interp(r, rho.insert(p as nat, 0nat)),
        forall|rho: Map<nat, nat>| #[trigger]
            interp(lhs_s, rho) == interp(l, rho.insert(p as nat, eff(rho, p as nat) + 1)),
        forall|rho: Map<nat, nat>| #[trigger]
            interp(rhs_s, rho) == interp(r, rho.insert(p as nat, eff(rho, p as nat) + 1)),
        forall|rho: Map<nat, nat>| #[trigger]
            interp(lhs_0, rho) as int <= interp(rhs_0, rho) as int + diff,
        forall|rho: Map<nat, nat>| #[trigger]
            interp(lhs_s, rho) as int <= interp(rhs_s, rho) as int + diff,
    ensures
        forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) as int <= interp(r, rho) as int + diff,
{
    assert forall|rho: Map<nat, nat>| interp(l, rho) as int <= interp(r, rho) as int + diff by {
        let x = eff(rho, p as nat);
        if x == 0 {
            noop_insert(l, rho, p as nat);
            noop_insert(r, rho, p as nat);
            assert(rho.insert(p as nat, 0nat) =~= rho.insert(p as nat, x));
            assert(interp(lhs_0, rho) == interp(l, rho.insert(p as nat, 0nat)));
            assert(interp(rhs_0, rho) == interp(r, rho.insert(p as nat, 0nat)));
            assert(interp(lhs_0, rho) as int <= interp(rhs_0, rho) as int + diff);
        } else {
            let y = (x - 1) as nat;
            let rho2 = rho.insert(p as nat, y);
            assert(eff(rho2, p as nat) == y);
            assert(rho2.insert(p as nat, eff(rho2, p as nat) + 1) =~= rho.insert(p as nat, x));
            noop_insert(l, rho, p as nat);
            noop_insert(r, rho, p as nat);
            assert(interp(lhs_s, rho2) == interp(
                l,
                rho2.insert(p as nat, eff(rho2, p as nat) + 1),
            ));
            assert(interp(rhs_s, rho2) == interp(
                r,
                rho2.insert(p as nat, eff(rho2, p as nat) + 1),
            ));
            assert(interp(lhs_s, rho2) as int <= interp(rhs_s, rho2) as int + diff);
        }
    }
}

/// Fuel-threaded, mutually-recursive counterpart to `leq_core_partial` +
/// `leq_imax_by_cases_via_partial`: instead of leaning on the (still
/// incomplete) structural termination argument, this sidesteps termination
/// entirely with an explicit budget, conservatively answering `false` once
/// it runs out. Since `false` never needs to be justified, this stays fully
/// sound for *any* fuel value while covering every shape `leq_core_partial`
/// didn't (nested/repeated `IMax`-by-cases splits) — the only shapes still
/// not attempted are the two "rewrite" `IMax`-vs-`Max`/`IMax` arms
/// (`is_any_max` in `level.rs`), which need their own distributivity lemmas
/// (e.g. `imax(a, imax(x,y)) == max(imax(a,y), imax(x,y))`) that haven't
/// been proven yet.
pub fn leq_core_fueled(l: &LevelSpec, r: &LevelSpec, diff: i64, fuel: u32) -> (result: bool)
    ensures
        result ==> forall|rho: Map<nat, nat>| #[trigger]
            interp(*l, rho) as int <= interp(*r, rho) as int + diff as int,
    decreases fuel,
{
    if fuel == 0 {
        return false;
    }
    let fuel1 = fuel - 1;
    match (l, r) {
        (LevelSpec::Zero, _) if diff >= 0 => true,
        (_, LevelSpec::Zero) if diff < 0 => false,
        (LevelSpec::Param(a), LevelSpec::Param(x)) => *a == *x && diff >= 0,
        (LevelSpec::Param(_), LevelSpec::Zero) => false,
        (LevelSpec::Zero, LevelSpec::Param(_)) => diff >= 0,
        (LevelSpec::Succ(s), _) => {
            match diff.checked_sub(1) {
                Some(d) => {
                    let sub = leq_core_fueled(&**s, r, d, fuel1);
                    assert(sub ==> forall|rho: Map<nat, nat>| #[trigger]
                        interp(**s, rho) as int <= interp(*r, rho) as int + d as int);
                    assert(forall|rho: Map<nat, nat>| #[trigger]
                        interp(*l, rho) == interp(**s, rho) + 1);
                    sub
                },
                None => false,
            }
        },
        (_, LevelSpec::Succ(s)) => {
            match diff.checked_add(1) {
                Some(d) => {
                    let sub = leq_core_fueled(l, &**s, d, fuel1);
                    assert(sub ==> forall|rho: Map<nat, nat>| #[trigger]
                        interp(*l, rho) as int <= interp(**s, rho) as int + d as int);
                    assert(forall|rho: Map<nat, nat>| #[trigger]
                        interp(*r, rho) == interp(**s, rho) + 1);
                    sub
                },
                None => false,
            }
        },
        (LevelSpec::Max(a, b), _) => {
            let ra = leq_core_fueled(&**a, r, diff, fuel1);
            let rb = leq_core_fueled(&**b, r, diff, fuel1);
            assert(ra ==> forall|rho: Map<nat, nat>| #[trigger]
                interp(**a, rho) as int <= interp(*r, rho) as int + diff as int);
            assert(rb ==> forall|rho: Map<nat, nat>| #[trigger]
                interp(**b, rho) as int <= interp(*r, rho) as int + diff as int);
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(*l, rho) == max_nat(interp(**a, rho), interp(**b, rho)));
            ra && rb
        },
        (LevelSpec::Param(_), LevelSpec::Max(x, y)) => {
            let rx = leq_core_fueled(l, &**x, diff, fuel1);
            let ry = leq_core_fueled(l, &**y, diff, fuel1);
            assert(rx ==> forall|rho: Map<nat, nat>| #[trigger]
                interp(*l, rho) as int <= interp(**x, rho) as int + diff as int);
            assert(ry ==> forall|rho: Map<nat, nat>| #[trigger]
                interp(*l, rho) as int <= interp(**y, rho) as int + diff as int);
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(*r, rho) == max_nat(interp(**x, rho), interp(**y, rho)));
            rx || ry
        },
        (LevelSpec::Zero, LevelSpec::Max(x, y)) => {
            let rx = leq_core_fueled(l, &**x, diff, fuel1);
            let ry = leq_core_fueled(l, &**y, diff, fuel1);
            assert(rx ==> forall|rho: Map<nat, nat>| #[trigger]
                interp(*l, rho) as int <= interp(**x, rho) as int + diff as int);
            assert(ry ==> forall|rho: Map<nat, nat>| #[trigger]
                interp(*l, rho) as int <= interp(**y, rho) as int + diff as int);
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(*r, rho) == max_nat(interp(**x, rho), interp(**y, rho)));
            rx || ry
        }
        // Real `leq_core` has a reflexivity fast-path here
        // ((IMax(a,b),IMax(x,y)) if a==x && b==y && diff>=0 => true), cheap
        // in the real arena since it's just pointer equality (hash-consing
        // makes it O(1)). There's no analogous cheap check in this
        // Box-recursive model (no interning, so "are these the same" would
        // mean a full recursive structural-equality function) — omitted
        // here since it isn't semantically required: an `l == r` case
        // still reaches the correct answer via the rewrite arms below
        // (recursing further rather than short-circuiting), just with more
        // fuel consumed. `verified_leq_core` (the real-arena version) does
        // implement this fast-path, using real `LevelPtr` equality.
        ,
        (LevelSpec::IMax(_, b), _) if matches!(**b, LevelSpec::Param(_)) => {
            match **b {
                LevelSpec::Param(p) => leq_imax_by_cases_fueled(dup(l), dup(r), p, diff, fuel1),
                _ => false,  // unreachable given the match guard above
            }
        },
        (_, LevelSpec::IMax(_, y)) if matches!(**y, LevelSpec::Param(_)) => {
            match **y {
                LevelSpec::Param(p) => leq_imax_by_cases_fueled(dup(l), dup(r), p, diff, fuel1),
                _ => false,  // unreachable given the match guard above
            }
        },
        (
            LevelSpec::IMax(a, b),
            _,
        ) if matches!(**b, LevelSpec::Max(_, _) | LevelSpec::IMax(_, _)) => {
            assert(*l == LevelSpec::IMax(Box::new(**a), Box::new(**b)));
            leq_core_imax_rewrite_left(a, b, l, r, diff, fuel1)
        },
        (
            _,
            LevelSpec::IMax(x, y),
        ) if matches!(**y, LevelSpec::Max(_, _) | LevelSpec::IMax(_, _)) => {
            assert(*r == LevelSpec::IMax(Box::new(**x), Box::new(**y)));
            leq_core_imax_rewrite_right(x, y, l, r, diff, fuel1)
        },
        _ => false,
    }
}

/// Implements `leq_core`'s first `is_any_max` rewrite arm: `l = IMax(a, b)`
/// where `b` is itself `Max`- or `IMax`-shaped, using `imax_imax_distrib`/
/// `imax_max_distrib` to justify rewriting to an equivalent term without an
/// `IMax` at this position, then recursing.
///
/// Verus quirk hit while writing the `Max` sub-case: given two separate
/// hypotheses `forall |rho| interp(new_max, rho) == interp(new_max_raw, rho)`
/// and `forall |rho| interp(new_max_raw, rho) == interp(l, rho)` (each
/// individually already proven, each with its own `#[trigger]`), a plain
/// `assert(forall |rho| interp(new_max, rho) == interp(l, rho))` — the
/// transitive combination — did NOT go through automatically, even though
/// it's immediate for any single `rho`. Z3 wasn't chaining the two
/// separately-triggered foralls together. Fix: wrap the *same* two facts in
/// `assert forall |rho| ... by { assert(...); assert(...); }` instead of a
/// bare `assert(forall |rho| ...)` — forcing both hypotheses to be
/// instantiated at one concrete, shared `rho` (rather than each pattern-
/// matching independently) is what let the transitivity go through. The
/// `#[allow(unused_variables)]` below is unrelated: `l`/`r` are only
/// referenced inside `assert`s, which are ghost/spec and erased under plain
/// (non-Verus) compilation, so plain `cargo build` sees them as unused.
#[allow(unused_variables)]
fn leq_core_imax_rewrite_left(
    a: &Box<LevelSpec>,
    b: &Box<LevelSpec>,
    l: &LevelSpec,
    r: &LevelSpec,
    diff: i64,
    fuel: u32,
) -> (result: bool)
    requires
        *l == LevelSpec::IMax(Box::new(**a), Box::new(**b)),
    ensures
        result ==> forall|rho: Map<nat, nat>| #[trigger]
            interp(*l, rho) as int <= interp(*r, rho) as int + diff as int,
    decreases fuel,
{
    if fuel == 0 {
        return false;
    }
    let fuel1 = fuel - 1;
    let r1 = dup(r);
    match &**b {
        LevelSpec::IMax(x, y) => {
            assert(**b == LevelSpec::IMax(Box::new(**x), Box::new(**y)));
            assert(*l == LevelSpec::IMax(
                Box::new(**a),
                Box::new(LevelSpec::IMax(Box::new(**x), Box::new(**y))),
            ));
            let a1 = dup(a);
            let y1 = dup(y);
            let x1 = dup(x);
            let y2 = dup(y);
            let new_max = LevelSpec::Max(
                Box::new(LevelSpec::IMax(Box::new(a1), Box::new(y1))),
                Box::new(LevelSpec::IMax(Box::new(x1), Box::new(y2))),
            );
            proof {
                imax_imax_distrib(**a, **x, **y);
            }
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(new_max, rho) == interp(
                    LevelSpec::IMax(
                        Box::new(**a),
                        Box::new(LevelSpec::IMax(Box::new(**x), Box::new(**y))),
                    ),
                    rho,
                ));
            assert(forall|rho: Map<nat, nat>| #[trigger] interp(new_max, rho) == interp(*l, rho));
            let result = leq_core_fueled(&new_max, &r1, diff, fuel1);
            assert(result ==> forall|rho: Map<nat, nat>| #[trigger]
                interp(new_max, rho) as int <= interp(r1, rho) as int + diff as int);
            assert(forall|rho: Map<nat, nat>| #[trigger] interp(r1, rho) == interp(*r, rho));
            assert(result ==> forall|rho: Map<nat, nat>| #[trigger]
                interp(*l, rho) as int <= interp(*r, rho) as int + diff as int);
            result
        },
        LevelSpec::Max(x, y) => {
            assert(**b == LevelSpec::Max(Box::new(**x), Box::new(**y)));
            assert(*l == LevelSpec::IMax(
                Box::new(**a),
                Box::new(LevelSpec::Max(Box::new(**x), Box::new(**y))),
            ));
            let a1 = dup(a);
            let x1 = dup(x);
            let a2 = dup(a);
            let y1 = dup(y);
            let new_max_raw = LevelSpec::Max(
                Box::new(LevelSpec::IMax(Box::new(a1), Box::new(x1))),
                Box::new(LevelSpec::IMax(Box::new(a2), Box::new(y1))),
            );
            proof {
                imax_max_distrib(**a, **x, **y);
            }
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(new_max_raw, rho) == interp(
                    LevelSpec::IMax(
                        Box::new(**a),
                        Box::new(LevelSpec::Max(Box::new(**x), Box::new(**y))),
                    ),
                    rho,
                ));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(new_max_raw, rho) == interp(*l, rho));
            let new_max = simplify_full(new_max_raw);
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(new_max, rho) == interp(new_max_raw, rho));
            assert forall|rho: Map<nat, nat>| interp(new_max, rho) == interp(*l, rho) by {
                assert(interp(new_max, rho) == interp(new_max_raw, rho));
                assert(interp(new_max_raw, rho) == interp(*l, rho));
            }
            let result = leq_core_fueled(&new_max, &r1, diff, fuel1);
            assert(result ==> forall|rho: Map<nat, nat>| #[trigger]
                interp(new_max, rho) as int <= interp(r1, rho) as int + diff as int);
            assert(forall|rho: Map<nat, nat>| #[trigger] interp(r1, rho) == interp(*r, rho));
            assert(result ==> forall|rho: Map<nat, nat>| #[trigger]
                interp(*l, rho) as int <= interp(*r, rho) as int + diff as int);
            result
        },
        _ => false,  // unreachable given the caller's match guard
    }
}

/// Mirror of `leq_core_imax_rewrite_left` for `leq_core`'s second
/// `is_any_max` rewrite arm: `r = IMax(x, y)` where `y` is `Max`- or
/// `IMax`-shaped.
#[allow(unused_variables)]
fn leq_core_imax_rewrite_right(
    x: &Box<LevelSpec>,
    y: &Box<LevelSpec>,
    l: &LevelSpec,
    r: &LevelSpec,
    diff: i64,
    fuel: u32,
) -> (result: bool)
    requires
        *r == LevelSpec::IMax(Box::new(**x), Box::new(**y)),
    ensures
        result ==> forall|rho: Map<nat, nat>| #[trigger]
            interp(*l, rho) as int <= interp(*r, rho) as int + diff as int,
    decreases fuel,
{
    if fuel == 0 {
        return false;
    }
    let fuel1 = fuel - 1;
    let l1 = dup(l);
    match &**y {
        LevelSpec::IMax(j, k) => {
            let x1 = dup(x);
            let k1 = dup(k);
            let j1 = dup(j);
            let k2 = dup(k);
            let new_max = LevelSpec::Max(
                Box::new(LevelSpec::IMax(Box::new(x1), Box::new(k1))),
                Box::new(LevelSpec::IMax(Box::new(j1), Box::new(k2))),
            );
            proof {
                imax_imax_distrib(**x, **j, **k);
            }
            assert(forall|rho: Map<nat, nat>| #[trigger] interp(new_max, rho) == interp(*r, rho));
            let result = leq_core_fueled(&l1, &new_max, diff, fuel1);
            assert(result ==> forall|rho: Map<nat, nat>| #[trigger]
                interp(l1, rho) as int <= interp(new_max, rho) as int + diff as int);
            assert(forall|rho: Map<nat, nat>| #[trigger] interp(l1, rho) == interp(*l, rho));
            result
        },
        LevelSpec::Max(j, k) => {
            let x1 = dup(x);
            let j1 = dup(j);
            let x2 = dup(x);
            let k1 = dup(k);
            let new_max_raw = LevelSpec::Max(
                Box::new(LevelSpec::IMax(Box::new(x1), Box::new(j1))),
                Box::new(LevelSpec::IMax(Box::new(x2), Box::new(k1))),
            );
            proof {
                imax_max_distrib(**x, **j, **k);
            }
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(new_max_raw, rho) == interp(*r, rho));
            let new_max = simplify_full(new_max_raw);
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(new_max, rho) == interp(new_max_raw, rho));
            let result = leq_core_fueled(&l1, &new_max, diff, fuel1);
            assert(result ==> forall|rho: Map<nat, nat>| #[trigger]
                interp(l1, rho) as int <= interp(new_max, rho) as int + diff as int);
            assert(forall|rho: Map<nat, nat>| #[trigger] interp(l1, rho) == interp(*l, rho));
            result
        },
        _ => false,  // unreachable given the caller's match guard
    }
}

/// Fuel-threaded counterpart to `leq_imax_by_cases_via_partial`, calling
/// back into `leq_core_fueled` (mutual recursion) instead of the
/// structurally-bounded `leq_core_partial`. Reuses `case_split_sound`
/// unchanged — that lemma only needs *some* sound facts about the two
/// subgoals, not anything about how they were decided.
pub fn leq_imax_by_cases_fueled(
    l_in: LevelSpec,
    r_in: LevelSpec,
    p: u64,
    diff: i64,
    fuel: u32,
) -> (result: bool)
    ensures
        result ==> forall|rho: Map<nat, nat>| #[trigger]
            interp(l_in, rho) as int <= interp(r_in, rho) as int + diff as int,
    decreases fuel,
{
    if fuel == 0 {
        return false;
    }
    let fuel1 = fuel - 1;

    let l_in2 = dup(&l_in);
    let r_in2 = dup(&r_in);
    let succ_p = LevelSpec::Succ(Box::new(LevelSpec::Param(p)));

    // `subst1` alone leaves e.g. `IMax(a, Zero)` as literal unsimplified
    // structure, which `leq_core_fueled` has no arm for (it only recognizes
    // `IMax(_, Param(_))`) — mirroring the real `subst_simp` (`subst_level`
    // then `simplify`) is what actually lets the recursive calls decide
    // anything nontrivial.
    let lhs_0_raw = subst1(l_in, p, &LevelSpec::Zero);
    let rhs_0_raw = subst1(r_in, p, &LevelSpec::Zero);
    let lhs_s_raw = subst1(l_in2, p, &succ_p);
    let rhs_s_raw = subst1(r_in2, p, &succ_p);
    let lhs_0 = simplify_full(lhs_0_raw);
    let rhs_0 = simplify_full(rhs_0_raw);
    let lhs_s = simplify_full(lhs_s_raw);
    let rhs_s = simplify_full(rhs_s_raw);

    let ok0 = leq_core_fueled(&lhs_0, &rhs_0, diff, fuel1);
    let oks = leq_core_fueled(&lhs_s, &rhs_s, diff, fuel1);

    assert(forall|rho: Map<nat, nat>| #[trigger]
        interp(succ_p, rho) == interp(LevelSpec::Param(p), rho) + 1);
    assert(forall|rho: Map<nat, nat>| #[trigger]
        interp(LevelSpec::Param(p), rho) == eff(rho, p as nat));
    assert(forall|rho: Map<nat, nat>| #[trigger] interp(succ_p, rho) == eff(rho, p as nat) + 1);
    assert(forall|rho: Map<nat, nat>| #[trigger] interp(lhs_0, rho) == interp(lhs_0_raw, rho));
    assert(forall|rho: Map<nat, nat>| #[trigger] interp(rhs_0, rho) == interp(rhs_0_raw, rho));
    assert(forall|rho: Map<nat, nat>| #[trigger] interp(lhs_s, rho) == interp(lhs_s_raw, rho));
    assert(forall|rho: Map<nat, nat>| #[trigger] interp(rhs_s, rho) == interp(rhs_s_raw, rho));
    assert(forall|rho: Map<nat, nat>| #[trigger]
        interp(lhs_0, rho) == interp(l_in, rho.insert(p as nat, 0nat)));
    assert(forall|rho: Map<nat, nat>| #[trigger]
        interp(rhs_0, rho) == interp(r_in, rho.insert(p as nat, 0nat)));
    assert(forall|rho: Map<nat, nat>| #[trigger]
        interp(lhs_s, rho) == interp(l_in, rho.insert(p as nat, eff(rho, p as nat) + 1)));
    assert(forall|rho: Map<nat, nat>| #[trigger]
        interp(rhs_s, rho) == interp(r_in, rho.insert(p as nat, eff(rho, p as nat) + 1)));

    if ok0 && oks {
        proof {
            case_split_sound(l_in, r_in, p, diff as int, lhs_0, rhs_0, lhs_s, rhs_s);
        }
        true
    } else {
        false
    }
}

/// A second, more general fact about `simplify`'s `IMax` case (compare
/// `simplify_imax_step` above): unconditionally taking the "`l_simp` is
/// *not* known to be zero-or-one" branch is always interp-preserving,
/// regardless of `r_simp`'s shape and regardless of whether `l_simp`
/// actually is zero-or-one — it just means we don't take the extra
/// shortcut the real `simplify` takes when it positively knows `l_simp` is
/// zero-or-one (in which case `IMax(l_simp, r) == r` exactly). That's a real
/// simplification opportunity being left on the table, but leaving it on
/// the table is sound: `IMax(l_simp, r_simp)`'s own interpretation is the
/// same formula either way, so returning it (in `Succ`/`Max`-normalized
/// form, or as a plain `IMax` when neither applies) never claims anything
/// false.
pub fn simplify_imax_step_general(l_simp: LevelSpec, r_simp: LevelSpec) -> (result: LevelSpec)
    ensures
        forall|rho: Map<nat, nat>| #[trigger]
            interp(result, rho) == interp(LevelSpec::IMax(Box::new(l_simp), Box::new(r_simp)), rho),
{
    match r_simp {
        LevelSpec::Zero => LevelSpec::Zero,
        LevelSpec::Succ(s) => combining(l_simp, LevelSpec::Succ(s)),
        _ => LevelSpec::IMax(Box::new(l_simp), Box::new(r_simp)),
    }
}

/// The full `simplify` (all five `Level` shapes, including `IMax`), always
/// interp-preserving. Unlike `simplify_no_imax`, this doesn't skip `IMax` —
/// it just never takes the "`l_simp` is zero-or-one" shortcut (see
/// `simplify_imax_step_general`'s doc comment for why that's sound), so it
/// occasionally simplifies less than `level.rs`'s real `simplify` would.
/// Purely structural, no fuel needed: unlike `leq_core`, `simplify` doesn't
/// case-split or substitute, so it terminates the ordinary way.
pub fn simplify_full(l: LevelSpec) -> (result: LevelSpec)
    ensures
        forall|rho: Map<nat, nat>| #[trigger] interp(result, rho) == interp(l, rho),
    decreases l,
{
    match l {
        LevelSpec::Zero => LevelSpec::Zero,
        LevelSpec::Param(p) => LevelSpec::Param(p),
        LevelSpec::Succ(a) => {
            let sub = simplify_full(*a);
            assert(forall|rho: Map<nat, nat>| #[trigger] interp(sub, rho) == interp(*a, rho));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(LevelSpec::Succ(Box::new(sub)), rho) == interp(sub, rho) + 1);
            assert(forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) == interp(*a, rho) + 1);
            LevelSpec::Succ(Box::new(sub))
        },
        LevelSpec::Max(a, b) => {
            let sa = simplify_full(*a);
            let sb = simplify_full(*b);
            let result = combining(sa, sb);
            assert(forall|rho: Map<nat, nat>| #[trigger] interp(sa, rho) == interp(*a, rho));
            assert(forall|rho: Map<nat, nat>| #[trigger] interp(sb, rho) == interp(*b, rho));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(result, rho) == max_nat(interp(sa, rho), interp(sb, rho)));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(l, rho) == max_nat(interp(*a, rho), interp(*b, rho)));
            result
        },
        LevelSpec::IMax(a, b) => {
            let sa = simplify_full(*a);
            let sb = simplify_full(*b);
            let result = simplify_imax_step_general(sa, sb);
            assert(forall|rho: Map<nat, nat>| #[trigger] interp(sa, rho) == interp(*a, rho));
            assert(forall|rho: Map<nat, nat>| #[trigger] interp(sb, rho) == interp(*b, rho));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(result, rho) == interp(LevelSpec::IMax(Box::new(sa), Box::new(sb)), rho));
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(LevelSpec::IMax(Box::new(sa), Box::new(sb)), rho) == if interp(sb, rho)
                    == 0 {
                    0
                } else {
                    max_nat(interp(sa, rho), interp(sb, rho))
                });
            assert(forall|rho: Map<nat, nat>| #[trigger]
                interp(l, rho) == if interp(*b, rho) == 0 {
                    0
                } else {
                    max_nat(interp(*a, rho), interp(*b, rho))
                });
            result
        },
    }
}

/// The identity behind `leq_core`'s first `is_any_max` rewrite arm (the one
/// missing from `leq_core_fueled`/`verified_leq_core` — see their doc
/// comments): `imax` distributes over a nested `imax` on its right. Holds
/// unconditionally, no side conditions on `a`, `x`, or `y`.
pub proof fn imax_imax_distrib(a: LevelSpec, x: LevelSpec, y: LevelSpec)
    ensures
        forall|rho: Map<nat, nat>| #[trigger]
            interp(
                LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::IMax(Box::new(x), Box::new(y)))),
                rho,
            ) == interp(
                LevelSpec::Max(
                    Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
                    Box::new(LevelSpec::IMax(Box::new(x), Box::new(y))),
                ),
                rho,
            ),
{
    assert forall|rho: Map<nat, nat>|
        interp(
            LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::IMax(Box::new(x), Box::new(y)))),
            rho,
        ) == interp(
            LevelSpec::Max(
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
                Box::new(LevelSpec::IMax(Box::new(x), Box::new(y))),
            ),
            rho,
        ) by {
        assert(interp(LevelSpec::IMax(Box::new(x), Box::new(y)), rho) == if interp(y, rho) == 0 {
            0
        } else {
            max_nat(interp(x, rho), interp(y, rho))
        });
        assert(interp(LevelSpec::IMax(Box::new(a), Box::new(y)), rho) == if interp(y, rho) == 0 {
            0
        } else {
            max_nat(interp(a, rho), interp(y, rho))
        });
        assert(interp(
            LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::IMax(Box::new(x), Box::new(y)))),
            rho,
        ) == if interp(LevelSpec::IMax(Box::new(x), Box::new(y)), rho) == 0 {
            0
        } else {
            max_nat(interp(a, rho), interp(LevelSpec::IMax(Box::new(x), Box::new(y)), rho))
        });
        assert(interp(
            LevelSpec::Max(
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
                Box::new(LevelSpec::IMax(Box::new(x), Box::new(y))),
            ),
            rho,
        ) == max_nat(
            interp(LevelSpec::IMax(Box::new(a), Box::new(y)), rho),
            interp(LevelSpec::IMax(Box::new(x), Box::new(y)), rho),
        ));
    }
}

/// The identity behind `leq_core`'s second `is_any_max` rewrite arm: `imax`
/// distributes over a `max` on its right. Also holds unconditionally.
pub proof fn imax_max_distrib(a: LevelSpec, x: LevelSpec, y: LevelSpec)
    ensures
        forall|rho: Map<nat, nat>| #[trigger]
            interp(
                LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::Max(Box::new(x), Box::new(y)))),
                rho,
            ) == interp(
                LevelSpec::Max(
                    Box::new(LevelSpec::IMax(Box::new(a), Box::new(x))),
                    Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
                ),
                rho,
            ),
{
    assert forall|rho: Map<nat, nat>|
        interp(
            LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::Max(Box::new(x), Box::new(y)))),
            rho,
        ) == interp(
            LevelSpec::Max(
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(x))),
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
            ),
            rho,
        ) by {
        assert(interp(LevelSpec::Max(Box::new(x), Box::new(y)), rho) == max_nat(
            interp(x, rho),
            interp(y, rho),
        ));
        assert(interp(LevelSpec::IMax(Box::new(a), Box::new(x)), rho) == if interp(x, rho) == 0 {
            0
        } else {
            max_nat(interp(a, rho), interp(x, rho))
        });
        assert(interp(LevelSpec::IMax(Box::new(a), Box::new(y)), rho) == if interp(y, rho) == 0 {
            0
        } else {
            max_nat(interp(a, rho), interp(y, rho))
        });
        assert(interp(
            LevelSpec::IMax(Box::new(a), Box::new(LevelSpec::Max(Box::new(x), Box::new(y)))),
            rho,
        ) == if interp(LevelSpec::Max(Box::new(x), Box::new(y)), rho) == 0 {
            0
        } else {
            max_nat(interp(a, rho), interp(LevelSpec::Max(Box::new(x), Box::new(y)), rho))
        });
        assert(interp(
            LevelSpec::Max(
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(x))),
                Box::new(LevelSpec::IMax(Box::new(a), Box::new(y))),
            ),
            rho,
        ) == max_nat(
            interp(LevelSpec::IMax(Box::new(a), Box::new(x)), rho),
            interp(LevelSpec::IMax(Box::new(a), Box::new(y)), rho),
        ));
    }
}

} // verus!
#[cfg(test)]
mod tests {
    use super::*;

    fn succ(l: LevelSpec) -> LevelSpec {
        LevelSpec::Succ(Box::new(l))
    }
    fn max(l: LevelSpec, r: LevelSpec) -> LevelSpec {
        LevelSpec::Max(Box::new(l), Box::new(r))
    }

    // Sanity checks that `leq_core_partial` is a real (non-vacuous) decision
    // procedure on the fragment it covers, not just a stub that always
    // returns `false`. Formal soundness (true results are always correct)
    // is checked by Verus; these just check it says `true` when it should.
    #[test]
    fn zero_leq_zero() {
        assert!(leq_core_partial(&LevelSpec::Zero, &LevelSpec::Zero, 0));
    }

    #[test]
    fn succ_chain() {
        // Succ(Succ(Zero)) <= Succ(Succ(Succ(Zero)))
        let l = succ(succ(LevelSpec::Zero));
        let r = succ(succ(succ(LevelSpec::Zero)));
        assert!(leq_core_partial(&l, &r, 0));
        // ... but not the other way around.
        assert!(!leq_core_partial(&r, &l, 0));
    }

    #[test]
    fn param_needs_matching_id() {
        let p0 = LevelSpec::Param(0);
        let p1 = LevelSpec::Param(1);
        assert!(leq_core_partial(&p0, &LevelSpec::Param(0), 0));
        assert!(!leq_core_partial(&p0, &p1, 0));
    }

    #[test]
    fn max_left_needs_both_arms() {
        // max(Param(0), Param(1)) <= Param(1) is NOT universally valid
        // (fails when Param(0)'s assignment exceeds Param(1)'s).
        let l = max(LevelSpec::Param(0), LevelSpec::Param(1));
        assert!(!leq_core_partial(&l, &LevelSpec::Param(1), 0));
        // max(Param(0), Param(0)) <= Param(0) is fine.
        let l2 = max(LevelSpec::Param(0), LevelSpec::Param(0));
        assert!(leq_core_partial(&l2, &LevelSpec::Param(0), 0));
    }

    #[test]
    fn imax_shapes_conservatively_false() {
        // Not a soundness bug: leq_core_partial just doesn't attempt IMax yet.
        let l = LevelSpec::IMax(Box::new(LevelSpec::Zero), Box::new(LevelSpec::Zero));
        assert!(!leq_core_partial(&l, &l, 0));
    }

    fn assert_not_imax(l: &LevelSpec) {
        assert!(!matches!(l, LevelSpec::IMax(..)));
    }

    // Sanity checks that the case-split termination lemma actually fires
    // (isn't vacuous) for a handful of concrete `a`s and both `flag` values
    // — this is the fact `leq_core_partial`'s doc comment says is needed
    // before the `IMax`-by-cases branches themselves can be added.
    #[test]
    fn case_split_zero_never_imax() {
        for flag in [false, true] {
            assert_not_imax(&case_split_resolves_zero(LevelSpec::Param(7), 5, flag));
            assert_not_imax(&case_split_resolves_zero(max(LevelSpec::Param(1), LevelSpec::Param(2)), 5, flag));
            assert_not_imax(&case_split_resolves_zero(LevelSpec::Zero, 5, flag));
        }
    }

    #[test]
    fn case_split_succ_never_imax() {
        for flag in [false, true] {
            assert_not_imax(&case_split_resolves_succ(LevelSpec::Param(7), 5, flag));
            assert_not_imax(&case_split_resolves_succ(max(LevelSpec::Param(1), LevelSpec::Param(2)), 5, flag));
            assert_not_imax(&case_split_resolves_succ(LevelSpec::Zero, 5, flag));
        }
    }

    fn imax(l: LevelSpec, r: LevelSpec) -> LevelSpec {
        LevelSpec::IMax(Box::new(l), Box::new(r))
    }

    // `leq_core_fueled` is the payoff: it actually decides real `IMax`
    // inequalities (given enough fuel) that `leq_core_partial` always
    // conservatively refused (see `imax_shapes_conservatively_false` above).
    #[test]
    fn fueled_handles_imax_case_split() {
        // imax(a, b) <= max(a, b) is universally valid (imax is either 0 or
        // exactly max(a,b)), but deciding it requires case-splitting on b.
        let l = imax(LevelSpec::Param(0), LevelSpec::Param(1));
        let r = max(LevelSpec::Param(0), LevelSpec::Param(1));
        assert!(leq_core_fueled(&l, &r, 0, 20));
    }

    #[test]
    fn fueled_rejects_invalid_imax_inequality() {
        // imax(Param(0), Param(1)) <= Zero is NOT universally valid (fails
        // whenever Param(1)'s assignment is nonzero).
        let l = imax(LevelSpec::Param(0), LevelSpec::Param(1));
        assert!(!leq_core_fueled(&l, &LevelSpec::Zero, 0, 20));
    }

    #[test]
    fn fueled_zero_fuel_is_conservative_not_wrong() {
        // With no fuel at all, it must refuse rather than guess - even for
        // a case it could otherwise decide easily.
        assert!(!leq_core_fueled(&LevelSpec::Zero, &LevelSpec::Zero, 0, 0));
        // Non-IMax cases don't actually need the fuel budget's IMax-splitting
        // capability, so a small fuel budget still resolves them.
        assert!(leq_core_fueled(&LevelSpec::Zero, &LevelSpec::Zero, 0, 1));
    }

    // These two exercise the `is_any_max` rewrite arms specifically: before
    // wiring in imax_imax_distrib/imax_max_distrib, both would fall through
    // to `_ => false`, i.e. wrongly refuse a universally-valid inequality
    // (an equality, in fact - both sides denote the same thing).
    #[test]
    fn fueled_handles_imax_imax_rewrite() {
        // imax(a, imax(x,y)) == max(imax(a,y), imax(x,y))
        let l = imax(LevelSpec::Param(0), imax(LevelSpec::Param(1), LevelSpec::Param(2)));
        let r = max(imax(LevelSpec::Param(0), LevelSpec::Param(2)), imax(LevelSpec::Param(1), LevelSpec::Param(2)));
        assert!(leq_core_fueled(&l, &r, 0, 20));
        assert!(leq_core_fueled(&r, &l, 0, 20));
    }

    #[test]
    fn fueled_handles_imax_max_rewrite() {
        // imax(a, max(x,y)) == max(imax(a,x), imax(a,y))
        let l = imax(LevelSpec::Param(0), max(LevelSpec::Param(1), LevelSpec::Param(2)));
        let r = max(imax(LevelSpec::Param(0), LevelSpec::Param(1)), imax(LevelSpec::Param(0), LevelSpec::Param(2)));
        assert!(leq_core_fueled(&l, &r, 0, 20));
        assert!(leq_core_fueled(&r, &l, 0, 20));
    }
}
