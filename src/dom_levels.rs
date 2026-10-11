//! LEVELS IN THE MODEL'S FIELD TYPES (docs/TYPED_TARGET.md, S6 "Universe
//! polymorphism", U3b): padded instances, level substitution through
//! spines, and a closed type's two instances converting.
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_model::{interp, subst_level_spec, subst_levels_spec};
#[cfg(verus_only)]
use crate::expr_model::subst_expr_levels;
#[cfg(verus_only)]
use crate::conv_cr::levs_eq;
#[cfg(verus_only)]
use crate::ti_syntax::{Sig, Ctx, Jd, derivable, eq, sort};
#[cfg(verus_only)]
use crate::beta_model::{spine_head, spine_args};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What level instantiation needs of the signature below every rank
/// (`ti_strip::strip_below`), at every instance: constants and the
/// recursors' rules mention only their own parameters, locals none.
#[verifier::opaque]
pub open spec fn sig_lps(sig: Sig) -> bool {
    forall|r: int, ks: Seq<u64>, vs: Seq<LevelSpec>| ks.len() == vs.len()
        ==> #[trigger] crate::ti_level::sig_lp_ok(crate::ti_strip::strip_below(sig, r), ks, vs)
}

pub proof fn sig_lps_at(sig: Sig, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        sig_lps(sig),
        ks.len() == vs.len(),
    ensures
        crate::ti_level::sig_lp_ok(crate::ti_strip::strip(sig), ks, vs),
{
    reveal(sig_lps);
    crate::ti_strip::strip_below_zero(sig);
    assert(crate::ti_level::sig_lp_ok(crate::ti_strip::strip_below(sig, 0), ks, vs));
}

/// A strip keeps the level facts.
pub proof fn sig_lps_strip(sig: Sig, r: int)
    requires
        sig_lps(sig),
    ensures
        sig_lps(crate::ti_strip::strip_below(sig, r)),
{
    reveal(sig_lps);
    let s1 = crate::ti_strip::strip_below(sig, r);
    assert forall|r2: int, ks: Seq<u64>, vs: Seq<LevelSpec>| ks.len() == vs.len()
        implies #[trigger] crate::ti_level::sig_lp_ok(crate::ti_strip::strip_below(s1, r2), ks, vs) by {
        crate::ti_strip::strip_below_twice(sig, r, r2);
        let m = if r <= r2 { r } else { r2 };
        assert(crate::ti_level::sig_lp_ok(crate::ti_strip::strip_below(sig, m), ks, vs));
    }
}

pub proof fn sig_lps_below(sig: Sig, r: int, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        sig_lps(sig),
        ks.len() == vs.len(),
    ensures
        crate::ti_level::sig_lp_ok(crate::ti_strip::strip_below(sig, r), ks, vs),
{
    reveal(sig_lps);
}

/// Padding keeps level equivalence.
pub proof fn lpad_levs_eq(a: Seq<LevelSpec>, b: Seq<LevelSpec>, n: nat)
    requires
        levs_eq(a, b),
    ensures
        levs_eq(crate::dom_rel::lpad(a, n), crate::dom_rel::lpad(b, n)),
{
    let (pa, pb) = (crate::dom_rel::lpad(a, n), crate::dom_rel::lpad(b, n));
    assert forall|i: int, rho: Map<nat, nat>| 0 <= i < pa.len() implies #[trigger] interp(pa[i], rho) == interp(pb[i], rho) by {
        if i < a.len() {
            assert(interp(a[i], rho) == interp(b[i], rho));
        }
    }
}

/// A level without parameters is fixed by every instance.
pub proof fn lp_none_id(l: LevelSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        crate::level_inst::lp_in(l, Seq::empty()),
    ensures
        subst_level_spec(l, ks, vs) == l,
    decreases l,
{
    match l {
        LevelSpec::Succ(a) => lp_none_id(*a, ks, vs),
        LevelSpec::Max(a, b) => { lp_none_id(*a, ks, vs); lp_none_id(*b, ks, vs); },
        LevelSpec::IMax(a, b) => { lp_none_id(*a, ks, vs); lp_none_id(*b, ks, vs); },
        _ => {},
    }
}

/// A term without level parameters is fixed by every instance.
pub proof fn elp_none_id(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        crate::level_inst::elp_in(e, Seq::empty()),
    ensures
        subst_expr_levels(e, ks, vs) == e,
    decreases e,
{
    match e {
        ExprSpec::Sort(l) => lp_none_id(l, ks, vs),
        ExprSpec::Const(id, ls) => {
            assert(subst_levels_spec(ls, ks, vs) =~= ls) by {
                assert forall|i: int| 0 <= i < ls.len() implies #[trigger] subst_levels_spec(ls, ks, vs)[i] == ls[i] by {
                    lp_none_id(ls[i], ks, vs);
                }
            }
        },
        ExprSpec::App(f, a) => { elp_none_id(*f, ks, vs); elp_none_id(*a, ks, vs); },
        ExprSpec::Bind(_, t, b) => { elp_none_id(*t, ks, vs); elp_none_id(*b, ks, vs); },
        ExprSpec::Let(t, v, b) => { elp_none_id(*t, ks, vs); elp_none_id(*v, ks, vs); elp_none_id(*b, ks, vs); },
        ExprSpec::Proj(_, st) => elp_none_id(*st, ks, vs),
        _ => {},
    }
}

/// Level substitution through a constant's spine.
pub proof fn sl_spine(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        spine_head(e) is Const,
    ensures
        spine_head(subst_expr_levels(e, ks, vs))
            == ExprSpec::Const(spine_head(e)->Const_0, subst_levels_spec(spine_head(e)->Const_1, ks, vs)),
        spine_args(subst_expr_levels(e, ks, vs)).len() == spine_args(e).len(),
        forall|q: int| 0 <= q < spine_args(e).len() ==> #[trigger] spine_args(subst_expr_levels(e, ks, vs))[q]
            == subst_expr_levels(spine_args(e)[q], ks, vs),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        sl_spine(*f, ks, vs);
        let (a1, a0) = (spine_args(subst_expr_levels(e, ks, vs)), spine_args(e));
        assert forall|q: int| 0 <= q < a0.len() implies #[trigger] a1[q] == subst_expr_levels(a0[q], ks, vs) by {
            if q < a0.len() - 1 {
                assert(a1[q] == spine_args(subst_expr_levels(*f, ks, vs))[q]);
                assert(a0[q] == spine_args(*f)[q]);
            }
        }
    }
}

/// A blind type's arguments are blind.
pub proof fn blind_args(sig: Sig, e: ExprSpec)
    requires
        crate::dom_code::blind_ty(sig, e),
    ensures
        forall|q: int| 0 <= q < spine_args(e).len() ==> #[trigger] crate::dom_code::blind_ty(sig, spine_args(e)[q]),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        blind_args(sig, *f);
        let a = spine_args(e);
        assert forall|q: int| 0 <= q < a.len() implies #[trigger] crate::dom_code::blind_ty(sig, a[q]) by {
            if q < a.len() - 1 {
                assert(a[q] == spine_args(*f)[q]);
            }
        }
    }
}

/// Substituting no levels changes nothing.
pub proof fn lp_nil(l: LevelSpec, ks: Seq<u64>)
    ensures
        subst_level_spec(l, ks, Seq::empty()) == l,
    decreases l,
{
    match l {
        LevelSpec::Succ(a) => lp_nil(*a, ks),
        LevelSpec::Max(a, b) => { lp_nil(*a, ks); lp_nil(*b, ks); },
        LevelSpec::IMax(a, b) => { lp_nil(*a, ks); lp_nil(*b, ks); },
        _ => {},
    }
}

pub proof fn sl_nil(e: ExprSpec, ks: Seq<u64>)
    ensures
        subst_expr_levels(e, ks, Seq::empty()) == e,
    decreases e,
{
    match e {
        ExprSpec::Sort(l) => lp_nil(l, ks),
        ExprSpec::Const(id, ls) => {
            assert(subst_levels_spec(ls, ks, Seq::empty()) =~= ls) by {
                assert forall|i: int| 0 <= i < ls.len() implies #[trigger] subst_levels_spec(ls, ks, Seq::empty())[i] == ls[i] by {
                    lp_nil(ls[i], ks);
                }
            }
        },
        ExprSpec::App(f, a) => { sl_nil(*f, ks); sl_nil(*a, ks); },
        ExprSpec::Bind(_, t, b) => { sl_nil(*t, ks); sl_nil(*b, ks); },
        ExprSpec::Let(t, v, b) => { sl_nil(*t, ks); sl_nil(*v, ks); sl_nil(*b, ks); },
        ExprSpec::Proj(_, st) => sl_nil(*st, ks),
        _ => {},
    }
}

/// A CLOSED TYPE'S TWO INSTANCES CONVERT, in any well-formed context --
/// typed below a rank (`ti_strip::strip_below`).
pub proof fn closed_conv(sig: Sig, rr: int, g: Ctx, r: ExprSpec, l: LevelSpec, ks: Seq<u64>, ls1: Seq<LevelSpec>, ls2: Seq<LevelSpec>)
    requires
        derivable(crate::ti_strip::strip_below(sig, rr), eq(Seq::empty(), r, r, sort(l))),
        crate::ti_syntax::iota_ok(sig) || rr <= 0,
        crate::expr_model::nlbv(r) == 0,
        derivable(sig, Jd::Wf(g)),
        sig_lps(sig),
        ks.len() == ls1.len(),
        levs_eq(ls1, ls2),
    ensures
        derivable(sig, eq(g, subst_expr_levels(r, ks, ls1), subst_expr_levels(r, ks, ls2), sort(subst_level_spec(l, ks, ls1)))),
        crate::ti_chain::tchain(sig, g, subst_expr_levels(r, ks, ls1), subst_expr_levels(r, ks, ls2)),
{
    let ss = crate::ti_strip::strip_below(sig, rr);
    sig_lps_below(sig, rr, ks, ls1);
    sig_lps_below(sig, rr, ks, ls2);
    crate::ti_ls2::ls_pair_nil(ss, r, r, sort(l), ks, ls1, ls2);
    let (r1, r2) = (subst_expr_levels(r, ks, ls1), subst_expr_levels(r, ks, ls2));
    let t1 = sort(subst_level_spec(l, ks, ls1));
    crate::ti_strip::derivable_up(sig, rr, eq(Seq::empty(), r1, r2, t1));
    crate::ti_level::ls_nlbv(r, ks, ls1);
    crate::ti_level::ls_nlbv(r, ks, ls2);
    crate::ti_sr::wk_closed(sig, g, r1, r2, t1);
    reveal(crate::ti_sub::tconvd);
    crate::ti_chain::tchain_one(sig, g, r1, r2);
}

/// Level parameters without repeats.
pub open spec fn lps_distinct(ks: Seq<u64>) -> bool {
    forall|i: int, j: int| #![trigger ks[i], ks[j]] 0 <= i < ks.len() && 0 <= j < ks.len() && ks[i] == ks[j] ==> i == j
}

/// At distinct parameters, the parameters' instance is the instance.
pub proof fn sl_plevels_id(ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        lps_distinct(ks),
        vs.len() == ks.len(),
    ensures
        subst_levels_spec(crate::rec_canon::plevels(ks), ks, vs) == vs,
{
    let a = subst_levels_spec(crate::rec_canon::plevels(ks), ks, vs);
    assert forall|i: int| 0 <= i < vs.len() implies #[trigger] a[i] == vs[i] by {
        let q = ks[i];
        crate::level_inst::find_level_idx_contains(ks, q);
        assert(ks.contains(q));
        crate::ti_ls2::find_level_idx_at(ks, q);
        let m = crate::level_model::find_level_idx(ks, q)->Some_0;
        assert(ks[m as int] == ks[i]);
        assert(m as int == i);
        assert(crate::rec_canon::plevels(ks)[i] == LevelSpec::Param(q));
    }
    assert(a =~= vs);
}

/// Parameter sets: every level parameter of `a` is in `b`.
pub open spec fn lps_sub(a: Seq<u64>, b: Seq<u64>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> b.contains(#[trigger] a[i])
}

pub proof fn lp_mono(l: LevelSpec, a: Seq<u64>, b: Seq<u64>)
    requires
        crate::level_inst::lp_in(l, a),
        lps_sub(a, b),
    ensures
        crate::level_inst::lp_in(l, b),
    decreases l,
{
    match l {
        LevelSpec::Succ(x) => lp_mono(*x, a, b),
        LevelSpec::Max(x, y) => { lp_mono(*x, a, b); lp_mono(*y, a, b); },
        LevelSpec::IMax(x, y) => { lp_mono(*x, a, b); lp_mono(*y, a, b); },
        LevelSpec::Param(q) => {
            crate::ti_ls2::find_level_idx_at(a, q);
            let i = crate::level_model::find_level_idx(a, q)->Some_0;
            assert(b.contains(a[i as int]));
            crate::level_inst::find_level_idx_contains(b, q);
        },
        _ => {},
    }
}

/// A term over the parameters `a` is over any superset.
pub proof fn elp_mono(e: ExprSpec, a: Seq<u64>, b: Seq<u64>)
    requires
        crate::level_inst::elp_in(e, a),
        lps_sub(a, b),
    ensures
        crate::level_inst::elp_in(e, b),
    decreases e,
{
    match e {
        ExprSpec::Sort(l) => lp_mono(l, a, b),
        ExprSpec::Const(_, ls) => {
            assert forall|i: int| 0 <= i < ls.len() implies crate::level_inst::lp_in(#[trigger] ls[i], b) by {
                lp_mono(ls[i], a, b);
            }
        },
        ExprSpec::App(f, x) => { elp_mono(*f, a, b); elp_mono(*x, a, b); },
        ExprSpec::Bind(_, t, x) => { elp_mono(*t, a, b); elp_mono(*x, a, b); },
        ExprSpec::Let(t, v, x) => { elp_mono(*t, a, b); elp_mono(*v, a, b); elp_mono(*x, a, b); },
        ExprSpec::Proj(_, x) => elp_mono(*x, a, b),
        _ => {},
    }
}

/// An equation at one sort holds at an equivalent one (sort types).
pub proof fn sort_retype2(sig: Sig, g: Ctx, x: ExprSpec, y: ExprSpec, l: LevelSpec, l2: LevelSpec)
    requires
        derivable(sig, eq(g, x, y, sort(l2))),
        crate::conv_cr::lev_eq(l2, l),
    ensures
        derivable(sig, eq(g, x, y, sort(l))),
{
    crate::ti_ls2::sort_retype(sig, g, x, y, l, l2);
}

/// Padding commutes with level substitution.
pub proof fn lpad_sl(us: Seq<LevelSpec>, n: nat, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        subst_levels_spec(crate::dom_rel::lpad(us, n), ks, vs) == crate::dom_rel::lpad(subst_levels_spec(us, ks, vs), n),
{
    assert(subst_levels_spec(crate::dom_rel::lpad(us, n), ks, vs) =~= crate::dom_rel::lpad(subst_levels_spec(us, ks, vs), n));
}

/// A canonical former's parameter sorts mention only its level parameters.
pub proof fn pdoms_elp(sig: Sig, j: u64, q: int)
    requires
        sig_lps(sig),
        crate::dom_code::has_canon(sig, j),
        0 <= q < crate::dom_code::canon_shape(sig, j).np,
    ensures
        crate::level_inst::elp_in(crate::dom_code::canon_shape(sig, j).pdoms[q], sig.consts[j].lps),
{
    let sh = crate::dom_code::canon_shape(sig, j);
    crate::dom_ctor_bound::ctor_shape_ind(sig, j);
    sig_lps_at(sig, Seq::empty(), Seq::empty());
    assert(crate::ti_strip::strip(sig).consts.contains_key(j));
    let t = sig.consts[j].ty;
    crate::ti_level::elp_binds(crate::expr_model::BinderKind::Pi, sh.pdoms + sh.idoms, crate::rec_canon::tbody(t, sh.np + sh.ni), sig.consts[j].lps);
    assert((sh.pdoms + sh.idoms)[q] == sh.pdoms[q]);
}

} // verus!
