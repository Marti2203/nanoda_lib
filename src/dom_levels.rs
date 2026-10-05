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

/// What level instantiation needs of the signature, at every instance:
/// constants mention only their own parameters, locals none.
#[verifier::opaque]
pub open spec fn sig_lps(sig: Sig) -> bool {
    forall|ks: Seq<u64>, vs: Seq<LevelSpec>| ks.len() == vs.len() ==> #[trigger] crate::ti_level::sig_lp_ok(crate::ti_strip::strip(sig), ks, vs)
}

pub proof fn sig_lps_at(sig: Sig, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        sig_lps(sig),
        ks.len() == vs.len(),
    ensures
        crate::ti_level::sig_lp_ok(crate::ti_strip::strip(sig), ks, vs),
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

/// A CLOSED TYPE'S TWO INSTANCES CONVERT, in any well-formed context.
pub proof fn closed_conv(sig: Sig, g: Ctx, r: ExprSpec, l: LevelSpec, ks: Seq<u64>, ls1: Seq<LevelSpec>, ls2: Seq<LevelSpec>)
    requires
        derivable(crate::ti_strip::strip(sig), eq(Seq::empty(), r, r, sort(l))),
        crate::expr_model::nlbv(r) == 0,
        derivable(sig, Jd::Wf(g)),
        sig_lps(sig),
        ks.len() == ls1.len(),
        levs_eq(ls1, ls2),
    ensures
        derivable(sig, eq(g, subst_expr_levels(r, ks, ls1), subst_expr_levels(r, ks, ls2), sort(subst_level_spec(l, ks, ls1)))),
        crate::ti_chain::tchain(sig, g, subst_expr_levels(r, ks, ls1), subst_expr_levels(r, ks, ls2)),
{
    let ss = crate::ti_strip::strip(sig);
    sig_lps_at(sig, ks, ls1);
    sig_lps_at(sig, ks, ls2);
    crate::ti_ls2::ls_pair_nil(ss, r, r, sort(l), ks, ls1, ls2);
    let (r1, r2) = (subst_expr_levels(r, ks, ls1), subst_expr_levels(r, ks, ls2));
    let t1 = sort(subst_level_spec(l, ks, ls1));
    crate::ti_strip::strip_derivable(sig, eq(Seq::empty(), r1, r2, t1));
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

} // verus!
