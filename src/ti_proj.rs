//! PROJECTIONS' SYNTAX (docs/TYPED_TARGET.md, "Structures stage plan",
//! T2b): a canonical structure's field types never mention the earlier
//! fields (`rec_canon::field_kind`), so a projection's type is its field's
//! type over the parameters alone, and it commutes with the operations the
//! derivation transformations apply.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[cfg(verus_only)]
use crate::ti_subst::{psub, up, Sub};
#[cfg(verus_only)]
use crate::ti_spine::vsub;
#[cfg(verus_only)]
use crate::beta_model::{spine_app, spine_head, spine_args};
#[cfg(verus_only)]
use crate::rec_canon::vars;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Substitutions agreeing below `k` act alike on a term with no loose
/// variable from `k` on.
pub proof fn psub_agree(e: ExprSpec, s: Sub, t: Sub, k: nat)
    requires
        crate::expr_model::nlbv(e) <= k,
        forall|i: nat| i < k ==> #[trigger] s(i) == t(i),
    ensures
        psub(e, s) == psub(e, t),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            psub_agree(*f, s, t, k);
            psub_agree(*a, s, t, k);
        },
        ExprSpec::Bind(_, ty, b) => {
            psub_agree(*ty, s, t, k);
            assert forall|i: nat| i < k + 1 implies #[trigger] up(s)(i) == up(t)(i) by {
                if i > 0 {
                    assert(s((i - 1) as nat) == t((i - 1) as nat));
                }
            }
            psub_agree(*b, up(s), up(t), k + 1);
        },
        ExprSpec::Let(ty, v, b) => {
            psub_agree(*ty, s, t, k);
            psub_agree(*v, s, t, k);
            assert forall|i: nat| i < k + 1 implies #[trigger] up(s)(i) == up(t)(i) by {
                if i > 0 {
                    assert(s((i - 1) as nat) == t((i - 1) as nat));
                }
            }
            psub_agree(*b, up(s), up(t), k + 1);
        },
        ExprSpec::Proj(_, x) => {
            psub_agree(*x, s, t, k);
        },
        _ => {},
    }
}

/// Substituting a telescope's instance: the substitution goes inside its
/// arguments.
pub proof fn psub_vsub(e: ExprSpec, xs: Seq<ExprSpec>, s: Sub)
    requires
        crate::expr_model::nlbv(e) <= xs.len(),
    ensures
        psub(vsub(e, xs), s) == vsub(e, crate::ti_subst::spsub(xs, s)),
{
    use crate::ti_beta::{tsub, tsub_at, vsub_tsub};
    let n = xs.len();
    let ys = crate::ti_subst::spsub(xs, s);
    vsub_tsub(e, xs);
    vsub_tsub(e, ys);
    crate::ti_subst::psub_psub(e, tsub(xs, n), s);
    assert forall|i: nat| i < n implies #[trigger] crate::ti_subst::comp_ss(tsub(xs, n), s)(i) == tsub(ys, n)(i) by {
        tsub_at(xs, n, i);
        tsub_at(ys, n, i);
    }
    psub_agree(e, crate::ti_subst::comp_ss(tsub(xs, n), s), tsub(ys, n), n);
}

/// A STRUCTURE'S FIELD at an instance, in its parameters' and earlier
/// fields' context.
pub open spec fn sfield(sig: Sig, s: u64, i: nat, us: Seq<LevelSpec>) -> ExprSpec {
    crate::expr_model::subst_expr_levels(crate::dom_code::canon_shape(sig, s).fields[0][i as int], sig.consts[s].lps, us)
}

/// It mentions only the parameters, and no variable past them and the
/// earlier fields.
pub proof fn sfield_vsub(sig: Sig, s: u64, i: nat, us: Seq<LevelSpec>, a: Seq<ExprSpec>, b: Seq<ExprSpec>, c: Seq<ExprSpec>)
    requires
        crate::dom_code::has_canon(sig, s),
        crate::dom_code::canon_shape(sig, s).nmin() == 1,
        crate::dom_code::canon_shape(sig, s).ni == 0,
        i < crate::dom_code::canon_shape(sig, s).fields[0].len(),
        a.len() == crate::dom_code::canon_shape(sig, s).np,
        b.len() == i,
        c.len() == i,
    ensures
        crate::expr_model::nlbv(sfield(sig, s, i, us)) <= crate::dom_code::canon_shape(sig, s).np + i,
        vsub(sfield(sig, s, i, us), a + b) == vsub(sfield(sig, s, i, us), a + c),
{
    let sh = crate::dom_code::canon_shape(sig, s);
    let np = sh.np;
    let f = sh.fields[0][i as int];
    let lps = sig.consts[s].lps;
    let fu = sfield(sig, s, i, us);
    let (xs, ys) = (a + b, a + c);
    crate::dom_canon::canon_fields(sig, s, 0, i as int);
    crate::dom_canon::sl_kinds(sig, s, sh.pdoms, np, i, f, 0, lps, us);
    if crate::rec_canon::direct_occ(f, s, sh.us(), np, sh.ni, i) {
        crate::dom_ctor_bound::ctor_shape(sig, s, 0);
        crate::beta_model::spine_recompose(f);
        assert(spine_args(f).subrange(0, np as int) =~= spine_args(f));
        assert(spine_args(f) =~= vars(i, np));
        let ci0 = ExprSpec::Const(s, sh.us());
        let ci = ExprSpec::Const(s, crate::level_model::subst_levels_spec(sh.us(), lps, us));
        crate::dom_rec_shape::sl_spine(ci0, vars(i, np), lps, us);
        crate::dom_rec_shape::sl_vars(i, np, lps, us);
        assert(fu == spine_app(ci, vars(i, np)));
        assert forall|q: int| 0 <= q < vars(i, np).len() implies crate::expr_model::nlbv(#[trigger] vars(i, np)[q]) <= np + i by {}
        spine_nlbv_le(ci, vars(i, np), np + i);
        crate::dom_iota::vars_vidx(i, np);
        crate::ti_spine::vsub_spine_vars(ci, crate::dom_iota::vidx(i, np), xs);
        crate::ti_spine::vsub_spine_vars(ci, crate::dom_iota::vidx(i, np), ys);
        assert(Seq::new(np, |q: int| xs[xs.len() - 1 - crate::dom_iota::vidx(i, np)[q]]) =~= a);
        assert(Seq::new(np, |q: int| ys[ys.len() - 1 - crate::dom_iota::vidx(i, np)[q]]) =~= a);
    } else if crate::rec_canon::simple_ty(sig, s, f) {
        crate::dom_iota::simple_closed(sig, s, f);
        crate::ti_level::ls_nlbv(f, lps, us);
        crate::ti_spine::vsub_closed(fu, xs);
        crate::ti_spine::vsub_closed(fu, ys);
    } else if crate::rec_canon::pvar_field(sh.pdoms, np, i, f) {
        let v = f->Var_0;
        assert(fu == f);
        crate::ti_spine::vsub_var(v, xs);
        crate::ti_spine::vsub_var(v, ys);
        assert(xs[xs.len() - 1 - v] == a[np + i - 1 - v]);
        assert(ys[ys.len() - 1 - v] == a[np + i - 1 - v]);
    } else {
        assert(crate::rec_canon::psimple(sig, s, sh.pdoms, np, i, fu));
        psimple_nlbv(sig, s, sh.pdoms, np, i, fu);
        crate::dom_psimple::plow_vsub(sig, s, sh.pdoms, np, i, fu, a, b);
        crate::dom_psimple::plow_vsub(sig, s, sh.pdoms, np, i, fu, a, c);
    }
}

/// A spine of terms below `n` is below `n`.
pub proof fn spine_nlbv_le(h: ExprSpec, args: Seq<ExprSpec>, n: nat)
    requires
        crate::expr_model::nlbv(h) <= n,
        forall|q: int| 0 <= q < args.len() ==> crate::expr_model::nlbv(#[trigger] args[q]) <= n,
    ensures
        crate::expr_model::nlbv(spine_app(h, args)) <= n,
    decreases args.len(),
{
    if args.len() > 0 {
        let init = args.subrange(0, args.len() - 1);
        spine_nlbv_le(h, init, n);
        assert(crate::expr_model::nlbv(args[args.len() - 1]) <= n);
    }
}

/// A simple type over the parameters mentions only them and the earlier
/// fields' slots.
pub proof fn psimple_nlbv(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec)
    requires
        crate::rec_canon::psimple(sig, ind, pdoms, np, k, e) || crate::rec_canon::psapp(sig, ind, pdoms, np, k, e),
    ensures
        crate::expr_model::nlbv(e) <= np + k,
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        psimple_nlbv(sig, ind, pdoms, np, k, *f);
        psimple_nlbv(sig, ind, pdoms, np, k, *x);
    }
}

/// A projection's type, unfolded: the field at the instance over the
/// parameters and the subject's earlier projections.
pub proof fn proj_ty_unfold(sig: Sig, st: ExprSpec, i: nat, x: ExprSpec)
    ensures ({
        let h = spine_head(st);
        let ps = spine_args(st);
        crate::ti_syntax::proj_ty(sig, st, i, x) == if h is Const && crate::ti_syntax::struct_of(sig, h->Const_0)
            && ps.len() == crate::dom_code::canon_shape(sig, h->Const_0).np && h->Const_1.len() == sig.consts[h->Const_0].lps.len()
            && i < crate::dom_code::canon_shape(sig, h->Const_0).fields[0].len() {
            Some(vsub(sfield(sig, h->Const_0, i, h->Const_1), ps + crate::ti_syntax::projs(x, i)))
        } else {
            None::<ExprSpec>
        }
    }),
{
    reveal(crate::ti_syntax::proj_ty);
}

/// It does not depend on the subject.
pub proof fn proj_ty_indep(sig: Sig, st: ExprSpec, i: nat, x: ExprSpec, y: ExprSpec)
    ensures
        crate::ti_syntax::proj_ty(sig, st, i, x) == crate::ti_syntax::proj_ty(sig, st, i, y),
{
    proj_ty_unfold(sig, st, i, x);
    proj_ty_unfold(sig, st, i, y);
    let h = spine_head(st);
    if h is Const && crate::ti_syntax::struct_of(sig, h->Const_0)
        && spine_args(st).len() == crate::dom_code::canon_shape(sig, h->Const_0).np && h->Const_1.len() == sig.consts[h->Const_0].lps.len()
        && i < crate::dom_code::canon_shape(sig, h->Const_0).fields[0].len() {
        reveal(crate::ti_syntax::struct_of);
        sfield_vsub(sig, h->Const_0, i, h->Const_1, spine_args(st), crate::ti_syntax::projs(x, i), crate::ti_syntax::projs(y, i));
    }
}

/// It commutes with substitution.
pub proof fn proj_ty_psub(sig: Sig, st: ExprSpec, i: nat, x: ExprSpec, t: Sub)
    requires
        spine_head(st) is Const,
    ensures
        crate::ti_syntax::proj_ty(sig, psub(st, t), i, psub(x, t)) == match crate::ti_syntax::proj_ty(sig, st, i, x) {
            Some(ty) => Some(psub(ty, t)),
            None => None::<ExprSpec>,
        },
        crate::ti_syntax::proj_prop(sig, psub(st, t)) == crate::ti_syntax::proj_prop(sig, st),
{
    let (h, ps) = (spine_head(st), spine_args(st));
    crate::ti_subst::psub_spine_const(t, st);
    proj_ty_unfold(sig, st, i, x);
    proj_ty_unfold(sig, psub(st, t), i, psub(x, t));
    reveal(crate::ti_syntax::proj_prop);
    if crate::ti_syntax::proj_ty(sig, st, i, x) is Some {
        reveal(crate::ti_syntax::struct_of);
        let f = sfield(sig, h->Const_0, i, h->Const_1);
        let np = crate::dom_code::canon_shape(sig, h->Const_0).np;
        let xs = ps + crate::ti_syntax::projs(x, i);
        sfield_vsub(sig, h->Const_0, i, h->Const_1, ps, crate::ti_syntax::projs(x, i), crate::ti_syntax::projs(x, i));
        psub_vsub(f, xs, t);
        assert(crate::ti_subst::spsub(xs, t) =~= crate::ti_subst::spsub(ps, t) + crate::ti_syntax::projs(psub(x, t), i));
    }
}

/// The projection redex commutes with substitution.
pub proof fn proj_fire_psub(sig: Sig, m: ExprSpec, t: Sub)
    requires
        crate::ti_syntax::proj_fire(sig, m),
    ensures
        crate::ti_syntax::proj_fire(sig, psub(m, t)),
        crate::ti_syntax::proj_result(sig, psub(m, t)) == psub(crate::ti_syntax::proj_result(sig, m), t),
{
    reveal(crate::ti_syntax::proj_fire);
    reveal(crate::ti_syntax::proj_result);
    let x = *m->Proj_1;
    crate::ti_subst::psub_spine_const(t, x);
}

} // verus!
