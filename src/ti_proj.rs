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
        spine_head(psub(st, t)) == spine_head(st),
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
/// A firing projection's subject is a constant's application.
pub proof fn proj_fire_head(sig: Sig, m: ExprSpec)
    requires
        crate::ti_syntax::proj_fire(sig, m),
    ensures
        m is Proj,
        spine_head(*m->Proj_1) is Const,
{
    reveal(crate::ti_syntax::proj_fire);
}

pub proof fn proj_fire_psub(sig: Sig, m: ExprSpec, t: Sub)
    requires
        crate::ti_syntax::proj_fire(sig, m),
    ensures
        crate::ti_syntax::proj_fire(sig, psub(m, t)),
        crate::ti_syntax::proj_result(sig, psub(m, t)) == psub(crate::ti_syntax::proj_result(sig, m), t),
        spine_head(psub(*m->Proj_1, t)) == spine_head(*m->Proj_1),
{
    reveal(crate::ti_syntax::proj_fire);
    reveal(crate::ti_syntax::proj_result);
    let x = *m->Proj_1;
    crate::ti_subst::psub_spine_const(t, x);
}

/// Swapping two locals commutes with instantiating a telescope.
pub proof fn fswap_vsub(e: ExprSpec, xs: Seq<ExprSpec>, x: nat, y: nat)
    ensures
        crate::swap_model::fswap(vsub(e, xs), x, y) == vsub(crate::swap_model::fswap(e, x, y), crate::swap_model::sswap(xs, x, y)),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let m = (xs.len() - 1) as nat;
        crate::ti_locals::fswap_inst(m, xs[0], e, x, y);
        fswap_vsub(crate::subst_algebra::inst(m, xs[0], e), xs.drop_first(), x, y);
        assert(crate::swap_model::sswap(xs, x, y).drop_first() =~= crate::swap_model::sswap(xs.drop_first(), x, y));
    }
}

/// Closing a local commutes with instantiating a telescope.
pub proof fn fclose_vsub(k: nat, c: nat, e: ExprSpec, xs: Seq<ExprSpec>)
    ensures
        crate::fclose::fclose(k, c, vsub(e, xs)) == vsub(crate::fclose::fclose(k, c + xs.len(), e), crate::fclose::sclose(k, c, xs)),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let m = (xs.len() - 1) as nat;
        let e1 = crate::subst_algebra::inst(m, xs[0], e);
        fclose_vsub(k, c, e1, xs.drop_first());
        crate::fclose::fclose_inst(k, c + m, m, xs[0], e);
        assert(crate::fclose::sclose(k, c, xs).drop_first() =~= crate::fclose::sclose(k, c, xs.drop_first()));
        assert((c + m + 1) as nat == c + xs.len());
    }
}

/// Level substitution commutes with instantiating a telescope.
pub proof fn ls_vsub(e: ExprSpec, xs: Seq<ExprSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        crate::expr_model::subst_expr_levels(vsub(e, xs), ks, vs)
            == vsub(crate::expr_model::subst_expr_levels(e, ks, vs), crate::level_inst::sli(xs, ks, vs)),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let m = (xs.len() - 1) as nat;
        crate::ti_level::ls_inst(m, xs[0], e, ks, vs);
        ls_vsub(crate::subst_algebra::inst(m, xs[0], e), xs.drop_first(), ks, vs);
        assert(crate::level_inst::sli(xs, ks, vs).drop_first() =~= crate::level_inst::sli(xs.drop_first(), ks, vs));
    }
}

/// A telescope's domains have no local when it has none.
pub proof fn binds_fv(bk: BinderKind, ds: Seq<ExprSpec>, b: ExprSpec, j: int)
    requires
        !crate::expr_model::has_fv(crate::rec_canon::binds(bk, ds, b)),
        0 <= j < ds.len(),
    ensures
        !crate::expr_model::has_fv(ds[j]),
    decreases ds.len(),
{
    if j > 0 {
        binds_fv(bk, ds.drop_first(), b, j - 1);
    }
}

/// A structure's field has no local when its constructor's type has none.
pub proof fn sfield_fv(sig: Sig, s: u64, i: nat, us: Seq<LevelSpec>)
    requires
        crate::dom_code::has_canon(sig, s),
        crate::dom_code::canon_shape(sig, s).nmin() == 1,
        i < crate::dom_code::canon_shape(sig, s).fields[0].len(),
        !crate::expr_model::has_fv(sig.consts[crate::dom_code::canon_shape(sig, s).ctors[0]].ty),
    ensures
        !crate::expr_model::has_fv(sfield(sig, s, i, us)),
{
    let sh = crate::dom_code::canon_shape(sig, s);
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
    let t = sig.consts[sh.ctors[0]].ty;
    let nf = sh.fields[0].len();
    binds_fv(BinderKind::Pi, sh.pdoms + sh.fields[0], crate::rec_canon::tbody(t, sh.np + nf), (sh.np + i) as int);
    assert((sh.pdoms + sh.fields[0])[(sh.np + i) as int] == sh.fields[0][i as int]);
    crate::expr_model::subst_expr_levels_has_fv(sh.fields[0][i as int], sig.consts[s].lps, us);
}

/// A structure is one, of the same shape, in a signature with the same
/// constants and inductive tables (its canonical recursor, where it has
/// one, is unique there).
pub proof fn struct_congr(s1: Sig, s2: Sig, s: u64)
    requires
        s1.consts == s2.consts,
        s1.ienv == s2.ienv,
        crate::ti_syntax::struct_of(s1, s),
    ensures
        crate::ti_syntax::struct_of(s2, s),
        crate::dom_code::has_rec(s1, s) ==> crate::dom_code::canon_rec(s1, s) == crate::dom_code::canon_rec(s2, s),
        crate::dom_code::canon_shape(s1, s) == crate::dom_code::canon_shape(s2, s),
{
    reveal(crate::ti_syntax::struct_of);
    assert forall|rid: u64| #[trigger] crate::rec_canon::rec_canon(s1, rid) == crate::rec_canon::rec_canon(s2, rid)
        && crate::rec_canon::rec_ind(s1, rid) == crate::rec_canon::rec_ind(s2, rid) by {
        crate::dom_rec_end::canon_congr(s1, s2, rid);
    }
    crate::dom_code::struct_decl_congr(s1, s2, s);
    if crate::dom_code::has_rec(s1, s) {
        let r1 = crate::dom_code::canon_rec(s1, s);
        crate::dom_code::canon_shape_rec(s1, s);
        assert(crate::rec_canon::rec_canon(s2, r1) && crate::rec_canon::rec_ind(s2, r1) == s);
        assert(crate::dom_code::has_rec(s2, s));
        crate::dom_code::canon_shape_rec(s2, s);
        let r2 = crate::dom_code::canon_rec(s2, s);
        assert(crate::rec_canon::rec_canon(s1, r2) && crate::rec_canon::rec_ind(s1, r2) == s);
        assert(r1 == r2);
    } else {
        assert(!crate::dom_code::has_rec(s2, s)) by {
            if crate::dom_code::has_rec(s2, s) {
                let r2 = choose|rid: u64| crate::rec_canon::rec_canon(s2, rid) && crate::rec_canon::rec_ind(s2, rid) == s;
                assert(crate::rec_canon::rec_canon(s1, r2) && crate::rec_canon::rec_ind(s1, r2) == s);
            }
        }
        crate::dom_code::canon_shape_struct(s1, s);
        crate::dom_code::canon_shape_struct(s2, s);
    }
    assert(crate::dom_code::canon_shape(s1, s) == crate::dom_code::canon_shape(s2, s));
    let sh = crate::dom_code::canon_shape(s1, s);
    assert forall|k: int| 0 <= k < sh.fields[0].len() implies
        crate::rec_canon::psimple(s2, s, sh.pdoms, sh.np, k as nat, #[trigger] sh.fields[0][k]) by {
        crate::dom_rec_end::psimple_congr(s1, s2, s, sh.pdoms, sh.np, k as nat, sh.fields[0][k]);
    }
    assert forall|a1: u64, a2: u64| #![trigger crate::rec_canon::rec_canon(s2, a1), crate::rec_canon::rec_canon(s2, a2)]
        crate::rec_canon::rec_canon(s2, a1) && crate::rec_canon::rec_ind(s2, a1) == s
        && crate::rec_canon::rec_canon(s2, a2) && crate::rec_canon::rec_ind(s2, a2) == s implies a1 == a2 by {
        assert(crate::rec_canon::rec_canon(s1, a1) && crate::rec_canon::rec_canon(s1, a2));
    }
}

/// The projection rules read only the constants and the inductive tables.
pub proof fn proj_sig_congr(s1: Sig, s2: Sig, st: ExprSpec, i: nat, x: ExprSpec, m: ExprSpec)
    requires
        s1.consts == s2.consts,
        s1.ienv == s2.ienv,
    ensures
        crate::ti_syntax::proj_ty(s1, st, i, x) == crate::ti_syntax::proj_ty(s2, st, i, x),
        crate::ti_syntax::proj_prop(s1, st) == crate::ti_syntax::proj_prop(s2, st),
        crate::ti_syntax::proj_fire(s1, m) == crate::ti_syntax::proj_fire(s2, m),
        crate::ti_syntax::proj_fire(s1, m) ==> crate::ti_syntax::proj_result(s1, m) == crate::ti_syntax::proj_result(s2, m),
{
    reveal(crate::ti_syntax::proj_ty);
    reveal(crate::ti_syntax::proj_prop);
    reveal(crate::ti_syntax::proj_fire);
    reveal(crate::ti_syntax::proj_result);
    let h = spine_head(st);
    if h is Const {
        if crate::ti_syntax::struct_of(s1, h->Const_0) {
            struct_congr(s1, s2, h->Const_0);
        } else if crate::ti_syntax::struct_of(s2, h->Const_0) {
            struct_congr(s2, s1, h->Const_0);
        }
    }
    let x0 = *m->Proj_1;
    let hc = spine_head(x0);
    if m is Proj && hc is Const && s1.ienv.ctor_ind.contains_key(hc->Const_0) {
        let ind = s1.ienv.ctor_ind[hc->Const_0];
        if crate::ti_syntax::struct_of(s1, ind) {
            struct_congr(s1, s2, ind);
        } else if crate::ti_syntax::struct_of(s2, ind) {
            struct_congr(s2, s1, ind);
        }
    }
}

/// A projection's type, swapped.
#[verifier::spinoff_prover]
pub proof fn proj_ty_fswap(sig: Sig, st: ExprSpec, i: nat, x: ExprSpec, xx: nat, yy: nat)
    requires
        spine_head(st) is Const,
        crate::ti_locals::sig_fv_free(sig),
    ensures
        crate::ti_syntax::proj_ty(sig, crate::swap_model::fswap(st, xx, yy), i, crate::swap_model::fswap(x, xx, yy))
            == match crate::ti_syntax::proj_ty(sig, st, i, x) {
                Some(ty) => Some(crate::swap_model::fswap(ty, xx, yy)),
                None => None::<ExprSpec>,
            },
        crate::ti_syntax::proj_prop(sig, crate::swap_model::fswap(st, xx, yy)) == crate::ti_syntax::proj_prop(sig, st),
        spine_head(crate::swap_model::fswap(st, xx, yy)) == spine_head(st),
{
    let (h, ps) = (spine_head(st), spine_args(st));
    crate::swap_model::fswap_spine(st, xx, yy);
    proj_ty_unfold(sig, st, i, x);
    proj_ty_unfold(sig, crate::swap_model::fswap(st, xx, yy), i, crate::swap_model::fswap(x, xx, yy));
    reveal(crate::ti_syntax::proj_prop);
    if crate::ti_syntax::proj_ty(sig, st, i, x) is Some {
        crate::ti_syntax::struct_of_basic(sig, h->Const_0);
        let sh = crate::dom_code::canon_shape(sig, h->Const_0);
        let f = sfield(sig, h->Const_0, i, h->Const_1);
        let xs = ps + crate::ti_syntax::projs(x, i);
        crate::dom_ctor_bound::ctor_shape(sig, h->Const_0, 0);
        sfield_fv(sig, h->Const_0, i, h->Const_1);
        crate::kclaims::no_fv_absent(f, xx);
        crate::kclaims::no_fv_absent(f, yy);
        crate::swap_model::fswap_noop(f, xx, yy);
        fswap_vsub(f, xs, xx, yy);
        assert(crate::swap_model::sswap(xs, xx, yy) =~= crate::swap_model::sswap(ps, xx, yy) + crate::ti_syntax::projs(crate::swap_model::fswap(x, xx, yy), i));
    }
}

/// A projection's type, closed.
#[verifier::spinoff_prover]
pub proof fn proj_ty_fclose(sig: Sig, st: ExprSpec, i: nat, x: ExprSpec, k: nat, c: nat)
    requires
        spine_head(st) is Const,
        crate::ti_locals::sig_fv_free(sig),
    ensures
        crate::ti_syntax::proj_ty(sig, crate::fclose::fclose(k, c, st), i, crate::fclose::fclose(k, c, x))
            == match crate::ti_syntax::proj_ty(sig, st, i, x) {
                Some(ty) => Some(crate::fclose::fclose(k, c, ty)),
                None => None::<ExprSpec>,
            },
        crate::ti_syntax::proj_prop(sig, crate::fclose::fclose(k, c, st)) == crate::ti_syntax::proj_prop(sig, st),
        spine_head(crate::fclose::fclose(k, c, st)) == spine_head(st),
{
    let (h, ps) = (spine_head(st), spine_args(st));
    crate::fclose::fclose_spine_const(k, c, st);
    proj_ty_unfold(sig, st, i, x);
    proj_ty_unfold(sig, crate::fclose::fclose(k, c, st), i, crate::fclose::fclose(k, c, x));
    reveal(crate::ti_syntax::proj_prop);
    if crate::ti_syntax::proj_ty(sig, st, i, x) is Some {
        reveal(crate::ti_syntax::struct_of);
        let f = sfield(sig, h->Const_0, i, h->Const_1);
        let xs = ps + crate::ti_syntax::projs(x, i);
        crate::dom_ctor_bound::ctor_shape(sig, h->Const_0, 0);
        sfield_fv(sig, h->Const_0, i, h->Const_1);
        sfield_vsub(sig, h->Const_0, i, h->Const_1, ps, crate::ti_syntax::projs(x, i), crate::ti_syntax::projs(x, i));
        crate::fclose::fclose_closed(k, c + xs.len(), f);
        fclose_vsub(k, c, f, xs);
        assert(crate::fclose::sclose(k, c, xs) =~= crate::fclose::sclose(k, c, ps) + crate::ti_syntax::projs(crate::fclose::fclose(k, c, x), i));
    }
}

/// The projection redex, swapped and closed.
pub proof fn proj_fire_locals(sig: Sig, m: ExprSpec, xx: nat, yy: nat, k: nat, c: nat)
    requires
        crate::ti_syntax::proj_fire(sig, m),
    ensures
        crate::ti_syntax::proj_fire(sig, crate::swap_model::fswap(m, xx, yy)),
        crate::ti_syntax::proj_result(sig, crate::swap_model::fswap(m, xx, yy)) == crate::swap_model::fswap(crate::ti_syntax::proj_result(sig, m), xx, yy),
        crate::ti_syntax::proj_fire(sig, crate::fclose::fclose(k, c, m)),
        crate::ti_syntax::proj_result(sig, crate::fclose::fclose(k, c, m)) == crate::fclose::fclose(k, c, crate::ti_syntax::proj_result(sig, m)),
        spine_head(crate::swap_model::fswap(*m->Proj_1, xx, yy)) == spine_head(*m->Proj_1),
        spine_head(crate::fclose::fclose(k, c, *m->Proj_1)) == spine_head(*m->Proj_1),
{
    reveal(crate::ti_syntax::proj_fire);
    reveal(crate::ti_syntax::proj_result);
    let x = *m->Proj_1;
    crate::swap_model::fswap_spine(x, xx, yy);
    crate::fclose::fclose_spine_const(k, c, x);
}

/// A telescope's body mentions only the telescope's level parameters.
pub proof fn elp_binds_body(bk: BinderKind, ds: Seq<ExprSpec>, b: ExprSpec, us: Seq<u64>)
    requires
        crate::level_inst::elp_in(crate::rec_canon::binds(bk, ds, b), us),
    ensures
        crate::level_inst::elp_in(b, us),
    decreases ds.len(),
{
    if ds.len() > 0 {
        elp_binds_body(bk, ds.drop_first(), b, us);
    }
}

/// A projection's type, at a level instance; a structure that may be a
/// proposition there may be one before.
pub proof fn proj_ty_ls(sig: Sig, st: ExprSpec, i: nat, x: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        spine_head(st) is Const,
        crate::ti_level::sig_lp_ok(sig, ks, vs),
    ensures
        crate::ti_syntax::proj_ty(sig, crate::expr_model::subst_expr_levels(st, ks, vs), i, crate::expr_model::subst_expr_levels(x, ks, vs))
            == match crate::ti_syntax::proj_ty(sig, st, i, x) {
                Some(ty) => Some(crate::expr_model::subst_expr_levels(ty, ks, vs)),
                None => None::<ExprSpec>,
            },
        crate::ti_syntax::proj_ty(sig, st, i, x) is Some ==>
            (crate::ti_syntax::proj_prop(sig, crate::expr_model::subst_expr_levels(st, ks, vs)) ==> crate::ti_syntax::proj_prop(sig, st)),
        spine_head(crate::expr_model::subst_expr_levels(st, ks, vs))->Const_0 == spine_head(st)->Const_0,
{
    use crate::expr_model::subst_expr_levels;
    let (h, ps) = (spine_head(st), spine_args(st));
    let st2 = subst_expr_levels(st, ks, vs);
    crate::level_inst::li_spine_const(st, ks, vs);
    proj_ty_unfold(sig, st, i, x);
    proj_ty_unfold(sig, st2, i, subst_expr_levels(x, ks, vs));
    if crate::ti_syntax::proj_ty(sig, st, i, x) is Some {
        reveal(crate::ti_syntax::struct_of);
        let (s, us) = (h->Const_0, h->Const_1);
        let us2 = crate::level_model::subst_levels_spec(us, ks, vs);
        let sh = crate::dom_code::canon_shape(sig, s);
        let lps = sig.consts[s].lps;
        crate::dom_ctor_bound::ctor_shape(sig, s, 0);
        let c = sh.ctors[0];
        let tc = sig.consts[c].ty;
        let nf = sh.fields[0].len();
        // the field at the instantiated instance
        assert(crate::level_inst::elp_in(tc, lps));
        crate::ti_level::elp_binds(BinderKind::Pi, sh.pdoms + sh.fields[0], crate::rec_canon::tbody(tc, sh.np + nf), lps);
        assert((sh.pdoms + sh.fields[0])[(sh.np + i) as int] == sh.fields[0][i as int]);
        crate::level_inst::expr_compose(sh.fields[0][i as int], lps, us, ks, vs);
        let f = sfield(sig, s, i, us);
        assert(subst_expr_levels(f, ks, vs) == sfield(sig, s, i, us2));
        let xs = ps + crate::ti_syntax::projs(x, i);
        ls_vsub(f, xs, ks, vs);
        assert(crate::level_inst::sli(xs, ks, vs) =~= crate::level_inst::sli(ps, ks, vs) + crate::ti_syntax::projs(subst_expr_levels(x, ks, vs), i));
        // the sort
        reveal(crate::ti_syntax::proj_prop);
        let ts = sig.consts[s].ty;
        crate::dom_ctor_bound::ctor_shape_ind(sig, s);
        crate::dom_rec_shape::tarity_binds(sh.pdoms + sh.idoms, crate::rec_canon::tbody(ts, sh.np + sh.ni));
        assert(crate::level_inst::elp_in(ts, lps));
        elp_binds_body(BinderKind::Pi, sh.pdoms + sh.idoms, crate::rec_canon::tbody(ts, sh.np + sh.ni), lps);
        let l0 = crate::rec_canon::tbody(ts, crate::rec_canon::tarity(ts))->Sort_0;
        assert(crate::level_inst::lp_in(l0, lps));
        crate::level_inst::lvl_compose(l0, lps, us, ks, vs);
        let l1 = crate::level_model::subst_level_spec(l0, lps, us);
        if crate::ti_syntax::proj_prop(sig, st2) {
            let rho = choose|rho: Map<nat, nat>| !(crate::level_model::interp(crate::level_model::subst_level_spec(l0, lps, us2), rho) > 0);
            crate::level_model::subst_level_spec_interp(l1, ks, vs, rho);
            let rho2 = crate::level_model::subst_env(rho, ks, vs);
            assert(!(crate::level_model::interp(l1, rho2) > 0));
        }
    }
}

/// The projection redex at a level instance.
pub proof fn proj_fire_ls(sig: Sig, m: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        crate::ti_syntax::proj_fire(sig, m),
    ensures
        crate::ti_syntax::proj_fire(sig, crate::expr_model::subst_expr_levels(m, ks, vs)),
        crate::ti_syntax::proj_result(sig, crate::expr_model::subst_expr_levels(m, ks, vs))
            == crate::expr_model::subst_expr_levels(crate::ti_syntax::proj_result(sig, m), ks, vs),
        spine_head(crate::expr_model::subst_expr_levels(*m->Proj_1, ks, vs))->Const_0 == spine_head(*m->Proj_1)->Const_0,
{
    reveal(crate::ti_syntax::proj_fire);
    reveal(crate::ti_syntax::proj_result);
    crate::level_inst::li_spine_const(*m->Proj_1, ks, vs);
}

/// The projected field's declared type, unfolded at a firing projection.
proof fn proj_fty_facts(sig: Sig, m: ExprSpec)
    requires
        crate::ti_syntax::proj_fire(sig, m),
    ensures ({
        let x = *m->Proj_1;
        let h = spine_head(x);
        let s = sig.ienv.ctor_ind[h->Const_0];
        let i = m->Proj_0 as nat;
        let np = crate::dom_code::canon_shape(sig, s).np;
        let a = spine_args(x).subrange(0, (np + i) as int);
        &&& m is Proj
        &&& h is Const && crate::ti_syntax::struct_of(sig, s)
        &&& h->Const_0 == crate::dom_code::canon_shape(sig, s).ctors[0]
        &&& i < crate::dom_code::canon_shape(sig, s).fields[0].len()
        &&& spine_args(x).len() == np + crate::dom_code::canon_shape(sig, s).fields[0].len()
        &&& crate::ti_syntax::proj_fty(sig, m) == vsub(sfield(sig, s, i, h->Const_1), a)
        &&& crate::expr_model::nlbv(sfield(sig, s, i, h->Const_1)) <= a.len()
    }),
{
    reveal(crate::ti_syntax::proj_fire);
    reveal(crate::ti_syntax::proj_fty);
    let x = *m->Proj_1;
    let h = spine_head(x);
    let s = sig.ienv.ctor_ind[h->Const_0];
    let i = m->Proj_0 as nat;
    let np = crate::dom_code::canon_shape(sig, s).np;
    let a = spine_args(x).subrange(0, (np + i) as int);
    reveal(crate::ti_syntax::struct_of);
    sfield_vsub(sig, s, i, h->Const_1, a.subrange(0, np as int), a.subrange(np as int, a.len() as int), a.subrange(np as int, a.len() as int));
}

/// It commutes with substitution.
pub proof fn proj_fty_psub(sig: Sig, m: ExprSpec, t: Sub)
    requires
        crate::ti_syntax::proj_fire(sig, m),
    ensures
        crate::ti_syntax::proj_fty(sig, psub(m, t)) == psub(crate::ti_syntax::proj_fty(sig, m), t),
{
    proj_fty_facts(sig, m);
    proj_fire_psub(sig, m, t);
    proj_fty_facts(sig, psub(m, t));
    let x = *m->Proj_1;
    crate::ti_subst::psub_spine_const(t, x);
    assert(psub(m, t) == ExprSpec::Proj(m->Proj_0, Box::new(psub(x, t))));
    proj_fty_facts(sig, psub(m, t));
    let h = spine_head(x);
    let s = sig.ienv.ctor_ind[h->Const_0];
    let np = crate::dom_code::canon_shape(sig, s).np;
    let a = spine_args(x).subrange(0, (np + m->Proj_0 as nat) as int);
    psub_vsub(sfield(sig, s, m->Proj_0 as nat, h->Const_1), a, t);
    assert(crate::ti_subst::spsub(a, t) =~= spine_args(psub(x, t)).subrange(0, (np + m->Proj_0 as nat) as int));
}

/// It commutes with swapping and closing locals.
pub proof fn proj_fty_locals(sig: Sig, m: ExprSpec, xx: nat, yy: nat, k: nat, c: nat)
    requires
        crate::ti_syntax::proj_fire(sig, m),
        crate::ti_locals::sig_fv_free(sig),
    ensures
        crate::ti_syntax::proj_fty(sig, crate::swap_model::fswap(m, xx, yy)) == crate::swap_model::fswap(crate::ti_syntax::proj_fty(sig, m), xx, yy),
        crate::ti_syntax::proj_fty(sig, crate::fclose::fclose(k, c, m)) == crate::fclose::fclose(k, c, crate::ti_syntax::proj_fty(sig, m)),
{
    proj_fty_swap(sig, m, xx, yy);
    proj_fty_close(sig, m, k, c);
}

#[verifier::spinoff_prover]
proof fn proj_fty_swap(sig: Sig, m: ExprSpec, xx: nat, yy: nat)
    requires
        crate::ti_syntax::proj_fire(sig, m),
        crate::ti_locals::sig_fv_free(sig),
    ensures
        crate::ti_syntax::proj_fty(sig, crate::swap_model::fswap(m, xx, yy)) == crate::swap_model::fswap(crate::ti_syntax::proj_fty(sig, m), xx, yy),
{
    proj_fty_facts(sig, m);
    proj_fire_locals(sig, m, xx, yy, 0, 0);
    let x = *m->Proj_1;
    crate::swap_model::fswap_spine(x, xx, yy);
    assert(crate::swap_model::fswap(m, xx, yy) == ExprSpec::Proj(m->Proj_0, Box::new(crate::swap_model::fswap(x, xx, yy))));
    proj_fty_facts(sig, crate::swap_model::fswap(m, xx, yy));
    let h = spine_head(x);
    let s = sig.ienv.ctor_ind[h->Const_0];
    let i = m->Proj_0 as nat;
    let np = crate::dom_code::canon_shape(sig, s).np;
    let a = spine_args(x).subrange(0, (np + i) as int);
    let f = sfield(sig, s, i, h->Const_1);
    reveal(crate::ti_syntax::struct_of);
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
    sfield_fv(sig, s, i, h->Const_1);
    crate::kclaims::no_fv_absent(f, xx);
    crate::kclaims::no_fv_absent(f, yy);
    crate::swap_model::fswap_noop(f, xx, yy);
    fswap_vsub(f, a, xx, yy);
    assert(crate::swap_model::sswap(a, xx, yy) =~= spine_args(crate::swap_model::fswap(x, xx, yy)).subrange(0, (np + i) as int));
}

#[verifier::spinoff_prover]
proof fn proj_fty_close(sig: Sig, m: ExprSpec, k: nat, c: nat)
    requires
        crate::ti_syntax::proj_fire(sig, m),
        crate::ti_locals::sig_fv_free(sig),
    ensures
        crate::ti_syntax::proj_fty(sig, crate::fclose::fclose(k, c, m)) == crate::fclose::fclose(k, c, crate::ti_syntax::proj_fty(sig, m)),
{
    proj_fty_facts(sig, m);
    proj_fire_locals(sig, m, 0, 0, k, c);
    let x = *m->Proj_1;
    crate::fclose::fclose_spine_const(k, c, x);
    assert(crate::fclose::fclose(k, c, m) == ExprSpec::Proj(m->Proj_0, Box::new(crate::fclose::fclose(k, c, x))));
    proj_fty_facts(sig, crate::fclose::fclose(k, c, m));
    let h = spine_head(x);
    let s = sig.ienv.ctor_ind[h->Const_0];
    let i = m->Proj_0 as nat;
    let np = crate::dom_code::canon_shape(sig, s).np;
    let a = spine_args(x).subrange(0, (np + i) as int);
    let f = sfield(sig, s, i, h->Const_1);
    reveal(crate::ti_syntax::struct_of);
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
    sfield_fv(sig, s, i, h->Const_1);
    crate::fclose::fclose_closed(k, c + a.len(), f);
    fclose_vsub(k, c, f, a);
    assert(crate::fclose::sclose(k, c, a) =~= spine_args(crate::fclose::fclose(k, c, x)).subrange(0, (np + i) as int));
}

/// It commutes with level instantiation.
pub proof fn proj_fty_ls(sig: Sig, m: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        crate::ti_syntax::proj_fire(sig, m),
        crate::ti_level::sig_lp_ok(sig, ks, vs),
    ensures
        crate::ti_syntax::proj_fty(sig, crate::expr_model::subst_expr_levels(m, ks, vs))
            == crate::expr_model::subst_expr_levels(crate::ti_syntax::proj_fty(sig, m), ks, vs),
{
    use crate::expr_model::subst_expr_levels;
    proj_fty_facts(sig, m);
    proj_fire_ls(sig, m, ks, vs);
    proj_fty_facts(sig, subst_expr_levels(m, ks, vs));
    let x = *m->Proj_1;
    let h = spine_head(x);
    let s = sig.ienv.ctor_ind[h->Const_0];
    let i = m->Proj_0 as nat;
    let sh = crate::dom_code::canon_shape(sig, s);
    let np = sh.np;
    let a = spine_args(x).subrange(0, (np + i) as int);
    crate::level_inst::li_spine_const(x, ks, vs);
    reveal(crate::ti_syntax::struct_of);
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
    let lps = sig.consts[s].lps;
    let tc = sig.consts[sh.ctors[0]].ty;
    let nf = sh.fields[0].len();
    assert(crate::level_inst::elp_in(tc, lps));
    crate::ti_level::elp_binds(BinderKind::Pi, sh.pdoms + sh.fields[0], crate::rec_canon::tbody(tc, sh.np + nf), lps);
    assert((sh.pdoms + sh.fields[0])[(sh.np + i) as int] == sh.fields[0][i as int]);
    reveal(crate::ti_syntax::proj_fire);
    crate::level_inst::expr_compose(sh.fields[0][i as int], lps, h->Const_1, ks, vs);
    let f = sfield(sig, s, i, h->Const_1);
    ls_vsub(f, a, ks, vs);
    assert(crate::level_inst::sli(a, ks, vs) =~= spine_args(subst_expr_levels(x, ks, vs)).subrange(0, (np + i) as int));
}

/// It reads only the constants and the inductive tables.
pub proof fn proj_fty_congr(s1: Sig, s2: Sig, m: ExprSpec)
    requires
        s1.consts == s2.consts,
        s1.ienv == s2.ienv,
        crate::ti_syntax::proj_fire(s1, m),
    ensures
        crate::ti_syntax::proj_fty(s1, m) == crate::ti_syntax::proj_fty(s2, m),
{
    reveal(crate::ti_syntax::proj_fire);
    reveal(crate::ti_syntax::proj_fty);
    let h = spine_head(*m->Proj_1);
    struct_congr(s1, s2, s1.ienv.ctor_ind[h->Const_0]);
}

/// Structure applications read only the constants and the inductive
/// tables.
pub proof fn seta_sig_congr(s1: Sig, s2: Sig, t: ExprSpec)
    requires
        s1.consts == s2.consts,
        s1.ienv == s2.ienv,
    ensures
        crate::ti_syntax::struct_ty(s1, t) == crate::ti_syntax::struct_ty(s2, t),
        crate::ti_syntax::struct_ty(s1, t) ==> crate::ti_syntax::struct_nf(s1, t) == crate::ti_syntax::struct_nf(s2, t)
            && crate::dom_code::smash(s1, spine_head(t)->Const_0) == crate::dom_code::smash(s2, spine_head(t)->Const_0),
{
    let h = spine_head(t);
    if h is Const {
        if crate::ti_syntax::struct_of(s1, h->Const_0) {
            struct_congr(s1, s2, h->Const_0);
        } else if crate::ti_syntax::struct_of(s2, h->Const_0) {
            struct_congr(s2, s1, h->Const_0);
        }
    }
}

/// Swapping locals keeps a structure application one, of the same
/// structure.
pub proof fn struct_ty_fswap(sig: Sig, t: ExprSpec, x: nat, y: nat)
    requires
        crate::ti_syntax::struct_ty(sig, t),
    ensures
        crate::ti_syntax::struct_ty(sig, crate::swap_model::fswap(t, x, y)),
        spine_head(crate::swap_model::fswap(t, x, y)) == spine_head(t),
        crate::ti_syntax::struct_nf(sig, crate::swap_model::fswap(t, x, y)) == crate::ti_syntax::struct_nf(sig, t),
{
    crate::swap_model::fswap_spine(t, x, y);
}

/// Substitution keeps a structure application one, of the same structure.
pub proof fn struct_ty_psub(sig: Sig, t: ExprSpec, q: Sub)
    requires
        crate::ti_syntax::struct_ty(sig, t),
    ensures
        crate::ti_syntax::struct_ty(sig, psub(t, q)),
        spine_head(psub(t, q)) == spine_head(t),
        crate::ti_syntax::struct_nf(sig, psub(t, q)) == crate::ti_syntax::struct_nf(sig, t),
{
    crate::ti_subst::psub_spine_const(q, t);
}

/// Closing a local keeps a structure application one, of the same
/// structure.
pub proof fn struct_ty_fclose(sig: Sig, t: ExprSpec, k: nat, c: nat)
    requires
        crate::ti_syntax::struct_ty(sig, t),
    ensures
        crate::ti_syntax::struct_ty(sig, crate::fclose::fclose(k, c, t)),
        spine_head(crate::fclose::fclose(k, c, t)) == spine_head(t),
        crate::ti_syntax::struct_nf(sig, crate::fclose::fclose(k, c, t)) == crate::ti_syntax::struct_nf(sig, t),
{
    crate::fclose::fclose_spine_const(k, c, t);
}

/// A level instance keeps a structure application one, of the same
/// structure.
pub proof fn struct_ty_ls(sig: Sig, t: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        crate::ti_syntax::struct_ty(sig, t),
    ensures
        crate::ti_syntax::struct_ty(sig, crate::expr_model::subst_expr_levels(t, ks, vs)),
        spine_head(crate::expr_model::subst_expr_levels(t, ks, vs))->Const_0 == spine_head(t)->Const_0,
        crate::ti_syntax::struct_nf(sig, crate::expr_model::subst_expr_levels(t, ks, vs)) == crate::ti_syntax::struct_nf(sig, t),
{
    crate::level_inst::li_spine_const(t, ks, vs);
}

} // verus!
