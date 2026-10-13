//! VALIDITY for the typed judgment (typed target, stage 3): the type of a
//! derivable conversion is a type. Every rule carries its presuppositions,
//! so each case reads the type's typing off a premise (or builds it from
//! premises: a Pi from its parts, an instance by substitution).
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::*;
#[cfg(verus_only)]
use crate::ti_meta::*;
#[cfg(verus_only)]
use crate::ti_sub::*;
#[cfg(verus_only)]
use crate::ti_chain::{wf_vars, inst_conv};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// THE TYPE OF A CONVERSION IS A TYPE.
pub proof fn d_ty(sig: Sig, d: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
    ensures
        tconvd(sig, concl(d)->Eq_0, concl(d)->Eq_3, concl(d)->Eq_3),
    decreases d,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let t = j->Eq_3;
    match rule {
        Rule::Var(_) => {
            wf_vars(sig, ps[0]);
        },
        Rule::Univ(l, _) => {
            assert(crate::conv_cr::lev_eq(succ(l), succ(l)));
            let u = d_univ(sig, ps[0], succ(l), succ(l));
            mk_t(sig, u, succ(succ(l)));
        },
        Rule::PiCong(l1, l2) => {
            let w = d_wf(sig, d);
            assert(crate::conv_cr::lev_eq(imax(l1, l2), imax(l1, l2)));
            let u = d_univ(sig, w, imax(l1, l2), imax(l1, l2));
            mk_t(sig, u, succ(imax(l1, l2)));
        },
        Rule::Sym | Rule::Trans => {
            d_ty(sig, ps[0]);
        },
        Rule::Conv(l) => {
            let r = d_right(sig, ps[1]);
            mk_t(sig, r, l);
        },
        Rule::Irr(l) => {
            mk_t(sig, ps[0], l);
        },
        Rule::ConstAx(l) | Rule::ConstDef(l) | Rule::Local(l) | Rule::Delta(l) | Rule::LitTy(l) => {
            let r = d_left(sig, ps[1]);
            mk_t(sig, r, l);
        },
        Rule::LamCong(l1, l2) => {
            let a = *t->Bind_1;
            let dl0 = d_left(sig, ps[0]);
            mk_d(sig, dl0);
            mk_d(sig, ps[1]);
            crate::dom_adeq_syn::d_pi_self(sig, g, a, *t->Bind_2, l1, l2);
        },
        Rule::Eta(l, l2) => {
            mk_d(sig, ps[0]);
            mk_d(sig, ps[4]);
            crate::dom_adeq_syn::d_pi_self(sig, g, *t->Bind_1, *t->Bind_2, l, l2);
        },
        Rule::AppCong(l1, l2) => {
            let pt = concl(ps[0])->Eq_3;
            let (a, b) = (*pt->Bind_1, *pt->Bind_2);
            let x = *j->Eq_1->App_1;
            let dx = d_left(sig, ps[1]);
            mk_d(sig, dx);
            mk_d(sig, ps[3]);
            inst_conv(sig, g, a, b, l2, x, x);
            let r = get(sig, eq(g, t, t, sort(l2)));
            mk_t(sig, r, l2);
        },
        Rule::Zeta(_) => {
            d_ty(sig, ps[2]);
        },
        Rule::Iota(_) | Rule::RedG(_) => {
            d_ty(sig, ps[0]);
        },
        Rule::RecEta(_) => {
            reveal(crate::ti_syntax::rec_eta_ok);
            d_ty(sig, ps[0]);
        },
        Rule::ProjG(l) => {
            reveal(crate::ti_syntax::proj_g_ok);
            mk_d(sig, ps[1]);
            let r = get(sig, eq(g, t, t, sort(l)));
            mk_t(sig, r, l);
        },
        Rule::ProjCong(l) => {
            reveal(crate::ti_syntax::proj_cong_ok);
            mk_d(sig, ps[1]);
            let r = get(sig, eq(g, t, t, sort(l)));
            mk_t(sig, r, l);
        },
        Rule::ProjIota(l) => {
            reveal(crate::ti_syntax::proj_iota_ok);
            mk_d(sig, ps[3]);
            let r = get(sig, eq(g, t, t, sort(l)));
            mk_t(sig, r, l);
        },
        Rule::StructEta(l) => {
            reveal(crate::ti_syntax::struct_eta_ok);
            mk_d(sig, ps[2]);
            let r = get(sig, eq(g, t, t, sort(l)));
            mk_t(sig, r, l);
        },
        Rule::Beta(l1, l2) => {
            let a = concl(ps[0])->Eq_1;
            let b = concl(ps[1])->Eq_3;
            let x = concl(ps[2])->Eq_1;
            mk_d(sig, ps[2]);
            mk_d(sig, ps[3]);
            inst_conv(sig, g, a, b, l2, x, x);
            let r = get(sig, eq(g, t, t, sort(l2)));
            mk_t(sig, r, l2);
        },
        _ => {},
    }
}

/// `sig2` extends `sig`: more constants and more locals, the old ones
/// unchanged (no old constant becomes a constructor), and every definition of `sig2` well ranked in it -- or the
/// same constants and ranks (`ti_strip::strip_below`).
pub open spec fn sig_ext(sig: Sig, sig2: Sig) -> bool {
    &&& forall|c: u64| #[trigger] sig.consts.contains_key(c) ==> sig2.consts.contains_key(c) && sig2.consts[c] == sig.consts[c]
    &&& forall|k: nat| #[trigger] sig.locals.contains_key(k) ==> sig2.locals.contains_key(k) && sig2.locals[k] == sig.locals[k]
    &&& (forall|c: u64, ls: Seq<LevelSpec>| #[trigger] is_def(sig2, c, ls) ==> def_ok(sig2, c, ls))
        || (sig2.consts == sig.consts && sig2.rank == sig.rank)
    &&& sig.ienv.sub(sig2.ienv)
    &&& sig.ienv.full == sig2.ienv.full
    &&& (!sig2.ienv.full ==> iota_ok(sig2))
    &&& forall|k: u64| #[trigger] sig.ienv.ctor_ind.contains_key(k) ==> sig2.ienv.ctor_ind.contains_key(k) && sig2.ienv.ctor_ind[k] == sig.ienv.ctor_ind[k]
    &&& forall|k: u64| #[trigger] sig.ienv.struct_ctor.contains_key(k) ==> sig2.ienv.struct_ctor.contains_key(k) && sig2.ienv.struct_ctor[k] == sig.ienv.struct_ctor[k]
    &&& forall|k: u64| #[trigger] sig.ienv.ctor_nf.contains_key(k) ==> sig2.ienv.ctor_nf.contains_key(k) && sig2.ienv.ctor_nf[k] == sig.ienv.ctor_nf[k]
    &&& forall|k: u64| #![trigger sig2.ienv.ctor_ind.contains_key(k), sig.consts.contains_key(k)]
        sig.consts.contains_key(k) && sig2.ienv.ctor_ind.contains_key(k) ==> sig.ienv.ctor_ind.contains_key(k)
}

/// A canonical recursor stays one in an extension, with the same
/// inductive, shape and interpretation.
pub proof fn canon_grow(sig: Sig, sig2: Sig, r: u64)
    requires
        sig_ext(sig, sig2),
        !sig.ienv.full,
        crate::rec_canon::rec_canon(sig, r),
    ensures
        crate::rec_canon::rec_canon(sig2, r),
        crate::dom_rec_ty::rec_scope_g(sig2, r),
        crate::dom_rec_end::rec_frag(sig2, r),
        sig2.ienv.recs[r] == sig.ienv.recs[r],
        crate::rec_canon::rec_ind(sig2, r) == crate::rec_canon::rec_ind(sig, r),
        crate::dom_rec_ty::rshape(sig2, r) == crate::dom_rec_ty::rshape(sig, r),
        crate::rec_canon::elim_level(sig2, r, crate::rec_canon::rec_ind(sig2, r)) == crate::rec_canon::elim_level(sig, r, crate::rec_canon::rec_ind(sig, r)),
        crate::dom_rec_end::rec_interp(sig2, r) == crate::dom_rec_end::rec_interp(sig, r),
{
    let rd = sig.ienv.recs[r];
    assert(sig2.ienv.recs[r] == rd);
    assert(sig2.consts[r] == sig.consts[r]);
    let ind = crate::rec_canon::rec_ind(sig, r);
    assert(crate::rec_canon::rec_ind(sig2, r) == ind);
    assert(sig2.consts[ind] == sig.consts[ind]);
    crate::ti_syntax::frag_of(sig2, r);
    let sh = crate::rec_canon::shape_of(sig, rd, ind);
    let sh2 = crate::rec_canon::shape_of(sig2, rd, ind);
    assert forall|j: int| 0 <= j < sh.nmin() implies sig2.consts[#[trigger] sh.ctors[j]] == sig.consts[sh.ctors[j]] by {
        assert(sig.consts.contains_key(sh.ctors[j]));
    }
    assert(sh2.ctors =~= sh.ctors);
    assert(sh2.fields =~= sh.fields);
    assert(sh2.tss =~= sh.tss);
    assert(sh2 == sh);
    reveal(crate::dom_rec_end::rec_interp);
    reveal(crate::dom_rec_end::rec_large);
}

/// A canonical recursor is no type former: its type ends in the motive
/// applied to the major premise, not in a sort.
pub proof fn rec_no_former(sig: Sig, j: u64)
    requires
        crate::rec_canon::rec_canon(sig, j),
    ensures
        !(crate::rec_canon::tbody(sig.consts[j].ty, crate::rec_canon::tarity(sig.consts[j].ty)) is Sort),
{
    let rd = sig.ienv.recs[j];
    let ind = crate::rec_canon::rec_ind(sig, j);
    let sh = crate::rec_canon::shape_of(sig, rd, ind);
    let lm = crate::rec_canon::elim_level(sig, j, ind);
    let (nmin, ni) = (sh.nmin(), sh.ni);
    let idx = Seq::new(ni, |k: int| crate::subst_algebra::lift(1 + nmin, k as nat, sh.idoms[k]));
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(1 + nmin + ni, sh.np) + crate::rec_canon::vars(0, ni));
    let args = crate::rec_canon::vars(1, ni).push(ExprSpec::Var(0));
    let body = crate::beta_model::spine_app(ExprSpec::Var(nmin + ni + 1), args);
    let ds = sh.head_doms(lm) + idx + seq![major];
    assert(sig.consts[j].ty == crate::rec_canon::binds(BinderKind::Pi, ds, body));
    assert(body is App);
    crate::dom_rec_shape::tarity_binds(ds, body);
    crate::dom_iota::tbody_binds(ds, body);
}

/// A former applied over the parameters is headed by another former.
pub proof fn psapp_head(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec)
    requires
        crate::rec_canon::psapp(sig, ind, pdoms, np, k, e),
    ensures
        crate::beta_model::spine_head(e) is Const,
        crate::rec_canon::other_former(sig, ind, crate::beta_model::spine_head(e)->Const_0),
        crate::beta_model::spine_head(e)->Const_1.len() == sig.consts[crate::beta_model::spine_head(e)->Const_0].lps.len(),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        psapp_head(sig, ind, pdoms, np, k, *f);
    }
}

/// A simple type over the parameters stays one in an extension: its
/// formers keep their declarations, and none becomes a recursor (every
/// recursor of the extension is canonical, so no former).
pub proof fn psimple_grow(sig: Sig, sig2: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec)
    requires
        sig_ext(sig, sig2),
        !sig.ienv.full,
    ensures
        crate::rec_canon::psimple(sig, ind, pdoms, np, k, e) ==> crate::rec_canon::psimple(sig2, ind, pdoms, np, k, e),
        crate::rec_canon::psapp(sig, ind, pdoms, np, k, e) ==> crate::rec_canon::psapp(sig2, ind, pdoms, np, k, e),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            psimple_grow(sig, sig2, ind, pdoms, np, k, *f);
            psimple_grow(sig, sig2, ind, pdoms, np, k, *x);
        },
        ExprSpec::Bind(crate::expr_model::BinderKind::Pi, a, b) => {
            psimple_grow(sig, sig2, ind, pdoms, np, k, *a);
            psimple_grow(sig, sig2, ind, pdoms, np, k + 1, *b);
        },
        ExprSpec::Const(j, _) => {
            if crate::rec_canon::other_former(sig, ind, j) {
                assert(sig2.consts[j] == sig.consts[j]);
                assert(!sig2.ienv.ctor_ind.contains_key(j));
                if sig2.ienv.recs.contains_key(j) {
                    frag_of(sig2, j);
                    rec_no_former(sig2, j);
                }
            }
        },
        _ => {},
    }
    if crate::rec_canon::psimple(sig, ind, pdoms, np, k, e) && !crate::rec_canon::pvar_field(pdoms, np, k, e)
        && !crate::rec_canon::parrow(sig, ind, pdoms, np, k, e) {
        psapp_head(sig, ind, pdoms, np, k, e);
        let j = crate::beta_model::spine_head(e)->Const_0;
        assert(sig2.consts[j] == sig.consts[j]);
    }
}

/// A field of both kinds is impossible: a simple type over the parameters
/// is no direct occurrence.
pub proof fn psimple_not_direct(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, us: Seq<LevelSpec>, np: nat, ni: nat, k: nat, e: ExprSpec)
    requires
        crate::rec_canon::psimple(sig, ind, pdoms, np, k, e),
    ensures
        !crate::rec_canon::direct_occ(e, ind, us, np, ni, k),
{
    if !crate::rec_canon::pvar_field(pdoms, np, k, e) && !crate::rec_canon::parrow(sig, ind, pdoms, np, k, e) {
        psapp_head(sig, ind, pdoms, np, k, e);
    }
}

/// Whether an inductive with a canonical recursor is a structure, and its
/// canonical recursor and shape, survive an extension.
pub proof fn struct_iff(sig: Sig, sig2: Sig, s: u64, r: u64)
    requires
        sig_ext(sig, sig2),
        !sig.ienv.full,
        crate::rec_canon::rec_canon(sig, r),
        crate::rec_canon::rec_ind(sig, r) == s,
    ensures
        crate::ti_syntax::struct_of(sig, s) == crate::ti_syntax::struct_of(sig2, s),
        crate::dom_code::canon_rec(sig, s) == r,
        crate::dom_code::canon_rec(sig2, s) == r,
        crate::dom_code::canon_shape(sig, s) == crate::dom_code::canon_shape(sig2, s),
        crate::dom_code::smash(sig, s) == crate::dom_code::smash(sig2, s),
        sig.consts.contains_key(s),
        sig2.consts[s] == sig.consts[s],
{
    reveal(crate::ti_syntax::struct_of);
    canon_grow(sig, sig2, r);
    assert(sig.consts.contains_key(s));
    assert forall|r2: u64| #[trigger] crate::rec_canon::rec_canon(sig, r2) && crate::rec_canon::rec_ind(sig, r2) == s implies r2 == r by {
        canon_grow(sig, sig2, r2);
    }
    assert(crate::dom_code::has_rec(sig, s));
    assert(crate::dom_code::has_rec(sig2, s));
    crate::dom_code::canon_shape_rec(sig, s);
    crate::dom_code::canon_shape_rec(sig2, s);
    let c1 = crate::dom_code::canon_rec(sig, s);
    let c2 = crate::dom_code::canon_rec(sig2, s);
    assert(c1 == r);
    assert(c2 == r);
    let sh = crate::dom_code::canon_shape(sig, s);
    assert(sh == crate::dom_code::canon_shape(sig2, s));
    // the fields' kinds: simple in one signature iff in the other
    if sh.nmin() == 1 {
        assert forall|k: int| 0 <= k < sh.fields[0].len() implies
            crate::rec_canon::psimple(sig, s, sh.pdoms, sh.np, k as nat, #[trigger] sh.fields[0][k])
            == crate::rec_canon::psimple(sig2, s, sh.pdoms, sh.np, k as nat, sh.fields[0][k]) by {
            let f = sh.fields[0][k];
            psimple_grow(sig, sig2, s, sh.pdoms, sh.np, k as nat, f);
            if crate::rec_canon::psimple(sig2, s, sh.pdoms, sh.np, k as nat, f) {
                reveal(crate::rec_canon::field_kind);
                assert(sh.ctors[0] == sh.ctors[0]);
                assert(crate::rec_canon::field_kind(sig, s, sh.pdoms, sh.us(), sh.np, sh.ni, k as nat, sh.fields[0][k]));
                psimple_not_direct(sig2, s, sh.pdoms, sh.us(), sh.np, sh.ni, k as nat, f);
            }
        }
    }
}

/// Rule ProjIota's parameter premises are the same in an extension: the
/// constructor's structure keeps its shape and declaration.
pub proof fn proj_pjs_ext(sig: Sig, sig2: Sig, g: Ctx, m: ExprSpec)
    requires
        sig_ext(sig, sig2),
        !sig.ienv.full,
        crate::ti_syntax::proj_fire(sig, m),
    ensures
        crate::ti_syntax::proj_pjs(sig2, g, m) == crate::ti_syntax::proj_pjs(sig, g, m),
{
    reveal(crate::ti_syntax::proj_fire);
    reveal(crate::ti_syntax::proj_pjs);
    let h = crate::beta_model::spine_head(*m->Proj_1);
    let s = sig.ienv.ctor_ind[h->Const_0];
    assert(sig2.ienv.ctor_ind[h->Const_0] == s);
    struct_grow(sig, sig2, s);
}

/// A structure stays one in an extension, with the same shape.
pub proof fn struct_grow(sig: Sig, sig2: Sig, s: u64)
    requires
        sig_ext(sig, sig2),
        !sig.ienv.full,
        crate::ti_syntax::struct_of(sig, s),
    ensures
        crate::ti_syntax::struct_of(sig2, s),
        crate::dom_code::canon_shape(sig, s) == crate::dom_code::canon_shape(sig2, s),
        crate::dom_code::smash(sig, s) == crate::dom_code::smash(sig2, s),
        sig.consts.contains_key(s),
        sig2.consts[s] == sig.consts[s],
{
    reveal(crate::ti_syntax::struct_of);
    if crate::dom_code::has_rec(sig, s) {
        crate::dom_code::canon_shape_rec(sig, s);
        let r = crate::dom_code::canon_rec(sig, s);
        struct_iff(sig, sig2, s, r);
    } else {
        // a structure from its declaration, kept; a recursor of it in the
        // extension is of the same shape and the only one (`rec_scope_g`)
        crate::dom_code::canon_shape_struct(sig, s);
        crate::dom_code::struct_decl_grow(sig, sig2, s);
        assert(sig.consts.contains_key(s)) by {
            reveal(crate::dom_code::struct_decl);
        }
        if crate::dom_code::has_rec(sig2, s) {
            crate::dom_code::canon_shape_rec(sig2, s);
            let r2 = crate::dom_code::canon_rec(sig2, s);
            crate::ti_syntax::frag_of(sig2, r2);
            assert(crate::dom_rec_ty::rec_scope_g(sig2, r2));
            assert forall|a1: u64, a2: u64| #![trigger crate::rec_canon::rec_canon(sig2, a1), crate::rec_canon::rec_canon(sig2, a2)]
                crate::rec_canon::rec_canon(sig2, a1) && crate::rec_canon::rec_ind(sig2, a1) == s
                && crate::rec_canon::rec_canon(sig2, a2) && crate::rec_canon::rec_ind(sig2, a2) == s implies a1 == a2 by {
                assert(a1 == r2);
                assert(a2 == r2);
            }
        } else {
            crate::dom_code::canon_shape_struct(sig2, s);
        }
        let sh = crate::dom_code::canon_shape(sig, s);
        assert forall|k: int| 0 <= k < sh.fields[0].len() implies
            crate::rec_canon::psimple(sig2, s, sh.pdoms, sh.np, k as nat, #[trigger] sh.fields[0][k]) by {
            psimple_grow(sig, sig2, s, sh.pdoms, sh.np, k as nat, sh.fields[0][k]);
        }
    }
}

/// The projection rules' side conditions survive an extension.
pub proof fn proj_grow(sig: Sig, sig2: Sig, st: ExprSpec, i: nat, x: ExprSpec, m: ExprSpec)
    requires
        sig_ext(sig, sig2),
        !sig.ienv.full,
    ensures
        crate::ti_syntax::proj_ty(sig, st, i, x) is Some ==> crate::ti_syntax::proj_ty(sig2, st, i, x) == crate::ti_syntax::proj_ty(sig, st, i, x)
            && crate::ti_syntax::proj_prop(sig2, st) == crate::ti_syntax::proj_prop(sig, st),
        crate::ti_syntax::proj_fire(sig, m) ==> crate::ti_syntax::proj_fire(sig2, m)
            && crate::ti_syntax::proj_result(sig2, m) == crate::ti_syntax::proj_result(sig, m)
            && crate::ti_syntax::proj_fty(sig2, m) == crate::ti_syntax::proj_fty(sig, m)
            && sig2.ienv.ctor_ind[crate::beta_model::spine_head(*m->Proj_1)->Const_0] == sig.ienv.ctor_ind[crate::beta_model::spine_head(*m->Proj_1)->Const_0],
{
    reveal(crate::ti_syntax::proj_ty);
    reveal(crate::ti_syntax::proj_prop);
    reveal(crate::ti_syntax::proj_fire);
    reveal(crate::ti_syntax::proj_result);
    reveal(crate::ti_syntax::proj_fty);
    let h = crate::beta_model::spine_head(st);
    if h is Const && crate::ti_syntax::struct_of(sig, h->Const_0) {
        struct_grow(sig, sig2, h->Const_0);
    }
    if crate::ti_syntax::proj_fire(sig, m) {
        let hc = crate::beta_model::spine_head(*m->Proj_1);
        let ind = sig.ienv.ctor_ind[hc->Const_0];
        struct_grow(sig, sig2, ind);
    }
}

/// A recursor redex of a smaller environment is one of a larger, with the
/// same rule instance.
pub proof fn rec_sub(env: crate::expr_arena_bridge::EnvSpec, env2: crate::expr_arena_bridge::EnvSpec, m: ExprSpec)
    requires
        env.sub(env2),
        crate::beta_model::rec_ready(env, m),
    ensures
        crate::beta_model::rec_ready(env2, m),
        crate::beta_model::rec_result(env2, m) == crate::beta_model::rec_result(env, m),
{
    use crate::beta_model::{spine_head, spine_args, find_rule, find_rule_spec};
    if let ExprSpec::Const(rid, lv) = spine_head(m) {
        assert(env.recs.contains_key(rid));
        let rd = env.recs[rid];
        let major = spine_args(m)[rd.major_idx as int];
        if let ExprSpec::Const(cid, clv) = spine_head(major) {
            find_rule_spec(rd.rules, cid);
            if let Some(ri) = find_rule(rd.rules, cid) {
                assert(env.ctor_np.contains_key(rd.rules[ri].ctor_id));
            }
        }
    }
}

/// Iota's parameter premises read only the recursor's entry and its
/// inductive's type, which an extension keeps.
proof fn pjs_ext(sig: Sig, sig2: Sig, g: crate::ti_syntax::Ctx, m: ExprSpec)
    requires
        sig_ext(sig, sig2),
        iota_ok(sig),
        sig.ienv.recs.contains_key(crate::beta_model::spine_head(m)->Const_0),
    ensures
        crate::ti_syntax::iota_pjs(sig2, g, m) == crate::ti_syntax::iota_pjs(sig, g, m),
        crate::ti_syntax::iota_lv(sig2, m) == crate::ti_syntax::iota_lv(sig, m),
        crate::ti_syntax::iota_prop(sig2, m) == crate::ti_syntax::iota_prop(sig, m),
        crate::ti_syntax::iota_lm(sig2, m) == crate::ti_syntax::iota_lm(sig, m),
        crate::dom_rec_end::rec_interp(sig2, crate::beta_model::spine_head(m)->Const_0) == crate::dom_rec_end::rec_interp(sig, crate::beta_model::spine_head(m)->Const_0),
{
    reveal(crate::ti_syntax::iota_pjs);
    reveal(crate::ti_syntax::iota_lv);
    reveal(crate::ti_syntax::iota_prop);
    reveal(crate::ti_syntax::iota_lm);
    reveal(crate::dom_rec_end::rec_interp);
    reveal(crate::dom_rec_end::rec_large);
    let rid = crate::beta_model::spine_head(m)->Const_0;
    crate::ti_syntax::frag_of(sig, rid);
    assert(crate::rec_canon::rec_canon(sig, rid));
    assert(sig2.ienv.recs[rid] == sig.ienv.recs[rid]);
    assert(sig2.consts[rid] == sig.consts[rid]);
    let ind = crate::rec_canon::rec_ind(sig, rid);
    assert(crate::rec_canon::rec_ind(sig2, rid) == ind);
    assert(sig2.consts[ind] == sig.consts[ind]);
    assert(crate::dom_rec_ty::rshape(sig2, rid).pdoms == crate::dom_rec_ty::rshape(sig, rid).pdoms);
    assert(crate::dom_rec_ty::rshape(sig2, rid).us() == crate::dom_rec_ty::rshape(sig, rid).us());
}

/// One rule instance stays correct in an extended signature.
proof fn step_ext(sig: Sig, sig2: Sig, r: Rule, j: Jd, ps: Seq<Deriv>)
    requires
        step_ok(sig, r, j, ps),
        sig_ext(sig, sig2),
    ensures
        step_ok(sig2, r, j, ps),
{
    match r {
        Rule::ConstAx(_) | Rule::ConstDef(_) | Rule::Delta(_) => {
            let c = j->Eq_1->Const_0;
            assert(sig.consts.contains_key(c));
            assert(sig2.consts[c] == sig.consts[c]);
            if !(r is ConstAx) {
                let ls = j->Eq_1->Const_1;
                assert(is_def(sig2, c, ls));
                if sig2.consts == sig.consts && sig2.rank == sig.rank {
                    crate::ti_locals::crank_same(sig, sig2, crate::ti_syntax::dval(sig, c, ls));
                }
                assert(def_ok(sig2, c, ls));
                if r is ConstDef {
                    let ls2 = j->Eq_2->Const_1;
                    assert(is_def(sig2, c, ls2));
                    if sig2.consts == sig.consts && sig2.rank == sig.rank {
                        crate::ti_locals::crank_same(sig, sig2, crate::ti_syntax::dval(sig, c, ls2));
                    }
                    assert(def_ok(sig2, c, ls2));
                }
            }
        },
        Rule::Local(_) => {
            let k = j->Eq_1->Free_0;
            assert(sig.locals.contains_key(k));
        },
        Rule::RedG(_) => {
            crate::full_red::full_conv_sub(sig, sig2, j->Eq_1, j->Eq_2, j->Eq_3);
        },
        Rule::Iota(_) => {
            let m = j->Eq_1;
            let rid = crate::beta_model::spine_head(m)->Const_0;
            rec_sub(sig.ienv, sig2.ienv, m);
            pjs_ext(sig, sig2, j->Eq_0, m);
            crate::ti_syntax::frag_of(sig, rid);
            struct_iff(sig, sig2, crate::rec_canon::rec_ind(sig, rid), rid);
            canon_grow(sig, sig2, rid);
            reveal(crate::ti_hred::fire_inst);
            reveal(crate::ti_hred::rec_smash);
        },
        Rule::ProjG(_) => {
            reveal(crate::ti_syntax::proj_g_ok);
            let st = concl(ps[0])->Eq_3;
            crate::full_red::gproj_congr(sig, sig2, st, j->Eq_1->Proj_0 as nat, *j->Eq_1->Proj_1);
        },
        Rule::ProjCong(_) => {
            reveal(crate::ti_syntax::proj_cong_ok);
            let st = concl(ps[0])->Eq_3;
            proj_grow(sig, sig2, st, j->Eq_1->Proj_0 as nat, *j->Eq_1->Proj_1, j->Eq_1);
        },
        Rule::ProjIota(_) => {
            reveal(crate::ti_syntax::proj_iota_ok);
            let st = concl(ps[2])->Eq_3;
            proj_grow(sig, sig2, st, j->Eq_1->Proj_0 as nat, *j->Eq_1->Proj_1, j->Eq_1);
            proj_pjs_ext(sig, sig2, j->Eq_0, j->Eq_1);
        },
        Rule::StructEta(_) => {
            reveal(crate::ti_syntax::struct_eta_ok);
            let (g, m, n, t) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
            struct_grow(sig, sig2, crate::beta_model::spine_head(t)->Const_0);
            assert forall|k: int| 0 <= k < crate::ti_syntax::struct_nf(sig2, t) implies #[trigger] concl(ps[3 + k])
                == eq(g, ExprSpec::Proj(k as usize, Box::new(m)), ExprSpec::Proj(k as usize, Box::new(n)), crate::ti_syntax::proj_ty(sig2, t, k as nat, m)->Some_0) by {
                reveal(crate::ti_syntax::proj_ty);
                proj_grow(sig, sig2, t, k as nat, m, m);
            }
        },
        Rule::RecEta(_) => {
            reveal(crate::ti_syntax::rec_eta_ok);
            reveal(crate::ti_syntax::iota_lm);
            let m = j->Eq_1;
            let rid = crate::beta_model::spine_head(m)->Const_0;
            crate::ti_syntax::frag_of(sig, rid);
            canon_grow(sig, sig2, rid);
            struct_iff(sig, sig2, crate::rec_canon::rec_ind(sig, rid), rid);
        },
        _ => {},
    }
}

/// DERIVATIONS SURVIVE SIGNATURE EXTENSION.
pub proof fn d_ext(sig: Sig, sig2: Sig, d: Deriv)
    requires
        valid(sig, d),
        sig_ext(sig, sig2),
    ensures
        valid(sig2, d),
    decreases d,
{
    valid_prems(sig, d);
    let Deriv::Node(r, j, ps) = d;
    assert forall|k: int| 0 <= k < ps.len() implies valid(sig2, #[trigger] ps[k]) by {
        d_ext(sig, sig2, ps[k]);
    }
    step_ext(sig, sig2, r, j, ps);
    valid_node(sig2, r, j, ps);
}

pub proof fn derivable_ext(sig: Sig, sig2: Sig, j: Jd)
    requires
        derivable(sig, j),
        sig_ext(sig, sig2),
    ensures
        derivable(sig2, j),
{
    let d = get(sig, j);
    d_ext(sig, sig2, d);
    mk_d(sig2, d);
}

} // verus!
