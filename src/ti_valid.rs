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
        Rule::ConstAx(l) | Rule::ConstDef(l) | Rule::Local(l) | Rule::Delta(l) => {
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
        Rule::Iota(_) => {
            d_ty(sig, ps[0]);
        },
        Rule::RecEta(_) => {
            reveal(crate::ti_syntax::rec_eta_ok);
            d_ty(sig, ps[0]);
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
/// unchanged, and every definition of `sig2` well ranked in it.
pub open spec fn sig_ext(sig: Sig, sig2: Sig) -> bool {
    &&& forall|c: u64| #[trigger] sig.consts.contains_key(c) ==> sig2.consts.contains_key(c) && sig2.consts[c] == sig.consts[c]
    &&& forall|k: nat| #[trigger] sig.locals.contains_key(k) ==> sig2.locals.contains_key(k) && sig2.locals[k] == sig.locals[k]
    &&& forall|c: u64, ls: Seq<LevelSpec>| #[trigger] is_def(sig2, c, ls) ==> def_ok(sig2, c, ls)
    &&& sig.ienv.sub(sig2.ienv)
    &&& iota_ok(sig2)
    &&& forall|k: u64| #[trigger] sig.ienv.ctor_ind.contains_key(k) ==> sig2.ienv.ctor_ind.contains_key(k) && sig2.ienv.ctor_ind[k] == sig.ienv.ctor_ind[k]
}

/// A canonical recursor stays one in an extension, with the same
/// inductive, shape and interpretation.
pub proof fn canon_grow(sig: Sig, sig2: Sig, r: u64)
    requires
        sig_ext(sig, sig2),
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

/// Whether an inductive with a canonical recursor is a structure, and its
/// canonical recursor and shape, survive an extension.
pub proof fn struct_iff(sig: Sig, sig2: Sig, s: u64, r: u64)
    requires
        sig_ext(sig, sig2),
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
    assert(crate::dom_code::has_canon(sig, s));
    assert(crate::dom_code::has_canon(sig2, s));
    let c1 = crate::dom_code::canon_rec(sig, s);
    let c2 = crate::dom_code::canon_rec(sig2, s);
    assert(c1 == r);
    assert(c2 == r);
    assert(crate::dom_code::canon_shape(sig, s) == crate::dom_code::canon_shape(sig2, s));
}

/// A structure stays one in an extension, with the same shape.
pub proof fn struct_grow(sig: Sig, sig2: Sig, s: u64)
    requires
        sig_ext(sig, sig2),
        crate::ti_syntax::struct_of(sig, s),
    ensures
        crate::ti_syntax::struct_of(sig2, s),
        crate::dom_code::canon_shape(sig, s) == crate::dom_code::canon_shape(sig2, s),
        crate::dom_code::smash(sig, s) == crate::dom_code::smash(sig2, s),
        sig.consts.contains_key(s),
        sig2.consts[s] == sig.consts[s],
{
    reveal(crate::ti_syntax::struct_of);
    let r = crate::dom_code::canon_rec(sig, s);
    struct_iff(sig, sig2, s, r);
}

/// The projection rules' side conditions survive an extension.
pub proof fn proj_grow(sig: Sig, sig2: Sig, st: ExprSpec, i: nat, x: ExprSpec, m: ExprSpec)
    requires
        sig_ext(sig, sig2),
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
                assert(def_ok(sig2, c, ls));
                if r is ConstDef {
                    let ls2 = j->Eq_2->Const_1;
                    assert(is_def(sig2, c, ls2));
                    assert(def_ok(sig2, c, ls2));
                }
            }
        },
        Rule::Local(_) => {
            let k = j->Eq_1->Free_0;
            assert(sig.locals.contains_key(k));
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
        Rule::ProjCong(_) => {
            reveal(crate::ti_syntax::proj_cong_ok);
            let st = concl(ps[0])->Eq_3;
            proj_grow(sig, sig2, st, j->Eq_1->Proj_0 as nat, *j->Eq_1->Proj_1, j->Eq_1);
        },
        Rule::ProjIota(_) => {
            reveal(crate::ti_syntax::proj_iota_ok);
            let st = concl(ps[2])->Eq_3;
            proj_grow(sig, sig2, st, j->Eq_1->Proj_0 as nat, *j->Eq_1->Proj_1, j->Eq_1);
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
