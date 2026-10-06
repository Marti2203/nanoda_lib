//! UNIQUENESS OF TYPES AND SUBJECT REDUCTION for the typed judgment (typed
//! target, stage 3). Both by induction on the term, from generation and
//! Pi/Sort injectivity for chains of type conversions: two typings of a
//! term give chained types, and a typed term converts with its head reduct
//! (beta, delta in a well-formed signature, zeta) at its type.
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
use crate::ti_chain::*;
#[cfg(verus_only)]
use crate::ti_gen::*;
#[cfg(verus_only)]
use crate::ti_subst::{psub, rn, psub_closed};
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Chaining two types to a common third.
proof fn tchain_meet(sig: Sig, g: Ctx, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires
        tchain(sig, g, x, z),
        tchain(sig, g, y, z),
    ensures
        tchain(sig, g, x, y),
{
    tchain_sym(sig, g, y, z);
    tchain_trans(sig, g, x, z, y);
}

proof fn chain_inst_k(sig: Sig, g: Ctx, a: ExprSpec, ch: Seq<ExprSpec>, x: ExprSpec, k: int)
    requires
        chain_ok(sig, g.push(a), ch),
        0 <= k < ch.len(),
        derivable(sig, eq(g, x, x, a)),
    ensures
        tchain(sig, g, inst(0, x, ch[0]), inst(0, x, ch[k])),
    decreases k,
{
    if k == 0 {
        tchain_refl(sig, g, inst(0, x, ch[0]));
    } else {
        chain_inst_k(sig, g, a, ch, x, k - 1);
        let i = k - 1;
        assert(tconvd(sig, g.push(a), ch[i], ch[i + 1]));
        let (l, d) = get_t(sig, g.push(a), ch[i], ch[i + 1]);
        mk_d(sig, d);
        inst_tm(sig, g, a, ch[i], ch[i + 1], sort(l), x);
        assert(inst(0, x, sort(l)) == sort(l));
        let q = get(sig, eq(g, inst(0, x, ch[i]), inst(0, x, ch[k]), sort(l)));
        mk_t(sig, q, l);
        tchain_one(sig, g, inst(0, x, ch[i]), inst(0, x, ch[k]));
        tchain_trans(sig, g, inst(0, x, ch[0]), inst(0, x, ch[i]), inst(0, x, ch[k]));
    }
}

/// A chain of types under a binder, instantiated with a typed argument.
pub proof fn chain_inst(sig: Sig, g: Ctx, a: ExprSpec, c1: ExprSpec, c2: ExprSpec, x: ExprSpec)
    requires
        tchain(sig, g.push(a), c1, c2),
        derivable(sig, eq(g, x, x, a)),
    ensures
        tchain(sig, g, inst(0, x, c1), inst(0, x, c2)),
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == c1 && #[trigger] ch[ch.len() - 1] == c2 && chain_ok(sig, g.push(a), ch);
    chain_inst_k(sig, g, a, ch, x, ch.len() - 1);
}

proof fn pi_chain_k(sig: Sig, g: Ctx, a: ExprSpec, l1: LevelSpec, ch: Seq<ExprSpec>, k: int)
    requires
        chain_ok(sig, g.push(a), ch),
        0 <= k < ch.len(),
        typ(sig, g, a, l1),
    ensures
        tchain(sig, g, pi(a, ch[0]), pi(a, ch[k])),
    decreases k,
{
    if k == 0 {
        tchain_refl(sig, g, pi(a, ch[0]));
    } else {
        pi_chain_k(sig, g, a, l1, ch, k - 1);
        let i = k - 1;
        assert(tconvd(sig, g.push(a), ch[i], ch[i + 1]));
        let (l, d) = get_t(sig, g.push(a), ch[i], ch[i + 1]);
        let da = get(sig, eq(g, a, a, sort(l1)));
        let pj = eq(g, pi(a, ch[i]), pi(a, ch[k]), sort(imax(l1, l)));
        let pp = seq![da, d, d];
        assert(prems(pp, seq![eq(g, a, a, sort(l1)), eq(g.push(a), ch[i], ch[k], sort(l)), eq(g.push(a), ch[i], ch[k], sort(l))]));
        valid_node(sig, Rule::PiCong(l1, l), pj, pp);
        let pd = node(Rule::PiCong(l1, l), pj, pp);
        mk_t(sig, pd, imax(l1, l));
        tchain_one(sig, g, pi(a, ch[i]), pi(a, ch[k]));
        tchain_trans(sig, g, pi(a, ch[0]), pi(a, ch[i]), pi(a, ch[k]));
    }
}

/// A chain of codomains, under a typed domain, is a chain of Pis.
pub proof fn pi_chain_cod(sig: Sig, g: Ctx, a: ExprSpec, l1: LevelSpec, c1: ExprSpec, c2: ExprSpec)
    requires
        typ(sig, g, a, l1),
        tchain(sig, g.push(a), c1, c2),
    ensures
        tchain(sig, g, pi(a, c1), pi(a, c2)),
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == c1 && #[trigger] ch[ch.len() - 1] == c2 && chain_ok(sig, g.push(a), ch);
    pi_chain_k(sig, g, a, l1, ch, ch.len() - 1);
}

/// A projection's two types: the subjects' chained types are applications
/// of one structure, whose parameter the field names they chain.
#[verifier::spinoff_prover]
proof fn uniq_proj(sig: Sig, g: Ctx, i: usize, x: ExprSpec, ta: ExprSpec, tb: ExprSpec, st1: ExprSpec, st2: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        tchain(sig, g, st1, st2),
        crate::ti_syntax::proj_ty(sig, st1, i as nat, x) is Some,
        crate::ti_syntax::proj_ty(sig, st2, i as nat, x) is Some,
        tchain(sig, g, ta, crate::ti_syntax::proj_ty(sig, st1, i as nat, x)->Some_0),
        tchain(sig, g, tb, crate::ti_syntax::proj_ty(sig, st2, i as nat, x)->Some_0),
    ensures
        tchain(sig, g, ta, tb),
{
    use crate::beta_model::{spine_head, spine_args};
    crate::ti_proj::proj_ty_unfold(sig, st1, i as nat, x);
    crate::ti_proj::proj_ty_unfold(sig, st2, i as nat, x);
    let (s1, us1, xs) = (spine_head(st1)->Const_0, spine_head(st1)->Const_1, spine_args(st1));
    let (s2, us2, ys) = (spine_head(st2)->Const_0, spine_head(st2)->Const_1, spine_args(st2));
    assert(crate::dom_proj_sound::struct_sem(sig, s1));
    assert(crate::dom_proj_sound::struct_sem(sig, s2));
    assert(crate::dom_model::sem_const(sig, s1, us1));
    assert(crate::dom_model::sem_const(sig, s2, us2));
    reveal(crate::ti_syntax::struct_of);
    crate::beta_model::spine_recompose(st1);
    // the second type is an application of the first's structure
    crate::dom_fund::ind_head_chain(sig, g, s1, us1, xs, st2);
    crate::dom_lift::iapp_self(sig, st2);
    crate::ti_hred::hred_stuck_self(sig, st2, crate::dom_rel::ir(sig, st2, s1));
    assert(s2 == s1);
    // both types are the parameter the field names
    let sh = crate::dom_code::canon_shape(sig, s1);
    crate::dom_adeq_proj::pfield(sig, s1, i as nat, us1);
    let q = (sh.np + i - 1 - sh.fields[0][i as int]->Var_0) as int;
    crate::dom_adeq_proj::pfield_vsub(sig, s1, i as nat, us1, xs + crate::ti_syntax::projs(x, i as nat));
    crate::dom_adeq_proj::pfield_vsub(sig, s1, i as nat, us2, ys + crate::ti_syntax::projs(x, i as nat));
    assert((xs + crate::ti_syntax::projs(x, i as nat))[q] == xs[q]);
    assert((ys + crate::ti_syntax::projs(x, i as nat))[q] == ys[q]);
    assert(tchain(sig, g, xs[q], ys[q]));
    tchain_trans(sig, g, ta, xs[q], ys[q]);
    tchain_meet(sig, g, ta, tb, ys[q]);
}

/// UNIQUENESS OF TYPES: two typings of a term have chained types.
pub proof fn uniq(sig: Sig, g: Ctx, m: ExprSpec, ta: ExprSpec, tb: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        derivable(sig, eq(g, m, m, ta)),
        derivable(sig, eq(g, m, m, tb)),
    ensures
        tchain(sig, g, ta, tb),
    decreases crate::ti_zsize::zsize(m),
{
    if let ExprSpec::Bind(bk, a, b) = m {
        crate::ti_zsize::zsize_bind(bk, *a, *b);
    }
    let da = get(sig, eq(g, m, m, ta));
    let db = get(sig, eq(g, m, m, tb));
    gen(sig, da);
    gen(sig, db);
    match m {
        ExprSpec::Proj(i, x) => {
            let (st1, l1) = choose|st: ExprSpec, l: LevelSpec| #[trigger] gmark(st, *x, l, l)
                && derivable(sig, eq(g, *x, *x, st)) && crate::ti_syntax::proj_ty(sig, st, i as nat, *x) is Some
                && typ(sig, g, crate::ti_syntax::proj_ty(sig, st, i as nat, *x)->Some_0, l)
                && (crate::ti_syntax::proj_prop(sig, st) ==> is_zero(l))
                && tchain(sig, g, ta, crate::ti_syntax::proj_ty(sig, st, i as nat, *x)->Some_0);
            let (st2, l2) = choose|st: ExprSpec, l: LevelSpec| #[trigger] gmark(st, *x, l, l)
                && derivable(sig, eq(g, *x, *x, st)) && crate::ti_syntax::proj_ty(sig, st, i as nat, *x) is Some
                && typ(sig, g, crate::ti_syntax::proj_ty(sig, st, i as nat, *x)->Some_0, l)
                && (crate::ti_syntax::proj_prop(sig, st) ==> is_zero(l))
                && tchain(sig, g, tb, crate::ti_syntax::proj_ty(sig, st, i as nat, *x)->Some_0);
            uniq(sig, g, *x, st1, st2);
            uniq_proj(sig, g, i, *x, ta, tb, st1, st2);
        },
        ExprSpec::Var(i) => {
            tchain_meet(sig, g, ta, tb, var_ty(g, i));
        },
        ExprSpec::Sort(l) => {
            tchain_meet(sig, g, ta, tb, sort(succ(l)));
        },
        ExprSpec::Free(k) => {
            tchain_meet(sig, g, ta, tb, sig.locals[k]);
        },
        ExprSpec::Const(c, ls) => {
            tchain_meet(sig, g, ta, tb, dty_at(sig, c, ls));
        },
        ExprSpec::Bind(bk, a, b) => {
            if bk == BinderKind::Pi {
                let (l1, l2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(*a, *b, l1, l2)
                    && typ(sig, g, *a, l1) && typ(sig, g.push(*a), *b, l2) && tchain(sig, g, ta, sort(imax(l1, l2)));
                let (k1, k2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(*a, *b, l1, l2)
                    && typ(sig, g, *a, l1) && typ(sig, g.push(*a), *b, l2) && tchain(sig, g, tb, sort(imax(l1, l2)));
                uniq(sig, g, *a, sort(l1), sort(k1));
                uniq(sig, g.push(*a), *b, sort(l2), sort(k2));
                crate::dom_fund::sort_inj_chain(sig, g, l1, k1);
                crate::dom_fund::sort_inj_chain(sig, g.push(*a), l2, k2);
                assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(imax(l1, l2), r) == crate::level_model::interp(imax(k1, k2), r) by {
                    assert(crate::level_model::interp(l1, r) == crate::level_model::interp(k1, r));
                    assert(crate::level_model::interp(l2, r) == crate::level_model::interp(k2, r));
                }
                let w = d_wf(sig, da);
                let u = d_univ(sig, w, imax(l1, l2), imax(k1, k2));
                mk_t(sig, u, succ(imax(l1, l2)));
                tchain_one(sig, g, sort(imax(l1, l2)), sort(imax(k1, k2)));
                tchain_trans(sig, g, ta, sort(imax(l1, l2)), sort(imax(k1, k2)));
                tchain_meet(sig, g, ta, tb, sort(imax(k1, k2)));
            } else {
                let (bt, l1, l2) = choose|bt: ExprSpec, l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(bt, *b, l1, l2)
                    && typ(sig, g, *a, l1) && derivable(sig, eq(g.push(*a), *b, *b, bt)) && typ(sig, g.push(*a), bt, l2)
                    && tchain(sig, g, ta, pi(*a, bt));
                let (bt2, k1, k2) = choose|bt: ExprSpec, l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(bt, *b, l1, l2)
                    && typ(sig, g, *a, l1) && derivable(sig, eq(g.push(*a), *b, *b, bt)) && typ(sig, g.push(*a), bt, l2)
                    && tchain(sig, g, tb, pi(*a, bt));
                uniq(sig, g.push(*a), *b, bt, bt2);
                pi_chain_cod(sig, g, *a, l1, bt, bt2);
                tchain_trans(sig, g, ta, pi(*a, bt), pi(*a, bt2));
                tchain_meet(sig, g, ta, tb, pi(*a, bt2));
            }
        },
        ExprSpec::App(f, x) => {
            let (a1, b1, l1) = choose|a: ExprSpec, b: ExprSpec, l2: LevelSpec| #[trigger] gmark(a, b, l2, l2)
                && derivable(sig, eq(g, *f, *f, pi(a, b))) && derivable(sig, eq(g, *x, *x, a)) && typ(sig, g.push(a), b, l2)
                && tchain(sig, g, ta, inst(0, *x, b));
            let (a2, b2, l2) = choose|a: ExprSpec, b: ExprSpec, l2: LevelSpec| #[trigger] gmark(a, b, l2, l2)
                && derivable(sig, eq(g, *f, *f, pi(a, b))) && derivable(sig, eq(g, *x, *x, a)) && typ(sig, g.push(a), b, l2)
                && tchain(sig, g, tb, inst(0, *x, b));
            uniq(sig, g, *f, pi(a1, b1), pi(a2, b2));
            crate::dom_fund::pi_inj_chain(sig, g, a1, b1, a2, b2);
            chain_inst(sig, g, a1, b1, b2, *x);
            tchain_trans(sig, g, ta, inst(0, *x, b1), inst(0, *x, b2));
            tchain_meet(sig, g, ta, tb, inst(0, *x, b2));
        },
        ExprSpec::Let(a, v, body) => {
            let (t1, l1) = choose|tt: ExprSpec, l1: LevelSpec| #[trigger] gmark(tt, *v, l1, l1)
                && typ(sig, g, *a, l1) && derivable(sig, eq(g, *v, *v, *a))
                && derivable(sig, eq(g, inst(0, *v, *body), inst(0, *v, *body), tt)) && tchain(sig, g, ta, tt);
            let (t2, k1) = choose|tt: ExprSpec, l1: LevelSpec| #[trigger] gmark(tt, *v, l1, l1)
                && typ(sig, g, *a, l1) && derivable(sig, eq(g, *v, *v, *a))
                && derivable(sig, eq(g, inst(0, *v, *body), inst(0, *v, *body), tt)) && tchain(sig, g, tb, tt);
            crate::ti_zsize::zsize_let(*a, *v, *body);
            uniq(sig, g, inst(0, *v, *body), t1, t2);
            tchain_trans(sig, g, ta, t1, t2);
            tchain_meet(sig, g, ta, tb, t2);
        },
        _ => {},
    }
}

/// A WELL-FORMED SIGNATURE: every definition's type and value, at every
/// level instance, are closed and typed in the empty context.
pub open spec fn sig_wf(sig: Sig) -> bool {
    forall|c: u64, ls: Seq<LevelSpec>| #[trigger] is_def(sig, c, ls) ==> def_ok(sig, c, ls)
        && crate::expr_model::nlbv(dty_at(sig, c, ls)) == 0
        && (exists|l: LevelSpec| #[trigger] derivable(sig, eq(Seq::empty(), dty_at(sig, c, ls), dty_at(sig, c, ls), sort(l))))
        && derivable(sig, eq(Seq::empty(), dval(sig, c, ls), dval(sig, c, ls), dty_at(sig, c, ls)))
}

/// A closed judgment of the empty context holds in every well-formed one.
pub proof fn wk_closed(sig: Sig, g: Ctx, m: ExprSpec, n: ExprSpec, t: ExprSpec)
    requires
        derivable(sig, eq(Seq::empty(), m, n, t)),
        derivable(sig, Jd::Wf(g)),
        crate::expr_model::nlbv(m) == 0,
        crate::expr_model::nlbv(n) == 0,
        crate::expr_model::nlbv(t) == 0,
    ensures
        derivable(sig, eq(g, m, n, t)),
{
    let d = get(sig, eq(Seq::empty(), m, n, t));
    let w = get(sig, Jd::Wf(g));
    let r = |i: nat| i;
    assert(ren_ok(Seq::<ExprSpec>::empty(), g, r));
    let e = d_ren(sig, d, w, g, r);
    psub_closed(m, rn(r));
    psub_closed(n, rn(r));
    psub_closed(t, rn(r));
    mk_d(sig, e);
}

/// THE IOTA NODE at the bare redex, extended over the extra arguments.
proof fn iota_node(sig: Sig, g: Ctx, m: ExprSpec, t: ExprSpec, e: ExprSpec, l: LevelSpec)
    requires
        crate::ti_syntax::iota_ok(sig),
        crate::dom_rec_end::sig_sr(sig),
        crate::ti_hred::rec_fire(sig, m),
        crate::ti_syntax::iota_lv(sig, m),
        l == crate::ti_syntax::iota_lm(sig, m),
        derivable(sig, eq(g, crate::beta_model::rec_result(sig.ienv, m), crate::beta_model::rec_result(sig.ienv, m), t)),
        derivable(sig, eq(g, crate::iota_sr::bare(sig, m), crate::iota_sr::bare(sig, m), e)),
        derivable(sig, eq(g, crate::beta_model::rec_result(sig.ienv, crate::iota_sr::bare(sig, m)),
            crate::beta_model::rec_result(sig.ienv, crate::iota_sr::bare(sig, m)), e)),
        derivable(sig, eq(g, e, e, sort(l))),
        forall|q: int| 0 <= q < crate::ti_syntax::iota_pjs(sig, g, m).len() ==> derivable(sig, #[trigger] crate::ti_syntax::iota_pjs(sig, g, m)[q]),
        derivable(sig, eq(g, m, m, t)),
    ensures
        derivable(sig, eq(g, m, crate::beta_model::rec_result(sig.ienv, m), t)),
{
    crate::iota_sr::bare_facts(sig, g, m);
    let (x1, ex) = (crate::iota_sr::bare(sig, m), crate::iota_sr::extra(sig, m));
    crate::ti_hred::fire_inst_head(sig, x1, m);
    let n1 = crate::beta_model::rec_result(sig.ienv, x1);
    let d0 = get(sig, eq(g, x1, x1, e));
    let d1 = get(sig, eq(g, n1, n1, e));
    let d2 = get(sig, eq(g, e, e, sort(l)));
    let ij = eq(g, x1, n1, e);
    let pj = crate::ti_syntax::iota_pjs(sig, g, x1);
    let ip = seq![d0, d1, d2] + Seq::new(pj.len(), |q: int| crate::ti_sub::pick(sig, pj[q]));
    assert forall|q: int| 0 <= q < pj.len() implies crate::ti_syntax::valid(sig, #[trigger] crate::ti_sub::pick(sig, pj[q]))
        && crate::ti_syntax::concl(crate::ti_sub::pick(sig, pj[q])) == pj[q] by {
        let dq = crate::ti_sub::get(sig, pj[q]);
        crate::ti_sub::pick_of(sig, dq);
    }
    assert(prems(ip, seq![eq(g, x1, x1, e), eq(g, n1, n1, e), eq(g, e, e, sort(l))] + pj));
    valid_node(sig, Rule::Iota(l), ij, ip);
    mk_d(sig, node(Rule::Iota(l), ij, ip));
    crate::ti_spine::reconv_spine(sig, g, x1, n1, e, ex, t);
}

/// SUBJECT REDUCTION's Iota case: a firing recursor application converts
/// with its rule instance. A recursor eliminating into any universe by its
/// field kinds (`iota_sr`), a Prop-only one generically (`iota_gen`).
#[verifier::spinoff_prover]
proof fn sr_iota(sig: Sig, g: Ctx, m: ExprSpec, t: ExprSpec)
    requires
        crate::ti_syntax::iota_ok(sig),
        crate::dom_rec_end::sig_sr(sig),
        derivable(sig, eq(g, m, m, t)),
        crate::ti_hred::rec_fire(sig, m),
    ensures
        derivable(sig, eq(g, m, crate::beta_model::rec_result(sig.ienv, m), t)),
{
    let h = crate::beta_model::spine_head(m);
    let (rid, lv) = (h->Const_0, h->Const_1);
    let rd = sig.ienv.recs[rid];
    let major = crate::beta_model::spine_args(m)[rd.major_idx as int];
    let pr = crate::iota_sr::fired_rule(sig, m);
    crate::beta_model::find_rule_spec(rd.rules, crate::beta_model::spine_head(major)->Const_0);
    crate::ti_syntax::frag_of(sig, rid);
    if !crate::dom_rec_end::rec_interp(sig, rid) {
        // not interpreted by the model: generic subject reduction, no
        // parameter premises
        assert(!crate::ti_syntax::no_recs(sig)) by {
            assert(sig.ienv.recs.contains_key(rid));
        }
        reveal(crate::dom_rec_end::sig_rec);
        assert(crate::dom_rec_end::rec_model_p(sig, rid));
        crate::dom_rec_ty::rinst_id(sig, rid, lv, ExprSpec::Sort(LevelSpec::Zero));
        crate::dom_rec_ty::rec_lps_sub(sig, rid);
        assert(crate::iota_gen::rule_typed_g(sig, rid, lv, pr));
        assert(crate::iota_gen::srg_ok(sig, rid, lv, pr));
        let l = crate::iota_gen::iota_sr_g(sig, g, m, t);
        crate::iota_sr::bare_facts(sig, g, m);
        assert(crate::iota_gen::iota_end_g(sig, crate::iota_sr::bare(sig, m)) == crate::iota_gen::iota_end_g(sig, m)) by {
            let args = crate::beta_model::spine_args(m);
            assert(args.subrange(0, (rd.major_idx + 1) as int).subrange(crate::beta_model::rec_prefix(rd) as int, (rd.major_idx + 1) as int)
                =~= args.subrange(crate::beta_model::rec_prefix(rd) as int, (rd.major_idx + 1) as int));
        }
        reveal(crate::ti_syntax::iota_pjs);
        iota_node(sig, g, m, t, crate::iota_gen::iota_end_g(sig, m), l);
    } else {
        crate::dom_rec_conv::sr_ok_of(sig, rid, lv, pr);
        let l = crate::iota_sr::iota_sr(sig, g, m, t);
        iota_node(sig, g, m, t, crate::iota_sr::iota_end(sig, m), l);
    }
}

/// A TERM CHAIN FROM A TYPED TERM is an equality at its type: each step's
/// type chains to it by uniqueness of typing.
pub proof fn mchain_typed(sig: Sig, g: Ctx, x: ExprSpec, y: ExprSpec, t: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        derivable(sig, eq(g, x, x, t)),
        crate::ti_chain::mchain(sig, g, x, y),
    ensures
        derivable(sig, eq(g, x, y, t)),
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && #[trigger] ch[ch.len() - 1] == y
        && crate::ti_chain::mchain_ok(sig, g, ch);
    mchain_typed_k(sig, g, ch, ch.len() - 1, t);
}

proof fn mchain_typed_k(sig: Sig, g: Ctx, ch: Seq<ExprSpec>, k: int, t: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        0 <= k < ch.len(),
        derivable(sig, eq(g, ch[0], ch[0], t)),
        crate::ti_chain::mchain_ok(sig, g, ch),
    ensures
        derivable(sig, eq(g, ch[0], ch[k], t)),
    decreases k,
{
    if k > 0 {
        mchain_typed_k(sig, g, ch, k - 1, t);
        crate::dom_adeq_syn::dsym(sig, g, ch[0], ch[k - 1], t);
        let i = k - 1;
        assert(crate::ti_chain::mconvd(sig, g, ch[i], ch[i + 1]));
        assert(i + 1 == k);
        reveal(crate::ti_chain::mconvd);
        let t1 = choose|t1: ExprSpec| #[trigger] derivable(sig, eq(g, ch[k - 1], ch[k], t1));
        crate::dom_adeq_syn::dsym(sig, g, ch[k - 1], ch[k], t1);
        uniq(sig, g, ch[k - 1], t1, t);
        crate::ti_chain::conv_chain(sig, g, ch[k - 1], ch[k], t1, t);
        crate::dom_adeq_syn::dtrans(sig, g, ch[0], ch[k - 1], ch[k], t);
    }
}

/// THE RECURSOR'S ETA STEP (rule RecEta): its result is typed at the
/// redex's type, through the eta expansion (StructEta under application
/// congruence) and the rule's instance there.
#[verifier::spinoff_prover]
proof fn sr_rec_eta(sig: Sig, g: Ctx, f: ExprSpec, x: ExprSpec, t: ExprSpec, a1: ExprSpec, b1: ExprSpec, l1: LevelSpec, l2: LevelSpec)
    requires
        sig_wf(sig),
        crate::ti_syntax::iota_ok(sig),
        crate::dom_rec_end::sig_sr(sig),
        crate::ti_hred::rec_eta(sig, ExprSpec::App(Box::new(f), Box::new(x))),
        derivable(sig, eq(g, ExprSpec::App(Box::new(f), Box::new(x)), ExprSpec::App(Box::new(f), Box::new(x)), t)),
        derivable(sig, eq(g, f, f, pi(a1, b1))),
        derivable(sig, eq(g, x, x, a1)),
        typ(sig, g, a1, l1),
        typ(sig, g.push(a1), b1, l2),
        tchain(sig, g, t, inst(0, x, b1)),
    ensures
        derivable(sig, eq(g, ExprSpec::App(Box::new(f), Box::new(x)),
            crate::ti_hred::rec_eta_result(sig, ExprSpec::App(Box::new(f), Box::new(x))), t)),
{
    use crate::beta_model::{spine_head, spine_args, spine_app};
    let m = ExprSpec::App(Box::new(f), Box::new(x));
    let h = spine_head(m);
    let (rid, lv) = (h->Const_0, h->Const_1);
    let rd = sig.ienv.recs[rid];
    let a0 = spine_args(m);
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    assert(crate::ti_eta::eta_ok(sig, rid, lv, a0));
    crate::ti_eta::eta_facts(sig, rid, lv, a0);
    let pre = (sh.np + 1 + sh.nmin()) as int;
    crate::beta_model::spine_recompose(m);
    crate::dom_bound::spine_push(h, a0);
    assert(a0.last() == x && a0[pre] == x);
    assert(spine_app(h, a0.subrange(0, pre)) == f);
    crate::ti_eta::eta_heads(sig, g, rid, lv, a0, t);
    crate::ti_eta::eta_struct_eq(sig, g, rid, lv, a0);
    let (cx, st) = (crate::ti_eta::eta_cx(sig, rid, lv, a0), crate::ti_eta::eta_st(sig, rid, lv, a0));
    // the expansion at the application's domain
    crate::dom_adeq_syn::dsym(sig, g, x, cx, st);
    uniq(sig, g, x, a1, st);
    tchain_sym(sig, g, a1, st);
    conv_chain(sig, g, x, cx, st, a1);
    // application congruence on the major
    let m2 = ExprSpec::App(Box::new(f), Box::new(cx));
    let d0 = get(sig, eq(g, f, f, pi(a1, b1)));
    let d1 = get(sig, eq(g, x, cx, a1));
    let d2 = get(sig, eq(g, a1, a1, sort(l1)));
    let d3 = get(sig, eq(g.push(a1), b1, b1, sort(l2)));
    let aj = eq(g, m, m2, inst(0, x, b1));
    let ap = seq![d0, d1, d2, d3];
    assert(prems(ap, seq![eq(g, f, f, pi(a1, b1)), eq(g, x, cx, a1), eq(g, a1, a1, sort(l1)), eq(g.push(a1), b1, b1, sort(l2))]));
    valid_node(sig, Rule::AppCong(l1, l2), aj, ap);
    mk_d(sig, node(Rule::AppCong(l1, l2), aj, ap));
    crate::dom_adeq_syn::dsym(sig, g, m, m2, inst(0, x, b1));
    // the recursor at the expansion fires Iota
    let us = crate::dom_rec_ty::rinst(sig, rid, lv);
    let c = sh.ctors[0];
    let nf = sh.fields[0].len();
    let cargs = a0.subrange(0, sh.np as int) + crate::ti_syntax::projs(x, nf);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(c, us), cargs);
    let a2 = a0.subrange(0, pre).push(cx);
    crate::dom_bound::spine_push(h, a2);
    assert(a2.subrange(0, pre) =~= a0.subrange(0, pre));
    crate::beta_model::spine_destruct_app(h, a2);
    crate::dom_rec_end::rec_canon_ok(sig, rid);
    crate::beta_model::find_rule_spec(rd.rules, c);
    crate::dom_rec_ty::scope_ctor(sig, rid, 0);
    assert(sh.ctors[0] == rd.rules[0].ctor_id);
    assert(crate::beta_model::find_rule(rd.rules, c) == Some(0int)) by {
        reveal_with_fuel(crate::beta_model::find_rule, 2);
    }
    assert(crate::ti_hred::fire_inst(sig, m2)) by { reveal(crate::ti_hred::fire_inst); }
    assert(crate::ti_hred::rec_fits(sig, m2));
    // the rule's instance at the expansion is typed at the application's type
    let tt = inst(0, x, b1);
    crate::dom_psimple::der_diag(sig, g, m2, m, tt);
    assert(crate::iota_sr::fired_rule(sig, m2) == 0);
    crate::dom_rec_conv::sr_ok_of(sig, rid, lv, 0);
    let _ = crate::iota_sr::iota_sr(sig, g, m2, tt);
    let n = crate::ti_hred::rec_eta_result(sig, m);
    assert(crate::beta_model::rec_result(sig.ienv, m2) == n) by {
        assert(cargs.subrange((cargs.len() - nf) as int, cargs.len() as int) =~= crate::ti_syntax::projs(x, nf));
        assert(a2.subrange((rd.major_idx + 1) as int, a2.len() as int) =~= Seq::<ExprSpec>::empty());
    }
    // the eta step's instance, at the motive at the expansion
    crate::iota_sr::bare_facts(sig, g, m2);
    assert(crate::beta_model::spine_args(m2).subrange(0, (rd.major_idx + 1) as int) =~= crate::beta_model::spine_args(m2));
    crate::beta_model::spine_recompose(m2);
    let e = crate::iota_sr::iota_end(sig, m2);
    let lm = crate::ti_syntax::iota_lm(sig, m2);
    crate::ti_hred::fire_inst_head(sig, m2, m);
    uniq(sig, g, m2, tt, e);
    conv_chain(sig, g, m, m, tt, e);
    conv_chain(sig, g, n, n, tt, e);
    assert(crate::ti_hred::reta_exp(sig, m) == m2);
    let q0 = get(sig, eq(g, m, m, e));
    let q1 = get(sig, eq(g, n, n, e));
    let q2 = get(sig, eq(g, e, e, sort(lm)));
    let q3 = get(sig, eq(g, x, cx, st));
    let q4 = get(sig, eq(g, m2, m2, e));
    let rj = eq(g, m, n, e);
    let rp = seq![q0, q1, q2, q3, q4];
    assert(prems(rp, seq![eq(g, m, m, e), eq(g, n, n, e), eq(g, e, e, sort(lm)), eq(g, x, cx, st), eq(g, m2, m2, e)]));
    assert(crate::ti_hred::rec_smashed(sig, m));
    assert(a0[rd.major_idx as int] == x);
    assert(step_ok(sig, Rule::RecEta(lm), rj, rp)) by { reveal(crate::ti_syntax::rec_eta_ok); }
    valid_node(sig, Rule::RecEta(lm), rj, rp);
    mk_d(sig, node(Rule::RecEta(lm), rj, rp));
    tchain_sym(sig, g, tt, e);
    tchain_sym(sig, g, t, tt);
    crate::ti_chain::tchain_trans(sig, g, e, tt, t);
    conv_chain(sig, g, m, n, e, t);
}

/// A PROJECTION OF A CONSTRUCTOR APPLICATION converts with its field: the
/// field is typed at its declared type, the parameter it names, which the
/// subject's type chains to its own parameter, the projection's type.
#[verifier::spinoff_prover]
pub proof fn sr_proj_fire(sig: Sig, g: Ctx, i: usize, x: ExprSpec, t: ExprSpec, st: ExprSpec, l: LevelSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        crate::ti_syntax::proj_fire(sig, ExprSpec::Proj(i, Box::new(x))),
        derivable(sig, eq(g, ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(x)), t)),
        derivable(sig, eq(g, x, x, st)),
        crate::ti_syntax::proj_ty(sig, st, i as nat, x) is Some,
        typ(sig, g, crate::ti_syntax::proj_ty(sig, st, i as nat, x)->Some_0, l),
        crate::ti_syntax::proj_prop(sig, st) ==> is_zero(l),
        tchain(sig, g, t, crate::ti_syntax::proj_ty(sig, st, i as nat, x)->Some_0),
    ensures
        derivable(sig, eq(g, ExprSpec::Proj(i, Box::new(x)), crate::ti_syntax::proj_result(sig, ExprSpec::Proj(i, Box::new(x))), t)),
{
    use crate::beta_model::{spine_head, spine_args, spine_app};
    let m = ExprSpec::Proj(i, Box::new(x));
    let ty = crate::ti_syntax::proj_ty(sig, st, i as nat, x)->Some_0;
    reveal(crate::ti_syntax::proj_fire);
    reveal(crate::ti_syntax::proj_result);
    let (c, cl) = (spine_head(x)->Const_0, spine_head(x)->Const_1);
    let s = sig.ienv.ctor_ind[c];
    let sh = crate::dom_code::canon_shape(sig, s);
    let (np, nf) = (sh.np, sh.fields[0].len());
    let aa = spine_args(x);
    assert(crate::dom_proj_sound::struct_sem(sig, s));
    assert(crate::dom_model::sem_const(sig, s, cl));
    reveal(crate::ti_syntax::struct_of);
    // the constructor application's type: the structure at the parameters
    let lps = sig.consts[s].lps;
    crate::dom_con_rel::ctor_inst(sig, c, cl, s, 0, np);
    crate::dom_con_rel::ctor_result(sig, c, cl, s, 0, np, aa);
    crate::dom_levels::sl_plevels_id(lps, cl);
    let tc = crate::ti_syntax::dty_at(sig, c, cl);
    let r = crate::dom_con_rel::trest(tc, aa);
    let ra = spine_args(r);
    crate::beta_model::spine_recompose(r);
    assert(ra =~= aa.subrange(0, np as int));
    crate::beta_model::spine_recompose(x);
    let thc = crate::dom_iota::spine_gen(sig, g, ExprSpec::Const(c, cl), aa, st);
    crate::ti_spine::const_typed(sig, g, c, cl, thc);
    let ds = crate::dom_rec_shape::sls(sh.pdoms + sh.fields[0], lps, cl);
    let body = spine_app(ExprSpec::Const(s, crate::level_model::subst_levels_spec(sh.us(), lps, cl)),
        crate::dom_rec_shape::sls(crate::rec_canon::vars(nf, np) + sh.tss[0], lps, cl));
    assert forall|k: int| 0 <= k < aa.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(tc, aa.subrange(0, k))) by {
        crate::ti_spine::tel_next(ds, body, aa, k);
    }
    crate::ti_spine::spine_ty(sig, g, ExprSpec::Const(c, cl), tc, aa, st);
    // the field, typed at the parameter it names
    crate::dom_adeq_proj::pfield(sig, s, i as nat, cl);
    let q = (np + i - 1 - sh.fields[0][i as int]->Var_0) as int;
    let fld = aa[np + i];
    crate::ti_spine::tel_next(ds, body, aa, (np + i) as int);
    assert(ds[np + i] == crate::ti_proj::sfield(sig, s, i as nat, cl));
    crate::dom_adeq_proj::pfield_vsub(sig, s, i as nat, cl, aa.subrange(0, (np + i) as int));
    assert(derivable(sig, eq(g, fld, fld, aa[q])));
    assert(crate::ti_syntax::proj_fty(sig, m) == aa[q]) by {
        reveal(crate::ti_syntax::proj_fty);
    }
    // the subject's type is an application of the same structure
    tchain_sym(sig, g, st, r);
    crate::dom_fund::ind_head_chain(sig, g, s, cl, ra, st);
    crate::ti_proj::proj_ty_unfold(sig, st, i as nat, x);
    let (s2, us2) = (spine_head(st)->Const_0, spine_head(st)->Const_1);
    assert(crate::dom_proj_sound::struct_sem(sig, s2));
    assert(crate::dom_model::sem_const(sig, s2, us2));
    crate::dom_lift::iapp_self(sig, st);
    crate::ti_hred::hred_stuck_self(sig, st, crate::dom_rel::ir(sig, st, s));
    assert(s2 == s);
    crate::dom_adeq_proj::pfield_vsub(sig, s, i as nat, us2, spine_args(st) + crate::ti_syntax::projs(x, i as nat));
    assert((spine_args(st) + crate::ti_syntax::projs(x, i as nat))[q] == spine_args(st)[q]);
    assert(ty == spine_args(st)[q]);
    assert(tchain(sig, g, aa[q], ty));
    // ProjIota, then back to the projection's type
    conv_chain(sig, g, fld, fld, aa[q], ty);
    conv_chain(sig, g, m, m, t, ty);
    let e0 = get(sig, eq(g, m, m, ty));
    let e1 = get(sig, eq(g, fld, fld, ty));
    let e2 = get(sig, eq(g, x, x, st));
    let e3 = get(sig, eq(g, ty, ty, sort(l)));
    let e4 = get(sig, eq(g, fld, fld, aa[q]));
    let ji = eq(g, m, fld, ty);
    let pi = seq![e0, e1, e2, e3, e4];
    assert(prems(pi, seq![eq(g, m, m, ty), eq(g, fld, fld, ty), eq(g, x, x, st), eq(g, ty, ty, sort(l)),
        eq(g, fld, fld, crate::ti_syntax::proj_fty(sig, m))]));
    assert(step_ok(sig, Rule::ProjIota(l), ji, pi)) by {
        reveal(crate::ti_syntax::proj_iota_ok);
    }
    valid_node(sig, Rule::ProjIota(l), ji, pi);
    mk_d(sig, node(Rule::ProjIota(l), ji, pi));
    tchain_sym(sig, g, t, ty);
    conv_chain(sig, g, m, fld, ty, t);
}

/// SUBJECT REDUCTION: a typed term converts with its head reduct, at its
/// type.
#[verifier::spinoff_prover]
pub proof fn sr(sig: Sig, g: Ctx, m: ExprSpec, t: ExprSpec)
    requires
        sig_wf(sig),
        crate::ti_syntax::iota_ok(sig),
        crate::dom_rec_end::sig_sr(sig),
        derivable(sig, eq(g, m, m, t)),
        crate::ti_hred::hstep(sig, m) is Some,
    ensures
        derivable(sig, eq(g, m, crate::ti_hred::hstep(sig, m)->Some_0, t)),
    decreases m,
{
    let dm = get(sig, eq(g, m, m, t));
    gen(sig, dm);
    let w = d_wf(sig, dm);
    mk_d(sig, w);
    match m {
        ExprSpec::Proj(i, x) => {
            let (st, l) = choose|st: ExprSpec, l: LevelSpec| #[trigger] gmark(st, *x, l, l)
                && derivable(sig, eq(g, *x, *x, st)) && crate::ti_syntax::proj_ty(sig, st, i as nat, *x) is Some
                && typ(sig, g, crate::ti_syntax::proj_ty(sig, st, i as nat, *x)->Some_0, l)
                && (crate::ti_syntax::proj_prop(sig, st) ==> is_zero(l))
                && tchain(sig, g, t, crate::ti_syntax::proj_ty(sig, st, i as nat, *x)->Some_0);
            let ty = crate::ti_syntax::proj_ty(sig, st, i as nat, *x)->Some_0;
            if crate::ti_syntax::proj_fire(sig, m) {
                sr_proj_fire(sig, g, i, *x, t, st, l);
            } else {
                // the subject reduced in place
                sr(sig, g, *x, st);
                let x2 = crate::ti_hred::hstep(sig, *x)->Some_0;
                let m2 = ExprSpec::Proj(i, Box::new(x2));
                let d0 = get(sig, eq(g, *x, x2, st));
                let d1 = get(sig, eq(g, ty, ty, sort(l)));
                let pj = eq(g, m, m2, ty);
                let pp = seq![d0, d1];
                assert(prems(pp, seq![eq(g, *x, x2, st), eq(g, ty, ty, sort(l))]));
                assert(step_ok(sig, Rule::ProjCong(l), pj, pp)) by {
                    reveal(crate::ti_syntax::proj_cong_ok);
                }
                valid_node(sig, Rule::ProjCong(l), pj, pp);
                mk_d(sig, node(Rule::ProjCong(l), pj, pp));
                tchain_sym(sig, g, t, ty);
                conv_chain(sig, g, m, m2, ty, t);
            }
        },
        ExprSpec::App(f, x) => {
            let (a1, b1, l2) = choose|a: ExprSpec, b: ExprSpec, l2: LevelSpec| #[trigger] gmark(a, b, l2, l2)
                && derivable(sig, eq(g, *f, *f, pi(a, b))) && derivable(sig, eq(g, *x, *x, a)) && typ(sig, g.push(a), b, l2)
                && tchain(sig, g, t, inst(0, *x, b));
            let df = get(sig, eq(g, *f, *f, pi(a1, b1)));
            crate::ti_valid::d_ty(sig, df);
            let (lp, dp) = get_t(sig, g, pi(a1, b1), pi(a1, b1));
            gen(sig, dp);
            let (l1, l2b) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(a1, b1, l1, l2)
                && typ(sig, g, a1, l1) && typ(sig, g.push(a1), b1, l2) && tchain(sig, g, sort(lp), sort(imax(l1, l2)));
            if let ExprSpec::Bind(BinderKind::Lam, a, body) = *f {
                gen(sig, df);
                let (bt, k1, k2) = choose|bt: ExprSpec, l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(bt, *body, l1, l2)
                    && typ(sig, g, *a, l1) && derivable(sig, eq(g.push(*a), *body, *body, bt)) && typ(sig, g.push(*a), bt, l2)
                    && tchain(sig, g, pi(a1, b1), pi(*a, bt));
                crate::dom_fund::pi_inj_chain(sig, g, a1, b1, *a, bt);
                conv_chain(sig, g, *x, *x, a1, *a);
                crate::dom_adeq_syn::beta_d(sig, g, *a, *body, bt, *x, k1, k2);
                chain_inst(sig, g, a1, b1, bt, *x);
                tchain_trans(sig, g, t, inst(0, *x, b1), inst(0, *x, bt));
                tchain_sym(sig, g, t, inst(0, *x, bt));
                conv_chain(sig, g, m, inst(0, *x, *body), inst(0, *x, bt), t);
            } else if crate::ti_hred::hstep(sig, *f) is Some {
                sr(sig, g, *f, pi(a1, b1));
                let f2 = crate::ti_hred::hstep(sig, *f)->Some_0;
                let d0 = get(sig, eq(g, *f, f2, pi(a1, b1)));
                let d1 = get(sig, eq(g, *x, *x, a1));
                let d2 = get(sig, eq(g, a1, a1, sort(l1)));
                let d3 = get(sig, eq(g.push(a1), b1, b1, sort(l2b)));
                let m2 = ExprSpec::App(Box::new(f2), x);
                let aj = eq(g, m, m2, inst(0, *x, b1));
                let ap = seq![d0, d1, d2, d3];
                assert(prems(ap, seq![eq(g, *f, f2, pi(a1, b1)), eq(g, *x, *x, a1), eq(g, a1, a1, sort(l1)), eq(g.push(a1), b1, b1, sort(l2b))]));
                valid_node(sig, Rule::AppCong(l1, l2b), aj, ap);
                mk_d(sig, node(Rule::AppCong(l1, l2b), aj, ap));
                tchain_sym(sig, g, t, inst(0, *x, b1));
                conv_chain(sig, g, m, m2, inst(0, *x, b1), t);
            } else if crate::ti_hred::rec_fire(sig, m) {
                // iota: the rule instance is typed at the redex's type
                sr_iota(sig, g, m, t);
            } else if crate::ti_hred::rec_eta(sig, m) {
                // a smashed structure's major, eta-expanded
                sr_rec_eta(sig, g, *f, *x, t, a1, b1, l1, l2b);
            } else {
                // the major of a recursor application, reduced in place
                assert(crate::ti_hred::rec_major(sig, m));
                sr(sig, g, *x, a1);
                let x2 = crate::ti_hred::hstep(sig, *x)->Some_0;
                let d0 = get(sig, eq(g, *f, *f, pi(a1, b1)));
                let d1 = get(sig, eq(g, *x, x2, a1));
                let d2 = get(sig, eq(g, a1, a1, sort(l1)));
                let d3 = get(sig, eq(g.push(a1), b1, b1, sort(l2b)));
                let m2 = ExprSpec::App(f, Box::new(x2));
                let aj = eq(g, m, m2, inst(0, *x, b1));
                let ap = seq![d0, d1, d2, d3];
                assert(prems(ap, seq![eq(g, *f, *f, pi(a1, b1)), eq(g, *x, x2, a1), eq(g, a1, a1, sort(l1)), eq(g.push(a1), b1, b1, sort(l2b))]));
                valid_node(sig, Rule::AppCong(l1, l2b), aj, ap);
                mk_d(sig, node(Rule::AppCong(l1, l2b), aj, ap));
                tchain_sym(sig, g, t, inst(0, *x, b1));
                conv_chain(sig, g, m, m2, inst(0, *x, b1), t);
            }
        },
        ExprSpec::Const(c, ls) => {
            let tc = dty_at(sig, c, ls);
            assert(is_def(sig, c, ls));
            let l = choose|l: LevelSpec| #[trigger] derivable(sig, eq(Seq::empty(), tc, tc, sort(l)));
            wk_closed(sig, g, tc, tc, sort(l));
            wk_closed(sig, g, dval(sig, c, ls), dval(sig, c, ls), tc);
            let q1 = get(sig, eq(g, tc, tc, sort(l)));
            let q2 = get(sig, eq(g, dval(sig, c, ls), dval(sig, c, ls), tc));
            let wg = get(sig, Jd::Wf(g));
            let dj = eq(g, m, dval(sig, c, ls), tc);
            let dp = seq![wg, q1, q2];
            assert(prems(dp, seq![Jd::Wf(g), eq(g, tc, tc, sort(l)), eq(g, dval(sig, c, ls), dval(sig, c, ls), tc)]));
            valid_node(sig, Rule::Delta(l), dj, dp);
            mk_d(sig, node(Rule::Delta(l), dj, dp));
            tchain_sym(sig, g, t, tc);
            conv_chain(sig, g, m, dval(sig, c, ls), tc, t);
        },
        ExprSpec::Let(a, v, body) => {
            let (tt, l1) = choose|tt: ExprSpec, l1: LevelSpec| #[trigger] gmark(tt, *v, l1, l1)
                && typ(sig, g, *a, l1) && derivable(sig, eq(g, *v, *v, *a))
                && derivable(sig, eq(g, inst(0, *v, *body), inst(0, *v, *body), tt)) && tchain(sig, g, t, tt);
            zeta_node(sig, g, *a, *v, *body, tt, l1);
            tchain_sym(sig, g, t, tt);
            conv_chain(sig, g, m, inst(0, *v, *body), tt, t);
        },
        _ => {},
    }
}

/// A `let` converts with its body's instance.
pub proof fn zeta_node(sig: Sig, g: Ctx, a: ExprSpec, v: ExprSpec, body: ExprSpec, tt: ExprSpec, l1: LevelSpec)
    requires
        derivable(sig, eq(g, a, a, sort(l1))),
        derivable(sig, eq(g, v, v, a)),
        derivable(sig, eq(g, inst(0, v, body), inst(0, v, body), tt)),
    ensures
        derivable(sig, eq(g, ExprSpec::Let(Box::new(a), Box::new(v), Box::new(body)), inst(0, v, body), tt)),
{
    let q0 = get(sig, eq(g, a, a, sort(l1)));
    let q1 = get(sig, eq(g, v, v, a));
    let q2 = get(sig, eq(g, inst(0, v, body), inst(0, v, body), tt));
    let m = ExprSpec::Let(Box::new(a), Box::new(v), Box::new(body));
    let zj = eq(g, m, inst(0, v, body), tt);
    let zp = seq![q0, q1, q2];
    assert(prems(zp, seq![eq(g, a, a, sort(l1)), eq(g, v, v, a), eq(g, inst(0, v, body), inst(0, v, body), tt)]));
    valid_node(sig, Rule::Zeta(l1), zj, zp);
    mk_d(sig, node(Rule::Zeta(l1), zj, zp));
}

} // verus!
