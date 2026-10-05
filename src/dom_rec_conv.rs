//! THE RECURSOR REDEX'S CONVERSION, built from the rules (docs/TYPED_TARGET.md,
//! "The landing"): congruence at the major, the Iota rule, and Beta through
//! the rule's lambdas. So the model does not need subject reduction.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::{Ctx, Sig, Jd, Rule, derivable, eq, sort, pi};
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::ti_subst::psub;
#[cfg(verus_only)]
use crate::ti_beta::tsub;
#[cfg(verus_only)]
use crate::dom_rec_ty::{rshape, rtds};
#[cfg(verus_only)]
use crate::dom_rec_end::{rule_ctx, rule_bty, rule_typed, rec_hyps};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The rule body's type under the arguments: the motive at the constructor
/// applied to the parameters and the fields.
pub proof fn bty_inst(sig: Sig, c: u64, lv: Seq<LevelSpec>, j: int, zs: Seq<ExprSpec>)
    requires
        0 <= j < rshape(sig, c).nmin(),
        zs.len() == rshape(sig, c).np + rshape(sig, c).nmin() + 1 + rshape(sig, c).fields[j].len(),
    ensures ({
        let np = rshape(sig, c).np as int;
        let pre = (rshape(sig, c).np + rshape(sig, c).nmin() + 1) as int;
        psub(rule_bty(sig, c, lv, j), tsub(zs, zs.len())) == ExprSpec::App(Box::new(zs[np]),
            Box::new(spine_app(ExprSpec::Const(rshape(sig, c).ctors[j], crate::dom_rec_ty::rinst(sig, c, lv)),
                zs.subrange(0, np) + zs.subrange(pre, zs.len() as int))))
    }),
{
    let sh = rshape(sig, c);
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[j].len());
    let n = zs.len();
    let pre = (np + nmin + 1) as int;
    let s = tsub(zs, n);
    let h = ExprSpec::Const(sh.ctors[j], crate::dom_rec_ty::rinst(sig, c, lv));
    let vs = crate::rec_canon::vars(1 + nmin + nf, np) + crate::rec_canon::vars(0, nf);
    let want = zs.subrange(0, np as int) + zs.subrange(pre, n as int);
    crate::ti_beta::tsub_at(zs, n, nmin + nf);
    crate::ti_subst::psub_spine_app(s, h, vs);
    assert forall|i: int| 0 <= i < np + nf implies #[trigger] crate::ti_subst::spsub(vs, s)[i] == want[i] by {
        if i < np {
            assert(vs[i] == ExprSpec::Var((1 + nmin + nf + np - 1 - i) as nat));
            crate::ti_beta::tsub_at(zs, n, (1 + nmin + nf + np - 1 - i) as nat);
        } else {
            assert(vs[i] == ExprSpec::Var((nf - 1 - (i - np)) as nat));
            crate::ti_beta::tsub_at(zs, n, (nf - 1 - (i - np)) as nat);
        }
    }
    assert(crate::ti_subst::spsub(vs, s) =~= want);
    assert(psub(ExprSpec::Var(nmin + nf), s) == zs[np as int]);
    assert(psub(h, s) == h);
    let e = ExprSpec::App(Box::new(ExprSpec::Var(nmin + nf)), Box::new(spine_app(h, vs)));
    assert(psub(e, s) == ExprSpec::App(Box::new(psub(ExprSpec::Var(nmin + nf), s)), Box::new(psub(spine_app(h, vs), s))));
}

/// A field binder of the rule, under the arguments before it: the field's
/// type at the recursor's instance, the parameters and the earlier fields.
proof fn field_ctx(sig: Sig, c: u64, lv: Seq<LevelSpec>, j: int, heads: Seq<ExprSpec>, args: Seq<ExprSpec>, k: int)
    requires
        rec_hyps(sig, c),
        0 <= j < rshape(sig, c).nmin(),
        heads.len() == rshape(sig, c).np + rshape(sig, c).nmin() + 1,
        args.len() == rshape(sig, c).fields[j].len(),
        0 <= k < args.len(),
    ensures ({
        let pre = heads.len() as int;
        psub(rule_ctx(sig, c, lv, j)[pre + k], tsub(heads + args, (pre + k) as nat))
            == crate::ti_spine::vsub(crate::iota_sr::cfu(sig, c, j, k, crate::dom_rec_ty::rinst(sig, c, lv)),
                heads.subrange(0, rshape(sig, c).np as int) + args.subrange(0, k))
    }),
{
    let sh = rshape(sig, c);
    let pre = heads.len() as int;
    let zs = heads + args;
    let i = pre + k;
    let ctx = rule_ctx(sig, c, lv, j);
    crate::dom_iota::major_form(sig, c, lv);
    crate::dom_rec_end::rec_canon_ok(sig, c);
    assert(ctx[i] == crate::dom_iota::ftds(sig, c, lv, j)[k]);
    crate::ti_beta::tsub_prefix(zs, i as nat);
    let zi = zs.subrange(0, i);
    crate::ti_subst::psub_ext(ctx[i], tsub(zs, i as nat), tsub(zi, i as nat));
    crate::ti_beta::vsub_tsub(ctx[i], zi);
    crate::iota_sr::ftds_vsub(sig, c, lv, j, heads, args, k);
}

/// THE RULE'S BETA CHAIN at the recursor's arguments: its instance converts
/// with its body under them, at the motive at the constructor application.
#[verifier::spinoff_prover]
pub proof fn rule_beta(sig: Sig, g: Ctx, c: u64, lv: Seq<LevelSpec>, j: int, heads: Seq<ExprSpec>, args: Seq<ExprSpec>)
    requires
        rec_hyps(sig, c),
        lv.len() == sig.ienv.recs[c].uparams.len(),
        0 <= j < rshape(sig, c).nmin(),
        heads.len() == rshape(sig, c).np + rshape(sig, c).nmin() + 1,
        args.len() == rshape(sig, c).fields[j].len(),
        derivable(sig, Jd::Wf(g)),
        forall|i: int| 0 <= i < heads.len() ==> derivable(sig, eq(g, #[trigger] heads[i], heads[i],
            crate::dom_rel::tel_dom(crate::ti_syntax::dty_at(sig, c, lv), heads, i as nat))),
        forall|k: int| 0 <= k < args.len() ==> derivable(sig, eq(g, #[trigger] args[k], args[k],
            crate::ti_spine::vsub(crate::iota_sr::cfu(sig, c, j, k, crate::dom_rec_ty::rinst(sig, c, lv)),
                heads.subrange(0, rshape(sig, c).np as int) + args.subrange(0, k)))),
    ensures ({
        let rd = sig.ienv.recs[c];
        let np = rshape(sig, c).np as int;
        let body = crate::expr_model::subst_expr_levels(rd.rules[j].rhs, rd.uparams, lv);
        let zs = heads + args;
        let r = spine_app(heads[np + 1 + j], args + crate::dom_rec_red::ih_tms(sig, c, lv, j, heads, args));
        let ty = ExprSpec::App(Box::new(heads[np]), Box::new(spine_app(ExprSpec::Const(rshape(sig, c).ctors[j],
            crate::dom_rec_ty::rinst(sig, c, lv)), heads.subrange(0, np) + args)));
        derivable(sig, eq(g, spine_app(body, zs), r, ty))
    }),
{
    let sh = rshape(sig, c);
    let rd = sig.ienv.recs[c];
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[j].len());
    let pre = (np + nmin + 1) as int;
    let ctx = rule_ctx(sig, c, lv, j);
    let (b, bt) = (crate::dom_iota::rule_body(sig, c, lv, j), rule_bty(sig, c, lv, j));
    let zs = heads + args;
    let n = zs.len();
    let t0 = crate::ti_syntax::dty_at(sig, c, lv);
    // the rule's typing, in the full signature
    reveal(crate::dom_rec_end::sig_rec);
    assert(rule_typed(sig, c, lv, j));
    let ss = crate::ti_strip::strip(sig);
    let lb = choose|lb: LevelSpec| #[trigger] derivable(ss, eq(ctx, bt, bt, sort(lb)));
    crate::ti_strip::strip_derivable(sig, Jd::Wf(ctx));
    crate::ti_strip::strip_derivable(sig, eq(ctx, b, b, bt));
    crate::ti_strip::strip_derivable(sig, eq(ctx, bt, bt, sort(lb)));
    crate::dom_iota::rule_split(sig, c, lv, j);
    crate::dom_rec_shape::nlbv_sl(rd.rules[j].rhs, rd.uparams, lv);
    crate::dom_iota::major_form(sig, c, lv);
    // the arguments at the binders' instances
    assert forall|i: int| 0 <= i < ctx.len() implies
        derivable(sig, eq(g, #[trigger] zs[i], zs[i], psub(ctx[i], tsub(zs, i as nat)))) by {
        if i < pre {
            assert(zs[i] == heads[i] && ctx[i] == rtds(sig, c, lv)[i]);
            crate::dom_rec_minor::rec_dom(sig, c, lv, heads, i);
            crate::ti_beta::vsub_tsub(rtds(sig, c, lv)[i], heads.subrange(0, i));
            crate::ti_beta::tsub_prefix(zs, i as nat);
            assert(zs.subrange(0, i) =~= heads.subrange(0, i));
            crate::ti_subst::psub_ext(rtds(sig, c, lv)[i], tsub(zs, i as nat), tsub(heads.subrange(0, i), i as nat));
        } else {
            let k = i - pre;
            assert(zs[i] == args[k]);
            field_ctx(sig, c, lv, j, heads, args, k);
        }
    }
    assert(crate::ti_beta::beta_pre(sig, g, ctx, b, bt, lb, zs));
    crate::ti_beta::beta_upto(sig, g, ctx, b, bt, lb, zs, n);
    assert(zs.subrange(0, n as int) =~= zs);
    assert(ctx.subrange(n as int, n as int) =~= Seq::<ExprSpec>::empty());
    bty_inst(sig, c, lv, j, zs);
    assert(zs.subrange(pre, n as int) =~= args);
    assert(zs.subrange(0, np as int) =~= heads.subrange(0, np as int));
    assert(zs[np as int] == heads[np as int]);
    crate::ti_beta::vsub_tsub(b, zs);
    crate::dom_rec_red::rule_vsub(sig, c, lv, j, heads, args);
}

/// THE REDEX CONVERTS WITH ITS REDUCT, one side: the recursor applied up
/// to a major that reduces to a constructor application converts, at the
/// motive at the major, with the minor at the fields and the recursive
/// calls. The constructor's own parameters, which Iota drops, equal the
/// recursor's at their sorts, and its own levels `cl` are equivalent to
/// the recursor's instance of the inductive.
#[verifier::spinoff_prover]
pub proof fn rec_conv_side(sig: Sig, g: Ctx, c: u64, lv: Seq<LevelSpec>, cl: Seq<LevelSpec>, heads: Seq<ExprSpec>, x: ExprSpec, j: int,
    pargs: Seq<ExprSpec>, args: Seq<ExprSpec>)
    requires
        rec_hyps(sig, c),
        forall|q: int| 0 <= q < rshape(sig, c).np ==> (#[trigger] rshape(sig, c).pdoms[q]) is Sort,
        lv.len() == sig.ienv.recs[c].uparams.len(),
        0 <= j < rshape(sig, c).nmin(),
        heads.len() == rshape(sig, c).np + rshape(sig, c).nmin() + 1,
        pargs.len() == rshape(sig, c).np,
        args.len() == rshape(sig, c).fields[j].len(),
        derivable(sig, eq(g, ExprSpec::Const(c, lv), ExprSpec::Const(c, lv), crate::ti_syntax::dty_at(sig, c, lv))),
        forall|i: int| 0 <= i < heads.len() ==> derivable(sig, eq(g, #[trigger] heads[i], heads[i],
            crate::dom_rel::tel_dom(crate::ti_syntax::dty_at(sig, c, lv), heads, i as nat))),
        forall|q: int| 0 <= q < rshape(sig, c).np ==> derivable(sig, eq(g, #[trigger] heads[q], pargs[q],
            crate::dom_rel::ptype(sig, rshape(sig, c).ind, crate::dom_rec_ty::rinst(sig, c, lv), q))),
        derivable(sig, eq(g, x, spine_app(ExprSpec::Const(rshape(sig, c).ctors[j], cl), pargs + args),
            spine_app(ExprSpec::Const(rshape(sig, c).ind, crate::dom_rec_ty::rinst(sig, c, lv)), heads.subrange(0, rshape(sig, c).np as int)))),
        crate::ti_hred::hred(sig, x, spine_app(ExprSpec::Const(rshape(sig, c).ctors[j], cl), pargs + args)),
        crate::conv_cr::levs_eq(crate::dom_rec_ty::rinst(sig, c, lv), cl),
        forall|k: int| 0 <= k < args.len() ==> derivable(sig, eq(g, #[trigger] args[k], args[k],
            crate::ti_spine::vsub(crate::iota_sr::cfu(sig, c, j, k, crate::dom_rec_ty::rinst(sig, c, lv)),
                heads.subrange(0, rshape(sig, c).np as int) + args.subrange(0, k)))),
    ensures
        derivable(sig, eq(g, spine_app(ExprSpec::Const(c, lv), heads.push(x)),
            spine_app(heads[rshape(sig, c).np + 1 + j], args + crate::dom_rec_red::ih_tms(sig, c, lv, j, heads, args)),
            ExprSpec::App(Box::new(heads[rshape(sig, c).np as int]), Box::new(x)))),
{
    let sh = rshape(sig, c);
    let rd = sig.ienv.recs[c];
    let np = sh.np;
    let pre = (np + sh.nmin() + 1) as int;
    let h = ExprSpec::Const(c, lv);
    let t0 = crate::ti_syntax::dty_at(sig, c, lv);
    let ps = heads.subrange(0, np as int);
    let ri = crate::dom_rec_ty::rinst(sig, c, lv);
    let ci = spine_app(ExprSpec::Const(sh.ind, ri), ps);
    let cc = ExprSpec::Const(sh.ctors[j], cl);
    let ccr = ExprSpec::Const(sh.ctors[j], ri);
    let cx = spine_app(cc, pargs + args);
    let (xs, xs1) = (heads.push(x), heads.push(cx));
    let p = heads[np as int];
    let t = ExprSpec::App(Box::new(p), Box::new(x));
    let ty1 = ExprSpec::App(Box::new(p), Box::new(cx));
    let dh = crate::ti_sub::get(sig, eq(g, h, h, t0));
    let w = crate::ti_meta::d_wf(sig, dh);
    crate::ti_meta::mk_d(sig, w);
    crate::dom_iota::major_form(sig, c, lv);
    // the major, reduced in place: congruence
    assert forall|i: int| 0 <= i < heads.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(t0, heads.subrange(0, i))) by {
        crate::dom_rec_end::rec_trest_pi(sig, c, lv, heads, i);
    }
    assert forall|i: int| 0 <= i < heads.len() implies derivable(sig, eq(g, #[trigger] heads[i], heads[i], crate::ti_spine::sdom(t0, heads, i))) by {
        crate::dom_rec_end::rec_trest_pi(sig, c, lv, heads, i);
    }
    crate::dom_rec_end::spine_build2(sig, g, h, h, t0, heads, heads);
    let f = spine_app(h, heads);
    let tt = crate::dom_con_rel::trest(t0, heads);
    crate::dom_rec_end::rec_trest_pi(sig, c, lv, xs, pre);
    crate::dom_rec_end::major_dom(sig, c, lv, xs);
    assert(xs.subrange(0, pre) =~= heads);
    assert(xs.subrange(0, np as int) =~= ps);
    let bb = *tt->Bind_2;
    assert(tt == pi(ci, bb));
    crate::ti_spine::pi_typed_of(sig, g, f, ci, bb);
    crate::ti_chain::tchain_refl(sig, g, tt);
    crate::dom_sem_rel::app_pair(sig, g, f, f, tt, ci, bb, x, cx);
    crate::dom_bound::spine_push(h, xs);
    crate::dom_bound::spine_push(h, xs1);
    assert(xs1.subrange(0, pre) =~= heads);
    crate::dom_con_rel::trest_push(t0, heads, x);
    crate::dom_rec_minor::rec_tend(sig, c, lv, xs);
    let (m, m1) = (spine_app(h, xs), spine_app(h, xs1));
    // the Iota step, and the rule's Beta chain
    crate::dom_rec_red::rec_red(sig, c, lv, cl, heads, x, j, pargs, args);
    let body = crate::expr_model::subst_expr_levels(rd.rules[j].rhs, rd.uparams, lv);
    let n1 = spine_app(body, heads + args);
    let r = spine_app(heads[np + 1 + j], args + crate::dom_rec_red::ih_tms(sig, c, lv, j, heads, args));
    rule_beta(sig, g, c, lv, j, heads, args);
    let ty0 = ExprSpec::App(Box::new(p), Box::new(spine_app(ccr, ps + args)));
    // the motive at the constructor at the recursor's parameters, then at
    // the constructor application, then at the major
    crate::dom_rec_minor::rec_dom(sig, c, lv, heads, np as int);
    assert(heads.subrange(0, np as int) =~= ps);
    assert(derivable(sig, eq(g, p, p, crate::ti_spine::vsub(rtds(sig, c, lv)[np as int], ps))));
    crate::dom_adeq_syn::dsym(sig, g, x, cx, ci);
    // at the recursor's instance, the constructor is equal to its own
    crate::dom_rec_end::rec_canon_ok(sig, c);
    crate::dom_rec_ty::scope_ctor(sig, c, j);
    crate::dom_rec_ty::scope_ctor_ind(sig, c);
    crate::dom_rec_ty::rec_lps_sub(sig, c);
    crate::dom_ctor_bound::ctor_shape(sig, sh.ind, j);
    crate::dom_rec_end::rec_model_at(sig, c, ri);
    crate::iota_sr::ctor_lv(sig, g, c, j, ri, cl);
    crate::iota_sr::ctor_at(sig, c, j, ri);
    crate::dom_rec_minor::rec_dom(sig, c, lv, heads, np as int);
    crate::iota_sr::sr_result(sig, g, c, lv, j, cl, heads, pargs, args);
    // at the major: the motive's application to the major's conversion
    let l = crate::iota_sr::motive_at(sig, c, lv, j, ps);
    let mt = crate::ti_syntax::pi(ci, sort(l));
    crate::ti_spine::pi_typed_of(sig, g, p, ci, sort(l));
    crate::ti_chain::tchain_refl(sig, g, mt);
    crate::dom_sem_rel::app_pair(sig, g, p, p, mt, ci, sort(l), cx, x);
    assert(crate::subst_algebra::inst(0, cx, sort(l)) == sort(l));
    let dt = crate::ti_sub::get(sig, eq(g, ty1, t, sort(l)));
    crate::ti_sub::mk_t(sig, dt, l);
    crate::ti_chain::tchain_one(sig, g, ty1, t);
    crate::ti_chain::tchain_trans(sig, g, ty0, ty1, t);
    crate::dom_adeq_syn::dsym(sig, g, n1, r, ty0);
    crate::ti_chain::conv_chain(sig, g, n1, n1, ty0, t);
    crate::ti_chain::conv_chain(sig, g, n1, r, ty0, t);
    // the Iota node
    crate::dom_adeq_syn::dsym(sig, g, m, m1, t);
    let d0 = crate::ti_sub::get(sig, eq(g, m1, m1, t));
    let d1 = crate::ti_sub::get(sig, eq(g, n1, n1, t));
    crate::dom_adeq_syn::dsym(sig, g, ty1, t, sort(l));
    let d2 = crate::ti_sub::get(sig, eq(g, t, t, sort(l)));
    let jd = eq(g, m1, n1, t);
    // the parameter premises: the recursor's parameters are the
    // constructor's own
    let pj = crate::ti_syntax::iota_pjs(sig, g, m1);
    reveal(crate::ti_syntax::iota_pjs);
    crate::beta_model::spine_destruct_app(h, xs1);
    crate::beta_model::spine_destruct_app(cc, pargs + args);
    assert(rd.num_params == np);
    assert(rd.major_idx == pre);
    assert(crate::ti_syntax::iota_lv(sig, m1)) by { reveal(crate::ti_syntax::iota_lv); }
    if crate::ti_syntax::iota_prop(sig, m1) {
        reveal(crate::ti_syntax::iota_prop);
        assert(l == LevelSpec::Zero);
        assert forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(l, rho) == 0 by {}
    }
    assert forall|q: int| 0 <= q < pj.len() implies derivable(sig, #[trigger] pj[q]) by {
        crate::ti_syntax::iota_pdom_id(sig, m1, q);
        let _pq = crate::dom_rec_ty::rshape(sig, c).pdoms[q];
        assert(xs1[q] == heads[q] && (pargs + args)[q] == pargs[q]);
    }
    let ps2 = seq![d0, d1, d2] + Seq::new(pj.len(), |q: int| crate::ti_sub::pick(sig, pj[q]));
    assert forall|q: int| 0 <= q < pj.len() implies crate::ti_syntax::valid(sig, #[trigger] crate::ti_sub::pick(sig, pj[q]))
        && crate::ti_syntax::concl(crate::ti_sub::pick(sig, pj[q])) == pj[q] by {
        let dq = crate::ti_sub::get(sig, pj[q]);
        crate::ti_sub::pick_of(sig, dq);
    }
    assert(crate::ti_syntax::prems(ps2, seq![eq(g, m1, m1, t), eq(g, n1, n1, t), eq(g, t, t, sort(l))] + pj));
    crate::ti_meta::valid_node(sig, Rule::Iota(l), jd, ps2);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(Rule::Iota(l), jd, ps2));
    crate::dom_adeq_syn::dtrans(sig, g, m, m1, n1, t);
    crate::dom_adeq_syn::dtrans(sig, g, m, n1, r, t);
}

/// SUBJECT REDUCTION'S IOTA FACTS, from the model's: a recursor of a
/// signature in the fragment has its rules' right-hand sides typed at
/// their rule types.
pub proof fn sr_ok_of(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int)
    requires
        crate::dom_rec_end::sig_sr(sig),
        crate::ti_syntax::iota_ok(sig),
        sig.ienv.recs.contains_key(rid),
        lv.len() == sig.ienv.recs[rid].uparams.len(),
        0 <= p < rshape(sig, rid).nmin(),
    ensures
        crate::iota_sr::sr_ok(sig, rid, lv, p),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    assert(crate::dom_rec_end::rec_frag(sig, rid));
    assert(!crate::ti_syntax::no_recs(sig));
    reveal(crate::dom_rec_end::sig_rec);
    assert(crate::dom_rec_end::rec_model(sig, rid));
    assert(rule_typed(sig, rid, lv, p));
    let ss = crate::ti_strip::strip(sig);
    let ctx = rule_ctx(sig, rid, lv, p);
    let (b, bt) = (crate::dom_iota::rule_body(sig, rid, lv, p), rule_bty(sig, rid, lv, p));
    let lb = choose|lb: LevelSpec| #[trigger] derivable(ss, eq(ctx, bt, bt, sort(lb)));
    assert(Seq::<ExprSpec>::empty() + ctx =~= ctx);
    crate::ti_beta::lam_tele(ss, Seq::empty(), ctx, b, bt, lb);
    let (lt, pt) = (crate::rec_canon::binds(BinderKind::Lam, ctx, b), crate::rec_canon::binds(BinderKind::Pi, ctx, bt));
    crate::ti_strip::strip_derivable(sig, eq(Seq::empty(), lt, lt, pt));
    crate::dom_iota::rule_split(sig, rid, lv, p);
    crate::iota_sr::rule_ty_split(sig, rid, lv, p);
    crate::dom_rec_ty::rec_lps_sub(sig, rid);
    crate::dom_rec_end::rec_model_at(sig, rid, crate::dom_rec_ty::rinst(sig, rid, lv));
    assert(crate::dom_rec_end::ty_closed(crate::ti_strip::strip(sig), crate::ti_syntax::dty_at(sig, sh.ctors[p], Seq::empty())));
}

} // verus!
