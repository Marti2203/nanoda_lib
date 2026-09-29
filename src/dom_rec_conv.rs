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
/// applied to the fields.
pub proof fn bty_inst(sig: Sig, c: u64, j: int, zs: Seq<ExprSpec>)
    requires
        rshape(sig, c).np == 0,
        0 <= j < rshape(sig, c).nmin(),
        zs.len() == rshape(sig, c).nmin() + 1 + rshape(sig, c).fields[j].len(),
    ensures ({
        let pre = (rshape(sig, c).nmin() + 1) as int;
        psub(rule_bty(sig, c, j), tsub(zs, zs.len())) == ExprSpec::App(Box::new(zs[0]),
            Box::new(spine_app(ExprSpec::Const(rshape(sig, c).ctors[j], Seq::empty()), zs.subrange(pre, zs.len() as int))))
    }),
{
    let sh = rshape(sig, c);
    let nf = sh.fields[j].len();
    let n = zs.len();
    let pre = (sh.nmin() + 1) as int;
    let s = tsub(zs, n);
    let h = ExprSpec::Const(sh.ctors[j], Seq::empty());
    let vs = crate::rec_canon::vars(0, nf);
    crate::ti_beta::tsub_at(zs, n, sh.nmin() + nf);
    crate::ti_subst::psub_spine_app(s, h, vs);
    assert forall|i: int| 0 <= i < nf implies #[trigger] crate::ti_subst::spsub(vs, s)[i] == zs.subrange(pre, n as int)[i] by {
        crate::ti_beta::tsub_at(zs, n, (nf - 1 - i) as nat);
    }
    assert(crate::ti_subst::spsub(vs, s) =~= zs.subrange(pre, n as int));
    assert(psub(ExprSpec::Var(sh.nmin() + nf), s) == zs[0]);
    assert(psub(h, s) == h);
    let e = ExprSpec::App(Box::new(ExprSpec::Var(sh.nmin() + nf)), Box::new(spine_app(h, vs)));
    assert(psub(e, s) == ExprSpec::App(Box::new(psub(ExprSpec::Var(sh.nmin() + nf), s)), Box::new(psub(spine_app(h, vs), s))));
}

/// THE RULE'S BETA CHAIN at the recursor's arguments: its instance converts
/// with its body under them, at the motive at the constructor application.
#[verifier::spinoff_prover]
pub proof fn rule_beta(sig: Sig, g: Ctx, c: u64, lv: Seq<LevelSpec>, j: int, heads: Seq<ExprSpec>, args: Seq<ExprSpec>)
    requires
        rec_hyps(sig, c),
        lv.len() == sig.ienv.recs[c].uparams.len(),
        0 <= j < rshape(sig, c).nmin(),
        heads.len() == rshape(sig, c).nmin() + 1,
        args.len() == rshape(sig, c).fields[j].len(),
        derivable(sig, Jd::Wf(g)),
        forall|i: int| 0 <= i < heads.len() ==> derivable(sig, eq(g, #[trigger] heads[i], heads[i],
            crate::dom_rel::tel_dom(crate::ti_syntax::dty_at(sig, c, lv), heads, i as nat))),
        forall|k: int| 0 <= k < args.len() ==> derivable(sig, eq(g, #[trigger] args[k], args[k], rshape(sig, c).fields[j][k])),
    ensures ({
        let rd = sig.ienv.recs[c];
        let body = crate::expr_model::subst_expr_levels(rd.rules[j].rhs, rd.uparams, lv);
        let zs = heads + args;
        let r = spine_app(heads[1 + j], args + crate::dom_rec_red::ih_tms(sig, c, lv, j, heads, args));
        let ty = ExprSpec::App(Box::new(heads[0]), Box::new(spine_app(ExprSpec::Const(rshape(sig, c).ctors[j], Seq::empty()), args)));
        derivable(sig, eq(g, spine_app(body, zs), r, ty))
    }),
{
    let sh = rshape(sig, c);
    let rd = sig.ienv.recs[c];
    let (nmin, nf) = (sh.nmin(), sh.fields[j].len());
    let pre = (nmin + 1) as int;
    let ctx = rule_ctx(sig, c, lv, j);
    let (b, bt) = (crate::dom_iota::rule_body(sig, c, lv, j), rule_bty(sig, c, j));
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
            assert(crate::dom_rec_minor::fields_plain(sig, c, lv, j));
            crate::subst_algebra::lift_closed((1 + nmin) as nat, k as nat, sh.fields[j][k]);
            assert(ctx[i] == crate::dom_iota::ftds(sig, c, lv, j)[k]);
            assert(ctx[i] == sh.fields[j][k]);
            crate::ti_subst::psub_closed(ctx[i], tsub(zs, i as nat));
        }
    }
    assert(crate::ti_beta::beta_pre(sig, g, ctx, b, bt, lb, zs));
    crate::ti_beta::beta_upto(sig, g, ctx, b, bt, lb, zs, n);
    assert(zs.subrange(0, n as int) =~= zs);
    assert(ctx.subrange(n as int, n as int) =~= Seq::<ExprSpec>::empty());
    bty_inst(sig, c, j, zs);
    assert(zs.subrange(pre, n as int) =~= args);
    assert(zs[0] == heads[0]);
    crate::ti_beta::vsub_tsub(b, zs);
    crate::dom_rec_red::rule_vsub(sig, c, lv, j, heads, args);
}

/// THE REDEX CONVERTS WITH ITS REDUCT, one side: the recursor applied up
/// to a major that reduces to a constructor application converts, at the
/// motive at the major, with the minor at the fields and the recursive
/// calls.
#[verifier::spinoff_prover]
pub proof fn rec_conv_side(sig: Sig, g: Ctx, c: u64, lv: Seq<LevelSpec>, heads: Seq<ExprSpec>, x: ExprSpec, j: int, args: Seq<ExprSpec>)
    requires
        rec_hyps(sig, c),
        lv.len() == sig.ienv.recs[c].uparams.len(),
        0 <= j < rshape(sig, c).nmin(),
        heads.len() == rshape(sig, c).nmin() + 1,
        args.len() == rshape(sig, c).fields[j].len(),
        derivable(sig, eq(g, ExprSpec::Const(c, lv), ExprSpec::Const(c, lv), crate::ti_syntax::dty_at(sig, c, lv))),
        forall|i: int| 0 <= i < heads.len() ==> derivable(sig, eq(g, #[trigger] heads[i], heads[i],
            crate::dom_rel::tel_dom(crate::ti_syntax::dty_at(sig, c, lv), heads, i as nat))),
        derivable(sig, eq(g, x, spine_app(ExprSpec::Const(rshape(sig, c).ctors[j], Seq::empty()), args),
            ExprSpec::Const(rshape(sig, c).ind, Seq::empty()))),
        crate::ti_hred::hred(sig, x, spine_app(ExprSpec::Const(rshape(sig, c).ctors[j], Seq::empty()), args)),
        forall|k: int| 0 <= k < args.len() ==> derivable(sig, eq(g, #[trigger] args[k], args[k], rshape(sig, c).fields[j][k])),
    ensures
        derivable(sig, eq(g, spine_app(ExprSpec::Const(c, lv), heads.push(x)),
            spine_app(heads[1 + j], args + crate::dom_rec_red::ih_tms(sig, c, lv, j, heads, args)),
            ExprSpec::App(Box::new(heads[0]), Box::new(x)))),
{
    let sh = rshape(sig, c);
    let rd = sig.ienv.recs[c];
    let pre = (sh.nmin() + 1) as int;
    let h = ExprSpec::Const(c, lv);
    let t0 = crate::ti_syntax::dty_at(sig, c, lv);
    let ci = ExprSpec::Const(sh.ind, Seq::empty());
    let cx = spine_app(ExprSpec::Const(sh.ctors[j], Seq::empty()), args);
    let (xs, xs1) = (heads.push(x), heads.push(cx));
    let p = heads[0];
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
    crate::dom_rec_red::rec_red(sig, c, lv, heads, x, j, args);
    let body = crate::expr_model::subst_expr_levels(rd.rules[j].rhs, rd.uparams, lv);
    let n1 = spine_app(body, heads + args);
    let r = spine_app(heads[1 + j], args + crate::dom_rec_red::ih_tms(sig, c, lv, j, heads, args));
    rule_beta(sig, g, c, lv, j, heads, args);
    // the motive at the constructor application, converted to at the major
    crate::dom_rec_minor::rec_dom(sig, c, lv, heads, 0);
    assert(heads.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
    crate::dom_rec_end::motive_form(sig, c, lv);
    let mt = rtds(sig, c, lv)[0];
    let so = *mt->Bind_2;
    assert(mt == pi(ci, so));
    crate::ti_spine::pi_typed_of(sig, g, p, ci, so);
    crate::ti_chain::tchain_refl(sig, g, mt);
    crate::dom_adeq_syn::dsym(sig, g, x, cx, ci);
    crate::dom_sem_rel::app_pair(sig, g, p, p, mt, ci, so, cx, x);
    assert(crate::subst_algebra::inst(0, cx, so) == so);
    let lm = so->Sort_0;
    assert(so == sort(lm));
    let dt = crate::ti_sub::get(sig, eq(g, ty1, t, sort(lm)));
    crate::ti_sub::mk_t(sig, dt, lm);
    crate::ti_chain::tchain_one(sig, g, ty1, t);
    crate::dom_adeq_syn::dsym(sig, g, n1, r, ty1);
    crate::ti_chain::conv_chain(sig, g, n1, n1, ty1, t);
    crate::ti_chain::conv_chain(sig, g, n1, r, ty1, t);
    // the Iota node
    crate::dom_adeq_syn::dsym(sig, g, m, m1, t);
    let d0 = crate::ti_sub::get(sig, eq(g, m1, m1, t));
    let d1 = crate::ti_sub::get(sig, eq(g, n1, n1, t));
    let jd = eq(g, m1, n1, t);
    let ps = seq![d0, d1];
    assert(crate::ti_syntax::prems(ps, seq![eq(g, m1, m1, t), eq(g, n1, n1, t)]));
    crate::ti_meta::valid_node(sig, Rule::Iota, jd, ps);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(Rule::Iota, jd, ps));
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
    let (b, bt) = (crate::dom_iota::rule_body(sig, rid, lv, p), rule_bty(sig, rid, p));
    let lb = choose|lb: LevelSpec| #[trigger] derivable(ss, eq(ctx, bt, bt, sort(lb)));
    assert(Seq::<ExprSpec>::empty() + ctx =~= ctx);
    crate::ti_beta::lam_tele(ss, Seq::empty(), ctx, b, bt, lb);
    let (lt, pt) = (crate::rec_canon::binds(BinderKind::Lam, ctx, b), crate::rec_canon::binds(BinderKind::Pi, ctx, bt));
    crate::ti_strip::strip_derivable(sig, eq(Seq::empty(), lt, lt, pt));
    crate::dom_iota::rule_split(sig, rid, lv, p);
    crate::iota_sr::rule_ty_split(sig, rid, lv, p);
    let nf = sh.fields[p].len();
    assert(crate::rec_canon::vars(1 + sh.nmin() + nf, sh.np) + crate::rec_canon::vars(0, nf) =~= crate::rec_canon::vars(0, nf));
    assert(crate::iota_sr::rbty(sig, rid, p) == bt);
    assert(crate::dom_rec_minor::fields_plain(sig, rid, lv, p));
}

} // verus!
