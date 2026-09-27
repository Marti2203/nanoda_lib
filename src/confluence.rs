//! CHURCH-ROSSER FOR PARALLEL REDUCTION (Takahashi). `complete(env, e)`
//! contracts every redex `pstep` can contract in `e`; every step out of
//! `e` lands one step short of it (`takahashi`), which gives the diamond,
//! the strip lemma and confluence of `pstep_star`, with no size or index
//! caps (indices are unbounded).
//!
//! `env_conf` is what confluence needs of the environment: definitions have
//! no loose bound variable, and no redex head is a definition -- delta must
//! not compete with iota, folding, quotients or literal expansion at the
//! same node. The kernel itself folds `Nat.add` on literals while `Nat.add`
//! is also a definition, trusting the two to agree; that agreement is a
//! separate hypothesis where conversion is related to reduction, not
//! something confluence can prove.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::beta_model::*;
#[cfg(verus_only)]
use crate::expr_model::{nlbv, NatLitPayload};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{EnvSpec, nat_bin_op_of, nat_succ_id, nat_zero_id, quot_kind_of};
#[cfg(verus_only)]
use crate::tc_model::{quot_ready, quot_result, quot_major_idx, quot_mk_spine};
#[cfg(verus_only)]
use crate::subst_algebra::{env_bv_free, pstep_inst, subst1_is_inst};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// An identifier that heads a redex other than delta.
pub open spec fn redex_head(env: EnvSpec, id: u64) -> bool {
    ||| env.rec_data(id) is Some
    ||| env.ctor_num_params(id) is Some
    ||| (env.nat_fold && nat_bin_op_of(env.export, id) is Some)
    ||| quot_kind_of(env.export, id) is Some
    ||| id == nat_zero_id(env.export)
    ||| id == nat_succ_id(env.export)
}

/// WHAT CONFLUENCE NEEDS OF THE ENVIRONMENT.
pub open spec fn env_conf(env: EnvSpec) -> bool {
    &&& env_bv_free(env)
    // no redex head is a definition
    &&& forall|id: u64| #[trigger] env.defs.contains_key(id) ==> !redex_head(env, id)
    // the redex kinds have distinct heads
    &&& forall|id: u64| #[trigger] env.rec_data(id) is Some ==> env.ctor_num_params(id) is None
        && nat_bin_op_of(env.export, id) is None && quot_kind_of(env.export, id) is None
    &&& forall|id: u64| #[trigger] env.ctor_num_params(id) is Some ==> nat_bin_op_of(env.export, id) is None
        && quot_kind_of(env.export, id) is None
    &&& forall|id: u64| #[trigger] nat_bin_op_of(env.export, id) is Some ==> quot_kind_of(env.export, id) is None
    // the numeral constructors head no other redex
    &&& env.rec_data(nat_zero_id(env.export)) is None && nat_bin_op_of(env.export, nat_zero_id(env.export)) is None
        && quot_kind_of(env.export, nat_zero_id(env.export)) is None
    &&& env.rec_data(nat_succ_id(env.export)) is None && nat_bin_op_of(env.export, nat_succ_id(env.export)) is None
        && quot_kind_of(env.export, nat_succ_id(env.export)) is None
}

/// The projection's decision form: the structure is an applied constructor
/// with enough arguments.
pub open spec fn proj_ready(env: EnvSpec, pidx: usize, s: ExprSpec) -> bool {
    match spine_head(s) {
        ExprSpec::Const(cid, _) => match env.ctor_num_params(cid) {
            Some(np) => (np as nat + pidx as nat) < spine_args(s).len(),
            None => false,
        },
        _ => false,
    }
}

pub open spec fn proj_result(env: EnvSpec, pidx: usize, s: ExprSpec) -> ExprSpec {
    match spine_head(s) {
        ExprSpec::Const(cid, _) => match env.ctor_num_params(cid) {
            Some(np) => spine_args(s)[(np as nat + pidx as nat) as int],
            None => s,
        },
        _ => s,
    }
}

/// The application's contraction, when one of the head rules applies.
pub open spec fn app_develop(env: EnvSpec, app: ExprSpec) -> ExprSpec {
    if rec_ready(env, app) {
        rec_result(env, app)
    } else if env.nat_fold && nat_fold_ready(env.export, app) {
        nat_fold_result(env.export, app)
    } else if quot_ready(env.export, app) {
        quot_result(env.export, app)
    } else {
        app
    }
}

/// THE COMPLETE DEVELOPMENT: every redex `pstep` can contract, contracted.
pub open spec fn complete(env: EnvSpec, e: ExprSpec) -> ExprSpec
    decreases e,
{
    match e {
        ExprSpec::Const(id, ls) => if env.contains_key(id) && env[id].0.len() == ls.len() {
            crate::expr_model::subst_expr_levels(env[id].1, env[id].0, ls)
        } else {
            e
        },
        ExprSpec::NatLit(n) => if n.0@ == 0 {
            const_expr_no_levels(nat_zero_id(env.export))
        } else {
            ExprSpec::App(
                Box::new(const_expr_no_levels(nat_succ_id(env.export))),
                Box::new(ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)))),
            )
        },
        ExprSpec::StringLit(len) => string_lit_expand_model(env.export, len.0@),
        ExprSpec::App(f, a) => match *f {
            ExprSpec::Bind(BinderKind::Lam, _, body) => subst1(complete(env, *body), complete(env, *a)),
            _ => app_develop(env, ExprSpec::App(Box::new(complete(env, *f)), Box::new(complete(env, *a)))),
        },
        ExprSpec::Bind(bk, t, b) => ExprSpec::Bind(bk, Box::new(complete(env, *t)), Box::new(complete(env, *b))),
        ExprSpec::Let(t, v, b) => subst1(complete(env, *b), complete(env, *v)),
        ExprSpec::Proj(pidx, s) => {
            let cs = complete(env, *s);
            if proj_ready(env, pidx, cs) {
                proj_result(env, pidx, cs)
            } else {
                ExprSpec::Proj(pidx, Box::new(cs))
            }
        },
        _ => e,
    }
}

/// The decision form's result is an `iota_extract`.
pub proof fn proj_ready_extract(env: EnvSpec, pidx: usize, s: ExprSpec)
    requires
        proj_ready(env, pidx, s),
    ensures
        iota_extract(env, pidx, s, proj_result(env, pidx, s)),
{
    spine_recompose(s);
    if let ExprSpec::Const(cid, lv) = spine_head(s) {
        let np = env.ctor_num_params(cid)->Some_0;
        let args2 = spine_args(s);
        assert(s == spine_app(ExprSpec::Const(cid, lv), args2));
        assert(proj_result(env, pidx, s) == args2[(np as nat + pidx as nat) as int]);
    }
}

/// EVERY TERM STEPS TO ITS COMPLETE DEVELOPMENT.
pub proof fn pstep_complete(env: EnvSpec, e: ExprSpec)
    ensures
        pstep(env, e, complete(env, e)),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            pstep_complete(env, *a);
            match *f {
                ExprSpec::Bind(BinderKind::Lam, t, body) => {
                    pstep_complete(env, *body);
                    assert(pstep(env, *body, complete(env, *body)) && pstep(env, *a, complete(env, *a))
                        && complete(env, e) == subst1(complete(env, *body), complete(env, *a)));
                },
                _ => {
                    pstep_complete(env, *f);
                    let cf = complete(env, *f);
                    let ca = complete(env, *a);
                    let app = ExprSpec::App(Box::new(cf), Box::new(ca));
                    if rec_ready(env, app) {
                        pstep_rec_intro(env, f, a, cf, ca, complete(env, e));
                    } else if env.nat_fold && nat_fold_ready(env.export, app) {
                        pstep_fold_intro(env, f, a, cf, ca, complete(env, e));
                    } else if quot_ready(env.export, app) {
                        pstep_quot_intro(env, f, a, cf, ca, complete(env, e));
                    } else {
                        assert(pstep(env, *f, cf) && pstep(env, *a, ca) && complete(env, e) == app);
                    }
                },
            }
        },
        ExprSpec::Bind(bk, t, b) => {
            pstep_complete(env, *t);
            pstep_complete(env, *b);
            assert(pstep(env, *t, complete(env, *t)) && pstep(env, *b, complete(env, *b)));
        },
        ExprSpec::Let(t, v, b) => {
            pstep_complete(env, *v);
            pstep_complete(env, *b);
            assert(pstep(env, *b, complete(env, *b)) && pstep(env, *v, complete(env, *v)));
        },
        ExprSpec::Proj(pidx, s) => {
            pstep_complete(env, *s);
            let cs = complete(env, *s);
            if proj_ready(env, pidx, cs) {
                proj_ready_extract(env, pidx, cs);
                assert(iota_reduct(cs));
            }
        },
        _ => {},
    }
}

/// Pointwise steps.
pub open spec fn pw(env: EnvSpec, a: Seq<ExprSpec>, b: Seq<ExprSpec>) -> bool {
    &&& a.len() == b.len()
    &&& forall|i: int| 0 <= i < a.len() ==> #[trigger] pstep(env, a[i], b[i])
}

/// How an application stepped, with the reducts: 0 refl, 1 beta (body,
/// argument), 2 congruence, 3 recursor, 4 fold, 5 quotient.
pub proof fn pstep_app_destruct(env: EnvSpec, f: ExprSpec, a: ExprSpec, e2: ExprSpec) -> (r: (u8, ExprSpec, ExprSpec))
    requires
        pstep(env, ExprSpec::App(Box::new(f), Box::new(a)), e2),
    ensures
        ({
            let (kind, x, y) = r;
            &&& kind <= 5
            &&& kind == 0 ==> e2 == ExprSpec::App(Box::new(f), Box::new(a))
            &&& kind == 1 ==> (f is Bind && f->Bind_0 == BinderKind::Lam && pstep(env, *f->Bind_2, x) && pstep(env, a, y) && e2 == subst1(x, y))
            &&& kind == 2 ==> (pstep(env, f, x) && pstep(env, a, y) && e2 == ExprSpec::App(Box::new(x), Box::new(y)))
            &&& kind == 3 ==> (pstep(env, f, x) && pstep(env, a, y) && rec_ready(env, ExprSpec::App(Box::new(x), Box::new(y)))
                && e2 == rec_result(env, ExprSpec::App(Box::new(x), Box::new(y))))
            &&& kind == 4 ==> (pstep(env, f, x) && pstep(env, a, y) && env.nat_fold && nat_fold_ready(env.export, ExprSpec::App(Box::new(x), Box::new(y)))
                && e2 == nat_fold_result(env.export, ExprSpec::App(Box::new(x), Box::new(y))))
            &&& kind == 5 ==> (pstep(env, f, x) && pstep(env, a, y) && quot_ready(env.export, ExprSpec::App(Box::new(x), Box::new(y)))
                && e2 == quot_result(env.export, ExprSpec::App(Box::new(x), Box::new(y))))
        }),
{
    let e = ExprSpec::App(Box::new(f), Box::new(a));
    if e2 == e {
        return (0u8, f, a);
    }
    if pstep_rec(env, f, a, e2) {
        let (x, y) = pstep_rec_destruct(env, f, a, e2);
        return (3u8, x, y);
    }
    if pstep_fold(env, f, a, e2) {
        let (x, y) = pstep_fold_destruct(env, f, a, e2);
        return (4u8, x, y);
    }
    if pstep_quot(env, f, a, e2) {
        let (x, y) = pstep_quot_destruct(env, f, a, e2);
        return (5u8, x, y);
    }
    if let ExprSpec::Bind(BinderKind::Lam, t, body) = f {
        if exists|body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
            pstep(env, *body, body2) && pstep(env, a, a2) && e2 == subst1(body2, a2) {
            let (x, y) = choose|body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                pstep(env, *body, body2) && pstep(env, a, a2) && e2 == subst1(body2, a2);
            return (1u8, x, y);
        }
    }
    let (x, y) = choose|f2: ExprSpec, a2: ExprSpec|
        pstep(env, f, f2) && pstep(env, a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
    (2u8, x, y)
}

/// Stepping the head and the arguments steps the spine.
pub proof fn pstep_spine_congr(env: EnvSpec, h: ExprSpec, h2: ExprSpec, args: Seq<ExprSpec>, args2: Seq<ExprSpec>)
    requires
        pstep(env, h, h2),
        pw(env, args, args2),
    ensures
        pstep(env, spine_app(h, args), spine_app(h2, args2)),
    decreases args.len(),
{
    if args.len() > 0 {
        let n = args.len() - 1;
        let i1 = args.subrange(0, n);
        let i2 = args2.subrange(0, n);
        assert(args =~= i1.push(args[n]));
        assert(args2 =~= i2.push(args2[n]));
        assert(pstep(env, args[n], args2[n]));
        pstep_spine_congr(env, h, h2, i1, i2);
        spine_app_compose_last(h, i1, args[n]);
        spine_app_compose_last(h2, i2, args2[n]);
        assert(pstep(env, spine_app(h, i1), spine_app(h2, i2)) && pstep(env, args[n], args2[n]));
    }
}

/// A head no rule but congruence applies to.
pub open spec fn inert_head(env: EnvSpec, id: u64, nargs: nat) -> bool {
    &&& !env.defs.contains_key(id)
    &&& env.rec_data(id) is None
    // a quotient eliminator short of its major premise, or none
    &&& (quot_kind_of(env.export, id) != Some(0u8) || nargs <= 5)
    &&& (quot_kind_of(env.export, id) != Some(1u8) || nargs <= 4)
    &&& (nat_bin_op_of(env.export, id) is None || nargs < 2)
}

/// A spine with an inert head steps pointwise.
pub proof fn inert_spine_step(env: EnvSpec, id: u64, lv: Seq<crate::level_model::LevelSpec>, args: Seq<ExprSpec>, t: ExprSpec) -> (args3: Seq<ExprSpec>)
    requires
        inert_head(env, id, args.len()),
        pstep(env, spine_app(ExprSpec::Const(id, lv), args), t),
    ensures
        pw(env, args, args3),
        t == spine_app(ExprSpec::Const(id, lv), args3),
    decreases args.len(),
{
    let h = ExprSpec::Const(id, lv);
    if args.len() == 0 {
        assert(t == h);
        return args;
    }
    let n = args.len() - 1;
    let init = args.subrange(0, n);
    let x = args[n];
    assert(args =~= init.push(x));
    spine_app_compose_last(h, init, x);
    let (kind, f2, x2) = pstep_app_destruct(env, spine_app(h, init), x, t);
    if kind == 0 {
        assert forall|i: int| 0 <= i < args.len() implies #[trigger] pstep(env, args[i], args[i]) by {}
        return args;
    }
    assert(!(spine_app(h, init) is Bind)) by {
        spine_head_spine_app(h, init);
    }
    let init3 = inert_spine_step(env, id, lv, init, f2);
    spine_head_spine_app(h, init3);
    let app2 = ExprSpec::App(Box::new(f2), Box::new(x2));
    spine_app_compose_last(h, init3, x2);
    spine_destruct_app(h, init3.push(x2));
    if kind == 3 || kind == 4 || kind == 5 {
        assert(spine_head(app2) == h);
        assert(spine_args(app2).len() == args.len());
        assert(false);
    }
    let args3 = init3.push(x2);
    assert forall|i: int| 0 <= i < args.len() implies #[trigger] pstep(env, args[i], args3[i]) by {
        if i < n {
            assert(args[i] == init[i] && args3[i] == init3[i]);
        }
    }
    args3
}

/// A constructor head is inert under `env_conf`.
pub proof fn ctor_inert(env: EnvSpec, cid: u64, n: nat)
    requires
        env_conf(env),
        env.ctor_num_params(cid) is Some,
    ensures
        inert_head(env, cid, n),
{
    if env.defs.contains_key(cid) {
        assert(!redex_head(env, cid));
    }
    if env.rec_data(cid) is Some {
        assert(env.ctor_num_params(cid) is None);
    }
}

/// One more argument after a ready recursor application.
pub proof fn rec_result_extend(env: EnvSpec, sp: ExprSpec, x: ExprSpec)
    requires
        rec_ready(env, sp),
    ensures
        rec_ready(env, ExprSpec::App(Box::new(sp), Box::new(x))),
        rec_result(env, ExprSpec::App(Box::new(sp), Box::new(x))) == ExprSpec::App(Box::new(rec_result(env, sp)), Box::new(x)),
{
    let (rid, lv, args, rd, major, cid, clv, cargs, ri, body) = rec_unpack(env, sp);
    let h = ExprSpec::Const(rid, lv);
    let args2 = args.push(x);
    spine_app_compose_last(h, args, x);
    spine_destruct_app(h, args2);
    let big = ExprSpec::App(Box::new(sp), Box::new(x));
    assert(big == spine_app(h, args2));
    assert(args2[rd.major_idx as int] == major);
    assert(rec_ready(env, big));
    let (_r, _l, _a, _rd, _m, _c, _cl, _ca, _ri, _b) = rec_unpack(env, big);
    let t1 = args.subrange((rd.major_idx + 1) as int, args.len() as int);
    let t2 = args2.subrange((rd.major_idx + 1) as int, args2.len() as int);
    assert(t2 =~= t1.push(x));
    assert(args2.subrange(0, rec_prefix(rd) as int) =~= args.subrange(0, rec_prefix(rd) as int));
    let a2 = spine_app(spine_app(body, args.subrange(0, rec_prefix(rd) as int)),
        cargs.subrange((cargs.len() - rd.rules[ri].nfields) as int, cargs.len() as int));
    spine_app_compose_last(a2, t1, x);
}

/// A ready recursor application whose arguments step pointwise stays ready,
/// and its rule instance steps.
#[verifier::spinoff_prover]
pub proof fn rec_result_pw(env: EnvSpec, rid: u64, lv: Seq<crate::level_model::LevelSpec>, args: Seq<ExprSpec>, args3: Seq<ExprSpec>)
    requires
        env_conf(env),
        rec_ready(env, spine_app(ExprSpec::Const(rid, lv), args)),
        pw(env, args, args3),
    ensures
        rec_ready(env, spine_app(ExprSpec::Const(rid, lv), args3)),
        pstep(env, rec_result(env, spine_app(ExprSpec::Const(rid, lv), args)), rec_result(env, spine_app(ExprSpec::Const(rid, lv), args3))),
{
    let h = ExprSpec::Const(rid, lv);
    let s1 = spine_app(h, args);
    let s3 = spine_app(h, args3);
    let (_rid, _lv, _args, rd, major, cid, clv, cargs, ri, body) = rec_unpack(env, s1);
    spine_destruct_app(h, args);
    spine_destruct_app(h, args3);
    let mi = rd.major_idx as int;
    assert(pstep(env, args[mi], args3[mi]));
    ctor_inert(env, cid, cargs.len());
    let cargs3 = inert_spine_step(env, cid, clv, cargs, args3[mi]);
    let major3 = args3[mi];
    spine_destruct_app(ExprSpec::Const(cid, clv), cargs3);
    assert(spine_head(major3) == ExprSpec::Const(cid, clv));
    assert(spine_args(major3) =~= cargs3);
    assert(rec_ready(env, s3));
    let (_r3, _l3, _a3, _rd3, _m3, _c3, _cl3, _ca3, _ri3, _b3) = rec_unpack(env, s3);
    let nf = rd.rules[ri].nfields;
    let pre = args.subrange(0, rec_prefix(rd) as int);
    let pre3 = args3.subrange(0, rec_prefix(rd) as int);
    let fl = cargs.subrange((cargs.len() - nf) as int, cargs.len() as int);
    let fl3 = cargs3.subrange((cargs3.len() - nf) as int, cargs3.len() as int);
    let tr = args.subrange(mi + 1, args.len() as int);
    let tr3 = args3.subrange(mi + 1, args3.len() as int);
    assert forall|i: int| 0 <= i < pre.len() implies #[trigger] pstep(env, pre[i], pre3[i]) by {
        assert(pre[i] == args[i] && pre3[i] == args3[i]);
    }
    assert forall|i: int| 0 <= i < fl.len() implies #[trigger] pstep(env, fl[i], fl3[i]) by {
        assert(fl[i] == cargs[(cargs.len() - nf) + i] && fl3[i] == cargs3[(cargs3.len() - nf) + i]);
    }
    assert forall|i: int| 0 <= i < tr.len() implies #[trigger] pstep(env, tr[i], tr3[i]) by {
        assert(tr[i] == args[mi + 1 + i] && tr3[i] == args3[mi + 1 + i]);
    }
    assert(pstep(env, body, body));
    pstep_spine_congr(env, body, body, pre, pre3);
    pstep_spine_congr(env, spine_app(body, pre), spine_app(body, pre3), fl, fl3);
    pstep_spine_congr(env, spine_app(spine_app(body, pre), fl), spine_app(spine_app(body, pre3), fl3), tr, tr3);
}

/// HOW A RECURSOR SPINE STEPS: pointwise, or pointwise with the rule fired
/// (at one node; the trailing arguments are the rule instance's).
pub proof fn rec_spine_step(env: EnvSpec, rid: u64, lv: Seq<crate::level_model::LevelSpec>, args: Seq<ExprSpec>, t: ExprSpec) -> (r: (Seq<ExprSpec>, bool))
    requires
        env_conf(env),
        env.rec_data(rid) is Some,
        pstep(env, spine_app(ExprSpec::Const(rid, lv), args), t),
    ensures
        pw(env, args, r.0),
        !r.1 ==> t == spine_app(ExprSpec::Const(rid, lv), r.0),
        r.1 ==> rec_ready(env, spine_app(ExprSpec::Const(rid, lv), r.0))
            && t == rec_result(env, spine_app(ExprSpec::Const(rid, lv), r.0)),
    decreases args.len(),
{
    let h = ExprSpec::Const(rid, lv);
    if !env.defs.contains_key(rid) {
    } else {
        assert(!redex_head(env, rid));
    }
    if args.len() == 0 {
        assert(t == h);
        return (args, false);
    }
    let n = args.len() - 1;
    let init = args.subrange(0, n);
    let x = args[n];
    assert(args =~= init.push(x));
    spine_app_compose_last(h, init, x);
    let (kind, f2, x2) = pstep_app_destruct(env, spine_app(h, init), x, t);
    if kind == 0 {
        assert forall|i: int| 0 <= i < args.len() implies #[trigger] pstep(env, args[i], args[i]) by {}
        return (args, false);
    }
    spine_head_spine_app(h, init);
    assert(!(spine_app(h, init) is Bind));
    let (init3, fired) = rec_spine_step(env, rid, lv, init, f2);
    let args3 = init3.push(x2);
    assert forall|i: int| 0 <= i < args.len() implies #[trigger] pstep(env, args[i], args3[i]) by {
        if i < n {
            assert(args[i] == init[i] && args3[i] == init3[i]);
        }
    }
    let app2 = ExprSpec::App(Box::new(f2), Box::new(x2));
    spine_app_compose_last(h, init3, x2);
    spine_destruct_app(h, args3);
    if fired {
        // the rule fired below: the head is the rule body, a binder
        let s3 = spine_app(h, init3);
        let (_r, _l, _a, _rd, _m, _c, _cl, _ca, _ri, body) = rec_unpack(env, s3);
        spine_head_spine_app(rec_result(env, s3), Seq::<ExprSpec>::empty());
        assert(spine_head(app2) == body);
        if kind == 2 {
            rec_result_extend(env, s3, x2);
            return (args3, true);
        }
        assert(!(spine_head(app2) is Const));
        assert(false);
        (args3, true)
    } else {
        assert(spine_head(app2) == h);
        if kind == 2 {
            return (args3, false);
        }
        if kind == 3 {
            return (args3, true);
        }
        // not a fold or quotient head
        assert(nat_bin_op_of(env.export, rid) is None && quot_kind_of(env.export, rid) is None);
        assert(false);
        (args3, false)
    }
}

/// A ready quotient elimination, unpacked.
pub proof fn quot_unpack(env: EnvSpec, sp: ExprSpec) -> (r: (u64, Seq<crate::level_model::LevelSpec>, Seq<ExprSpec>, nat))
    requires
        quot_ready(env.export, sp),
    ensures
        ({
            let (qid, lv, args, qi) = r;
            &&& spine_head(sp) == ExprSpec::Const(qid, lv)
            &&& spine_args(sp) == args
            &&& sp == spine_app(ExprSpec::Const(qid, lv), args)
            &&& quot_major_idx(env.export, sp) == Some(qi)
            &&& (qi == 5 || qi == 4)
            &&& (quot_kind_of(env.export, qid) == Some(0u8) || quot_kind_of(env.export, qid) == Some(1u8))
            &&& (quot_kind_of(env.export, qid) == Some(0u8) ==> qi == 5)
            &&& (quot_kind_of(env.export, qid) == Some(1u8) ==> qi == 4)
            &&& args.len() > qi
            &&& quot_mk_spine(env.export, args[qi as int])
            &&& quot_result(env.export, sp) == spine_app(
                ExprSpec::App(Box::new(args[3int]), Box::new(spine_args(args[qi as int])[2])),
                args.skip(qi as int + 1))
        }),
{
    spine_recompose(sp);
    if let ExprSpec::Const(qid, lv) = spine_head(sp) {
        let qi = quot_major_idx(env.export, sp)->Some_0;
        (qid, lv, spine_args(sp), qi)
    } else {
        assert(false);
        (0u64, Seq::empty(), Seq::empty(), 0nat)
    }
}

/// The spine of a quotient eliminator depends only on its head.
proof fn quot_ready_head(env: EnvSpec, qid: u64, lv: Seq<crate::level_model::LevelSpec>, args: Seq<ExprSpec>)
    requires
        quot_kind_of(env.export, qid) == Some(0u8) || quot_kind_of(env.export, qid) == Some(1u8),
    ensures
        spine_head(spine_app(ExprSpec::Const(qid, lv), args)) == ExprSpec::Const(qid, lv),
        spine_args(spine_app(ExprSpec::Const(qid, lv), args)) == args,
        quot_major_idx(env.export, spine_app(ExprSpec::Const(qid, lv), args))
            == if quot_kind_of(env.export, qid) == Some(0u8) { Some(5nat) } else { Some(4nat) },
{
    spine_destruct_app(ExprSpec::Const(qid, lv), args);
    assert(spine_args(spine_app(ExprSpec::Const(qid, lv), args)) =~= args);
}

pub proof fn quot_result_extend(env: EnvSpec, sp: ExprSpec, x: ExprSpec)
    requires
        quot_ready(env.export, sp),
    ensures
        quot_ready(env.export, ExprSpec::App(Box::new(sp), Box::new(x))),
        quot_result(env.export, ExprSpec::App(Box::new(sp), Box::new(x))) == ExprSpec::App(Box::new(quot_result(env.export, sp)), Box::new(x)),
{
    let (qid, lv, args, qi) = quot_unpack(env, sp);
    let h = ExprSpec::Const(qid, lv);
    let args2 = args.push(x);
    spine_app_compose_last(h, args, x);
    quot_ready_head(env, qid, lv, args2);
    let big = ExprSpec::App(Box::new(sp), Box::new(x));
    assert(big == spine_app(h, args2));
    assert(args2[qi as int] == args[qi as int]);
    assert(args2[3int] == args[3int]);
    assert(quot_ready(env.export, big));
    let (_q, _l, _a, _qi) = quot_unpack(env, big);
    assert(args2.skip(qi as int + 1) =~= args.skip(qi as int + 1).push(x));
    spine_app_compose_last(ExprSpec::App(Box::new(args[3int]), Box::new(spine_args(args[qi as int])[2])), args.skip(qi as int + 1), x);
}

/// `Quot.mk` is inert.
pub proof fn quot_mk_inert(env: EnvSpec, mid: u64, n: nat)
    requires
        env_conf(env),
        quot_kind_of(env.export, mid) == Some(2u8),
    ensures
        inert_head(env, mid, n),
{
    if env.defs.contains_key(mid) {
        assert(!redex_head(env, mid));
    }
    if env.rec_data(mid) is Some {
        assert(quot_kind_of(env.export, mid) is None);
    }
    if nat_bin_op_of(env.export, mid) is Some {
        assert(quot_kind_of(env.export, mid) is None);
    }
}

#[verifier::spinoff_prover]
pub proof fn quot_result_pw(env: EnvSpec, qid: u64, lv: Seq<crate::level_model::LevelSpec>, args: Seq<ExprSpec>, args3: Seq<ExprSpec>)
    requires
        env_conf(env),
        quot_ready(env.export, spine_app(ExprSpec::Const(qid, lv), args)),
        pw(env, args, args3),
    ensures
        quot_ready(env.export, spine_app(ExprSpec::Const(qid, lv), args3)),
        pstep(env, quot_result(env.export, spine_app(ExprSpec::Const(qid, lv), args)),
            quot_result(env.export, spine_app(ExprSpec::Const(qid, lv), args3))),
{
    let h = ExprSpec::Const(qid, lv);
    let s1 = spine_app(h, args);
    let s3 = spine_app(h, args3);
    spine_destruct_app(h, args);
    assert(spine_args(s1) =~= args);
    let (_q, _l, _a, qi) = quot_unpack(env, s1);
    quot_ready_head(env, qid, lv, args3);
    let m = args[qi as int];
    let m3 = args3[qi as int];
    assert(pstep(env, m, m3));
    spine_recompose(m);
    if let ExprSpec::Const(mid, mlv) = spine_head(m) {
        quot_mk_inert(env, mid, spine_args(m).len());
        let margs3 = inert_spine_step(env, mid, mlv, spine_args(m), m3);
        spine_destruct_app(ExprSpec::Const(mid, mlv), margs3);
        assert(spine_args(m3) =~= margs3);
        assert(quot_mk_spine(env.export, m3));
        assert(quot_ready(env.export, s3));
        let (_q3, _l3, _a3, _qi3) = quot_unpack(env, s3);
        assert(pstep(env, spine_args(m)[2], margs3[2]));
        assert(pstep(env, args[3int], args3[3int]));
        let hd = ExprSpec::App(Box::new(args[3int]), Box::new(spine_args(m)[2]));
        let hd3 = ExprSpec::App(Box::new(args3[3int]), Box::new(spine_args(m3)[2]));
        assert(pstep(env, hd, hd3));
        let t = args.skip(qi as int + 1);
        let t3 = args3.skip(qi as int + 1);
        assert forall|i: int| 0 <= i < t.len() implies #[trigger] pstep(env, t[i], t3[i]) by {
            assert(t[i] == args[qi as int + 1 + i] && t3[i] == args3[qi as int + 1 + i]);
        }
        pstep_spine_congr(env, hd, hd3, t, t3);
    }
}

/// HOW A READY QUOTIENT SPINE STEPS: pointwise, or as a step out of its
/// contraction (after the rule fires, the node above may fire anything the
/// function's head allows).
pub proof fn quot_spine_step(env: EnvSpec, qid: u64, lv: Seq<crate::level_model::LevelSpec>, args: Seq<ExprSpec>, t: ExprSpec) -> (r: (Seq<ExprSpec>, bool))
    requires
        env_conf(env),
        quot_kind_of(env.export, qid) == Some(0u8) || quot_kind_of(env.export, qid) == Some(1u8),
        // the source's major premise, when present, is already a `Quot.mk`
        // spine (a term can step INTO one, e.g. by delta, so this is not
        // derivable from the target)
        quot_kind_of(env.export, qid) == Some(0u8) && 5 < args.len() ==> quot_mk_spine(env.export, args[5]),
        quot_kind_of(env.export, qid) == Some(1u8) && 4 < args.len() ==> quot_mk_spine(env.export, args[4]),
        pstep(env, spine_app(ExprSpec::Const(qid, lv), args), t),
    ensures
        pw(env, args, r.0),
        !r.1 ==> t == spine_app(ExprSpec::Const(qid, lv), r.0),
        r.1 ==> quot_ready(env.export, spine_app(ExprSpec::Const(qid, lv), args))
            && pstep(env, quot_result(env.export, spine_app(ExprSpec::Const(qid, lv), args)), t),
    decreases args.len(),
{
    let h = ExprSpec::Const(qid, lv);
    if env.defs.contains_key(qid) {
        assert(!redex_head(env, qid));
    }
    if env.rec_data(qid) is Some {
        assert(quot_kind_of(env.export, qid) is None);
    }
    if nat_bin_op_of(env.export, qid) is Some {
        assert(quot_kind_of(env.export, qid) is None);
    }
    if args.len() == 0 {
        assert(t == h);
        return (args, false);
    }
    let n = args.len() - 1;
    let init = args.subrange(0, n);
    let x = args[n];
    assert(args =~= init.push(x));
    spine_app_compose_last(h, init, x);
    let (kind, f2, x2) = pstep_app_destruct(env, spine_app(h, init), x, t);
    if kind == 0 {
        assert forall|i: int| 0 <= i < args.len() implies #[trigger] pstep(env, args[i], args[i]) by {}
        return (args, false);
    }
    spine_head_spine_app(h, init);
    assert(!(spine_app(h, init) is Bind));
    let (init3, fired) = quot_spine_step(env, qid, lv, init, f2);
    let args3 = init3.push(x2);
    assert forall|i: int| 0 <= i < args.len() implies #[trigger] pstep(env, args[i], args3[i]) by {
        if i < n {
            assert(args[i] == init[i] && args3[i] == init3[i]);
        }
    }
    let app2 = ExprSpec::App(Box::new(f2), Box::new(x2));
    spine_app_compose_last(h, init3, x2);
    quot_ready_head(env, qid, lv, args3);
    quot_ready_head(env, qid, lv, args);
    if fired {
        // contracted below: the full spine is ready too, and its
        // contraction is the lower one's, applied to `x`
        let lower = spine_app(h, init);
        quot_result_extend(env, lower, x);
        let q = quot_result(env.export, lower);
        assert(quot_result(env.export, spine_app(h, args)) == ExprSpec::App(Box::new(q), Box::new(x)));
        // the same rule at this node, out of `q x`
        if kind == 2 {
            assert(pstep(env, q, f2) && pstep(env, x, x2));
        } else if kind == 3 {
            pstep_rec_intro(env, Box::new(q), Box::new(x), f2, x2, t);
        } else if kind == 4 {
            pstep_fold_intro(env, Box::new(q), Box::new(x), f2, x2, t);
        } else {
            pstep_quot_intro(env, Box::new(q), Box::new(x), f2, x2, t);
        }
        (args3, true)
    } else {
        assert(spine_head(app2) == h);
        if kind == 2 {
            return (args3, false);
        }
        if kind == 5 {
            // fired here: the source is ready (the stepped major is a
            // `Quot.mk` spine only if the source's was: `Quot.mk` is inert)
            let (_q, _l, _a, qi) = quot_unpack(env, app2);
            assert(quot_ready(env.export, spine_app(h, args)));
            quot_result_pw(env, qid, lv, args, args3);
            return (args3, true);
        }
        assert(false);
        (args3, false)
    }
}

/// Stepping keeps a numeral's value.
pub proof fn nat_value_step(env: EnvSpec, v: ExprSpec, v2: ExprSpec)
    requires
        env_conf(env),
        pstep(env, v, v2),
        nat_value(env.export, v) is Some,
    ensures
        nat_value(env.export, v2) == nat_value(env.export, v),
    decreases v,
{
    let zid = nat_zero_id(env.export);
    let sid = nat_succ_id(env.export);
    match v {
        ExprSpec::NatLit(n) => {
            if v2 != v {
                if n.0@ == 0 {
                    assert(v2 == const_expr_no_levels(zid));
                } else {
                    let p = ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)));
                    assert(v2 == ExprSpec::App(Box::new(const_expr_no_levels(sid)), Box::new(p)));
                    assert(nat_value(env.export, p) == Some((n.0@ - 1) as nat));
                    assert(nat_value(env.export, v2) == Some(n.0@)) by {
                        reveal_with_fuel(nat_value, 2);
                    }
                }
            }
        },
        ExprSpec::Const(id, ls) => {
            if env.defs.contains_key(id) {
                assert(!redex_head(env, id));
            }
        },
        ExprSpec::App(f, x) => {
            if let ExprSpec::Const(id, ls) = *f {
                assert(id == sid && ls.len() == 0);
                assert(inert_head(env, sid, 1)) by {
                    if env.defs.contains_key(sid) {
                        assert(!redex_head(env, sid));
                    }
                }
                let one = seq![*x];
                assert(spine_app(*f, one) == v) by {
                    reveal_with_fuel(spine_app, 2);
                    assert(one.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
                }
                let args3 = inert_spine_step(env, sid, ls, one, v2);
                assert(pstep(env, one[0], args3[0]));
                nat_value_step(env, *x, args3[0]);
                assert(v2 == spine_app(*f, args3));
                assert(args3 =~= seq![args3[0]]);
                assert(v2 == ExprSpec::App(Box::new(*f), Box::new(args3[0]))) by {
                    reveal_with_fuel(spine_app, 2);
                    assert(args3.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
                }
                assert(nat_value(env.export, v2) == nat_value(env.export, v)) by {
                    reveal_with_fuel(nat_value, 2);
                }
            }
        },
        _ => {},
    }
}

/// A prefix of a ready recursor application that still holds the major
/// premise is ready.
pub proof fn rec_ready_prefix(env: EnvSpec, rid: u64, lv: Seq<crate::level_model::LevelSpec>, args: Seq<ExprSpec>, n: int)
    requires
        rec_ready(env, spine_app(ExprSpec::Const(rid, lv), args)),
        env.rec_data(rid) is Some,
        env.rec_data(rid)->Some_0.major_idx < n <= args.len(),
    ensures
        rec_ready(env, spine_app(ExprSpec::Const(rid, lv), args.subrange(0, n))),
{
    let h = ExprSpec::Const(rid, lv);
    spine_destruct_app(h, args);
    spine_destruct_app(h, args.subrange(0, n));
    let (_r, _l, _a, rd, major, cid, clv, cargs, ri, body) = rec_unpack(env, spine_app(h, args));
    assert(args.subrange(0, n)[rd.major_idx as int] == major);
}

/// THE NODE JOIN: the function and the argument step to their developments,
/// so the application steps to the node's development.
pub proof fn node_join(env: EnvSpec, f: ExprSpec, x: ExprSpec, cf: ExprSpec, cx: ExprSpec)
    requires
        pstep(env, f, cf),
        pstep(env, x, cx),
    ensures
        pstep(env, ExprSpec::App(Box::new(f), Box::new(x)), app_develop(env, ExprSpec::App(Box::new(cf), Box::new(cx)))),
{
    let c = ExprSpec::App(Box::new(cf), Box::new(cx));
    if rec_ready(env, c) {
        pstep_rec_intro(env, Box::new(f), Box::new(x), cf, cx, app_develop(env, c));
    } else if env.nat_fold && nat_fold_ready(env.export, c) {
        pstep_fold_intro(env, Box::new(f), Box::new(x), cf, cx, app_develop(env, c));
    } else if quot_ready(env.export, c) {
        pstep_quot_intro(env, Box::new(f), Box::new(x), cf, cx, app_develop(env, c));
    } else {
        assert(pstep(env, f, cf) && pstep(env, x, cx) && app_develop(env, c) == c);
    }
}

/// A recursor fired at this node rejoins the development.
#[verifier::spinoff_prover]
proof fn rec_vs_develop(env: EnvSpec, f2: ExprSpec, x2: ExprSpec, cf: ExprSpec, cx: ExprSpec)
    requires
        env_conf(env),
        pstep(env, f2, cf),
        pstep(env, x2, cx),
        rec_ready(env, ExprSpec::App(Box::new(f2), Box::new(x2))),
    ensures
        pstep(env, rec_result(env, ExprSpec::App(Box::new(f2), Box::new(x2))), app_develop(env, ExprSpec::App(Box::new(cf), Box::new(cx)))),
{
    let e = ExprSpec::App(Box::new(f2), Box::new(x2));
    let (rid, lv, args, rd, major, cid, clv, cargs, ri, body) = rec_unpack(env, e);
    let h = ExprSpec::Const(rid, lv);
    let n = args.len() - 1;
    let init = args.subrange(0, n);
    assert(args =~= init.push(x2)) by {
        spine_app_compose_last(h, init, args[n]);
        spine_destruct_app(h, args);
    }
    spine_app_compose_last(h, init, x2);
    assert(f2 == spine_app(h, init));
    let (init3, fired) = rec_spine_step(env, rid, lv, init, cf);
    let args3 = init3.push(cx);
    assert forall|i: int| 0 <= i < args.len() implies #[trigger] pstep(env, args[i], args3[i]) by {
        if i < n {
            assert(args[i] == init[i] && args3[i] == init3[i]);
        }
    }
    spine_app_compose_last(h, init3, cx);
    let c = ExprSpec::App(Box::new(cf), Box::new(cx));
    if !fired {
        assert(c == spine_app(h, args3));
        rec_result_pw(env, rid, lv, args, args3);
        assert(app_develop(env, c) == rec_result(env, c));
    } else {
        let s3 = spine_app(h, init3);
        let (_r3, _l3, _a3, rd3, _m3, _c3, _cl3, _ca3, _ri3, _b3) = rec_unpack(env, s3);
        spine_destruct_app(h, init3);
        rec_ready_prefix(env, rid, lv, args, n);
        let s1 = spine_app(h, init);
        rec_result_extend(env, s1, x2);
        rec_result_pw(env, rid, lv, init, init3);
        node_join(env, rec_result(env, s1), x2, cf, cx);
    }
}

/// A quotient fired at this node rejoins the development.
#[verifier::spinoff_prover]
proof fn quot_vs_develop(env: EnvSpec, f2: ExprSpec, x2: ExprSpec, cf: ExprSpec, cx: ExprSpec)
    requires
        env_conf(env),
        pstep(env, f2, cf),
        pstep(env, x2, cx),
        quot_ready(env.export, ExprSpec::App(Box::new(f2), Box::new(x2))),
    ensures
        pstep(env, quot_result(env.export, ExprSpec::App(Box::new(f2), Box::new(x2))), app_develop(env, ExprSpec::App(Box::new(cf), Box::new(cx)))),
{
    let e = ExprSpec::App(Box::new(f2), Box::new(x2));
    let (qid, lv, args, qi) = quot_unpack(env, e);
    let h = ExprSpec::Const(qid, lv);
    let n = args.len() - 1;
    let init = args.subrange(0, n);
    assert(args =~= init.push(x2)) by {
        spine_app_compose_last(h, init, args[n]);
        spine_destruct_app(h, args);
    }
    spine_app_compose_last(h, init, x2);
    assert(f2 == spine_app(h, init));
    if env.rec_data(qid) is Some {
        assert(quot_kind_of(env.export, qid) is None);
    }
    if nat_bin_op_of(env.export, qid) is Some {
        assert(quot_kind_of(env.export, qid) is None);
    }
    let (init3, fired) = quot_spine_step(env, qid, lv, init, cf);
    let args3 = init3.push(cx);
    assert forall|i: int| 0 <= i < args.len() implies #[trigger] pstep(env, args[i], args3[i]) by {
        if i < n {
            assert(args[i] == init[i] && args3[i] == init3[i]);
        }
    }
    spine_app_compose_last(h, init3, cx);
    let c = ExprSpec::App(Box::new(cf), Box::new(cx));
    if !fired {
        assert(c == spine_app(h, args3));
        quot_result_pw(env, qid, lv, args, args3);
        quot_ready_head(env, qid, lv, args3);
        assert(!rec_ready(env, c));
        assert(!nat_fold_ready(env.export, c));
        assert(app_develop(env, c) == quot_result(env.export, c));
    } else {
        let s1 = spine_app(h, init);
        quot_result_extend(env, s1, x2);
        node_join(env, quot_result(env.export, s1), x2, cf, cx);
    }
}

/// A fold fired at this node is the development.
#[verifier::spinoff_prover]
proof fn fold_vs_develop(env: EnvSpec, f2: ExprSpec, x2: ExprSpec, cf: ExprSpec, cx: ExprSpec)
    requires
        env_conf(env),
        pstep(env, f2, cf),
        pstep(env, x2, cx),
        env.nat_fold,
        nat_fold_ready(env.export, ExprSpec::App(Box::new(f2), Box::new(x2))),
    ensures
        pstep(env, nat_fold_result(env.export, ExprSpec::App(Box::new(f2), Box::new(x2))), app_develop(env, ExprSpec::App(Box::new(cf), Box::new(cx)))),
{
    let e = ExprSpec::App(Box::new(f2), Box::new(x2));
    spine_recompose(e);
    let args = spine_args(e);
    if let ExprSpec::Const(oid, lv) = spine_head(e) {
        let h = ExprSpec::Const(oid, lv);
        assert(args.len() == 2);
        let init = seq![args[0]];
        assert(args =~= init.push(args[1]));
        spine_app_compose_last(h, init, args[1]);
        assert(e == spine_app(h, args));
        assert(x2 == args[1]);
        assert(f2 == spine_app(h, init));
        assert(inert_head(env, oid, 1)) by {
            if env.defs.contains_key(oid) {
                assert(!redex_head(env, oid));
            }
            if env.rec_data(oid) is Some {
                assert(nat_bin_op_of(env.export, oid) is None);
            }
        }
        let init3 = inert_spine_step(env, oid, lv, init, cf);
        assert(pstep(env, init[0], init3[0]));
        nat_value_step(env, args[0], init3[0]);
        nat_value_step(env, x2, cx);
        let args3 = init3.push(cx);
        spine_app_compose_last(h, init3, cx);
        let c = ExprSpec::App(Box::new(cf), Box::new(cx));
        assert(c == spine_app(h, args3));
        spine_destruct_app(h, args3);
        assert(spine_args(c) =~= args3);
        assert(nat_fold_ready(env.export, c));
        if env.rec_data(oid) is Some {
            assert(nat_bin_op_of(env.export, oid) is None);
        }
        assert(!rec_ready(env, c));
        assert(app_develop(env, c) == nat_fold_result(env.export, c));
        assert(nat_fold_result(env.export, c) == nat_fold_result(env.export, e));
    }
}

/// THE APPLICATION CASE of Takahashi, for a head that is not a lambda.
#[verifier::spinoff_prover]
proof fn app_join(env: EnvSpec, f: ExprSpec, a: ExprSpec, e2: ExprSpec)
    requires
        env_conf(env),
        !(f is Bind && f->Bind_0 == BinderKind::Lam),
        pstep(env, ExprSpec::App(Box::new(f), Box::new(a)), e2),
        forall|x: ExprSpec| #[trigger] pstep(env, f, x) ==> pstep(env, x, complete(env, f)),
        forall|x: ExprSpec| #[trigger] pstep(env, a, x) ==> pstep(env, x, complete(env, a)),
    ensures
        pstep(env, e2, complete(env, ExprSpec::App(Box::new(f), Box::new(a)))),
{
    let e = ExprSpec::App(Box::new(f), Box::new(a));
    let cf = complete(env, f);
    let ca = complete(env, a);
    assert(complete(env, e) == app_develop(env, ExprSpec::App(Box::new(cf), Box::new(ca))));
    let (kind, f2, x2) = pstep_app_destruct(env, f, a, e2);
    if kind == 0 {
        pstep_complete(env, e);
        return;
    }
    assert(kind != 1);
    assert(pstep(env, f2, cf));
    assert(pstep(env, x2, ca));
    if kind == 2 {
        node_join(env, f2, x2, cf, ca);
    } else if kind == 3 {
        rec_vs_develop(env, f2, x2, cf, ca);
    } else if kind == 4 {
        fold_vs_develop(env, f2, x2, cf, ca);
    } else {
        quot_vs_develop(env, f2, x2, cf, ca);
    }
}

/// A reduct of a binder is a binder of the same kind.
pub proof fn pstep_bind_shape(env: EnvSpec, bk: BinderKind, t: ExprSpec, b: ExprSpec, x: ExprSpec) -> (r: (ExprSpec, ExprSpec))
    requires
        pstep(env, ExprSpec::Bind(bk, Box::new(t), Box::new(b)), x),
    ensures
        pstep(env, t, r.0),
        pstep(env, b, r.1),
        x == ExprSpec::Bind(bk, Box::new(r.0), Box::new(r.1)),
{
    if x == ExprSpec::Bind(bk, Box::new(t), Box::new(b)) {
        (t, b)
    } else {
        choose|t2: ExprSpec, b2: ExprSpec| pstep(env, t, t2) && pstep(env, b, b2) && x == ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))
    }
}

/// TAKAHASHI: every step out of `e` lands one step short of `complete(e)`.
#[verifier::spinoff_prover]
pub proof fn takahashi(env: EnvSpec, e: ExprSpec, e2: ExprSpec)
    requires
        env_conf(env),
        pstep(env, e, e2),
    ensures
        pstep(env, e2, complete(env, e)),
    decreases e,
{
    if e2 == e {
        pstep_complete(env, e);
        return;
    }
    match e {
        ExprSpec::App(f, a) => {
            assert forall|x: ExprSpec| #[trigger] pstep(env, *a, x) implies pstep(env, x, complete(env, *a)) by {
                takahashi(env, *a, x);
            }
            if let ExprSpec::Bind(BinderKind::Lam, t, body) = *f {
                assert forall|x: ExprSpec| #[trigger] pstep(env, *body, x) implies pstep(env, x, complete(env, *body)) by {
                    takahashi(env, *body, x);
                }
                let cb = complete(env, *body);
                let ca = complete(env, *a);
                let (kind, x1, y1) = pstep_app_destruct(env, *f, *a, e2);
                if kind == 1 {
                    // beta against beta: substitution of the developments
                    pstep_inst(env, 0, y1, ca, x1, cb);
                    subst1_is_inst(x1, y1);
                    subst1_is_inst(cb, ca);
                } else if kind == 2 {
                    let (t2, b2) = pstep_bind_shape(env, BinderKind::Lam, *t, *body, x1);
                    assert(pstep(env, b2, cb) && pstep(env, y1, ca) && complete(env, e) == subst1(cb, ca));
                    assert(pstep(env, e2, complete(env, e)));
                } else {
                    // no head rule fires on a lambda head
                    let (t2, b2) = pstep_bind_shape(env, BinderKind::Lam, *t, *body, x1);
                    let app = ExprSpec::App(Box::new(x1), Box::new(y1));
                    spine_head_spine_app(x1, seq![y1]);
                    assert(app == spine_app(x1, seq![y1])) by {
                        reveal_with_fuel(spine_app, 2);
                        assert(seq![y1].subrange(0, 0) =~= Seq::<ExprSpec>::empty());
                    }
                    assert(!(spine_head(app) is Const));
                    assert(false);
                }
            } else {
                assert forall|x: ExprSpec| #[trigger] pstep(env, *f, x) implies pstep(env, x, complete(env, *f)) by {
                    takahashi(env, *f, x);
                }
                app_join(env, *f, *a, e2);
            }
        },
        ExprSpec::Bind(bk, t, b) => {
            let (t2, b2) = pstep_bind_shape(env, bk, *t, *b, e2);
            takahashi(env, *t, t2);
            takahashi(env, *b, b2);
            assert(pstep(env, t2, complete(env, *t)) && pstep(env, b2, complete(env, *b)));
        },
        ExprSpec::Let(t, v, b) => {
            let cb = complete(env, *b);
            let cv = complete(env, *v);
            if exists|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)] pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2) {
                let (b2, v2) = choose|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);
                takahashi(env, *b, b2);
                takahashi(env, *v, v2);
                pstep_inst(env, 0, v2, cv, b2, cb);
                subst1_is_inst(b2, v2);
                subst1_is_inst(cb, cv);
            } else {
                let (t2, v2, b2) = choose|t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                    pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                takahashi(env, *b, b2);
                takahashi(env, *v, v2);
                assert(pstep(env, b2, cb) && pstep(env, v2, cv) && complete(env, e) == subst1(cb, cv));
            }
        },
        ExprSpec::Proj(pidx, inner) => {
            let cs = complete(env, *inner);
            if let ExprSpec::Proj(pidx2, inner2) = e2 {
                if pidx == pidx2 && pstep(env, *inner, *inner2) {
                    takahashi(env, *inner, *inner2);
                    if proj_ready(env, pidx, cs) {
                        proj_ready_extract(env, pidx, cs);
                        assert(iota_reduct(cs));
                    }
                    return;
                }
            }
            let s2 = choose|s2: ExprSpec| (#[trigger] iota_reduct(s2)) && pstep(env, *inner, s2) && iota_extract(env, pidx, s2, e2);
            takahashi(env, *inner, s2);
            let (cid, lv, args2, np) = choose|cid: u64, lv: Seq<crate::level_model::LevelSpec>, args2: Seq<ExprSpec>, np: u16|
                #![trigger spine_app(ExprSpec::Const(cid, lv), args2), args2[(np as nat + pidx as nat) as int]]
                s2 == spine_app(ExprSpec::Const(cid, lv), args2) && env.ctor_num_params(cid) == Some(np)
                    && ((np as nat + pidx as nat) < args2.len()) && (e2 == args2[(np as nat + pidx as nat) as int]);
            ctor_inert(env, cid, args2.len());
            let args3 = inert_spine_step(env, cid, lv, args2, cs);
            spine_destruct_app(ExprSpec::Const(cid, lv), args3);
            assert(spine_args(cs) =~= args3);
            assert(proj_ready(env, pidx, cs));
            assert(complete(env, e) == args3[(np as nat + pidx as nat) as int]);
            assert(pstep(env, args2[(np as nat + pidx as nat) as int], args3[(np as nat + pidx as nat) as int]));
        },
        _ => {},
    }
}

/// THE DIAMOND.
pub proof fn pstep_diamond(env: EnvSpec, e: ExprSpec, e1: ExprSpec, e2: ExprSpec) -> (d: ExprSpec)
    requires
        env_conf(env),
        pstep(env, e, e1),
        pstep(env, e, e2),
    ensures
        pstep(env, e1, d),
        pstep(env, e2, d),
{
    takahashi(env, e, e1);
    takahashi(env, e, e2);
    complete(env, e)
}

/// A valid chain from `ch[0]` to its last element.
pub open spec fn chain_ok(env: EnvSpec, ch: Seq<ExprSpec>) -> bool {
    ch.len() >= 1 && pstep_chain_valid(env, ch)
}

proof fn chain_star(env: EnvSpec, ch: Seq<ExprSpec>)
    requires
        chain_ok(env, ch),
    ensures
        pstep_star(env, ch[0], ch[ch.len() - 1]),
{
}

proof fn star_chain(env: EnvSpec, a: ExprSpec, b: ExprSpec) -> (ch: Seq<ExprSpec>)
    requires
        pstep_star(env, a, b),
    ensures
        chain_ok(env, ch),
        ch[0] == a,
        ch[ch.len() - 1] == b,
{
    choose|chain: Seq<ExprSpec>| chain.len() >= 1 && chain[0] == a && chain[chain.len() - 1] == b && pstep_chain_valid(env, chain)
}

/// THE STRIP LEMMA: one step against many.
pub proof fn strip(env: EnvSpec, ch: Seq<ExprSpec>, e1: ExprSpec) -> (d: ExprSpec)
    requires
        env_conf(env),
        chain_ok(env, ch),
        pstep(env, ch[0], e1),
    ensures
        pstep(env, ch[ch.len() - 1], d),
        pstep_star(env, e1, d),
    decreases ch.len(),
{
    if ch.len() == 1 {
        pstep_star_refl(env, e1);
        e1
    } else {
        let z = 0int;
        assert(pstep(env, ch[z], ch[z + 1]));
        let d1 = pstep_diamond(env, ch[0], e1, ch[1]);
        let rest = ch.subrange(1, ch.len() as int);
        assert(chain_ok(env, rest)) by {
            assert forall|i: int| #![trigger pstep(env, rest[i], rest[i + 1])] 0 <= i < rest.len() - 1 implies pstep(env, rest[i], rest[i + 1]) by {
                assert(rest[i] == ch[i + 1] && rest[i + 1] == ch[i + 2]);
                assert(pstep(env, ch[i + 1], ch[(i + 1) + 1]));
            }
        }
        let d = strip(env, rest, d1);
        pstep_star_one(env, e1, d1);
        pstep_star_trans(env, e1, d1, d);
        d
    }
}

/// CONFLUENCE of multi-step reduction.
pub proof fn confluent(env: EnvSpec, ch1: Seq<ExprSpec>, ch2: Seq<ExprSpec>) -> (d: ExprSpec)
    requires
        env_conf(env),
        chain_ok(env, ch1),
        chain_ok(env, ch2),
        ch1[0] == ch2[0],
    ensures
        pstep_star(env, ch1[ch1.len() - 1], d),
        pstep_star(env, ch2[ch2.len() - 1], d),
    decreases ch1.len(),
{
    if ch1.len() == 1 {
        chain_star(env, ch2);
        pstep_star_refl(env, ch2[ch2.len() - 1]);
        ch2[ch2.len() - 1]
    } else {
        let z = 0int;
        assert(pstep(env, ch1[z], ch1[z + 1]));
        let d1 = strip(env, ch2, ch1[1]);
        let rest = ch1.subrange(1, ch1.len() as int);
        assert(chain_ok(env, rest)) by {
            assert forall|i: int| #![trigger pstep(env, rest[i], rest[i + 1])] 0 <= i < rest.len() - 1 implies pstep(env, rest[i], rest[i + 1]) by {
                assert(rest[i] == ch1[i + 1] && rest[i + 1] == ch1[i + 2]);
                assert(pstep(env, ch1[i + 1], ch1[(i + 1) + 1]));
            }
        }
        let ch3 = star_chain(env, ch1[1], d1);
        let d = confluent(env, rest, ch3);
        pstep_star_one(env, ch2[ch2.len() - 1], d1);
        pstep_star_trans(env, ch2[ch2.len() - 1], d1, d);
        d
    }
}

/// Two reductions from one term meet.
pub proof fn pstep_star_confluent(env: EnvSpec, e: ExprSpec, a: ExprSpec, b: ExprSpec) -> (d: ExprSpec)
    requires
        env_conf(env),
        pstep_star(env, e, a),
        pstep_star(env, e, b),
    ensures
        pstep_star(env, a, d),
        pstep_star(env, b, d),
{
    let ch1 = star_chain(env, e, a);
    let ch2 = star_chain(env, e, b);
    confluent(env, ch1, ch2)
}

/// JOINABILITY IS TRANSITIVE.
pub proof fn defeq_trans(env: EnvSpec, a: ExprSpec, b: ExprSpec, c: ExprSpec)
    requires
        env_conf(env),
        defeq(env, a, b),
        defeq(env, b, c),
    ensures
        defeq(env, a, c),
{
    let x = choose|z: ExprSpec| #[trigger] pstep_star(env, a, z) && #[trigger] pstep_star(env, b, z);
    let y = choose|z: ExprSpec| #[trigger] pstep_star(env, b, z) && #[trigger] pstep_star(env, c, z);
    let d = pstep_star_confluent(env, b, x, y);
    pstep_star_trans(env, a, x, d);
    pstep_star_trans(env, c, y, d);
}

} // verus!
