//! REGULARITY OF PROJECTIONS: the field type `infer_proj` returns is a type
//! wherever the projection is really typed, and an `InferWt` type of it.
//!
//! The kernel walks the constructor's type: `whnf` to a Pi, instantiate with
//! the next parameter of the structure's type, or with an earlier projection,
//! and read the field type off the last binder. Its `whnf` steps carry
//! reduction claims (`cwh`). In a context where the projection is really
//! typed, each stage of the walk is a type and converts to the constructor's
//! own telescope instantiated as far (`peel_inst`): the claim moves typing to
//! the Pi, and Pi-injectivity moves the conversion to the next stage, whose
//! argument is typed at the telescope's domain (the parameters by E2', the
//! projections by `proj_typed`). The same claims give the `InferWt` walk.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_model::{fv_absent, nlbv, subst_full, subst_expr_levels};
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::beta_model::{pi_spine, spine_app};
#[cfg(verus_only)]
use crate::metatheory::{hyps, hyps_all, is_type, kconv_wt_implies_tconv, lctx_wf, pi, s_sound, tconv, tconv_of, tconv_symm, tconv_trans, typed};
#[cfg(verus_only)]
use crate::tc_model::*;
#[cfg(verus_only)]
use crate::ctor_typing::{ctor_cod, ctor_const_type, ctor_params_ok, ctor_params_ok1, ctor_ty_at, gen_app_ty, pdom, peel_inst_prefix, peel_pis, pi_spine_li, pi_spine_shorter, proj_typed, projs_from, spine_head_typed, spine_type, struct_ok, struct_ok1};
#[cfg(verus_only)]
use crate::telescope::peel_inst;
#[cfg(verus_only)]
use crate::kclaims::{ci, ci_at, ci_use, cw, cwh, gen_bind_ty, gen_proj, kh, rctx_part, rctx_two, rt_at, rtyped, rtyped_closed, spine_arg_fv, sub_trans, tconv_refl, tp_to};
#[cfg(verus_only)]
use crate::rctx::{rctx, rctx_mono, subst_free_fv};
#[cfg(verus_only)]
use crate::swap_typed::fv_free;
#[cfg(verus_only)]
use crate::weaken::sub;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A binder's body.
pub open spec fn pbod(e: ExprSpec) -> ExprSpec {
    match e {
        ExprSpec::Bind(_, _, b) => *b,
        _ => ExprSpec::Closed,
    }
}

/// What the walk instantiates with, in order: the parameters, then the
/// projections before the field.
pub open spec fn psq(am: Seq<ExprSpec>, np: nat, s: ExprSpec, idx: nat) -> Seq<ExprSpec> {
    am.subrange(0, np as int) + projs_from(s, 0, idx)
}

pub proof fn psq_at(am: Seq<ExprSpec>, np: nat, s: ExprSpec, idx: nat, k: int)
    requires
        np <= am.len(),
        0 <= k < np + idx,
    ensures
        psq(am, np, s, idx).len() == np + idx,
        k < np ==> psq(am, np, s, idx)[k] == am[k],
        k >= np ==> psq(am, np, s, idx)[k] == ExprSpec::Proj((k - np) as usize, Box::new(s)),
{
    let sq = psq(am, np, s, idx);
    if k >= np {
        assert(sq[k] == projs_from(s, 0, idx)[k - np]);
    }
}

/// The walk's shape at stage `j`: `proj_field_type`'s arguments.
pub open spec fn pw_skip(j: nat, np: nat) -> nat {
    if j < np { j } else { np }
}

pub open spec fn pw_np(j: nat, np: nat) -> nat {
    if j < np { (np - j) as nat } else { 0 }
}

pub open spec fn pw_fld(j: nat, np: nat) -> nat {
    if j < np { 0 } else { (j - np) as nat }
}

pub open spec fn pw_rem(j: nat, np: nat, idx: nat) -> nat {
    if j < np { idx } else { (idx - (j - np)) as nat }
}

/// THE KERNEL'S WALK, as `infer_proj` records it: the constructor type at
/// the structure's universes, each stage `cs[k]` reduced to the Pi `ws[k]`
/// (a reduction claim), the next stage its body at `psq[k]`, the field type
/// the last Pi's domain; and the structure's inference claim.
pub open spec fn pwalk_ok(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
) -> bool {
    let np = denv.ctor_np[cid] as nat;
    let m = np + idx as nat;
    let sq = psq(am, np, s, idx as nat);
    &&& denv.struct_ctor(ind) == Some(cid)
    &&& denv.ctor_np.contains_key(cid)
    &&& np <= am.len()
    &&& denv.ctor_nf.contains_key(cid)
    &&& (idx as nat) < denv.ctor_nf[cid] as nat
    &&& dty.contains_key(cid)
    &&& ls.len() == dty[cid].0.len()
    &&& cs.len() == m + 1
    &&& ws.len() == m + 1
    &&& cs[0] == ctor_ty_at(dty, cid, ls)
    &&& forall|k: int| 0 <= k <= m ==> #[trigger] cwh(dty, denv, g, cs[k], ws[k])
    &&& forall|k: int| 0 <= k <= m ==> (#[trigger] ws[k]) is Bind && ws[k]->Bind_0 == BinderKind::Pi
    &&& forall|k: int| #![trigger ws[k]] 0 <= k < m ==> cs[k + 1] == subst_full(pbod(ws[k]), seq![sq[k]], 0)
    &&& pdom(ws[m as int]) == btm
    &&& ci(dty, denv, g, s, spine_app(ExprSpec::Const(ind, ls), am))
    &&& nlbv(s) <= 0
    &&& forall|k: int| 0 <= k < am.len() ==> nlbv(#[trigger] am[k]) <= 0
}

/// A declaration's type at some universes is a closed type anywhere.
pub proof fn decl_is_type(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, cid: u64, ls: Seq<LevelSpec>)
    requires
        kh(dty, denv),
        dty.contains_key(cid),
        ls.len() == dty[cid].0.len(),
    ensures
        is_type(dty, denv, d, ctor_ty_at(dty, cid, ls)),
        forall|i: nat| fv_absent(#[trigger] ctor_ty_at(dty, cid, ls), i),
        nlbv(ctor_ty_at(dty, cid, ls)) <= 0,
{
    let (ks, decl) = dty[cid];
    let t = subst_expr_levels(decl, ks, ls);
    let em = Map::<nat, ExprSpec>::empty();
    assert(is_type(dty, denv, em, decl));
    let (s, l) = choose|s: ExprSpec, l: LevelSpec| #![trigger typed(dty, denv, em, decl, s), tconv(dty, denv, em, s, ExprSpec::Sort(l))]
        typed(dty, denv, em, decl, s) && tconv(dty, denv, em, s, ExprSpec::Sort(l));
    let f = choose|f: nat| #[trigger] types_to(dty, denv, em, IoMode::Real, decl, s, f);
    let hl = choose|h: nat| #[trigger] deq_p(dty, denv, em, IoMode::Real, s, ExprSpec::Sort(l), h);
    crate::real_gen::rt_fv_in(dty, denv, em, decl, s, f);
    crate::real_gen::rt_closed(dty, denv, em, decl, s, f);
    crate::expr_model::subst_expr_levels_fn_rel(decl, ks, ls);
    crate::beta_model::subst_expr_levels_rel_nlbv(decl, ks, ls, t);
    assert forall|i: nat| fv_absent(#[trigger] ctor_ty_at(dty, cid, ls), i) by {
        assert(fv_absent(decl, i) || em.contains_key(i));
        crate::level_inst::li_fv_absent(decl, ks, ls, i);
    }
    crate::level_typed::lt_closed(dty, denv, IoMode::Real, decl, s, f, ks, ls);
    crate::level_typed::lt_deq_p(dty, denv, em, IoMode::Real, s, ExprSpec::Sort(l), hl, ks, ls);
    assert(crate::level_typed::lg(em, ks, ls) =~= em);
    let ts = subst_expr_levels(s, ks, ls);
    let sl = subst_expr_levels(ExprSpec::Sort(l), ks, ls);
    assert(sl == ExprSpec::Sort(sl->Sort_0));
    crate::weaken::wk_types_to(dty, denv, em, d, IoMode::Real, t, ts, f);
    crate::weaken::wk_deq_p(dty, denv, em, d, IoMode::Real, ts, sl, hl);
    assert(typed(dty, denv, d, t, ts));
    tconv_of(dty, denv, d, ts, sl, hl);
}

/// The walk's stages reach only what the structure does, and are closed.
proof fn pwalk_reach(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
    j: nat,
)
    requires
        kh(dty, denv),
        pwalk_ok(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm),
        j <= denv.ctor_np[cid] as nat + idx as nat,
    ensures
        sub(rctx(g, cs[j as int]), rctx(g, s)),
        nlbv(cs[j as int]) <= 0,
    decreases j,
{
    let np = denv.ctor_np[cid] as nat;
    let sq = psq(am, np, s, idx as nat);
    let sp = spine_app(ExprSpec::Const(ind, ls), am);
    if j == 0 {
        decl_is_type(dty, denv, g, cid, ls);
        rctx_mono(g, cs[0], s);
    } else {
        let k = (j - 1) as int;
        pwalk_reach(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, (j - 1) as nat);
        assert(cwh(dty, denv, g, cs[k], ws[k]));
        assert(ws[k] is Bind);
        let b = pbod(ws[k]);
        let x = sq[k];
        psq_at(am, np, s, idx as nat, k);
        assert(nlbv(x) <= 0);
        crate::beta_model::subst_full_nlbv_bound(b, x, 0);
        assert(cs[j as int] == subst_full(b, seq![x], 0));
        sub_trans(rctx(g, ws[k]), rctx(g, cs[k]), rctx(g, s));
        if k < np {
            spine_arg_fv(ExprSpec::Const(ind, ls), am, k);
            rctx_mono(g, x, sp);
            sub_trans(rctx(g, x), rctx(g, sp), rctx(g, s));
        } else {
            rctx_mono(g, x, s);
        }
        assert forall|i: nat| #[trigger] fv_absent(ws[k], i) && fv_absent(x, i) implies fv_absent(cs[j as int], i) by {
            if !fv_absent(cs[j as int], i) {
                subst_free_fv(b, x, 0, i);
            }
        }
        rctx_two(g, cs[j as int], ws[k], x, rctx(g, s));
    }
}

/// Every stage of the constructor's telescope, up to the field, is a Pi.
proof fn stage_pis(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, ind: u64, cid: u64, ls: Seq<LevelSpec>, sq: Seq<ExprSpec>, m: nat)
    requires
        struct_ok(dty, denv),
        denv.struct_ctor(ind) == Some(cid),
        m < denv.ctor_np[cid] as nat + denv.ctor_nf[cid] as nat,
        sq.len() == m,
        forall|i: int| 0 <= i < sq.len() ==> nlbv(#[trigger] sq[i]) == 0,
    ensures
        forall|i: nat| i <= m ==> #[trigger] peel_inst(ctor_ty_at(dty, cid, ls), sq, i) is Bind
            && peel_inst(ctor_ty_at(dty, cid, ls), sq, i)->Bind_0 == BinderKind::Pi,
{
    assert(struct_ok1(dty, denv, ind, cid));
    let ils = choose|ils: Seq<LevelSpec>| #[trigger] ctor_cod(dty, denv, ind, cid, ils);
    let n = denv.ctor_np[cid] as nat + denv.ctor_nf[cid] as nat;
    let cty = ctor_ty_at(dty, cid, ls);
    pi_spine_li(dty[cid].1, n, dty[cid].0, ls);
    pi_spine_shorter(cty, m + 1, n);
    let sq2 = sq.push(ExprSpec::Closed);
    assert forall|i: int| 0 <= i < sq2.len() implies nlbv(#[trigger] sq2[i]) == 0 by {
        if i < sq.len() {
            assert(sq2[i] == sq[i]);
        }
    }
    peel_pis(cty, sq2, m + 1);
    assert forall|i: nat| i <= m implies #[trigger] peel_inst(cty, sq, i) is Bind && peel_inst(cty, sq, i)->Bind_0 == BinderKind::Pi by {
        assert forall|q: int| 0 <= q < i implies sq[q] == sq2[q] by {}
        peel_inst_prefix(cty, sq, sq2, i);
    }
}

/// The walk's argument at stage `j` is typed at that stage's domain.
proof fn stage_arg(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    s: ExprSpec,
    sty: ExprSpec,
    fx: nat,
    hx: nat,
    tsp: ExprSpec,
    idx: nat,
    j: nat,
) -> (tx: ExprSpec)
    requires
        hyps_all(dty, denv),
        struct_ok(dty, denv),
        ctor_params_ok(dty, denv),
        denv.struct_ctor(ind) == Some(cid),
        denv.ctor_np[cid] as nat <= am.len(),
        idx < denv.ctor_nf[cid] as nat,
        ls.len() == dty[cid].0.len(),
        nlbv(s) == 0,
        forall|k: int| 0 <= k < am.len() ==> nlbv(#[trigger] am[k]) == 0,
        types_to(dty, denv, d, IoMode::Real, s, sty, fx),
        deq_p(dty, denv, d, IoMode::Real, sty, spine_app(ExprSpec::Const(ind, ls), am), hx),
        typed(dty, denv, d, spine_app(ExprSpec::Const(ind, ls), am), tsp),
        j < denv.ctor_np[cid] as nat + idx,
    ensures
        typed(dty, denv, d, psq(am, denv.ctor_np[cid] as nat, s, idx)[j as int], tx),
        tconv(dty, denv, d, tx, pdom(peel_inst(ctor_ty_at(dty, cid, ls), psq(am, denv.ctor_np[cid] as nat, s, idx), j))),
{
    assert(hyps(dty, denv, d));
    let np = denv.ctor_np[cid] as nat;
    let sq = psq(am, np, s, idx);
    let cty = ctor_ty_at(dty, cid, ls);
    psq_at(am, np, s, idx, j as int);
    assert forall|i: int| 0 <= i < sq.len() implies nlbv(#[trigger] sq[i]) == 0 by {
        psq_at(am, np, s, idx, i);
    }
    if j >= np {
        let k = (j - np) as nat;
        let t = proj_typed(dty, denv, d, ind, cid, ls, am, s, sty, fx, hx, k);
        let sqk = am.subrange(0, np as int) + projs_from(s, 0, k);
        assert forall|q: int| 0 <= q < j implies sqk[q] == sq[q] by {
            psq_at(am, np, s, idx, q);
            psq_at(am, np, s, k, q);
        }
        peel_inst_prefix(cty, sqk, sq, j);
        assert(sq[j as int] == ExprSpec::Proj(k as usize, Box::new(s)));
        tconv_refl(dty, denv, d, t);
        t
    } else {
        // the constructor applied to the parameters is typed (E2')
        let ps = am.subrange(0, np as int);
        let rest = am.subrange(np as int, am.len() as int);
        assert(ps + rest =~= am);
        assert(struct_ok1(dty, denv, ind, cid));
        assert(ctor_params_ok1(dty, denv, ind, cid));
        let c = ExprSpec::Const(cid, ls);
        assert(spine_app(c, ps) == spine_app(c, ps));
        let tps = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, spine_app(c, ps), t);
        // the prefix through the `j`-th parameter
        let tj1 = spine_prefix_typed(dty, denv, d, c, ps, tps, j + 1);
        let pre = ps.subrange(0, j as int);
        assert(ps.subrange(0, j as int + 1) =~= pre.push(ps[j as int]));
        crate::beta_model::spine_app_compose_last(c, pre, ps[j as int]);
        let (ft, aty, bt, aty2) = gen_app_ty(dty, denv, d, spine_app(c, pre), ps[j as int], tj1);
        let th = spine_head_typed(dty, denv, d, c, pre, ft);
        ctor_const_type(dty, denv, d, cid, ls, th);
        stage_pis(dty, denv, ind, cid, ls, sq, np + idx);
        assert(sq.subrange(0, j as int) =~= pre) by {
            assert forall|q: int| 0 <= q < j implies sq.subrange(0, j as int)[q] == pre[q] by {
                psq_at(am, np, s, idx, q);
            }
        }
        spine_type(dty, denv, d, c, th, cty, sq, j, ft);
        let p = peel_inst(cty, sq, j);
        assert(p is Bind && p->Bind_0 == BinderKind::Pi);
        if let ExprSpec::Bind(_, pa, pb) = p {
            assert(p == pi(*pa, *pb));
            tconv_symm(dty, denv, d, ft, p);
            tconv_trans(dty, denv, d, p, ft, pi(aty, bt));
            tconv_symm(dty, denv, d, p, pi(aty, bt));
            assert(tconv(dty, denv, d, pi(aty, bt), pi(*pa, *pb)));
            assert(tconv(dty, denv, d, aty, *pa));
            tconv_trans(dty, denv, d, aty2, aty, *pa);
        }
        assert(ps[j as int] == am[j as int]);
        aty2
    }
}

/// A prefix of a really typed spine is really typed.
proof fn spine_prefix_typed(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, h: ExprSpec, args: Seq<ExprSpec>, t: ExprSpec, k: nat)
    -> (tk: ExprSpec)
    requires
        typed(dty, denv, d, spine_app(h, args), t),
        k <= args.len(),
    ensures
        typed(dty, denv, d, spine_app(h, args.subrange(0, k as int)), tk),
    decreases args.len() - k,
{
    if k == args.len() {
        assert(args.subrange(0, k as int) =~= args);
        t
    } else {
        let t1 = spine_prefix_typed(dty, denv, d, h, args, t, k + 1);
        let a1 = args.subrange(0, k as int + 1);
        let a0 = args.subrange(0, k as int);
        assert(a1 =~= a0.push(args[k as int]));
        crate::beta_model::spine_app_compose_last(h, a0, args[k as int]);
        let (ft, _, _, _) = gen_app_ty(dty, denv, d, spine_app(h, a0), args[k as int], t1);
        ft
    }
}

/// ONE STAGE: the kernel's Pi converts to the telescope's, so their domains
/// convert and so do their bodies at an argument of the telescope's domain;
/// that body is a type (`reg_app`), and so is the domain.
proof fn stage_step(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    cur: ExprSpec,
    pa: ExprSpec,
    pb: ExprSpec,
    bt: ExprSpec,
    b: ExprSpec,
    x: ExprSpec,
    tx: ExprSpec,
)
    requires
        hyps_all(dty, denv),
        fv_free(dty, denv),
        is_type(dty, denv, d, pi(bt, b)),
        tconv(dty, denv, d, cur, pi(pa, pb)),
        tconv(dty, denv, d, cur, pi(bt, b)),
        typed(dty, denv, d, x, tx),
        tconv(dty, denv, d, tx, pa),
        nlbv(x) == 0,
    ensures
        is_type(dty, denv, d, subst_full(b, seq![x], 0)),
        tconv(dty, denv, d, subst_full(b, seq![x], 0), subst_full(pb, seq![x], 0)),
        is_type(dty, denv, d, bt),
{
    let r = IoMode::Real;
    assert(hyps(dty, denv, d));
    tconv_symm(dty, denv, d, cur, pi(bt, b));
    tconv_trans(dty, denv, d, pi(bt, b), cur, pi(pa, pb));
    assert(tconv(dty, denv, d, bt, pa));
    assert(tconv(dty, denv, d, subst_full(b, seq![x], 0), subst_full(pb, seq![x], 0)));
    let (tp, l) = choose|s: ExprSpec, l: LevelSpec| #![trigger typed(dty, denv, d, pi(bt, b), s), tconv(dty, denv, d, s, ExprSpec::Sort(l))]
        typed(dty, denv, d, pi(bt, b), s) && tconv(dty, denv, d, s, ExprSpec::Sort(l));
    let fp = choose|f: nat| #[trigger] types_to(dty, denv, d, r, pi(bt, b), tp, f);
    let (btt, g1, dl) = gen_bind_ty(dty, denv, d, BinderKind::Pi, bt, b, tp, fp);
    assert(typed(dty, denv, d, bt, btt));
    tconv_of(dty, denv, d, btt, ExprSpec::Sort(dl), g1);
    // the argument's type converts to the kernel's domain
    tconv_symm(dty, denv, d, bt, pa);
    tconv_trans(dty, denv, d, tx, pa, bt);
    let hc = choose|h: nat| #[trigger] deq_p(dty, denv, d, r, tx, bt, h);
    let fx = choose|f: nat| #[trigger] types_to(dty, denv, d, r, x, tx, f);
    let dd = fx + hc;
    types_to_mono(dty, denv, d, r, x, tx, fx, dd);
    deq_p_mono(dty, denv, d, r, tx, bt, hc, dd);
    let res = crate::regularity::reg_app(dty, denv, d, bt, b, tp, fp, x, tx, dd);
    assert(typed(dty, denv, d, subst_full(b, seq![x], 0), res.0));
    tconv_of(dty, denv, d, res.0, ExprSpec::Sort(res.1), res.2);
}

/// At a stage that is a type in `d`, the kernel's reduction claim gives the
/// Pi as a type too, `InferWt`-convertible to the stage.
proof fn pwalk_conv_at(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    d: Map<nat, ExprSpec>,
    c: ExprSpec,
    w: ExprSpec,
)
    requires
        kh(dty, denv),
        cwh(dty, denv, g, c, w),
        lctx_wf(dty, denv, d),
        is_type(dty, denv, d, c),
        sub(rctx(g, c), d),
        nlbv(c) <= 0,
    ensures
        is_type(dty, denv, d, w),
        deq_p_any(dty, denv, d, IoMode::InferWt, c, w),
        tconv(dty, denv, d, c, w),
{
    let (sc, l) = choose|s: ExprSpec, l: LevelSpec| #![trigger typed(dty, denv, d, c, s), tconv(dty, denv, d, s, ExprSpec::Sort(l))]
        typed(dty, denv, d, c, s) && tconv(dty, denv, d, s, ExprSpec::Sort(l));
    let t2 = choose|t2: ExprSpec| #[trigger] typed(dty, denv, d, w, t2) && tconv(dty, denv, d, t2, sc);
    tconv_trans(dty, denv, d, t2, sc, ExprSpec::Sort(l));
    assert(is_type(dty, denv, d, w));
    sub_trans(rctx(g, w), rctx(g, c), d);
    assert(rtyped(dty, denv, d, c));
    assert(rtyped(dty, denv, d, w));
    assert(deq_p_any(dty, denv, d, IoMode::InferWt, c, w));
    kconv_wt_implies_tconv(dty, denv, d, c, w);
}

/// THE STAGES, in `d`: each is a type, reached from the structure, and
/// converts to the telescope's stage; its Pi is `InferWt`-convertible to it.
proof fn pwalk_stage(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    d: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
    sty: ExprSpec,
    fx: nat,
    hx: nat,
    tsp: ExprSpec,
    j: nat,
)
    requires
        kh(dty, denv),
        pwalk_ok(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm),
        lctx_wf(dty, denv, d),
        sub(rctx(g, s), d),
        nlbv(s) == 0,
        types_to(dty, denv, d, IoMode::Real, s, sty, fx),
        deq_p(dty, denv, d, IoMode::Real, sty, spine_app(ExprSpec::Const(ind, ls), am), hx),
        typed(dty, denv, d, spine_app(ExprSpec::Const(ind, ls), am), tsp),
        j <= denv.ctor_np[cid] as nat + idx as nat,
    ensures
        is_type(dty, denv, d, cs[j as int]),
        tconv(dty, denv, d, cs[j as int], peel_inst(ctor_ty_at(dty, cid, ls), psq(am, denv.ctor_np[cid] as nat, s, idx as nat), j)),
        is_type(dty, denv, d, ws[j as int]),
        deq_p_any(dty, denv, d, IoMode::InferWt, cs[j as int], ws[j as int]),
        tconv(dty, denv, d, cs[j as int], ws[j as int]),
    decreases j,
{
    let np = denv.ctor_np[cid] as nat;
    let m = np + idx as nat;
    let sq = psq(am, np, s, idx as nat);
    let cty = ctor_ty_at(dty, cid, ls);
    pwalk_reach(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, j);
    sub_trans(rctx(g, cs[j as int]), rctx(g, s), d);
    assert(cwh(dty, denv, g, cs[j as int], ws[j as int]));
    if j == 0 {
        decl_is_type(dty, denv, d, cid, ls);
        tconv_refl(dty, denv, d, cty);
    } else {
        let k = (j - 1) as int;
        pwalk_stage(dty, denv, g, d, idx, s, ind, cid, ls, am, cs, ws, btm, sty, fx, hx, tsp, (j - 1) as nat);
        assert forall|q: int| 0 <= q < am.len() implies nlbv(#[trigger] am[q]) == 0 by {}
        let tx = stage_arg(dty, denv, d, ind, cid, ls, am, s, sty, fx, hx, tsp, idx as nat, (j - 1) as nat);
        assert forall|i: int| 0 <= i < sq.len() implies nlbv(#[trigger] sq[i]) == 0 by {
            psq_at(am, np, s, idx as nat, i);
        }
        stage_pis(dty, denv, ind, cid, ls, sq, m);
        let p = peel_inst(cty, sq, (j - 1) as nat);
        assert(p is Bind && p->Bind_0 == BinderKind::Pi);
        assert(ws[k] is Bind && ws[k]->Bind_0 == BinderKind::Pi);
        let w = ws[k];
        assert(w == pi(pdom(w), pbod(w)));
        assert(p == pi(pdom(p), pbod(p)));
        psq_at(am, np, s, idx as nat, k);
        stage_step(dty, denv, d, cs[k], pdom(p), pbod(p), pdom(w), pbod(w), sq[k], tx);
        assert(cs[j as int] == subst_full(pbod(w), seq![sq[k]], 0));
        assert(peel_inst(cty, sq, j) == subst_full(pbod(p), seq![sq[k]], 0));
    }
    pwalk_conv_at(dty, denv, g, d, cs[j as int], ws[j as int]);
}

/// THE `InferWt` WALK from stage `j`, built from the stages' conversions.
proof fn pw_walk(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    io: IoMode,
    am: Seq<ExprSpec>,
    np: nat,
    idx: usize,
    s: ExprSpec,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
    j: nat,
) -> (h: nat)
    requires
        np <= am.len(),
        cs.len() == np + idx as nat + 1,
        ws.len() == np + idx as nat + 1,
        j <= np + idx as nat,
        forall|k: int| j <= k <= np + idx as nat ==> #[trigger] deq_p_any(dty, denv, d, io, cs[k], ws[k]),
        forall|k: int| 0 <= k <= np + idx as nat ==> (#[trigger] ws[k]) is Bind && ws[k]->Bind_0 == BinderKind::Pi,
        forall|k: int| #![trigger ws[k]] 0 <= k < np + idx as nat ==> cs[k + 1] == subst_full(pbod(ws[k]), seq![psq(am, np, s, idx as nat)[k]], 0),
        pdom(ws[(np + idx as nat) as int]) == btm,
    ensures
        proj_field_type(dty, denv, d, io, h, cs[j as int], am.skip(pw_skip(j, np) as int), pw_np(j, np),
            pw_fld(j, np) as usize, pw_rem(j, np, idx as nat), s, btm),
    decreases np + idx as nat - j,
{
    let w = io;
    let m = np + idx as nat;
    let jj = j as int;
    assert(deq_p_any(dty, denv, d, w, cs[jj], ws[jj]));
    let hj = choose|h: nat| #[trigger] deq_p(dty, denv, d, w, cs[jj], ws[jj], h);
    assert(ws[jj] is Bind);
    let bt = pdom(ws[jj]);
    let b = pbod(ws[jj]);
    assert(ws[jj] == ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(b)));
    if j == m {
        proj_field_type_final_p(dty, denv, d, w, hj, cs[jj], bt, b, am.skip(np as int), idx, s);
        hj
    } else {
        let hr = pw_walk(dty, denv, d, io, am, np, idx, s, cs, ws, btm, j + 1);
        let hh = hj + hr;
        deq_p_mono(dty, denv, d, w, cs[jj], ws[jj], hj, hh);
        let j1 = j + 1;
        proj_field_type_mono(dty, denv, d, w, hr, hh, cs[jj + 1], am.skip(pw_skip(j1, np) as int), pw_np(j1, np),
            pw_fld(j1, np) as usize, pw_rem(j1, np, idx as nat), s, btm);
        psq_at(am, np, s, idx as nat, jj);
        assert(cs[jj + 1] == subst_full(b, seq![psq(am, np, s, idx as nat)[jj]], 0));
        if j < np {
            let args = am.skip(jj);
            assert(args[0] == am[jj]);
            assert(args.drop_first() =~= am.skip(jj + 1));
            proj_field_type_param_step_p(dty, denv, d, w, hh, cs[jj], bt, b, args, (np - j) as nat, 0, idx as nat, s, btm);
        } else {
            let fld = (j - np) as usize;
            assert(fld + 1 == (j1 - np) as usize);
            proj_field_type_field_step_p(dty, denv, d, w, hh, cs[jj], bt, b, am.skip(np as int), fld, (idx - (j - np)) as nat, s, btm);
        }
        hh
    }
}

/// REGULARITY, PROJECTION: the field type the kernel's walk returns.
#[verifier::spinoff_prover]
pub proof fn ci_proj(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
)
    requires
        pwalk_ok(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm),
    ensures
        ci(dty, denv, g, ExprSpec::Proj(idx, Box::new(s)), btm),
{
    let w = IoMode::InferWt;
    let e = ExprSpec::Proj(idx, Box::new(s));
    let np = denv.ctor_np[cid] as nat;
    let m = np + idx as nat;
    let sp = spine_app(ExprSpec::Const(ind, ls), am);
    let cty = ctor_ty_at(dty, cid, ls);
    if kh(dty, denv) {
        rctx_mono(g, s, e);
        rctx_mono(g, e, s);
        pwalk_reach(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, m);
        assert(cwh(dty, denv, g, cs[m as int], ws[m as int]));
        assert(ws[m as int] is Bind);
        rctx_mono(g, btm, ws[m as int]);
        sub_trans(rctx(g, btm), rctx(g, ws[m as int]), rctx(g, cs[m as int]));
        sub_trans(rctx(g, btm), rctx(g, cs[m as int]), rctx(g, s));
        sub_trans(rctx(g, btm), rctx(g, s), rctx(g, e));
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e)
            implies #[trigger] ci_at(dty, denv, d, e, btm) by {
            gen_proj(dty, denv, d, idx, s);
            rctx_part(g, s, e, d);
            let (ts, fs, hs) = ci_use(dty, denv, g, d, s, sp);
            let (tsp, l0) = choose|t: ExprSpec, l: LevelSpec| #![trigger typed(dty, denv, d, sp, t), tconv(dty, denv, d, t, ExprSpec::Sort(l))]
                typed(dty, denv, d, sp, t) && tconv(dty, denv, d, t, ExprSpec::Sort(l));
            let (sty, fx) = rt_at(dty, denv, d, s);
            rtyped_closed(dty, denv, d, s);
            s_sound(dty, denv, d, s, ts, sty, fs, fx);
            assert(deq_p_any(dty, denv, d, w, ts, sp));
            kconv_wt_implies_tconv(dty, denv, d, ts, sp);
            tconv_symm(dty, denv, d, ts, sty);
            tconv_trans(dty, denv, d, sty, ts, sp);
            let hx = choose|h: nat| #[trigger] deq_p(dty, denv, d, IoMode::Real, sty, sp, h);
            // every stage, then the InferWt walk
            assert forall|k: int| 0 <= k <= m implies #[trigger] deq_p_any(dty, denv, d, w, cs[k], ws[k]) by {
                pwalk_stage(dty, denv, g, d, idx, s, ind, cid, ls, am, cs, ws, btm, sty, fx, hx, tsp, k as nat);
            }
            pwalk_stage(dty, denv, g, d, idx, s, ind, cid, ls, am, cs, ws, btm, sty, fx, hx, tsp, m);
            let hw = pw_walk(dty, denv, d, w, am, np, idx, s, cs, ws, btm, 0);
            assert(am.skip(0) =~= am);
            // the field type is a type: the domain of the last Pi
            let wm = ws[m as int];
            assert(wm == ExprSpec::Bind(BinderKind::Pi, Box::new(btm), Box::new(pbod(wm))));
            let (tw, lw) = choose|t: ExprSpec, l: LevelSpec| #![trigger typed(dty, denv, d, wm, t), tconv(dty, denv, d, t, ExprSpec::Sort(l))]
                typed(dty, denv, d, wm, t) && tconv(dty, denv, d, t, ExprSpec::Sort(l));
            let fw = choose|f: nat| #[trigger] types_to(dty, denv, d, IoMode::Real, wm, tw, f);
            let (btt, g1, dl) = gen_bind_ty(dty, denv, d, BinderKind::Pi, btm, pbod(wm), tw, fw);
            assert(typed(dty, denv, d, btm, btt));
            tconv_of(dty, denv, d, btt, ExprSpec::Sort(dl), g1);
            assert(is_type(dty, denv, d, btm));
            // the InferWt projection rule
            assert(struct_ok1(dty, denv, ind, cid));
            crate::expr_model::subst_expr_levels_sat_rel(dty[cid].1, dty[cid].0, ls);
            let ff = fs + hs + hw;
            types_to_mono(dty, denv, d, w, s, ts, fs, ff);
            let hsp = choose|h: nat| #[trigger] deq_p(dty, denv, d, w, ts, sp, h);
            deq_p_mono(dty, denv, d, w, ts, sp, hsp, ff + hsp);
            let f2 = ff + hsp;
            types_to_mono(dty, denv, d, w, s, ts, ff, f2);
            assert(types_to(dty, denv, d, w, ExprSpec::Const(cid, ls), cty, f2));
            proj_field_type_mono(dty, denv, d, w, hw, f2, cty, am, np, 0, idx as nat, s, btm);
            assert(denv.ctor_num_params(cid) == Some(np as u16));
            assert(proj_marker(f2, ts, ind, ls, am, cid, np as u16, cty));
            assert(types_to(dty, denv, d, w, e, btm, f2 + 1));
            deq_p_refl(dty, denv, d, w, btm, 0);
            assert(wt_marker(btm, f2 + 1));
        }
    }
}

/// CHECK, PROJECTION: the structure checks at the kernel's structure type,
/// so the stages are types and the real walk goes through, at exactly the
/// kernel's field type.
#[verifier::spinoff_prover]
pub proof fn cc_proj(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
)
    requires
        pwalk_ok(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm),
        crate::kclaims::cc(dty, denv, g, s, spine_app(ExprSpec::Const(ind, ls), am)),
    ensures
        crate::kclaims::cc(dty, denv, g, ExprSpec::Proj(idx, Box::new(s)), btm),
{
    let r = IoMode::Real;
    let e = ExprSpec::Proj(idx, Box::new(s));
    let np = denv.ctor_np[cid] as nat;
    let m = np + idx as nat;
    let sp = spine_app(ExprSpec::Const(ind, ls), am);
    let cty = ctor_ty_at(dty, cid, ls);
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d)
            implies #[trigger] crate::kclaims::cc_at(dty, denv, d, e, btm) by {
            rctx_part(g, s, e, d);
            let sty = crate::kclaims::cc_use(dty, denv, g, d, s, sp);
            rtyped_closed(dty, denv, d, s);
            let _ = ci_use(dty, denv, g, d, s, sp);
            let (tsp, l0) = choose|t: ExprSpec, l: LevelSpec| #![trigger typed(dty, denv, d, sp, t), tconv(dty, denv, d, t, ExprSpec::Sort(l))]
                typed(dty, denv, d, sp, t) && tconv(dty, denv, d, t, ExprSpec::Sort(l));
            let fx = choose|n: nat| #[trigger] types_to(dty, denv, d, r, s, sty, n);
            let hx = choose|h: nat| #[trigger] deq_p(dty, denv, d, r, sty, sp, h);
            assert forall|k: int| 0 <= k <= m implies #[trigger] deq_p_any(dty, denv, d, r, cs[k], ws[k]) by {
                pwalk_stage(dty, denv, g, d, idx, s, ind, cid, ls, am, cs, ws, btm, sty, fx, hx, tsp, k as nat);
            }
            let hw = pw_walk(dty, denv, d, r, am, np, idx, s, cs, ws, btm, 0);
            assert(am.skip(0) =~= am);
            assert(struct_ok1(dty, denv, ind, cid));
            crate::expr_model::subst_expr_levels_sat_rel(dty[cid].1, dty[cid].0, ls);
            let f2 = fx + hx + hw;
            types_to_mono(dty, denv, d, r, s, sty, fx, f2);
            deq_p_mono(dty, denv, d, r, sty, sp, hx, f2);
            assert(types_to(dty, denv, d, r, ExprSpec::Const(cid, ls), cty, f2));
            proj_field_type_mono(dty, denv, d, r, hw, f2, cty, am, np, 0, idx as nat, s, btm);
            assert(denv.ctor_num_params(cid) == Some(np as u16));
            assert(proj_marker(f2, sty, ind, ls, am, cid, np as u16, cty));
            assert(types_to(dty, denv, d, r, e, btm, f2 + 1));
            assert(typed(dty, denv, d, e, btm));
            tconv_refl(dty, denv, d, btm);
        }
    }
}

} // verus!
