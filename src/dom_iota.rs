//! SOUNDNESS OF IOTA (steps 4-5 of the S6.4c/d plan in
//! docs/TYPED_TARGET.md): pieces for relating the recursor's application
//! at a constructor application to its rule's right-hand side.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_model::*;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::dom_bound::{spine_mem, spine_mem_intro, args_w};
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A larger type has the same table shape, entry by entry above.
pub proof fn tbl_le(a: Cpt, a2: Cpt, p: int)
    requires
        a is Nd,
        le(a, a2),
        0 <= p < tbl(a->Nd_1).len(),
        tbl(a->Nd_1)[p] is Nd,
    ensures
        a2 is Nd,
        p < tbl(a2->Nd_1).len(),
        tbl(a2->Nd_1)[p] is Nd,
        tbl(a2->Nd_1)[p]->Nd_1.len() == tbl(a->Nd_1)[p]->Nd_1.len(),
        forall|i: int| 0 <= i < tbl(a->Nd_1)[p]->Nd_1.len() ==> le(#[trigger] tbl(a->Nd_1)[p]->Nd_1[i], tbl(a2->Nd_1)[p]->Nd_1[i]),
{
    let (ts, ts2) = (a->Nd_1, a2->Nd_1);
    crate::dom_sem::nd_le_inv(a->Nd_0, ts, a2);
    let l = ts.len() - 1;
    assert(ts.last() == ts[l] && ts2.last() == ts2[l]);
    crate::dom_sem::nd_le_inv(ts[l]->Nd_0, ts[l]->Nd_1, ts2[l]);
    let (b, b2) = (tbl(ts)[p], tbl(ts2)[p]);
    crate::dom_sem::nd_le_inv(b->Nd_0, b->Nd_1, b2);
}

/// A TYPED VALUE'S RECURSIVE FIELD, where a code above its type marks the
/// field recursive, is typed at the type itself (or bottom).
pub proof fn rec_field_typed(n: nat, u: Cpt, a: Cpt, c0: Cpt, k: int)
    requires
        has_type(n, u, a),
        u is Nd && u->Nd_0 is Con,
        0 <= k < u->Nd_1.len(),
        le(a, c0),
        c0 is Nd,
        (u->Nd_0->Con_1 as int) < tbl(c0->Nd_1).len(),
        tbl(c0->Nd_1)[u->Nd_0->Con_1 as int] is Nd,
        k < tbl(c0->Nd_1)[u->Nd_0->Con_1 as int]->Nd_1.len(),
        tbl(c0->Nd_1)[u->Nd_0->Con_1 as int]->Nd_1[k] == rmark(),
    ensures
        u->Nd_1[k] is Bot || has_type(n, u->Nd_1[k], a),
{
    let p = u->Nd_0->Con_1 as int;
    let f = u->Nd_1[k];
    assert(a is Nd && a->Nd_0 is Ty);
    let es = tbl(a->Nd_1)[p]->Nd_1;
    assert(f is Bot || (es[k] == rmark() && has_type(n, f, a)) || (is_centry(es[k]) && has_type(n, f, ecode(es[k]))));
    tbl_le(a, c0, p);
    let e = es[k];
    assert(le(e, rmark()));
    assert(wf(a)) by {
        assert(stg(n, a));
    }
    if !(e is Bot) {
        tbl_wf(a);
        assert(wf(tbl(a->Nd_1)[p]->Nd_1[k]));
        head_le(e, rmark());
        crate::dom_sem::nd_le_inv(e->Nd_0, e->Nd_1, rmark());
        assert(e->Nd_1 =~= Seq::<Cpt>::empty());
        assert(e == rmark());
    }
}

/// OVER VARIABLE ARGUMENTS, a closed head's spine denotes alike in two
/// environments giving the variables the same values.
pub proof fn var_spine_transfer(sig: Sig, h: ExprSpec, vs1: Seq<nat>, vs2: Seq<nat>, rho1: Env, rho2: Env, u: Cpt)
    requires
        crate::expr_model::nlbv(h) == 0,
        vs1.len() == vs2.len(),
        forall|q: int| 0 <= q < vs1.len() ==> #[trigger] rho1(vs1[q]) == rho2(vs2[q]),
        mem(sig, spine_app(h, Seq::new(vs1.len(), |q: int| ExprSpec::Var(vs1[q]))), rho1, u),
    ensures
        mem(sig, spine_app(h, Seq::new(vs2.len(), |q: int| ExprSpec::Var(vs2[q]))), rho2, u),
{
    let a1 = Seq::new(vs1.len(), |q: int| ExprSpec::Var(vs1[q]));
    let a2 = Seq::new(vs2.len(), |q: int| ExprSpec::Var(vs2[q]));
    let (hw, ws) = spine_mem(sig, h, a1, rho1, u);
    crate::dom_model::mem_closed_env(sig, h, rho1, hw);
    crate::dom_model::mem_closed_env(sig, h, rho2, hw);
    reveal(mem);
    assert forall|q: int| 0 <= q < a2.len() implies #[trigger] mem(sig, a2[q], rho2, ws[q]) && wf(ws[q]) by {
        assert(mem(sig, a1[q], rho1, ws[q]));
        let w = choose|w: Wit| #[trigger] mem_w(sig, ExprSpec::Var(vs1[q]), rho1, ws[q], w);
        assert(rho1(vs1[q]) == rho2(vs2[q]));
        assert(mem_w(sig, ExprSpec::Var(vs2[q]), rho2, ws[q], Wit::Nil));
    }
    spine_mem_intro(sig, h, a2, rho2, hw, ws, u);
}

/// A spine over two argument lists in turn.
pub proof fn spine_concat(h: ExprSpec, a: Seq<ExprSpec>, b: Seq<ExprSpec>)
    ensures
        spine_app(h, a + b) == spine_app(spine_app(h, a), b),
    decreases b.len(),
{
    if b.len() > 0 {
        spine_concat(h, a, b.subrange(0, b.len() - 1));
        assert((a + b).subrange(0, (a + b).len() - 1) =~= a + b.subrange(0, b.len() - 1));
        assert((a + b)[(a + b).len() - 1] == b[b.len() - 1]);
    } else {
        assert(a + b =~= a);
    }
}

/// The parameters instantiated by distinct names are the instance.
pub proof fn plevels_inst(ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        ks.len() == vs.len(),
        forall|i: int, j: int| 0 <= i < ks.len() && 0 <= j < ks.len() && #[trigger] ks[i] == #[trigger] ks[j] ==> i == j,
    ensures
        crate::level_model::subst_levels_spec(crate::rec_canon::plevels(ks), ks, vs) == vs,
{
    let r = crate::level_model::subst_levels_spec(crate::rec_canon::plevels(ks), ks, vs);
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] r[i] == vs[i] by {
        assert forall|j: int| 0 <= j < i implies ks[j] != ks[i] by {}
        crate::level_model::find_level_idx_first_match(ks, ks[i], i as nat);
    }
    assert(r =~= vs);
}

/// Closed simple types have no loose variables.
pub proof fn simple_closed(sig: Sig, ind: u64, e: ExprSpec)
    requires
        crate::rec_canon::simple_app(sig, ind, e) || crate::rec_canon::simple_ty(sig, ind, e),
    ensures
        crate::expr_model::nlbv(e) == 0,
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        simple_closed(sig, ind, *f);
        simple_closed(sig, ind, *x);
    }
}

/// The fields after `ws` more arguments from position `k`.
pub open spec fn cacc(fs: Seq<Cpt>, ws: Seq<Cpt>, k: nat, np: nat) -> Seq<Cpt> {
    if k >= np {
        fs + ws
    } else if k + ws.len() > np {
        fs + ws.subrange(np - k, ws.len() as int)
    } else {
        fs
    }
}

/// A CONSTRUCTOR APPROXIMATION APPLIED THROUGH ITS TELESCOPE lies below
/// the value over the fields.
pub proof fn cf_apps(ind: u64, pc: nat, np: nat, ds: Seq<ExprSpec>, body: ExprSpec, fs: Seq<Cpt>, k: nat, v: Cpt, ws: Seq<Cpt>)
    requires
        cf_fun(ind, pc, np, crate::rec_canon::binds(BinderKind::Pi, ds, body), fs, k, v),
        !(body is Bind && body->Bind_0 == BinderKind::Pi),
        wf(v),
        crate::dom_code::aw(ws),
        ws.len() == ds.len(),
    ensures
        le(crate::dom_rec::apps(v, ws), Cpt::Nd(NdKey::Con(ind, pc), cacc(fs, ws, k, np))),
    decreases ds.len(),
{
    if ds.len() == 0 {
        assert(crate::dom_rec::apps(v, ws) == v);
        assert(cacc(fs, ws, k, np) =~= fs);
        if v is Bot {
            reveal_with_fuel(le_set, 1);
        }
        return;
    }
    let (ta, rest) = (ds[0], ds.drop_first());
    let tb = crate::rec_canon::binds(BinderKind::Pi, rest, body);
    assert(crate::rec_canon::binds(BinderKind::Pi, ds, body) == ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb)));
    crate::dom_tele::apps_front(v, ws);
    let w0 = ws[0];
    assert(wf(w0));
    let v2 = app(v, w0);
    let wr = ws.drop_first();
    assert forall|i: int| 0 <= i < wr.len() implies #[trigger] wf(wr[i]) by {
        assert(wr[i] == ws[i + 1]);
    }
    let fs2 = if k < np { fs } else { fs.push(w0) };
    if v is Lam {
        appk_wf(v, w0, true);
        crate::dom_con_rel::cf_app(ind, pc, np, ta, tb, fs, k, v, w0);
    } else {
        assert(v is Bot);
        assert(v2 == Cpt::Bot);
    }
    cf_apps(ind, pc, np, rest, body, fs2, k + 1, v2, wr);
    if k >= np {
        assert(fs.push(w0) + wr =~= fs + ws);
    } else if k + 1 >= np {
        assert(k + 1 == np);
        assert(ws.subrange(np - k, ws.len() as int) =~= wr);
    } else if k + 1 + wr.len() > np {
        assert(ws.subrange(np - k, ws.len() as int) =~= wr.subrange(np - (k + 1), wr.len() as int));
    }
}

/// Applying bottom gives bottom.
pub proof fn apps_bot(ws: Seq<Cpt>)
    ensures
        crate::dom_rec::apps(Cpt::Bot, ws) == Cpt::Bot,
    decreases ws.len(),
{
    if ws.len() > 0 {
        apps_bot(ws.drop_last());
    }
}

/// Applying a non-lambda gives bottom.
pub proof fn apps_nonlam(v: Cpt, ws: Seq<Cpt>)
    requires
        !(v is Lam),
        ws.len() > 0,
    ensures
        crate::dom_rec::apps(v, ws) == Cpt::Bot,
    decreases ws.len(),
{
    if ws.len() > 1 {
        apps_nonlam(v, ws.drop_last());
        assert(app(Cpt::Bot, ws.last()) == Cpt::Bot);
    } else {
        assert(ws.drop_last() =~= Seq::<Cpt>::empty());
        assert(crate::dom_rec::apps(v, ws.drop_last()) == v);
        assert(app(v, ws.last()) == Cpt::Bot);
    }
}

/// A constructor approximation applied to fewer arguments than its
/// telescope is a lambda or bottom.
pub proof fn cf_apps_partial(ind: u64, pc: nat, np: nat, ds: Seq<ExprSpec>, body: ExprSpec, fs: Seq<Cpt>, k: nat, v: Cpt, ws: Seq<Cpt>)
    requires
        cf_fun(ind, pc, np, crate::rec_canon::binds(BinderKind::Pi, ds, body), fs, k, v),
        wf(v),
        crate::dom_code::aw(ws),
        ws.len() < ds.len(),
    ensures
        crate::dom_rec::apps(v, ws) is Lam || crate::dom_rec::apps(v, ws) is Bot,
    decreases ws.len(),
{
    let (ta, rest) = (ds[0], ds.drop_first());
    let tb = crate::rec_canon::binds(BinderKind::Pi, rest, body);
    assert(crate::rec_canon::binds(BinderKind::Pi, ds, body) == ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb)));
    if ws.len() == 0 {
        assert(crate::dom_rec::apps(v, ws) == v);
        return;
    }
    crate::dom_tele::apps_front(v, ws);
    let w0 = ws[0];
    assert(wf(w0));
    let wr = ws.drop_first();
    assert forall|i: int| 0 <= i < wr.len() implies #[trigger] wf(wr[i]) by {
        assert(wr[i] == ws[i + 1]);
    }
    if v is Lam {
        appk_wf(v, w0, true);
        crate::dom_con_rel::cf_app(ind, pc, np, ta, tb, fs, k, v, w0);
        cf_apps_partial(ind, pc, np, rest, body, if k < np { fs } else { fs.push(w0) }, k + 1, app(v, w0), wr);
    } else {
        assert(app(v, w0) == Cpt::Bot);
        apps_bot(wr);
    }
}

/// A constructor's type's domains at a level instance.
pub open spec fn ctds(sig: Sig, rid: u64, p: int, clv: Seq<LevelSpec>) -> Seq<ExprSpec> {
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    crate::dom_rec_shape::sls(sh.pdoms + sh.fields[p], sig.consts[sh.ctors[p]].lps, clv)
}

pub open spec fn cbody(sig: Sig, rid: u64, p: int, clv: Seq<LevelSpec>) -> ExprSpec {
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let tc = sig.consts[sh.ctors[p]].ty;
    crate::expr_model::subst_expr_levels(crate::rec_canon::tbody(tc, sh.np + sh.fields[p].len()), sig.consts[sh.ctors[p]].lps, clv)
}

/// The constructor's instantiated type splits into its domains and body,
/// which is no binder.
pub proof fn ctor_ty_split(sig: Sig, rid: u64, p: int, clv: Seq<LevelSpec>)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        0 <= p < crate::dom_rec_ty::rshape(sig, rid).nmin(),
    ensures
        crate::ti_syntax::dty_at(sig, crate::dom_rec_ty::rshape(sig, rid).ctors[p], clv)
            == crate::rec_canon::binds(BinderKind::Pi, ctds(sig, rid, p, clv), cbody(sig, rid, p, clv)),
        !(cbody(sig, rid, p, clv) is Bind),
        ctds(sig, rid, p, clv).len() == crate::dom_rec_ty::rshape(sig, rid).np + crate::dom_rec_ty::rshape(sig, rid).fields[p].len(),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let c = sh.ctors[p];
    let tc = sig.consts[c].ty;
    let nf = sh.fields[p].len();
    assert(tc == crate::rec_canon::binds(BinderKind::Pi, sh.pdoms + sh.fields[p], crate::rec_canon::tbody(tc, sh.np + nf)));
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms + sh.fields[p], crate::rec_canon::tbody(tc, sh.np + nf), sig.consts[c].lps, clv);
    let b = crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(nf, sh.np) + sh.tss[p]);
    assert(crate::rec_canon::tbody(tc, sh.np + nf) == b);
    crate::dom_rec_shape::sl_spine(ExprSpec::Const(sh.ind, sh.us()), crate::rec_canon::vars(nf, sh.np) + sh.tss[p], sig.consts[c].lps, clv);
    crate::dom_rec_ty::spine_const_nonbind(sh.ind, crate::level_model::subst_levels_spec(sh.us(), sig.consts[c].lps, clv),
        crate::dom_rec_shape::sls(crate::rec_canon::vars(nf, sh.np) + sh.tss[p], sig.consts[c].lps, clv));
}

/// THE MAJOR PREMISE: a value below a member of a constructor
/// application's denotation forces the constructor's exact arity; its
/// constructor's position is the constructor's, and its fields lie below
/// projections of the arguments typed along the constructor's type.
#[verifier::spinoff_prover]
pub proof fn iota_major(sig: Sig, rid: u64, p: int, clv: Seq<LevelSpec>, lc: LevelSpec, cargs: Seq<ExprSpec>, rho: Env, wmaj: Cpt, x: Cpt)
    -> (r: (Seq<Cpt>, Seq<Cpt>))
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        0 <= p < crate::dom_rec_ty::rshape(sig, rid).nmin(),
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(Seq::empty(),
            crate::ti_syntax::dty_at(sig, crate::dom_rec_ty::rshape(sig, rid).ctors[p], clv),
            crate::ti_syntax::dty_at(sig, crate::dom_rec_ty::rshape(sig, rid).ctors[p], clv), crate::ti_syntax::sort(lc))),
        forall|i: nat| #[trigger] wf(rho(i)),
        mem(sig, spine_app(ExprSpec::Const(crate::dom_rec_ty::rshape(sig, rid).ctors[p], clv), cargs), rho, wmaj),
        le(x, wmaj),
        wf(x),
        x is Nd && x->Nd_0 is Con,
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let np = sh.np;
        let nf = sh.fields[p].len();
        &&& cargs.len() == np + nf
        &&& x->Nd_0 == NdKey::Con(sh.ind, p as nat)
        &&& x->Nd_1.len() == nf
        &&& crate::dom_tele::chain_ok(sig, ctds(sig, rid, p, clv), bot_env(), r.1, r.0)
        &&& forall|i: int| 0 <= i < cargs.len() ==> #[trigger] mem(sig, cargs[i], rho, r.0[i])
        &&& forall|i: int| 0 <= i < nf ==> le(#[trigger] x->Nd_1[i], r.0[np + i])
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let (np, nf) = (sh.np, sh.fields[p].len());
    let c = sh.ctors[p];
    let ind = sh.ind;
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    ctor_ty_split(sig, rid, p, clv);
    let tds = ctds(sig, rid, p, clv);
    let body = cbody(sig, rid, p, clv);
    let (hwc, cws) = spine_mem(sig, ExprSpec::Const(c, clv), cargs, rho, wmaj);
    assert forall|i: int| 0 <= i < cws.len() implies #[trigger] wf(cws[i]) by {
        assert(mem(sig, cargs[i], rho, cws[i]));
    }
    le_trans(x, wmaj, crate::dom_rec::apps(hwc, cws));
    // the head is a member of the constructor above bottom
    if !crate::dom_model::sem_const(sig, c, clv) {
        crate::dom_bound::nonsem_bot(sig, c, clv, rho);
    }
    if hwc is Bot {
        apps_bot(cws);
        head_le(x, Cpt::Bot);
    }
    crate::dom_sem::mem_sem(sig, c, clv, rho, hwc);
    let (ac, vc) = choose|a: Cpt, v: Cpt| #[trigger] crate::dom_sem::sem_mem(sig, c, clv, hwc, a, v);
    typed_wf(vc, ac);
    typed_wf(ac, Cpt::U);
    head_le(hwc, vc);
    assert(cf_fun(ind, ctor_pos(sig, ind, c) as nat, crate::dom_code::canon_shape(sig, ind).np,
        crate::ti_syntax::dty_at(sig, c, clv), Seq::empty(), 0, vc));
    assert(forall|i: int| 0 <= i < cws.len() ==> le(#[trigger] cws[i], cws[i])) by {
        assert forall|i: int| 0 <= i < cws.len() implies le(#[trigger] cws[i], cws[i]) by {
            le_refl(cws[i]);
        }
    }
    crate::dom_rec::apps_mono(hwc, vc, cws, cws);
    let big = crate::dom_rec::apps(vc, cws);
    le_trans(x, crate::dom_rec::apps(hwc, cws), big);
    // exact arity
    if cargs.len() < np + nf {
        cf_apps_partial(ind, p as nat, np, tds, body, Seq::empty(), 0, vc, cws);
        head_le(x, big);
    }
    if cargs.len() > np + nf {
        let k = (np + nf) as int;
        let (c1, c2) = (cws.subrange(0, k), cws.subrange(k, cws.len() as int));
        assert(c1 + c2 =~= cws);
        crate::dom_rec_ty::apps_concat(vc, c1, c2);
        assert forall|i: int| 0 <= i < c1.len() implies #[trigger] wf(c1[i]) by {
            assert(c1[i] == cws[i]);
        }
        cf_apps(ind, p as nat, np, tds, body, Seq::empty(), 0, vc, c1);
        let v1 = crate::dom_rec::apps(vc, c1);
        crate::dom_rec::apps_wf(vc, c1);
        if !(v1 is Lam) {
            apps_nonlam(v1, c2);
        } else {
            head_le(v1, Cpt::Nd(NdKey::Con(ind, p as nat), cacc(Seq::empty(), c1, 0, np)));
        }
        head_le(x, big);
    }
    assert(cargs.len() == np + nf);
    // along the constructor's type
    let (cws2, _e, _l2, dcs) = crate::dom_tele::tele_apps(sig, Seq::empty(), tds, body, lc, bot_env(), ac, vc, cws);
    assert(crate::dom_sound::fits_env(sig, Seq::empty(), bot_env()));
    cf_apps(ind, p as nat, np, tds, body, Seq::empty(), 0, vc, cws2);
    let node = Cpt::Nd(NdKey::Con(ind, p as nat), cacc(Seq::empty(), cws2, 0, np));
    le_trans(x, big, node);
    head_le(x, node);
    crate::dom_sem::nd_le_inv(x->Nd_0, x->Nd_1, node);
    assert(cacc(Seq::empty(), cws2, 0, np) =~= cws2.subrange(np as int, cws2.len() as int));
    assert forall|i: int| 0 <= i < nf implies le(#[trigger] x->Nd_1[i], cws2[np + i]) by {
        assert(cacc(Seq::empty(), cws2, 0, np)[i] == cws2[np + i]);
    }
    assert forall|i: int| 0 <= i < cargs.len() implies #[trigger] mem(sig, cargs[i], rho, cws2[i]) by {
        assert(mem(sig, cargs[i], rho, cws[i]));
        assert(le(cws2[i], cws[i]));
        assert(wf(cws2[i]));
        mem_down_e(sig, cargs[i], rho, cws[i], cws2[i]);
    }
    (cws2, dcs)
}

/// The recursive call at the `r`-th recursive field in rule `p`'s body.
pub open spec fn ihterm(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int, r: int) -> ExprSpec {
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let k = sh.rposj(p)[r];
    spine_app(ExprSpec::Const(rid, lv), crate::rec_canon::vars(1 + nmin + nf, np) + seq![ExprSpec::Var(nmin + nf)]
        + crate::rec_canon::vars(nf, nmin) + seq![ExprSpec::Var((nf - 1 - k) as nat)])
}

/// Rule `p`'s body: its minor at the fields and the recursive calls.
pub open spec fn rule_body(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int) -> ExprSpec {
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let (nmin, nf) = (sh.nmin(), sh.fields[p].len());
    spine_app(ExprSpec::Var((nmin - 1 - p + nf) as nat),
        crate::rec_canon::vars(0, nf) + Seq::new(sh.rposj(p).len(), |r: int| ihterm(sig, rid, lv, p, r)))
}

/// Rule `p`'s field binders at the instance.
pub open spec fn ftds(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int) -> Seq<ExprSpec> {
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    crate::dom_rec_shape::sls(Seq::new(sh.fields[p].len(), |i: int| sh.field_at(p, i, 1 + sh.nmin())),
        sig.ienv.recs[rid].uparams, lv)
}

/// THE RULE AT THE INSTANCE: a lambda over the recursor's head binders and
/// the fields, of its body.
pub proof fn rule_split(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        0 <= p < crate::dom_rec_ty::rshape(sig, rid).nmin(),
        lv.len() == sig.ienv.recs[rid].uparams.len(),
        forall|i: int, j: int| 0 <= i < sig.ienv.recs[rid].uparams.len() && 0 <= j < sig.ienv.recs[rid].uparams.len()
            && #[trigger] sig.ienv.recs[rid].uparams[i] == #[trigger] sig.ienv.recs[rid].uparams[j] ==> i == j,
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let pre = sh.np + 1 + sh.nmin();
        crate::expr_model::subst_expr_levels(sig.ienv.recs[rid].rules[p].rhs, sig.ienv.recs[rid].uparams, lv)
            == crate::rec_canon::binds(BinderKind::Lam, crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0, pre as int) + ftds(sig, rid, lv, p),
                rule_body(sig, rid, lv, p))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let ind = crate::rec_canon::rec_ind(sig, rid);
    let lm = crate::rec_canon::elim_level(sig, rid, ind);
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let rls = crate::rec_canon::plevels(rd.uparams);
    let (ks, vs) = (rd.uparams, lv);
    let rp = sh.rposj(p);
    let fds = Seq::new(nf, |i: int| sh.field_at(p, i, 1 + nmin));
    let ih = |r: int| {
        let k = rp[r];
        let idx = crate::rec_canon::occ_idx(sh.fields[p][k as int], np, sh.ni);
        let idx2 = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k, idx[q])));
        spine_app(ExprSpec::Const(rid, rls),
            crate::rec_canon::vars(1 + nmin + nf, np) + seq![ExprSpec::Var(nmin + nf)] + crate::rec_canon::vars(nf, nmin) + idx2.push(ExprSpec::Var((nf - 1 - k) as nat)))
    };
    let ihs = Seq::new(rp.len(), ih);
    let body = spine_app(ExprSpec::Var((nmin - 1 - p + nf) as nat), crate::rec_canon::vars(0, nf) + ihs);
    assert(rd.rules[p].rhs == crate::rec_canon::binds(BinderKind::Lam, sh.head_doms(lm) + fds, body));
    crate::dom_rec_shape::sl_binds(BinderKind::Lam, sh.head_doms(lm) + fds, body, ks, vs);
    crate::dom_rec_shape::sls_concat(sh.head_doms(lm), fds, ks, vs);
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(1 + nmin, np));
    crate::dom_rec_shape::sls_concat(sh.head_doms(lm), seq![major], ks, vs);
    assert(crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0, (np + 1 + nmin) as int) =~= crate::dom_rec_shape::sls(sh.head_doms(lm), ks, vs));
    // the body
    crate::dom_rec_shape::sl_spine(ExprSpec::Var((nmin - 1 - p + nf) as nat), crate::rec_canon::vars(0, nf) + ihs, ks, vs);
    crate::dom_rec_shape::sls_concat(crate::rec_canon::vars(0, nf), ihs, ks, vs);
    crate::dom_rec_shape::sl_vars(0, nf, ks, vs);
    plevels_inst(ks, vs);
    assert forall|r: int| 0 <= r < rp.len() implies #[trigger] crate::dom_rec_shape::sls(ihs, ks, vs)[r] == ihterm(sig, rid, lv, p, r) by {
        let k = rp[r];
        let idx = crate::rec_canon::occ_idx(sh.fields[p][k as int], np, sh.ni);
        let idx2 = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k, idx[q])));
        assert(idx2 =~= Seq::<ExprSpec>::empty());
        let args = crate::rec_canon::vars(1 + nmin + nf, np) + seq![ExprSpec::Var(nmin + nf)] + crate::rec_canon::vars(nf, nmin) + idx2.push(ExprSpec::Var((nf - 1 - k) as nat));
        assert(idx2.push(ExprSpec::Var((nf - 1 - k) as nat)) =~= seq![ExprSpec::Var((nf - 1 - k) as nat)]);
        assert(ihs[r] == spine_app(ExprSpec::Const(rid, rls), args));
        crate::dom_rec_shape::sl_spine(ExprSpec::Const(rid, rls), args, ks, vs);
        assert(crate::dom_rec_shape::sls(args, ks, vs) =~= args);
    }
    assert(crate::dom_rec_shape::sls(ihs, ks, vs) =~= Seq::new(rp.len(), |r: int| ihterm(sig, rid, lv, p, r)));
    assert(crate::expr_model::subst_expr_levels(ExprSpec::Var((nmin - 1 - p + nf) as nat), ks, vs) == ExprSpec::Var((nmin - 1 - p + nf) as nat));
}

} // verus!
