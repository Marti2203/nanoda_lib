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
use crate::beta_model::{spine_app, spine_head};
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
pub proof fn cf_apps(ind: u64, pc: nat, sm: bool, np: nat, ds: Seq<ExprSpec>, body: ExprSpec, fs: Seq<Cpt>, k: nat, v: Cpt, ws: Seq<Cpt>)
    requires
        cf_fun(ind, pc, sm, np, crate::rec_canon::binds(BinderKind::Pi, ds, body), fs, k, v),
        !(body is Bind && body->Bind_0 == BinderKind::Pi),
        wf(v),
        crate::dom_code::aw(ws),
        ws.len() == ds.len(),
    ensures
        le(crate::dom_rec::apps(v, ws), Cpt::Nd(NdKey::Con(ind, pc, sm), cacc(fs, ws, k, np))),
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
        crate::dom_con_rel::cf_app(ind, pc, sm, np, ta, tb, fs, k, v, w0);
    } else {
        assert(v is Bot);
        assert(v2 == Cpt::Bot);
    }
    cf_apps(ind, pc, sm, np, rest, body, fs2, k + 1, v2, wr);
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
pub proof fn cf_apps_partial(ind: u64, pc: nat, sm: bool, np: nat, ds: Seq<ExprSpec>, body: ExprSpec, fs: Seq<Cpt>, k: nat, v: Cpt, ws: Seq<Cpt>)
    requires
        cf_fun(ind, pc, sm, np, crate::rec_canon::binds(BinderKind::Pi, ds, body), fs, k, v),
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
        crate::dom_con_rel::cf_app(ind, pc, sm, np, ta, tb, fs, k, v, w0);
        cf_apps_partial(ind, pc, sm, np, rest, body, if k < np { fs } else { fs.push(w0) }, k + 1, app(v, w0), wr);
    } else {
        assert(app(v, w0) == Cpt::Bot);
        apps_bot(wr);
    }
}

/// A constructor's type's domains at a level instance.
pub open spec fn ctds(sig: Sig, rid: u64, p: int, clv: Seq<LevelSpec>) -> Seq<ExprSpec> {
    ctds_s(sig, crate::dom_rec_ty::rshape(sig, rid), p, clv)
}

pub open spec fn cbody(sig: Sig, rid: u64, p: int, clv: Seq<LevelSpec>) -> ExprSpec {
    cbody_s(sig, crate::dom_rec_ty::rshape(sig, rid), p, clv)
}

/// The constructor's instantiated type splits into its domains and body,
/// which is no binder.
pub proof fn ctor_ty_split(sig: Sig, rid: u64, p: int, clv: Seq<LevelSpec>)
    requires
        crate::dom_rec_ty::rec_scope_g(sig, rid),
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

/// `ctds` and `cbody` over an inductive's shape (`ind_scope`), with or
/// without a recursor.
pub open spec fn ctds_s(sig: Sig, sh: crate::rec_canon::IndShape, p: int, clv: Seq<LevelSpec>) -> Seq<ExprSpec> {
    crate::dom_rec_shape::sls(sh.pdoms + sh.fields[p], sig.consts[sh.ctors[p]].lps, clv)
}

pub open spec fn cbody_s(sig: Sig, sh: crate::rec_canon::IndShape, p: int, clv: Seq<LevelSpec>) -> ExprSpec {
    let tc = sig.consts[sh.ctors[p]].ty;
    crate::expr_model::subst_expr_levels(crate::rec_canon::tbody(tc, sh.np + sh.fields[p].len()), sig.consts[sh.ctors[p]].lps, clv)
}

/// `ctor_ty_split` over a shape in scope.
pub proof fn ctor_ty_split_s(sig: Sig, sh: crate::rec_canon::IndShape, p: int, clv: Seq<LevelSpec>)
    requires
        crate::dom_rec_ty::ind_scope(sig, sh),
        0 <= p < sh.nmin(),
    ensures
        crate::ti_syntax::dty_at(sig, sh.ctors[p], clv) == crate::rec_canon::binds(BinderKind::Pi, ctds_s(sig, sh, p, clv), cbody_s(sig, sh, p, clv)),
        !(cbody_s(sig, sh, p, clv) is Bind),
        ctds_s(sig, sh, p, clv).len() == sh.np + sh.fields[p].len(),
{
    reveal(crate::dom_code::ind_side);
    let c = sh.ctors[p];
    let tc = sig.consts[c].ty;
    let nf = sh.fields[p].len();
    assert(c == sh.ctors[p]);
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
pub proof fn iota_major(ss: Sig, sig: Sig, rid: u64, p: int, clv: Seq<LevelSpec>, lc: LevelSpec, cargs: Seq<ExprSpec>, rho: Env, wmaj: Cpt, x: Cpt)
    -> (r: (Seq<Cpt>, Seq<Cpt>))
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        crate::dom_rec_ty::rec_scope(sig, rid),
        0 <= p < crate::dom_rec_ty::rshape(sig, rid).nmin(),
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(Seq::empty(),
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
        &&& x->Nd_0 == NdKey::Con(sh.ind, p as nat, crate::dom_code::smash(sig, sh.ind))
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
    assert(cf_fun(ind, ctor_pos(sig, ind, c) as nat, crate::dom_code::smash(sig, ind), crate::dom_code::canon_shape(sig, ind).np,
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
        cf_apps_partial(ind, p as nat, crate::dom_code::smash(sig, ind), np, tds, body, Seq::empty(), 0, vc, cws);
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
        cf_apps(ind, p as nat, crate::dom_code::smash(sig, ind), np, tds, body, Seq::empty(), 0, vc, c1);
        let v1 = crate::dom_rec::apps(vc, c1);
        crate::dom_rec::apps_wf(vc, c1);
        if !(v1 is Lam) {
            apps_nonlam(v1, c2);
        } else {
            head_le(v1, Cpt::Nd(NdKey::Con(ind, p as nat, crate::dom_code::smash(sig, ind)), cacc(Seq::empty(), c1, 0, np)));
        }
        head_le(x, big);
    }
    assert(cargs.len() == np + nf);
    // along the constructor's type
    let (cws2, _e, _l2, dcs) = crate::dom_tele::tele_apps(ss, sig, Seq::empty(), tds, body, lc, bot_env(), ac, vc, cws);
    assert(crate::dom_sound::fits_env(sig, Seq::empty(), bot_env()));
    cf_apps(ind, p as nat, crate::dom_code::smash(sig, ind), np, tds, body, Seq::empty(), 0, vc, cws2);
    let node = Cpt::Nd(NdKey::Con(ind, p as nat, crate::dom_code::smash(sig, ind)), cacc(Seq::empty(), cws2, 0, np));
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

/// The body after all of a telescope's binders.
pub proof fn tbody_binds(ds: Seq<ExprSpec>, b: ExprSpec)
    ensures
        crate::rec_canon::tbody(crate::rec_canon::binds(BinderKind::Pi, ds, b), ds.len()) == b,
    decreases ds.len(),
{
    if ds.len() > 0 {
        tbody_binds(ds.drop_first(), b);
    }
}

/// The recursor's major domain at the instance: the inductive at the
/// parameters.
pub proof fn major_form(sig: Sig, rid: u64, lv: Seq<LevelSpec>)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let pre = sh.np + 1 + sh.nmin();
        &&& crate::dom_rec_ty::rtds(sig, rid, lv).len() == pre + 1
        &&& crate::dom_rec_ty::rtds(sig, rid, lv)[pre as int] == spine_app(ExprSpec::Const(sh.ind,
            crate::level_model::subst_levels_spec(sh.us(), sig.ienv.recs[rid].uparams, lv)), crate::rec_canon::vars(1 + sh.nmin(), sh.np))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let ind = crate::rec_canon::rec_ind(sig, rid);
    let lm = crate::rec_canon::elim_level(sig, rid, ind);
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(1 + sh.nmin(), sh.np));
    assert(sh.pdoms.len() == sh.np);
    assert((sh.head_doms(lm) + seq![major])[(sh.np + 1 + sh.nmin()) as int] == major);
    crate::dom_rec_shape::sl_spine(ExprSpec::Const(sh.ind, sh.us()), crate::rec_canon::vars(1 + sh.nmin(), sh.np), rd.uparams, lv);
    crate::dom_rec_shape::sl_vars(1 + sh.nmin(), sh.np, rd.uparams, lv);
}

/// A MEMBER OF THE MAJOR'S DOMAIN lies below the inductive's canonical
/// code at witnesses of the parameters (or is bottom).
pub proof fn major_code(sig: Sig, rid: u64, lv: Seq<LevelSpec>, env: Env, d: Cpt) -> (ws: Seq<Cpt>)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        mem(sig, spine_app(ExprSpec::Const(crate::dom_rec_ty::rshape(sig, rid).ind,
            crate::level_model::subst_levels_spec(crate::dom_rec_ty::rshape(sig, rid).us(), sig.ienv.recs[rid].uparams, lv)),
            crate::rec_canon::vars(1 + crate::dom_rec_ty::rshape(sig, rid).nmin(), crate::dom_rec_ty::rshape(sig, rid).np)), env, d),
        forall|i: nat| #[trigger] wf(env(i)),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let us2 = crate::level_model::subst_levels_spec(sh.us(), sig.ienv.recs[rid].uparams, lv);
        d is Bot || ((crate::dom_code::canon_ok(sig, sh.ind) ==> crate::dom_code::tabled(sig, sh.ind, us2, ws))
            && le(d, crate::dom_code::canon_code(sig, sh.ind, us2, ws))
            && ws.len() == sh.np && crate::dom_code::aw(ws)
            && forall|q: int| 0 <= q < sh.np ==> #[trigger] le(ws[q], env((1 + sh.nmin() + sh.np - 1 - q) as nat)))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let ind = sh.ind;
    crate::dom_rec_ty::scope_canon(sig, rid);
    let us2 = crate::level_model::subst_levels_spec(sh.us(), sig.ienv.recs[rid].uparams, lv);
    let args = crate::rec_canon::vars(1 + sh.nmin(), sh.np);
    if !crate::dom_model::sem_const(sig, ind, us2) {
        assert(sig.consts.contains_key(ind) && sig.consts[ind].val is None);
        crate::dom_bound::nonsem_bot(sig, ind, us2, env);
        crate::dom_bound::spine_bot(sig, ExprSpec::Const(ind, us2), args, env, d);
        return Seq::empty();
    }
    // the inductive's type: parameters, then a sort
    let ti = sig.consts[ind].ty;
    let lps = sig.consts[ind].lps;
    assert(sh.idoms.len() == 0);
    assert(sh.pdoms + sh.idoms =~= sh.pdoms);
    let b = crate::rec_canon::tbody(ti, sh.np + sh.ni);
    assert(ti == crate::rec_canon::binds(BinderKind::Pi, sh.pdoms, b));
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms, b, lps, us2);
    let pd2 = crate::dom_rec_shape::sls(sh.pdoms, lps, us2);
    let b2 = crate::expr_model::subst_expr_levels(b, lps, us2);
    crate::dom_rec_shape::tarity_binds(pd2, b2);
    tbody_binds(pd2, b2);
    let ws = crate::dom_bound::tf_spine(sig, ind, us2, args, env, d);
    assert(b2 is Sort);
    assert forall|q: int| 0 <= q < sh.np implies #[trigger] le(ws[q], env((1 + sh.nmin() + sh.np - 1 - q) as nat)) by {
        crate::dom_bound::args_w_at(sig, args, env, ws, q);
        crate::dom_rec_end::var_arg_le(sig, 1 + sh.nmin(), sh.np, env, q, ws[q]);
    }
    assert forall|q: int| 0 <= q < ws.len() implies #[trigger] wf(ws[q]) by {
        crate::dom_bound::args_w_at(sig, args, env, ws, q);
    }
    ws
}

/// ALONG A TYPED CHAIN, the major value's recursive fields are typed at the
/// major's domain code (or bottom).
pub proof fn rec_field_ok(sig: Sig, rid: u64, lv: Seq<LevelSpec>, ds: Seq<Cpt>, xs: Seq<Cpt>, k: int)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv), bot_env(), ds, xs),
        crate::dom_rec::rec_ok(sig, rid, xs),
        0 <= k < xs.last()->Nd_1.len(),
        crate::rec_canon::direct_occ(crate::dom_rec_ty::rshape(sig, rid).fields[xs.last()->Nd_0->Con_1 as int][k],
            crate::dom_rec_ty::rshape(sig, rid).ind, crate::dom_rec_ty::rshape(sig, rid).us(),
            crate::dom_rec_ty::rshape(sig, rid).np, crate::dom_rec_ty::rshape(sig, rid).ni, k as nat),
    ensures
        xs.last()->Nd_1[k] is Bot || typed(xs.last()->Nd_1[k], ds[xs.len() - 1]),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let pre = sh.np + 1 + sh.nmin();
    let tds = crate::dom_rec_ty::rtds(sig, rid, lv);
    major_form(sig, rid, lv);
    let x = xs.last();
    let p = x->Nd_0->Con_1 as int;
    let dm = ds[pre as int];
    let env = crate::dom_tele::exts(bot_env(), xs.subrange(0, pre as int));
    assert(crate::dom_sound::dfit(sig, tds[pre as int], env, dm, xs[pre as int]));
    assert(xs.len() == pre + 1);
    assert(xs[pre as int] == x);
    assert forall|i: nat| #[trigger] wf(env(i)) by {
        crate::dom_rec_ty::exts_at(bot_env(), xs.subrange(0, pre as int), i);
        if i < pre {
            let j = pre - 1 - i;
            assert(crate::dom_sound::dfit(sig, tds[j as int], crate::dom_tele::exts(bot_env(), xs.subrange(0, j as int)), ds[j as int], xs[j as int]));
            typed_wf(xs[j as int], ds[j as int]);
        }
    }
    let ws = major_code(sig, rid, lv, env, dm);
    typed_wf(x, dm);
    let n = cstage(x, dm);
    typed_up(x, dm, n);
    if dm is Bot {
        ty_of_bot(n, x);
    }
    let us2 = crate::level_model::subst_levels_spec(sh.us(), sig.ienv.recs[rid].uparams, lv);
    let c0 = crate::dom_code::canon_code(sig, sh.ind, us2, ws);
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    assert(sh.fields[p].len() == sig.ienv.recs[rid].rules[p].nfields);
    if !crate::dom_code::canon_ok(sig, sh.ind) {
        // no table: nothing is typed at the code but bottom
        assert(!crate::dom_code::tabled(sig, sh.ind, us2, ws));
        assert(c0->Nd_1.last() == Cpt::Nd(NdKey::Tag(2), Seq::empty()));
        assert(tbl(c0->Nd_1) =~= Seq::<Cpt>::empty());
        assert(p < tbl(dm->Nd_1).len() && tbl(dm->Nd_1)[p] is Nd);
        tbl_le(dm, c0, p);
        assert(false);
    }
    crate::dom_code::canon_rmark(sig, sh.ind, us2, ws, p as nat, k as nat);
    rec_field_typed(n, x, dm, c0, k);
    if !(x->Nd_1[k] is Bot) {
        typed_down(x->Nd_1[k], dm, n);
    }
}

/// ALONG A TYPED CHAIN, the major's domain code lies below its inductive's
/// canonical table (docs/TYPED_TARGET.md, S6 "Parameters", P2b).
pub proof fn major_bnd(sig: Sig, rid: u64, lv: Seq<LevelSpec>, ds: Seq<Cpt>, xs: Seq<Cpt>)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv), bot_env(), ds, xs),
    ensures
        ds[(crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int] is Bot
            || crate::dom_lift::tbl_canon(sig, crate::dom_rec_ty::rshape(sig, rid).ind, xs.subrange(0, crate::dom_rec_ty::rshape(sig, rid).np as int),
                ds[(crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int]),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let pre = sh.np + 1 + sh.nmin();
    let tds = crate::dom_rec_ty::rtds(sig, rid, lv);
    major_form(sig, rid, lv);
    let dm = ds[pre as int];
    let env = crate::dom_tele::exts(bot_env(), xs.subrange(0, pre as int));
    assert(crate::dom_sound::dfit(sig, tds[pre as int], env, dm, xs[pre as int]));
    assert forall|i: nat| #[trigger] wf(env(i)) by {
        crate::dom_rec_ty::exts_at(bot_env(), xs.subrange(0, pre as int), i);
        if i < pre {
            let j = pre - 1 - i;
            assert(crate::dom_sound::dfit(sig, tds[j as int], crate::dom_tele::exts(bot_env(), xs.subrange(0, j as int)), ds[j as int], xs[j as int]));
            typed_wf(xs[j as int], ds[j as int]);
        }
    }
    let ws = major_code(sig, rid, lv, env, dm);
    crate::dom_rec_ty::scope_canon(sig, rid);
    typed_wf(xs[pre as int], dm);
    if !(dm is Bot) {
        let us2 = crate::level_model::subst_levels_spec(sh.us(), sig.ienv.recs[rid].uparams, lv);
        crate::dom_lift::canon_is_tbl(sig, sh.ind, us2, ws);
        crate::dom_lift::tbl_canon_le(sig, sh.ind, ws, dm, crate::dom_code::canon_code(sig, sh.ind, us2, ws));
        // the parameters' codes lie below their values
        let pv = xs.subrange(0, sh.np as int);
        assert forall|q: int| 0 <= q < sh.np implies le(#[trigger] ws[q], pv[q]) by {
            crate::dom_rec_ty::exts_at(bot_env(), xs.subrange(0, pre as int), (1 + sh.nmin() + sh.np - 1 - q) as nat);
        }
        assert forall|q: int| 0 <= q < pv.len() implies #[trigger] wf(pv[q]) by {
            assert(wf(env((pre - 1 - q) as nat)));
            crate::dom_rec_ty::exts_at(bot_env(), xs.subrange(0, pre as int), (pre - 1 - q) as nat);
        }
        crate::dom_lift::tbl_canon_mono(sig, sh.ind, ws, pv, dm);
    }
}

/// Variables as a sequence of indices.
pub open spec fn vidx(from: nat, n: nat) -> Seq<nat> {
    Seq::new(n, |q: int| (from + n - 1 - q) as nat)
}

pub proof fn vars_vidx(from: nat, n: nat)
    ensures
        crate::rec_canon::vars(from, n) == Seq::new(n, |q: int| ExprSpec::Var(vidx(from, n)[q])),
{
    assert(crate::rec_canon::vars(from, n) =~= Seq::new(n, |q: int| ExprSpec::Var(vidx(from, n)[q])));
}

/// THE MAJOR'S DOMAIN, MOVED to where the parameters sit at `from`.
pub proof fn maj_transfer(sig: Sig, rid: u64, lv: Seq<LevelSpec>, xs: Seq<Cpt>, env: Env, from: nat, d: Cpt)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        xs.len() >= crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin(),
        mem(sig, crate::dom_rec_ty::rtds(sig, rid, lv)[(crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int],
            crate::dom_tele::exts(bot_env(), xs.subrange(0, (crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int)), d),
        forall|q: int| 0 <= q < crate::dom_rec_ty::rshape(sig, rid).np ==>
            #[trigger] env((from + crate::dom_rec_ty::rshape(sig, rid).np - 1 - q) as nat) == xs[q],
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        mem(sig, spine_app(ExprSpec::Const(sh.ind, crate::level_model::subst_levels_spec(sh.us(), sig.ienv.recs[rid].uparams, lv)),
            crate::rec_canon::vars(from, sh.np)), env, d)
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = np + 1 + nmin;
    major_form(sig, rid, lv);
    let us2 = crate::level_model::subst_levels_spec(sh.us(), sig.ienv.recs[rid].uparams, lv);
    let h = ExprSpec::Const(sh.ind, us2);
    let e1 = crate::dom_tele::exts(bot_env(), xs.subrange(0, pre as int));
    let (v1, v2) = (vidx(1 + nmin, np), vidx(from, np));
    vars_vidx(1 + nmin, np);
    vars_vidx(from, np);
    assert forall|q: int| 0 <= q < v1.len() implies #[trigger] e1(v1[q]) == env(v2[q]) by {
        crate::dom_rec_ty::exts_at(bot_env(), xs.subrange(0, pre as int), v1[q]);
        assert(env((from + np - 1 - q) as nat) == xs[q]);
    }
    var_spine_transfer(sig, h, v1, v2, e1, env, d);
}

/// Recursor membership as the model will have it once the recursor is
/// interpreted: bottom, or below a typed approximation of its code
/// function.
pub open spec fn rsem(sig: Sig, rid: u64, ls: Seq<LevelSpec>, u: Cpt, a: Cpt, v: Cpt) -> bool {
    &&& wf(u)
    &&& le(u, v)
    &&& typed(a, Cpt::U)
    &&& typed(v, a)
    &&& rf_fun(sig, rid, crate::ti_syntax::dty_at(sig, rid, ls), Seq::empty(), v)
    &&& mem(sig, crate::ti_syntax::dty_at(sig, rid, ls), bot_env(), a)
}

pub open spec fn rec_wired(sig: Sig) -> bool {
    forall|rid: u64, ls: Seq<LevelSpec>, rho: Env, u: Cpt|
        crate::dom_rec_end::rec_hyps(sig, rid) && crate::dom_model::sem_const(sig, rid, ls) ==>
        (#[trigger] mem(sig, ExprSpec::Const(rid, ls), rho, u) == (u is Bot || exists|a: Cpt, v: Cpt| #[trigger] rsem(sig, rid, ls, u, a, v)))
}

/// The model interprets its recursors so: bottom, or below a typed
/// approximation of the code function.
pub proof fn rec_wired_holds(sig: Sig)
    ensures
        rec_wired(sig),
{
    assert forall|rid: u64, ls: Seq<LevelSpec>, rho: Env, u: Cpt|
        crate::dom_rec_end::rec_hyps(sig, rid) && crate::dom_model::sem_const(sig, rid, ls) implies
        (#[trigger] mem(sig, ExprSpec::Const(rid, ls), rho, u) == (u is Bot || exists|a: Cpt, v: Cpt| #[trigger] rsem(sig, rid, ls, u, a, v))) by {
        crate::dom_sem::mem_sem(sig, rid, ls, rho, u);
        assert forall|a: Cpt, v: Cpt| #[trigger] crate::dom_sem::sem_mem(sig, rid, ls, u, a, v) == rsem(sig, rid, ls, u, a, v) by {}
        if exists|a: Cpt, v: Cpt| #[trigger] rsem(sig, rid, ls, u, a, v) {
            let (a, v) = choose|a: Cpt, v: Cpt| #[trigger] rsem(sig, rid, ls, u, a, v);
            assert(crate::dom_sem::sem_mem(sig, rid, ls, u, a, v));
        }
        if exists|a: Cpt, v: Cpt| #[trigger] crate::dom_sem::sem_mem(sig, rid, ls, u, a, v) {
            let (a, v) = choose|a: Cpt, v: Cpt| #[trigger] crate::dom_sem::sem_mem(sig, rid, ls, u, a, v);
            assert(rsem(sig, rid, ls, u, a, v));
        }
    }
}

/// Variable members: a value is a member of a variable holding it.
pub proof fn var_mem(sig: Sig, i: nat, env: Env)
    requires
        wf(env(i)),
    ensures
        mem(sig, ExprSpec::Var(i), env, env(i)),
{
    reveal(mem);
    le_refl(env(i));
    assert(mem_w(sig, ExprSpec::Var(i), env, env(i), Wit::Nil));
}

/// THE RECURSIVE CALL at a recursive field, under the rule's lambda
/// environment, holds the recursor's value there.
#[verifier::spinoff_prover]
pub proof fn ih_mem(ss: Sig, sig: Sig, rid: u64, lv: Seq<LevelSpec>, l: LevelSpec, ds: Seq<Cpt>, xs: Seq<Cpt>, xf: Seq<Cpt>, r: int)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        rec_wired(sig),
        crate::dom_rec_end::rec_hyps(sig, rid),
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::dom_model::sem_const(sig, rid, lv),
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(sig, rid, lv),
            crate::ti_syntax::dty_at(sig, rid, lv), crate::ti_syntax::sort(l))),
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv), bot_env(), ds, xs),
        crate::dom_rec::rec_ok(sig, rid, xs),
        xf.len() == xs.last()->Nd_1.len(),
        crate::dom_code::aw(xf),
        0 <= r < crate::dom_rec_ty::rshape(sig, rid).rposj(xs.last()->Nd_0->Con_1 as int).len(),
        xf[crate::dom_rec_ty::rshape(sig, rid).rposj(xs.last()->Nd_0->Con_1 as int)[r] as int]
            == xs.last()->Nd_1[crate::dom_rec_ty::rshape(sig, rid).rposj(xs.last()->Nd_0->Con_1 as int)[r] as int],
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let pre = sh.np + 1 + sh.nmin();
        let p = xs.last()->Nd_0->Con_1 as int;
        let k = sh.rposj(p)[r];
        mem(sig, ihterm(sig, rid, lv, p, r), crate::dom_tele::exts(bot_env(), xs.subrange(0, pre as int) + xf),
            crate::dom_rec::recval(sig, rid, crate::dom_rec::ih_in(sig.ienv.recs[rid], xs, xs.last()->Nd_1[k as int])))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = np + 1 + nmin;
    let x = xs.last();
    let p = x->Nd_0->Con_1 as int;
    let nf = x->Nd_1.len();
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    assert(sh.fields[p].len() == rd.rules[p].nfields);
    let rp = sh.rposj(p);
    crate::dom_rec_ty::rec_pos_facts(sh.fields[p], sh.ind, sh.us(), np, sh.ni, sh.fields[p].len());
    let k = rp[r];
    let f = x->Nd_1[k as int];
    let ih = crate::dom_rec::ih_in(rd, xs, f);
    let env = crate::dom_tele::exts(bot_env(), xs.subrange(0, pre as int) + xf);
    let rv = crate::dom_rec::recval(sig, rid, ih);
    assert(ih =~= xs.subrange(0, pre as int).push(f));
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] wf(xs[i]) by {
        assert(crate::dom_sound::dfit(sig, crate::dom_rec_ty::rtds(sig, rid, lv)[i], crate::dom_tele::exts(bot_env(), xs.subrange(0, i)), ds[i], xs[i]));
        typed_wf(xs[i], ds[i]);
    }
    assert(xs.len() == pre + 1);
    assert(wf(xs[pre as int]));
    assert forall|i: int| 0 <= i < ih.len() implies #[trigger] wf(ih[i]) by {
        if i < pre { assert(ih[i] == xs[i]); } else { assert(ih[i] == f); }
    }
    crate::dom_rec::recval_wf(sig, rid, ih);
    if !crate::dom_rec::rec_ok(sig, rid, ih) {
        if crate::dom_rec::rec_bot_ok(sig, rid, ih) {
            // irrefutable only at a structure, which has no recursive field
            assert(p == 0);
            assert(crate::dom_rec::rec_field(sig, rid, p, k as int));
        }
        mem_bot(sig, ihterm(sig, rid, lv, p, r), env);
        reveal(mem);
        return;
    }
    // the chain with the field as the major
    let tds = crate::dom_rec_ty::rtds(sig, rid, lv);
    major_form(sig, rid, lv);
    rec_field_ok(sig, rid, lv, ds, xs, k as int);
    assert(!(f is Bot));
    let ds2 = ds.subrange(0, pre as int).push(ds[pre as int]);
    assert forall|i: int| 0 <= i < tds.len() implies #[trigger] crate::dom_sound::dfit(sig, tds[i],
        crate::dom_tele::exts(bot_env(), ih.subrange(0, i)), ds2[i], ih[i]) by {
        assert(crate::dom_sound::dfit(sig, tds[i], crate::dom_tele::exts(bot_env(), xs.subrange(0, i)), ds[i], xs[i]));
        assert(ih.subrange(0, i) =~= xs.subrange(0, i));
        if i < pre { assert(ih[i] == xs[i] && ds2[i] == ds[i]); } else { assert(ih[i] == f && ds2[i] == ds[i]); }
    }
    let (a, sa) = crate::dom_rec_ty::rec_step(ss, sig, rid, lv, l, bot_env(), ds2, ih);
    typed_wf(sa, a);
    le_refl(sa);
    assert(rsem(sig, rid, lv, sa, a, sa));
    assert(mem(sig, ExprSpec::Const(rid, lv), env, sa));
    // the call's arguments are the chain's values
    let args = crate::rec_canon::vars(1 + nmin + nf, np) + seq![ExprSpec::Var(nmin + nf)]
        + crate::rec_canon::vars(nf, nmin) + seq![ExprSpec::Var((nf - 1 - k) as nat)];
    let xl = xs.subrange(0, pre as int) + xf;
    assert forall|j: nat| #[trigger] wf(env(j)) by {
        crate::dom_rec_ty::exts_at(bot_env(), xl, j);
        if j < xl.len() {
            let t = xl.len() - 1 - j;
            if t < pre { assert(xl[t] == xs[t]); } else { assert(xl[t] == xf[t - pre]); }
        }
    }
    assert forall|i: int| 0 <= i < args.len() implies #[trigger] mem(sig, args[i], env, ih[i]) && wf(ih[i]) by {
        if i < np {
            let v = (1 + nmin + nf + np - 1 - i) as nat;
            assert(args[i] == ExprSpec::Var(v));
            crate::dom_rec_ty::exts_at(bot_env(), xl, v);
            assert(xl[i] == xs[i]);
        } else if i == np {
            let v = (nmin + nf) as nat;
            assert(args[i] == ExprSpec::Var(v));
            crate::dom_rec_ty::exts_at(bot_env(), xl, v);
            assert(xl[np as int] == xs[np as int]);
        } else if i < pre {
            let v = (nf + nmin - 1 - (i - np - 1)) as nat;
            assert(args[i] == ExprSpec::Var(v));
            crate::dom_rec_ty::exts_at(bot_env(), xl, v);
            assert(xl[i] == xs[i]);
        } else {
            let v = (nf - 1 - k) as nat;
            assert(args[i] == ExprSpec::Var(v));
            crate::dom_rec_ty::exts_at(bot_env(), xl, v);
            assert(xl[(pre + k) as int] == xf[k as int]);
        }
        var_mem(sig, match args[i] { ExprSpec::Var(v) => v, _ => 0 }, env);
    }
    assert(ihterm(sig, rid, lv, p, r) == spine_app(ExprSpec::Const(rid, lv), args));
    crate::dom_bound::spine_mem_intro(sig, ExprSpec::Const(rid, lv), args, env, sa, ih, rv);
}

/// The minor's field binders at the instance.
pub open spec fn mfds(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int) -> Seq<ExprSpec> {
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    crate::dom_rec_shape::sls(Seq::new(sh.fields[p].len(), |i: int| sh.field_at(p, i, (1 + p) as nat)),
        sig.ienv.recs[rid].uparams, lv)
}

/// Field `k` of rule `p` is recursive.
pub open spec fn isrec(sig: Sig, rid: u64, p: int, k: int) -> bool {
    isrec_s(crate::dom_rec_ty::rshape(sig, rid), p, k)
}

pub open spec fn isrec_s(sh: crate::rec_canon::IndShape, p: int, k: int) -> bool {
    crate::rec_canon::direct_occ(sh.fields[p][k], sh.ind, sh.us(), sh.np, sh.ni, k as nat)
}

/// THE MINOR'S FIELDS: recursive ones pass, typed at the major's code;
/// the others are projected onto the minor's inputs.
#[verifier::spinoff_prover]
pub proof fn minor_mix(ss: Sig, sig: Sig, rid: u64, lv: Seq<LevelSpec>, l: LevelSpec, ds: Seq<Cpt>, xs: Seq<Cpt>) -> (r: (Seq<Cpt>, Seq<Cpt>))
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(sig, rid, lv),
            crate::ti_syntax::dty_at(sig, rid, lv), crate::ti_syntax::sort(l))),
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv), bot_env(), ds, xs),
        crate::dom_rec::rec_ok(sig, rid, xs),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let p = xs.last()->Nd_0->Con_1 as int;
        let fs = xs.last()->Nd_1;
        let mi = sh.np + 1 + p;
        &&& r.0.len() == fs.len()
        &&& crate::dom_code::aw(r.0)
        &&& crate::dom_sem::pre_le(r.0, fs)
        &&& forall|k: int| 0 <= k < fs.len() && isrec(sig, rid, p, k) ==> #[trigger] r.0[k] == fs[k]
        &&& crate::dom_rec::apps(xs[mi as int], fs) == crate::dom_rec::apps(xs[mi as int], r.0)
        &&& crate::dom_tele::chain_ok(sig, mfds(sig, rid, lv, p), crate::dom_tele::exts(bot_env(), xs.subrange(0, mi as int)), r.1, r.0)
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = np + 1 + nmin;
    let tds = crate::dom_rec_ty::rtds(sig, rid, lv);
    crate::dom_rec_ty::rec_ty_split(sig, rid, lv);
    major_form(sig, rid, lv);
    let x = xs.last();
    let p = x->Nd_0->Con_1 as int;
    let fs = x->Nd_1;
    let nf = fs.len();
    let mi = np + 1 + p;
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    assert(sh.fields[p].len() == rd.rules[p].nfields);
    let ind = crate::rec_canon::rec_ind(sig, rid);
    let lm = crate::rec_canon::elim_level(sig, rid, ind);
    assert(sh.head_doms(lm)[mi as int] == sh.minor_ty(p));
    assert(tds[mi as int] == crate::expr_model::subst_expr_levels(sh.minor_ty(p), rd.uparams, lv));
    let (f2, i2) = crate::dom_rec_shape::minor_shape(sh, p, rd.uparams, lv);
    let nr = i2.len();
    let us2 = crate::level_model::subst_levels_spec(sh.us(), rd.uparams, lv);
    let body = crate::dom_rec_ty::minor_body((p + nf + nr) as nat, sh.ctors[p], us2,
        crate::rec_canon::vars((1 + p + nf + nr) as nat, np), nf, nr);
    crate::dom_rec_shape::binds_concat(BinderKind::Pi, f2, i2, body);
    let li = crate::dom_tele::tele_prefix(ss, sig, Seq::empty(), tds, crate::dom_rec_ty::rbody(sig, rid), l, bot_env(), ds, xs, mi as int);
    let g = Seq::<ExprSpec>::empty() + tds.subrange(0, mi as int);
    let rho = crate::dom_tele::exts(bot_env(), xs.subrange(0, mi as int));
    assert(crate::dom_sound::dfit(sig, tds[mi as int], rho, ds[mi as int], xs[mi as int]));
    // the major's code, and the fields that pass
    let dm = ds[pre as int];
    assert(xs.len() == pre + 1);
    assert(crate::dom_sound::dfit(sig, tds[pre as int], crate::dom_tele::exts(bot_env(), xs.subrange(0, pre as int)), dm, xs[pre as int]));
    let fit = Seq::new(nf, |k: int| isrec(sig, rid, p, k));
    let axs = Seq::new(nf, |k: int| dm);
    assert forall|i: int| 0 <= i < fs.len() implies #[trigger] wf(fs[i]) by {
        typed_wf(xs[pre as int], dm);
    }
    assert forall|k: int, vals: Seq<Cpt>| 0 <= k < f2.len() && fit[k] && vals.len() == k
        implies #[trigger] crate::dom_sound::dfit(sig, f2[k], crate::dom_tele::exts(rho, vals), axs[k], fs[k]) by {
        crate::dom_rec_shape::occ_form(sh, p, k, (1 + p) as nat, rd.uparams, lv);
        assert(f2[k] == crate::expr_model::subst_expr_levels(sh.field_at(p, k, (1 + p) as nat), rd.uparams, lv));
        let env = crate::dom_tele::exts(rho, vals);
        let from = (k + 1 + p) as nat;
        assert forall|q: int| 0 <= q < np implies #[trigger] env((from + np - 1 - q) as nat) == xs[q] by {
            let j = (from + np - 1 - q) as nat;
            crate::dom_rec_ty::exts_at(rho, vals, j);
            crate::dom_rec_ty::exts_at(bot_env(), xs.subrange(0, mi as int), (j - k) as nat);
        }
        maj_transfer(sig, rid, lv, xs, env, from, dm);
        assert((k + 1 + p) as nat == k as nat + (1 + p) as nat);
        rec_field_ok(sig, rid, lv, ds, xs, k);
        if fs[k] is Bot {
            crate::dom_tele::bot_typed(dm);
        }
    }
    let (xf, dsf) = crate::dom_tele::tele_mix(ss, sig, g, f2, crate::rec_canon::binds(BinderKind::Pi, i2, body), li, rho,
        ds[mi as int], xs[mi as int], fs, fit, axs);
    assert forall|k: int| 0 <= k < fs.len() && isrec(sig, rid, p, k) implies #[trigger] xf[k] == fs[k] by {
        assert(fit[k]);
    }
    assert(f2 == mfds(sig, rid, lv, p));
    (xf, dsf)
}

/// THE RULE'S BODY holds the recursor's value, under the lambda
/// environment of the head inputs and the minor's field inputs.
#[verifier::spinoff_prover]
pub proof fn rhs_body_mem(ss: Sig, sig: Sig, rid: u64, lv: Seq<LevelSpec>, l: LevelSpec, ds: Seq<Cpt>, xs: Seq<Cpt>, xf: Seq<Cpt>)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        rec_wired(sig),
        crate::dom_rec_end::rec_hyps(sig, rid),
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::dom_model::sem_const(sig, rid, lv),
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(sig, rid, lv),
            crate::ti_syntax::dty_at(sig, rid, lv), crate::ti_syntax::sort(l))),
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv), bot_env(), ds, xs),
        crate::dom_rec::rec_ok(sig, rid, xs),
        xf.len() == xs.last()->Nd_1.len(),
        crate::dom_code::aw(xf),
        forall|k: int| 0 <= k < xf.len() && isrec(sig, rid, xs.last()->Nd_0->Con_1 as int, k) ==> #[trigger] xf[k] == xs.last()->Nd_1[k],
        crate::dom_rec::apps(xs[(crate::dom_rec_ty::rshape(sig, rid).np + 1 + xs.last()->Nd_0->Con_1) as int], xs.last()->Nd_1)
            == crate::dom_rec::apps(xs[(crate::dom_rec_ty::rshape(sig, rid).np + 1 + xs.last()->Nd_0->Con_1) as int], xf),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let pre = sh.np + 1 + sh.nmin();
        mem(sig, rule_body(sig, rid, lv, xs.last()->Nd_0->Con_1 as int), crate::dom_tele::exts(bot_env(), xs.subrange(0, pre as int) + xf),
            crate::dom_rec::recval(sig, rid, xs))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = np + 1 + nmin;
    let x = xs.last();
    let p = x->Nd_0->Con_1 as int;
    let fs = x->Nd_1;
    let nf = fs.len();
    let mi = np + 1 + p;
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    assert(sh.fields[p].len() == rd.rules[p].nfields);
    let minor = xs[mi as int];
    let hs = crate::dom_rec::rec_ihs(sig, rid, xs, nf);
    crate::dom_rec_ty::rec_ihs_at(sig, rid, xs, nf);
    let rp = sh.rposj(p);
    let nr = rp.len();
    crate::dom_rec_ty::rec_pos_facts(sh.fields[p], sh.ind, sh.us(), np, sh.ni, nf);
    let rv = crate::dom_rec::recval(sig, rid, xs);
    assert(rv == crate::dom_rec::apps(crate::dom_rec::apps(minor, fs), hs));
    crate::dom_rec_ty::apps_concat(minor, xf, hs);
    let xl = xs.subrange(0, pre as int) + xf;
    let env = crate::dom_tele::exts(bot_env(), xl);
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] wf(xs[i]) by {
        assert(crate::dom_sound::dfit(sig, crate::dom_rec_ty::rtds(sig, rid, lv)[i], crate::dom_tele::exts(bot_env(), xs.subrange(0, i)), ds[i], xs[i]));
        typed_wf(xs[i], ds[i]);
    }
    assert forall|j: nat| #[trigger] wf(env(j)) by {
        crate::dom_rec_ty::exts_at(bot_env(), xl, j);
        if j < xl.len() {
            let t = xl.len() - 1 - j;
            if t < pre { assert(xl[t] == xs[t]); } else { assert(xl[t] == xf[t - pre]); }
        }
    }
    // the head: the minor
    let v0 = (nmin - 1 - p + nf) as nat;
    crate::dom_rec_ty::exts_at(bot_env(), xl, v0);
    assert(xl[mi as int] == minor);
    var_mem(sig, v0, env);
    // the arguments: the field inputs, then the recursive calls
    let args = crate::rec_canon::vars(0, nf) + Seq::new(nr, |r: int| ihterm(sig, rid, lv, p, r));
    let wsx = xf + hs;
    assert forall|i: int| 0 <= i < args.len() implies #[trigger] mem(sig, args[i], env, wsx[i]) && wf(wsx[i]) by {
        if i < nf {
            let v = (nf - 1 - i) as nat;
            assert(args[i] == ExprSpec::Var(v));
            crate::dom_rec_ty::exts_at(bot_env(), xl, v);
            assert(xl[pre + i] == xf[i] && wsx[i] == xf[i]);
            var_mem(sig, v, env);
        } else {
            let r = i - nf;
            let k = rp[r];
            assert(args[i] == ihterm(sig, rid, lv, p, r));
            assert(isrec(sig, rid, p, k as int));
            assert(xf[k as int] == fs[k as int]);
            ih_mem(ss, sig, rid, lv, l, ds, xs, xf, r);
            assert(wsx[i] == hs[r]);
            crate::dom_rec::rec_ihs_wf(sig, rid, xs, nf);
        }
    }
    crate::dom_rec::recval_wf(sig, rid, xs);
    le_refl(rv);
    assert(rule_body(sig, rid, lv, p) == spine_app(ExprSpec::Var(v0), args));
    crate::dom_bound::spine_mem_intro(sig, ExprSpec::Var(v0), args, env, minor, wsx, rv);
}

/// THE RULE'S LAMBDA CHAIN: the recursor's head chain, then the minor's
/// field chain moved under the rule's binders.
#[verifier::spinoff_prover]
pub proof fn rule_chain(sig: Sig, rid: u64, lv: Seq<LevelSpec>, ds: Seq<Cpt>, xs: Seq<Cpt>, xf: Seq<Cpt>, dsf: Seq<Cpt>)
    requires
        crate::dom_rec_end::rec_hyps(sig, rid),
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv), bot_env(), ds, xs),
        crate::dom_rec::rec_ok(sig, rid, xs),
        crate::dom_tele::chain_ok(sig, mfds(sig, rid, lv, xs.last()->Nd_0->Con_1 as int),
            crate::dom_tele::exts(bot_env(), xs.subrange(0, (crate::dom_rec_ty::rshape(sig, rid).np + 1 + xs.last()->Nd_0->Con_1) as int)), dsf, xf),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let pre = (sh.np + 1 + sh.nmin()) as int;
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0, pre) + ftds(sig, rid, lv, xs.last()->Nd_0->Con_1 as int),
            bot_env(), ds.subrange(0, pre) + dsf, xs.subrange(0, pre) + xf)
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + 1 + nmin) as int;
    let x = xs.last();
    let p = x->Nd_0->Con_1 as int;
    let nf = x->Nd_1.len();
    let mi = (np + 1 + p) as int;
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    assert(sh.fields[p].len() == rd.rules[p].nfields);
    let tds = crate::dom_rec_ty::rtds(sig, rid, lv);
    crate::dom_rec_ty::rec_ty_split(sig, rid, lv);
    major_form(sig, rid, lv);
    let tl = tds.subrange(0, pre) + ftds(sig, rid, lv, p);
    let dl = ds.subrange(0, pre) + dsf;
    let xl = xs.subrange(0, pre) + xf;
    let rho = crate::dom_tele::exts(bot_env(), xs.subrange(0, mi));
    let mf = mfds(sig, rid, lv, p);
    let ff = ftds(sig, rid, lv, p);
    assert forall|i: int| 0 <= i < tl.len() implies #[trigger] crate::dom_sound::dfit(sig, tl[i],
        crate::dom_tele::exts(bot_env(), xl.subrange(0, i)), dl[i], xl[i]) by {
        if i < pre {
            assert(crate::dom_sound::dfit(sig, tds[i], crate::dom_tele::exts(bot_env(), xs.subrange(0, i)), ds[i], xs[i]));
            assert(xl.subrange(0, i) =~= xs.subrange(0, i));
            assert(tl[i] == tds[i] && dl[i] == ds[i] && xl[i] == xs[i]);
        } else {
            let k = i - pre;
            assert(crate::dom_sound::dfit(sig, mf[k], crate::dom_tele::exts(rho, xf.subrange(0, k)), dsf[k], xf[k]));
            assert(tl[i] == ff[k] && dl[i] == dsf[k] && xl[i] == xf[k]);
            let e1 = crate::dom_tele::exts(rho, xf.subrange(0, k));
            let e2 = crate::dom_tele::exts(bot_env(), xl.subrange(0, i));
            let us2 = crate::level_model::subst_levels_spec(sh.us(), rd.uparams, lv);
            if isrec(sig, rid, p, k) {
                crate::dom_rec_shape::occ_form(sh, p, k, (1 + p) as nat, rd.uparams, lv);
                crate::dom_rec_shape::occ_form(sh, p, k, (1 + nmin) as nat, rd.uparams, lv);
                let (a1, a2) = ((k + 1 + p) as nat, (k + 1 + nmin) as nat);
                let (v1, v2) = (vidx(a1, np), vidx(a2, np));
                vars_vidx(a1, np);
                vars_vidx(a2, np);
                assert forall|q: int| 0 <= q < v1.len() implies #[trigger] e1(v1[q]) == e2(v2[q]) by {
                    crate::dom_rec_ty::exts_at(rho, xf.subrange(0, k), v1[q]);
                    crate::dom_rec_ty::exts_at(bot_env(), xs.subrange(0, mi), (v1[q] - k) as nat);
                    crate::dom_rec_ty::exts_at(bot_env(), xl.subrange(0, i), v2[q]);
                    assert(xl[q] == xs[q]);
                }
                var_spine_transfer(sig, ExprSpec::Const(sh.ind, us2), v1, v2, e1, e2, dsf[k]);
            } else if crate::rec_canon::pvar_field(sh.pdoms, np, k as nat, sh.fields[p][k]) {
                // a parameter-typed field: the same parameter's value in both
                let v = sh.fields[p][k]->Var_0;
                let q = (np + k - 1 - v) as int;
                let (i1, i2) = ((v + 1 + p) as nat, (v + 1 + nmin) as nat);
                assert(crate::subst_algebra::lift((1 + p) as nat, k as nat, sh.fields[p][k]) == ExprSpec::Var(i1));
                assert(crate::subst_algebra::lift((1 + nmin) as nat, k as nat, sh.fields[p][k]) == ExprSpec::Var(i2));
                assert(mf[k] == ExprSpec::Var(i1));
                assert(ff[k] == ExprSpec::Var(i2));
                crate::dom_rec_ty::exts_at(rho, xf.subrange(0, k), i1);
                crate::dom_rec_ty::exts_at(bot_env(), xs.subrange(0, mi), (i1 - k) as nat);
                crate::dom_rec_ty::exts_at(bot_env(), xl.subrange(0, i), i2);
                assert(xl[q] == xs[q]);
                assert(e1(i1) == e2(i2));
                crate::dom_adeq_base::mem_var(sig, i1, e1, dsf[k]);
                crate::dom_adeq_base::mem_var(sig, i2, e2, dsf[k]);
            } else if !crate::rec_canon::simple_ty(sig, sh.ind, sh.fields[p][k]) {
                // a type over the parameters: the same parameters' values in both
                let f = sh.fields[p][k];
                crate::dom_rec_ty::scope_ctor(sig, rid, p);
                crate::dom_canon::canon_fields(sig, sh.ind, p, k);
                crate::ti_level::ls_lift((1 + p) as nat, k as nat, f, rd.uparams, lv);
                crate::ti_level::ls_lift((1 + nmin) as nat, k as nat, f, rd.uparams, lv);
                // over the parameters, so without level parameters
                crate::dom_rec_end::rec_canon_ok(sig, rid);
                crate::dom_rec_ty::rec_lps_sub(sig, rid);
                crate::dom_rec_ty::rec_elp_parts(sig, rid, p);
                crate::dom_rec_ty::rinst_id(sig, rid, lv, f);
                let fu = crate::iota_sr::cfu(sig, rid, p, k, crate::dom_rec_ty::rinst(sig, rid, lv));
                crate::iota_sr::ps_field_at(sig, rid, p, k, crate::dom_rec_ty::rinst(sig, rid, lv));
                assert(crate::expr_model::subst_expr_levels(f, rd.uparams, lv) == fu);
                assert(mf[k] == crate::subst_algebra::lift((1 + p) as nat, k as nat, fu));
                assert(ff[k] == crate::subst_algebra::lift((1 + nmin) as nat, k as nat, fu));
                assert forall|j: nat| j < np implies #[trigger] e1(j + (k as nat) + ((1 + p) as nat)) == e2(j + (k as nat) + ((1 + nmin) as nat)) by {
                    let (i1, i2) = ((j + k + 1 + p) as nat, (j + k + 1 + nmin) as nat);
                    let q = (np - 1 - j) as int;
                    crate::dom_rec_ty::exts_at(rho, xf.subrange(0, k), i1);
                    crate::dom_rec_ty::exts_at(bot_env(), xs.subrange(0, mi), (i1 - k) as nat);
                    crate::dom_rec_ty::exts_at(bot_env(), xl.subrange(0, i), i2);
                    assert(xl[q] == xs[q]);
                }
                crate::dom_psimple::ps_mem_transfer(sig, sh.ind, sh.pdoms, np, k as nat, fu, (1 + p) as nat, (1 + nmin) as nat, e1, e2, dsf[k]);
            } else {
                crate::dom_rec_ty::scope_ctor(sig, rid, p);
                crate::dom_canon::canon_fields(sig, sh.ind, p, k);
                assert(crate::rec_canon::simple_ty(sig, sh.ind, sh.fields[p][k]));
                simple_closed(sig, sh.ind, sh.fields[p][k]);
                crate::subst_algebra::lift_closed((1 + p) as nat, k as nat, sh.fields[p][k]);
                crate::subst_algebra::lift_closed((1 + nmin) as nat, k as nat, sh.fields[p][k]);
                assert(mf[k] == ff[k]);
                crate::dom_rec_shape::nlbv_sl(sh.fields[p][k], rd.uparams, lv);
                crate::dom_model::mem_closed_env(sig, mf[k], e1, dsf[k]);
                crate::dom_model::mem_closed_env(sig, mf[k], e2, dsf[k]);
            }
        }
    }
}

/// THE RULE'S RIGHT-HAND SIDE, at the instance, has a member which applied
/// to the head inputs and field inputs below the major's fields gives at
/// least the recursor's value.
#[verifier::spinoff_prover]
pub proof fn iota_rhs_mem(ss: Sig, sig: Sig, rid: u64, lv: Seq<LevelSpec>, l: LevelSpec, ds: Seq<Cpt>, xs: Seq<Cpt>) -> (r: (Cpt, Seq<Cpt>))
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        rec_wired(sig),
        crate::dom_rec_end::rec_hyps(sig, rid),
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::dom_model::sem_const(sig, rid, lv),
        lv.len() == sig.ienv.recs[rid].uparams.len(),
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(sig, rid, lv),
            crate::ti_syntax::dty_at(sig, rid, lv), crate::ti_syntax::sort(l))),
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv), bot_env(), ds, xs),
        crate::dom_rec::rec_ok(sig, rid, xs),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let pre = (sh.np + 1 + sh.nmin()) as int;
        let p = xs.last()->Nd_0->Con_1 as int;
        let fs = xs.last()->Nd_1;
        &&& mem(sig, crate::expr_model::subst_expr_levels(sig.ienv.recs[rid].rules[p].rhs, sig.ienv.recs[rid].uparams, lv), bot_env(), r.0)
        &&& r.1.len() == pre + fs.len()
        &&& crate::dom_code::aw(r.1)
        &&& forall|i: int| 0 <= i < pre ==> #[trigger] r.1[i] == xs[i]
        &&& forall|k: int| 0 <= k < fs.len() ==> le(#[trigger] r.1[pre + k], fs[k])
        &&& le(crate::dom_rec::recval(sig, rid, xs), crate::dom_rec::apps(r.0, r.1))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + 1 + nmin) as int;
    let x = xs.last();
    let p = x->Nd_0->Con_1 as int;
    let fs = x->Nd_1;
    let (xf, dsf) = minor_mix(ss, sig, rid, lv, l, ds, xs);
    rhs_body_mem(ss, sig, rid, lv, l, ds, xs, xf);
    rule_chain(sig, rid, lv, ds, xs, xf, dsf);
    let tl = crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0, pre) + ftds(sig, rid, lv, p);
    let dl = ds.subrange(0, pre) + dsf;
    let xl = xs.subrange(0, pre) + xf;
    let rv = crate::dom_rec::recval(sig, rid, xs);
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] wf(xs[i]) by {
        assert(crate::dom_sound::dfit(sig, crate::dom_rec_ty::rtds(sig, rid, lv)[i], crate::dom_tele::exts(bot_env(), xs.subrange(0, i)), ds[i], xs[i]));
        typed_wf(xs[i], ds[i]);
    }
    crate::dom_rec::recval_wf(sig, rid, xs);
    crate::dom_tele::lamchain_mem(sig, tl, rule_body(sig, rid, lv, p), bot_env(), dl, xl, rv);
    let lc = crate::dom_tele::lamchain(xl, rv);
    assert forall|i: int| 0 <= i < xl.len() implies #[trigger] wf(xl[i]) by {
        assert(crate::dom_sound::dfit(sig, tl[i], crate::dom_tele::exts(bot_env(), xl.subrange(0, i)), dl[i], xl[i]));
        typed_wf(xl[i], dl[i]);
    }
    crate::dom_tele::lamchain_apps(xl, rv);
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    rule_split(sig, rid, lv, p);
    assert forall|k: int| 0 <= k < fs.len() implies le(#[trigger] xl[pre + k], fs[k]) by {
        assert(xl[pre + k] == xf[k]);
    }
    (lc, xl)
}

/// THE RULE'S MEMBER at a smashed structure's irrefutable match: the rule
/// over the head inputs and bottom fields holds the minor at bottom fields
/// (the structure has no recursive fields, so its rule has no recursive
/// calls).
#[verifier::spinoff_prover]
pub proof fn iota_rhs_mem_bot(ss: Sig, sig: Sig, rid: u64, lv: Seq<LevelSpec>, l: LevelSpec, ds: Seq<Cpt>, xs: Seq<Cpt>) -> (r: (Cpt, Seq<Cpt>))
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        rec_wired(sig),
        crate::dom_rec_end::rec_hyps(sig, rid),
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::dom_model::sem_const(sig, rid, lv),
        lv.len() == sig.ienv.recs[rid].uparams.len(),
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(sig, rid, lv),
            crate::ti_syntax::dty_at(sig, rid, lv), crate::ti_syntax::sort(l))),
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv), bot_env(), ds, xs),
        !crate::dom_rec::rec_ok(sig, rid, xs),
        crate::dom_rec::rec_bot_ok(sig, rid, xs),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let pre = (sh.np + 1 + sh.nmin()) as int;
        let nf = sh.fields[0].len();
        &&& mem(sig, crate::expr_model::subst_expr_levels(sig.ienv.recs[rid].rules[0].rhs, sig.ienv.recs[rid].uparams, lv), bot_env(), r.0)
        &&& r.1.len() == pre + nf
        &&& crate::dom_code::aw(r.1)
        &&& forall|i: int| 0 <= i < pre ==> #[trigger] r.1[i] == xs[i]
        &&& forall|k: int| 0 <= k < nf ==> #[trigger] r.1[pre + k] is Bot
        &&& le(crate::dom_rec::recval(sig, rid, xs), crate::dom_rec::apps(r.0, r.1))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + 1 + nmin) as int;
    let p: int = 0;
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    let nf = sh.fields[p].len();
    assert(sh.fields[p].len() == rd.rules[p].nfields);
    let xf = crate::dom_rec::bot_fields(sig, rid);
    let dsf = crate::dom_rec::bot_fields(sig, rid);
    let mi = (np + 1 + p) as int;
    let minor = xs[mi];
    let rv = crate::dom_rec::recval(sig, rid, xs);
    assert(rv == crate::dom_rec::apps(minor, xf));
    // no recursive fields
    crate::dom_rec_ty::rec_pos_facts(sh.fields[p], sh.ind, sh.us(), np, sh.ni, nf);
    if sh.rposj(p).len() > 0 {
        let k = sh.rposj(p)[0] as int;
        assert(crate::dom_rec::rec_field(sig, rid, p, k));
    }
    let xl = xs.subrange(0, pre) + xf;
    let dl = ds.subrange(0, pre) + dsf;
    let env = crate::dom_tele::exts(bot_env(), xl);
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] wf(xs[i]) by {
        assert(crate::dom_sound::dfit(sig, crate::dom_rec_ty::rtds(sig, rid, lv)[i], crate::dom_tele::exts(bot_env(), xs.subrange(0, i)), ds[i], xs[i]));
        typed_wf(xs[i], ds[i]);
    }
    assert forall|i: int| 0 <= i < xl.len() implies #[trigger] wf(xl[i]) by {
        if i < pre { assert(xl[i] == xs[i]); } else { assert(xl[i] == Cpt::Bot); }
    }
    assert forall|j: nat| #[trigger] wf(env(j)) by {
        crate::dom_rec_ty::exts_at(bot_env(), xl, j);
    }
    // the body: the minor at the field variables, each holding bottom
    let v0 = (nmin - 1 - p + nf) as nat;
    crate::dom_rec_ty::exts_at(bot_env(), xl, v0);
    assert(xl[mi] == minor);
    var_mem(sig, v0, env);
    let args = crate::rec_canon::vars(0, nf) + Seq::new(sh.rposj(p).len(), |r: int| ihterm(sig, rid, lv, p, r));
    assert(args =~= crate::rec_canon::vars(0, nf));
    assert forall|i: int| 0 <= i < args.len() implies #[trigger] mem(sig, args[i], env, xf[i]) && wf(xf[i]) by {
        mem_bot(sig, args[i], env);
        reveal(mem);
    }
    crate::dom_rec::recval_wf(sig, rid, xs);
    le_refl(rv);
    assert(rule_body(sig, rid, lv, p) == spine_app(ExprSpec::Var(v0), args));
    crate::dom_bound::spine_mem_intro(sig, ExprSpec::Var(v0), args, env, minor, xf, rv);
    // the rule's chain: the head inputs, then the bottom fields at bottom codes
    let tl = crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0, pre) + ftds(sig, rid, lv, p);
    crate::dom_rec_ty::rec_ty_split(sig, rid, lv);
    major_form(sig, rid, lv);
    crate::dom_sound::typed_basic();
    assert forall|i: int| 0 <= i < tl.len() implies #[trigger] crate::dom_sound::dfit(sig, tl[i],
        crate::dom_tele::exts(bot_env(), xl.subrange(0, i)), dl[i], xl[i]) by {
        if i < pre {
            assert(crate::dom_sound::dfit(sig, crate::dom_rec_ty::rtds(sig, rid, lv)[i],
                crate::dom_tele::exts(bot_env(), xs.subrange(0, i)), ds[i], xs[i]));
            assert(xl.subrange(0, i) =~= xs.subrange(0, i));
            assert(tl[i] == crate::dom_rec_ty::rtds(sig, rid, lv)[i] && dl[i] == ds[i] && xl[i] == xs[i]);
        } else {
            assert(xl[i] == Cpt::Bot && dl[i] == Cpt::Bot);
            mem_bot(sig, tl[i], crate::dom_tele::exts(bot_env(), xl.subrange(0, i)));
            reveal(mem);
        }
    }
    assert(crate::dom_tele::chain_ok(sig, tl, bot_env(), dl, xl));
    crate::dom_tele::lamchain_mem(sig, tl, rule_body(sig, rid, lv, p), bot_env(), dl, xl, rv);
    let lc = crate::dom_tele::lamchain(xl, rv);
    crate::dom_tele::lamchain_apps(xl, rv);
    rule_split(sig, rid, lv, p);
    (lc, xl)
}

/// IOTA, LEFT IN RIGHT, without extra arguments: a member of the recursor
/// applied up to its major, a constructor application, is a member of the
/// rule applied to the head arguments and the fields.
#[verifier::spinoff_prover]
pub proof fn iota_core_l2r(ss: Sig, sig: Sig, rid: u64, lv: Seq<LevelSpec>, l: LevelSpec, ri: int, clv: Seq<LevelSpec>, lc: LevelSpec,
    a0: Seq<ExprSpec>, cargs: Seq<ExprSpec>, rho: Env, u0: Cpt)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        rec_wired(sig),
        crate::dom_rec_end::rec_hyps(sig, rid),
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::dom_model::sem_const(sig, rid, lv),
        lv.len() == sig.ienv.recs[rid].uparams.len(),
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(sig, rid, lv),
            crate::ti_syntax::dty_at(sig, rid, lv), crate::ti_syntax::sort(l))),
        0 <= ri < sig.ienv.recs[rid].rules.len(),
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(Seq::empty(),
            crate::ti_syntax::dty_at(sig, sig.ienv.recs[rid].rules[ri].ctor_id, clv),
            crate::ti_syntax::dty_at(sig, sig.ienv.recs[rid].rules[ri].ctor_id, clv), crate::ti_syntax::sort(lc))),
        crate::expr_model::nlbv(sig.ienv.recs[rid].rules[ri].rhs) == 0,
        forall|i: nat| #[trigger] wf(rho(i)),
        a0.len() == crate::dom_rec_ty::rshape(sig, rid).np + 2 + crate::dom_rec_ty::rshape(sig, rid).nmin(),
        a0.last() == spine_app(ExprSpec::Const(sig.ienv.recs[rid].rules[ri].ctor_id, clv), cargs),
        sig.ienv.recs[rid].rules[ri].nfields <= cargs.len(),
        mem(sig, spine_app(ExprSpec::Const(rid, lv), a0), rho, u0),
    ensures ({
        let pre = (crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int;
        let nf = sig.ienv.recs[rid].rules[ri].nfields;
        mem(sig, spine_app(spine_app(crate::expr_model::subst_expr_levels(sig.ienv.recs[rid].rules[ri].rhs, sig.ienv.recs[rid].uparams, lv),
            a0.subrange(0, pre)), cargs.subrange(cargs.len() - nf, cargs.len() as int)), rho, u0)
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + 1 + nmin) as int;
    let nf = rd.rules[ri].nfields;
    let body = crate::expr_model::subst_expr_levels(rd.rules[ri].rhs, rd.uparams, lv);
    let fargs = cargs.subrange(cargs.len() - nf, cargs.len() as int);
    let core = spine_app(spine_app(body, a0.subrange(0, pre)), fargs);
    crate::dom_rec_shape::nlbv_sl(rd.rules[ri].rhs, rd.uparams, lv);
    let (hw, ws) = spine_mem(sig, ExprSpec::Const(rid, lv), a0, rho, u0);
    if u0 is Bot {
        mem_bot(sig, core, rho);
        reveal(mem);
        return;
    }
    if hw is Bot {
        apps_bot(ws);
        head_le(u0, Cpt::Bot);
    }
    assert(mem(sig, ExprSpec::Const(rid, lv), rho, hw));
    let (a, v) = choose|a: Cpt, v: Cpt| #[trigger] rsem(sig, rid, lv, hw, a, v);
    typed_wf(v, a);
    // along the recursor's type: typed projections, and below recval
    let tds = crate::dom_rec_ty::rtds(sig, rid, lv);
    crate::dom_rec_ty::rec_ty_split(sig, rid, lv);
    major_form(sig, rid, lv);
    assert forall|i: int| 0 <= i < ws.len() implies #[trigger] wf(ws[i]) by {
        assert(mem(sig, a0[i], rho, ws[i]));
    }
    assert(crate::dom_sound::fits_env(sig, Seq::empty(), bot_env()));
    let (ws2, _e, _l2, dcs) = crate::dom_tele::tele_apps(ss, sig, Seq::empty(), tds, crate::dom_rec_ty::rbody(sig, rid), l, bot_env(), a, v, ws);
    assert(crate::dom_tele::chain_ok(sig, tds, bot_env(), dcs, ws2));
    crate::dom_rec_ty::rf_apps(sig, rid, tds, crate::dom_rec_ty::rbody(sig, rid), Seq::empty(), v, ws2);
    assert(Seq::<Cpt>::empty() + ws2 =~= ws2);
    let rv = crate::dom_rec::recval(sig, rid, ws2);
    assert forall|i: int| 0 <= i < ws.len() implies le(#[trigger] ws[i], ws[i]) by {
        le_refl(ws[i]);
    }
    crate::dom_rec::apps_mono(hw, v, ws, ws);
    le_trans(u0, crate::dom_rec::apps(hw, ws), crate::dom_rec::apps(v, ws));
    le_trans(u0, crate::dom_rec::apps(v, ws2), rv);
    if !crate::dom_rec::rec_ok(sig, rid, ws2) {
        if !crate::dom_rec::rec_bot_ok(sig, rid, ws2) {
            head_le(u0, rv);
            assert(false);
        }
        iota_l2r_bot(ss, sig, rid, lv, l, ri, a0, cargs, rho, u0, ws, ws2, dcs, rv);
        return;
    }
    // the major
    let x = ws2.last();
    crate::beta_model::find_rule_spec(rd.rules, rd.rules[ri].ctor_id);
    assert(sh.ctors[ri] == rd.rules[ri].ctor_id);
    assert(ri < sh.nmin());
    assert(mem(sig, a0[pre], rho, ws[pre]));
    assert(le(ws2[pre], ws[pre]));
    assert(ws2[pre] == x);
    assert(crate::dom_sound::dfit(sig, tds[pre], crate::dom_tele::exts(bot_env(), ws2.subrange(0, pre)), dcs[pre], ws2[pre]));
    typed_wf(x, dcs[pre]);
    let (cws2, _cds) = iota_major(ss, sig, rid, ri, clv, lc, cargs, rho, ws[pre], x);
    let p = x->Nd_0->Con_1 as int;
    assert(p == ri);
    assert(fargs =~= cargs.subrange(np as int, cargs.len() as int));
    // the rule's member
    let (lc2, xl) = iota_rhs_mem(ss, sig, rid, lv, l, dcs, ws2);
    crate::dom_model::mem_closed_env(sig, body, rho, lc2);
    let fl = a0.subrange(0, pre) + fargs;
    assert forall|i: int| 0 <= i < fl.len() implies #[trigger] mem(sig, fl[i], rho, xl[i]) && wf(xl[i]) by {
        if i < pre {
            assert(fl[i] == a0[i] && xl[i] == ws2[i]);
            assert(mem(sig, a0[i], rho, ws[i]));
            mem_down_e(sig, a0[i], rho, ws[i], ws2[i]);
        } else {
            let k = i - pre;
            assert(fl[i] == cargs[np + k]);
            assert(le(xl[pre + k], x->Nd_1[k]));
            assert(le(x->Nd_1[k], cws2[np + k]));
            le_trans(xl[i], x->Nd_1[k], cws2[np + k]);
            mem_down_e(sig, cargs[np + k], rho, cws2[np + k], xl[i]);
        }
    }
    spine_concat(body, a0.subrange(0, pre), fargs);
    assert forall|i: int| 0 <= i < ws2.len() implies #[trigger] wf(ws2[i]) by {}
    crate::dom_rec::recval_wf(sig, rid, ws2);
    crate::dom_bound::spine_mem_intro(sig, body, fl, rho, lc2, xl, rv);
    mem_down_e(sig, core, rho, rv, u0);
}

/// IOTA, LEFT IN RIGHT, at a smashed structure's irrefutable match: the
/// recursor's value is the rule's at the head inputs and bottom fields,
/// and bottom is a member of every field argument.
#[verifier::spinoff_prover]
proof fn iota_l2r_bot(ss: Sig, sig: Sig, rid: u64, lv: Seq<LevelSpec>, l: LevelSpec, ri: int,
    a0: Seq<ExprSpec>, cargs: Seq<ExprSpec>, rho: Env, u0: Cpt, ws: Seq<Cpt>, ws2: Seq<Cpt>, dcs: Seq<Cpt>, rv: Cpt)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        rec_wired(sig),
        crate::dom_rec_end::rec_hyps(sig, rid),
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::dom_model::sem_const(sig, rid, lv),
        lv.len() == sig.ienv.recs[rid].uparams.len(),
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(sig, rid, lv),
            crate::ti_syntax::dty_at(sig, rid, lv), crate::ti_syntax::sort(l))),
        0 <= ri < sig.ienv.recs[rid].rules.len(),
        crate::expr_model::nlbv(sig.ienv.recs[rid].rules[ri].rhs) == 0,
        forall|i: nat| #[trigger] wf(rho(i)),
        a0.len() == crate::dom_rec_ty::rshape(sig, rid).np + 2 + crate::dom_rec_ty::rshape(sig, rid).nmin(),
        sig.ienv.recs[rid].rules[ri].nfields <= cargs.len(),
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv), bot_env(), dcs, ws2),
        ws.len() == a0.len(),
        ws2.len() == a0.len(),
        forall|i: int| 0 <= i < a0.len() ==> #[trigger] mem(sig, a0[i], rho, ws[i]) && le(ws2[i], ws[i]),
        !crate::dom_rec::rec_ok(sig, rid, ws2),
        crate::dom_rec::rec_bot_ok(sig, rid, ws2),
        rv == crate::dom_rec::recval(sig, rid, ws2),
        crate::dom_compact::le(u0, rv),
        wf(u0),
    ensures ({
        let pre = (crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int;
        let nf = sig.ienv.recs[rid].rules[ri].nfields;
        mem(sig, spine_app(spine_app(crate::expr_model::subst_expr_levels(sig.ienv.recs[rid].rules[ri].rhs, sig.ienv.recs[rid].uparams, lv),
            a0.subrange(0, pre)), cargs.subrange(cargs.len() - nf, cargs.len() as int)), rho, u0)
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + 1 + nmin) as int;
    assert(ri == 0);
    crate::dom_rec_ty::scope_ctor(sig, rid, 0);
    let nf = rd.rules[ri].nfields;
    assert(sh.fields[0].len() == nf);
    let body = crate::expr_model::subst_expr_levels(rd.rules[ri].rhs, rd.uparams, lv);
    let fargs = cargs.subrange(cargs.len() - nf, cargs.len() as int);
    let core = spine_app(spine_app(body, a0.subrange(0, pre)), fargs);
    crate::dom_rec_shape::nlbv_sl(rd.rules[ri].rhs, rd.uparams, lv);
    let (lc2, xl) = iota_rhs_mem_bot(ss, sig, rid, lv, l, dcs, ws2);
    crate::dom_model::mem_closed_env(sig, body, rho, lc2);
    let fl = a0.subrange(0, pre) + fargs;
    assert forall|i: int| 0 <= i < ws2.len() implies #[trigger] wf(ws2[i]) by {
        assert(crate::dom_sound::dfit(sig, crate::dom_rec_ty::rtds(sig, rid, lv)[i], crate::dom_tele::exts(bot_env(), ws2.subrange(0, i)), dcs[i], ws2[i]));
        typed_wf(ws2[i], dcs[i]);
    }
    assert forall|i: int| 0 <= i < fl.len() implies #[trigger] mem(sig, fl[i], rho, xl[i]) && wf(xl[i]) by {
        if i < pre {
            assert(fl[i] == a0[i] && xl[i] == ws2[i]);
            assert(mem(sig, a0[i], rho, ws[i]));
            mem_down_e(sig, a0[i], rho, ws[i], ws2[i]);
        } else {
            let k = i - pre;
            assert(xl[pre + k] is Bot);
            mem_bot(sig, fl[i], rho);
            reveal(mem);
        }
    }
    spine_concat(body, a0.subrange(0, pre), fargs);
    crate::dom_rec::recval_wf(sig, rid, ws2);
    crate::dom_bound::spine_mem_intro(sig, body, fl, rho, lc2, xl, rv);
    mem_down_e(sig, core, rho, rv, u0);
}

/// A DERIVABLE SPINE has a derivable head.
pub proof fn spine_gen(sig: Sig, g: crate::ti_syntax::Ctx, h: ExprSpec, args: Seq<ExprSpec>, t: ExprSpec) -> (th: ExprSpec)
    requires
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, spine_app(h, args), spine_app(h, args), t)),
    ensures
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, h, h, th)),
    decreases args.len(),
{
    if args.len() == 0 {
        return t;
    }
    let init = args.subrange(0, args.len() - 1);
    crate::dom_bound::spine_push(h, args);
    let f = spine_app(h, init);
    let x = args.last();
    let d = crate::ti_sub::get(sig, crate::ti_syntax::eq(g, spine_app(h, args), spine_app(h, args), t));
    crate::ti_gen::gen(sig, d);
    let (a, b, l2) = choose|a: ExprSpec, b: ExprSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(a, b, l2, l2)
        && crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, f, f, crate::ti_syntax::pi(a, b)))
        && crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, x, x, a)) && crate::ti_gen::typ(sig, g.push(a), b, l2)
        && crate::ti_chain::tchain(sig, g, t, crate::subst_algebra::inst(0, x, b));
    spine_gen(sig, g, h, init, crate::ti_syntax::pi(a, b))
}

/// A chain's lambda approximates a constructor's code function when its
/// output lies below the value over the collected fields.
pub proof fn lamchain_cf(ind: u64, pc: nat, sm: bool, np: nat, tds: Seq<ExprSpec>, body: ExprSpec, fs: Seq<Cpt>, k: nat, xs: Seq<Cpt>, out: Cpt)
    requires
        xs.len() == tds.len(),
        !(body is Bind),
        spine_head(body) == ExprSpec::Const(ind, spine_head(body)->Const_1),
        k + xs.len() >= np,
        le(out, Cpt::Nd(NdKey::Con(ind, pc, sm), cacc(fs, xs, k, np))),
    ensures
        cf_fun(ind, pc, sm, np, crate::rec_canon::binds(BinderKind::Pi, tds, body), fs, k, crate::dom_tele::lamchain(xs, out)),
    decreases tds.len(),
{
    if tds.len() == 0 {
        assert(cacc(fs, xs, k, np) =~= fs);
        return;
    }
    if out is Bot {
        return;
    }
    let (t2, x2) = (tds.drop_first(), xs.drop_first());
    let x0 = xs[0];
    let fs2 = if k < np { fs } else { fs.push(x0) };
    if k >= np {
        assert(fs.push(x0) + x2 =~= fs + xs);
    } else if k + 1 >= np {
        assert(xs.subrange(np - k, xs.len() as int) =~= x2);
    } else if k + 1 + x2.len() > np {
        assert(xs.subrange(np - k, xs.len() as int) =~= x2.subrange(np - (k + 1), x2.len() as int));
    }
    assert(cacc(fs2, x2, k + 1, np) == cacc(fs, xs, k, np));
    lamchain_cf(ind, pc, sm, np, t2, body, fs2, k + 1, x2, out);
    let l2 = crate::dom_tele::lamchain(x2, out);
    let f = seq![(x0, l2)];
    assert(f[0] == (x0, l2));
    assert(crate::rec_canon::binds(BinderKind::Pi, tds, body) == ExprSpec::Bind(BinderKind::Pi, Box::new(tds[0]), Box::new(crate::rec_canon::binds(BinderKind::Pi, t2, body))));
    assert(crate::dom_tele::lamchain(xs, out) == Cpt::Lam(f));
}

/// Bottom inputs.
pub open spec fn bots(n: nat) -> Seq<Cpt> {
    Seq::new(n, |i: int| Cpt::Bot)
}

/// A bottom chain: bottom domains, bottom inputs.
pub proof fn bot_chain(sig: Sig, tds: Seq<ExprSpec>, rho: Env)
    ensures
        crate::dom_tele::chain_ok(sig, tds, rho, bots(tds.len()), bots(tds.len())),
{
    crate::dom_sound::typed_basic();
    assert forall|i: int| 0 <= i < tds.len() implies #[trigger] crate::dom_sound::dfit(sig, tds[i],
        crate::dom_tele::exts(rho, bots(tds.len()).subrange(0, i)), bots(tds.len())[i], bots(tds.len())[i]) by {
        mem_bot(sig, tds[i], crate::dom_tele::exts(rho, bots(tds.len()).subrange(0, i)));
        reveal(mem);
    }
}

/// Field `k` of rule `p` is typed by a type parameter.
pub open spec fn ispvar(sig: Sig, rid: u64, p: int, k: int) -> bool {
    ispvar_s(sig, crate::dom_rec_ty::rshape(sig, rid), p, k)
}

/// The parameter a parameter-typed field is typed by.
pub open spec fn pvq(sig: Sig, rid: u64, p: int, k: int) -> int {
    pvq_s(sig, crate::dom_rec_ty::rshape(sig, rid), p, k)
}

/// The parameters' sorts at an instance.
pub open spec fn pdoms_at(sig: Sig, rid: u64, cl: Seq<LevelSpec>) -> Seq<ExprSpec> {
    pdoms_at_s(sig, crate::dom_rec_ty::rshape(sig, rid), cl)
}

/// What the constructor step needs, at the constructor's instance `cl`:
/// the parameters' values typed along their sorts there, and the fields:
/// closed ones typed at members of their types, parameter-typed ones at
/// codes below their parameter's value, recursive ones at the canonical
/// code at the parameters' values.
pub open spec fn cf_fields_ok(sig: Sig, rid: u64, p: int, cl: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>, xf: Seq<Cpt>, ak: Seq<Cpt>) -> bool {
    &&& crate::dom_rec_ty::rec_scope(sig, rid)
    &&& cf_fields_ok_s(sig, crate::dom_rec_ty::rshape(sig, rid), p, cl, dps, pv, xf, ak)
}

/// The constructor chain's domains.
pub open spec fn cf_ds(sig: Sig, rid: u64, p: int, cl: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>, ak: Seq<Cpt>) -> Seq<Cpt> {
    cf_ds_s(sig, crate::dom_rec_ty::rshape(sig, rid), p, cl, dps, pv, ak)
}

/// The parameters' sorts at an instance are their sorts in the constructor's
/// and the inductive's types there.
pub proof fn pdoms_at_facts(sig: Sig, rid: u64, p: int, cl: Seq<LevelSpec>)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        0 <= p < crate::dom_rec_ty::rshape(sig, rid).nmin(),
        cl.len() == sig.consts[crate::dom_rec_ty::rshape(sig, rid).ind].lps.len(),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let tds = ctds(sig, rid, p, cl);
        &&& pdoms_at(sig, rid, cl).len() == sh.np
        &&& sh.lps == sig.consts[sh.ind].lps
        &&& crate::ti_syntax::dty_at(sig, sh.ctors[p], cl) == crate::iota_sr::ctel(sig, rid, p, cl)
        &&& cbody(sig, rid, p, cl) == spine_app(ExprSpec::Const(sh.ind, cl), crate::rec_canon::vars(sh.fields[p].len(), sh.np))
        &&& !(cbody(sig, rid, p, cl) is Bind)
        &&& tds.len() == sh.np + sh.fields[p].len()
        &&& forall|q: int| 0 <= q < sh.np ==> #[trigger] tds[q] == pdoms_at(sig, rid, cl)[q]
        &&& forall|k: int| 0 <= k < sh.fields[p].len() ==> #[trigger] tds[sh.np + k] == crate::iota_sr::cfu(sig, rid, p, k, cl)
    }),
{
    crate::dom_rec_ty::rec_scope_ind(sig, rid);
    pdoms_at_facts_s(sig, crate::dom_rec_ty::rshape(sig, rid), p, cl);
}

/// THE CONSTRUCTOR CHAIN: the parameters' values, then the fields at
/// their members; it ends in the canonical code at those values.
#[verifier::spinoff_prover]
pub proof fn cf_chain(sig: Sig, rid: u64, p: int, cl: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>, xf: Seq<Cpt>, ak: Seq<Cpt>)
    requires
        cf_fields_ok(sig, rid, p, cl, dps, pv, xf, ak),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let xsc = pv + xf;
        &&& crate::dom_tele::chain_ok(sig, ctds(sig, rid, p, cl), bot_env(), cf_ds(sig, rid, p, cl, dps, pv, ak), xsc)
        &&& mem(sig, cbody(sig, rid, p, cl), crate::dom_tele::exts(bot_env(), xsc),
                crate::dom_code::canon_code(sig, sh.ind, cl, pv))
    }),
{
    crate::dom_rec_ty::rec_scope_ind(sig, rid);
    cf_chain_s(sig, crate::dom_rec_ty::rshape(sig, rid), p, cl, dps, pv, xf, ak);
}

/// The chain's inputs are well formed.
proof fn ind_pv_mem_wf(sig: Sig, rid: u64, cl: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>, xf: Seq<Cpt>, j: nat)
    requires
        crate::dom_tele::chain_ok(sig, pdoms_at(sig, rid, cl), bot_env(), dps, pv),
        crate::dom_code::aw(xf),
    ensures
        forall|i: int| 0 <= i < (pv + xf).len() ==> #[trigger] wf((pv + xf)[i]),
{
    ind_pv_mem_wf_s(sig, crate::dom_rec_ty::rshape(sig, rid), cl, dps, pv, xf, j);
}

/// A field over the parameters: its value typed at the table's entry,
/// its type's code at the parameters' values.
#[verifier::spinoff_prover]
proof fn cf_ps_typed(sig: Sig, rid: u64, p: int, cl: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>, xf: Seq<Cpt>, ak: Seq<Cpt>, k: int)
    requires
        crate::ti_syntax::iota_ok(sig),
        cf_fields_ok(sig, rid, p, cl, dps, pv, xf, ak),
        0 <= k < xf.len(),
        !isrec(sig, rid, p, k),
        !ispvar(sig, rid, p, k),
        !crate::rec_canon::simple_ty(sig, crate::dom_rec_ty::rshape(sig, rid).ind, crate::dom_rec_ty::rshape(sig, rid).fields[p][k]),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let pe = crate::dom_code::fpe(pv, sh.np, k as nat);
        let cv = crate::dom_code::ceval(sig, crate::dom_code::rk(sig, sh.ind), sh.ind, Seq::empty(), pe, sh.fields[p][k]);
        typed(xf[k], cv)
    }),
{
    crate::dom_rec_ty::rec_scope_ind(sig, rid);
    cf_ps_typed_s(sig, crate::dom_rec_ty::rshape(sig, rid), p, cl, dps, pv, xf, ak, k);
}

/// THE VALUE, typed at the canonical code at the parameters' values.
#[verifier::spinoff_prover]
pub proof fn cf_val_typed(sig: Sig, rid: u64, p: int, cl: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>, xf: Seq<Cpt>, ak: Seq<Cpt>)
    requires
        crate::ti_syntax::iota_ok(sig),
        cf_fields_ok(sig, rid, p, cl, dps, pv, xf, ak),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        typed(crate::dom_code::cval(sh.ind, p as nat, crate::dom_code::smash(sig, sh.ind), xf), crate::dom_code::canon_code(sig, sh.ind, cl, pv))
    }),
{
    crate::dom_rec_ty::rec_scope_ind(sig, rid);
    cf_val_typed_s(sig, crate::dom_rec_ty::rshape(sig, rid), p, cl, dps, pv, xf, ak);
}

/// THE CONSTRUCTOR'S STEP APPROXIMATION at the parameters' values and
/// typed fields: typed at a member of its type, approximating its code
/// function, and applied along the chain giving at least the value.
#[verifier::spinoff_prover]
pub proof fn cf_step(sig: Sig, rid: u64, p: int, clv: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>, xf: Seq<Cpt>, ak: Seq<Cpt>) -> (r: (Cpt, Cpt))
    requires
        crate::ti_syntax::iota_ok(sig),
        cf_fields_ok(sig, rid, p, clv, dps, pv, xf, ak),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let c = sh.ctors[p];
        &&& mem(sig, crate::ti_syntax::dty_at(sig, c, clv), bot_env(), r.0)
        &&& typed(r.0, Cpt::U)
        &&& typed(r.1, r.0)
        &&& cf_fun(sh.ind, p as nat, crate::dom_code::smash(sig, sh.ind), sh.np, crate::ti_syntax::dty_at(sig, c, clv), Seq::empty(), 0, r.1)
        &&& le(crate::dom_code::cval(sh.ind, p as nat, crate::dom_code::smash(sig, sh.ind), xf), crate::dom_rec::apps(r.1, pv + xf))
    }),
{
    crate::dom_rec_ty::rec_scope_ind(sig, rid);
    cf_step_s(sig, crate::dom_rec_ty::rshape(sig, rid), p, clv, dps, pv, xf, ak)
}

/// The inductive's type at an instance: the parameters' sorts there, then
/// a sort.
pub proof fn ind_ty_plain(sig: Sig, rid: u64, cl: Seq<LevelSpec>) -> (l: LevelSpec)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        &&& crate::ti_syntax::dty_at(sig, sh.ind, cl) == crate::rec_canon::binds(BinderKind::Pi, pdoms_at(sig, rid, cl), ExprSpec::Sort(l))
        &&& sh.pdoms.len() == sh.np
    }),
{
    crate::dom_rec_ty::rec_scope_ind(sig, rid);
    ind_ty_plain_s(sig, crate::dom_rec_ty::rshape(sig, rid), cl)
}

/// THE INDUCTIVE AT ITS PARAMETERS' VALUES: its canonical code there is a
/// type, and a member of the inductive applied to parameter variables
/// holding at least those values.
pub proof fn ind_pv_mem(sig: Sig, rid: u64, cl: Seq<LevelSpec>, from: nat, env: Env, dps: Seq<Cpt>, pv: Seq<Cpt>)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::dom_model::sem_const(sig, crate::dom_rec_ty::rshape(sig, rid).ind, cl),
        crate::dom_tele::chain_ok(sig, pdoms_at(sig, rid, cl), bot_env(), dps, pv),
        forall|i: nat| #[trigger] wf(env(i)),
        forall|q: int| 0 <= q < crate::dom_rec_ty::rshape(sig, rid).np
            ==> #[trigger] le(pv[q], env((from + crate::dom_rec_ty::rshape(sig, rid).np - 1 - q) as nat)),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        &&& mem(sig, spine_app(ExprSpec::Const(sh.ind, cl), crate::rec_canon::vars(from, sh.np)), env,
                crate::dom_code::canon_code(sig, sh.ind, cl, pv))
        &&& typed(crate::dom_code::canon_code(sig, sh.ind, cl, pv), Cpt::U)
        &&& crate::dom_code::aw(pv)
    }),
{
    crate::dom_rec_ty::rec_scope_ind(sig, rid);
    ind_pv_mem_s(sig, crate::dom_rec_ty::rshape(sig, rid), cl, from, env, dps, pv);
}

/// A VALUE TYPED AT A MEMBER of the inductive at parameter variables below
/// the parameters' values is typed at the canonical code at those values.
#[verifier::spinoff_prover]
pub proof fn typed_at_pv(sig: Sig, rid: u64, cl: Seq<LevelSpec>, from: nat, env: Env, x: Cpt, d: Cpt, dps: Seq<Cpt>, pv: Seq<Cpt>)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::dom_model::sem_const(sig, crate::dom_rec_ty::rshape(sig, rid).ind, cl),
        crate::dom_tele::chain_ok(sig, pdoms_at(sig, rid, cl), bot_env(), dps, pv),
        forall|i: nat| #[trigger] wf(env(i)),
        forall|q: int| 0 <= q < crate::dom_rec_ty::rshape(sig, rid).np
            ==> #[trigger] le(env((from + crate::dom_rec_ty::rshape(sig, rid).np - 1 - q) as nat), pv[q]),
        mem(sig, spine_app(ExprSpec::Const(crate::dom_rec_ty::rshape(sig, rid).ind, cl),
            crate::rec_canon::vars(from, crate::dom_rec_ty::rshape(sig, rid).np)), env, d),
        typed(x, d),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        typed(x, crate::dom_code::canon_code(sig, sh.ind, cl, pv))
    }),
{
    crate::dom_rec_ty::rec_scope_ind(sig, rid);
    typed_at_pv_s(sig, crate::dom_rec_ty::rshape(sig, rid), cl, from, env, x, d, dps, pv);
}

/// A RECURSOR CALL OVER VARIABLES: its members lie below the code
/// function at the variables' values.
#[verifier::spinoff_prover]
pub proof fn ih_bound(ss: Sig, sig: Sig, rid: u64, lv: Seq<LevelSpec>, l: LevelSpec, args: Seq<ExprSpec>, env: Env, vals: Seq<Cpt>, u: Cpt)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        rec_wired(sig),
        crate::dom_rec_end::rec_hyps(sig, rid),
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::dom_model::sem_const(sig, rid, lv),
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(sig, rid, lv),
            crate::ti_syntax::dty_at(sig, rid, lv), crate::ti_syntax::sort(l))),
        args.len() == crate::dom_rec_ty::rtds(sig, rid, lv).len(),
        vals.len() == args.len(),
        forall|i: int| 0 <= i < args.len() ==> #[trigger] args[i] is Var && env(args[i]->Var_0) == vals[i],
        crate::dom_code::aw(vals),
        mem(sig, spine_app(ExprSpec::Const(rid, lv), args), env, u),
    ensures
        le(u, crate::dom_rec::recval(sig, rid, vals)),
{
    let (hw, ws) = crate::dom_bound::spine_mem(sig, ExprSpec::Const(rid, lv), args, env, u);
    reveal(mem);
    assert forall|i: int| 0 <= i < ws.len() implies le(#[trigger] ws[i], vals[i]) && wf(ws[i]) by {
        assert(mem(sig, args[i], env, ws[i]));
        let w = choose|w: Wit| #[trigger] mem_w(sig, args[i], env, ws[i], w);
    }
    crate::dom_rec::recval_wf(sig, rid, vals);
    if hw is Bot {
        apps_bot(ws);
        if !(u is Bot) {
            head_le(u, Cpt::Bot);
        }
        return;
    }
    assert(mem(sig, ExprSpec::Const(rid, lv), env, hw));
    let (a, v) = choose|a: Cpt, v: Cpt| #[trigger] rsem(sig, rid, lv, hw, a, v);
    typed_wf(v, a);
    let tds = crate::dom_rec_ty::rtds(sig, rid, lv);
    crate::dom_rec_ty::rec_ty_split(sig, rid, lv);
    assert(crate::dom_sound::fits_env(sig, Seq::empty(), bot_env()));
    let (ws2, _e, _l2, _dcs) = crate::dom_tele::tele_apps(ss, sig, Seq::empty(), tds, crate::dom_rec_ty::rbody(sig, rid), l, bot_env(), a, v, ws);
    crate::dom_rec_ty::rf_apps(sig, rid, tds, crate::dom_rec_ty::rbody(sig, rid), Seq::empty(), v, ws2);
    assert(Seq::<Cpt>::empty() + ws2 =~= ws2);
    assert forall|i: int| 0 <= i < ws.len() implies le(#[trigger] ws[i], ws[i]) by {
        le_refl(ws[i]);
    }
    crate::dom_rec::apps_mono(hw, v, ws, ws);
    assert forall|i: int| 0 <= i < ws2.len() implies le(#[trigger] ws2[i], vals[i]) by {
        le_trans(ws2[i], ws[i], vals[i]);
    }
    crate::dom_rec::recval_mono(sig, rid, ws2, vals);
    le_trans(u, crate::dom_rec::apps(hw, ws), crate::dom_rec::apps(v, ws));
    le_trans(u, crate::dom_rec::apps(v, ws2), crate::dom_rec::recval(sig, rid, ws2));
    le_trans(u, crate::dom_rec::recval(sig, rid, ws2), crate::dom_rec::recval(sig, rid, vals));
}

/// The recursor's inputs with the major rebuilt from rule `p`'s field
/// inputs.
pub open spec fn rebuilt(sig: Sig, rid: u64, p: int, xs: Seq<Cpt>) -> Seq<Cpt> {
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let pre = (sh.np + 1 + sh.nmin()) as int;
    xs.subrange(0, pre).push(crate::dom_code::cval(sh.ind, p as nat, crate::dom_code::smash(sig, sh.ind), xs.subrange(pre, xs.len() as int)))
}

/// The arguments of rule `p`'s body.
pub open spec fn body_args(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int) -> Seq<ExprSpec> {
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let nf = sh.fields[p].len();
    crate::rec_canon::vars(0, nf) + Seq::new(sh.rposj(p).len(), |r: int| ihterm(sig, rid, lv, p, r))
}

/// What the body's arguments hold at most: the field inputs, then the
/// code function at the recursive fields.
pub open spec fn body_top(sig: Sig, rid: u64, p: int, xs: Seq<Cpt>) -> Seq<Cpt> {
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let xf = xs.subrange((sh.np + 1 + sh.nmin()) as int, xs.len() as int);
    xf + crate::dom_rec::rec_ihs(sig, rid, rebuilt(sig, rid, p, xs), xf.len())
}

/// Common facts of the rebuilt inputs: the recursor there is the rule's
/// minor at the field inputs and the recursive results, whether the major
/// is the constructor's node or (a smashed structure at bottom fields)
/// bottom.
pub proof fn rebuilt_facts(sig: Sig, rid: u64, p: int, xs: Seq<Cpt>)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        0 <= p < crate::dom_rec_ty::rshape(sig, rid).nmin(),
        xs.len() == crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()
            + crate::dom_rec_ty::rshape(sig, rid).fields[p].len(),
        crate::dom_code::aw(xs),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let pre = (sh.np + 1 + sh.nmin()) as int;
        let x = rebuilt(sig, rid, p, xs);
        let xf = xs.subrange(pre, xs.len() as int);
        let mi = (sh.np + 1 + p) as int;
        &&& crate::dom_code::aw(x)
        &&& x.len() == pre + 1
        &&& x.last() == crate::dom_code::cval(sh.ind, p as nat, crate::dom_code::smash(sig, sh.ind), xf)
        &&& !(x.last() is Bot) ==> crate::dom_rec::rec_ok(sig, rid, x)
            && x.last() == Cpt::Nd(NdKey::Con(sh.ind, p as nat, crate::dom_code::smash(sig, sh.ind)), xf)
        &&& forall|i: int| 0 <= i < pre ==> #[trigger] x[i] == xs[i]
        &&& crate::dom_rec::recval(sig, rid, x) == crate::dom_rec::apps(crate::dom_rec::apps(xs[mi], xf),
            crate::dom_rec::rec_ihs(sig, rid, x, xf.len()))
        &&& crate::dom_code::aw(body_top(sig, rid, p, xs))
        &&& body_top(sig, rid, p, xs).len() == sh.fields[p].len() + sh.rposj(p).len()
        &&& x.last() is Bot ==> sh.rposj(p).len() == 0 && !crate::dom_rec::rec_ok(sig, rid, x) && crate::dom_rec::rec_bot_ok(sig, rid, x)
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let pre = (sh.np + 1 + sh.nmin()) as int;
    let nf = sh.fields[p].len();
    let mi = (sh.np + 1 + p) as int;
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    assert(sh.fields[p].len() == rd.rules[p].nfields);
    let xf = xs.subrange(pre, xs.len() as int);
    let x = rebuilt(sig, rid, p, xs);
    let sm = crate::dom_code::smash(sig, sh.ind);
    assert forall|i: int| 0 <= i < xf.len() implies #[trigger] wf(xf[i]) by {
        assert(xf[i] == xs[pre + i]);
    }
    crate::dom_code::cval_wf(sh.ind, p as nat, sm, xf);
    assert forall|i: int| 0 <= i < x.len() implies #[trigger] wf(x[i]) by {
        if i < pre { assert(x[i] == xs[i]); }
    }
    crate::dom_rec::rec_ihs_wf(sig, rid, x, nf);
    let hs = crate::dom_rec::rec_ihs(sig, rid, x, nf);
    crate::dom_rec_ty::rec_pos_facts(sh.fields[p], sh.ind, sh.us(), sh.np, sh.ni, nf);
    if x.last() is Bot {
        rebuilt_bot_ihs(sig, rid, p, xs);
        assert(!crate::dom_rec::rec_ok(sig, rid, x));
        crate::dom_rec_ty::scope_ctor_ind(sig, rid);
        assert(crate::dom_rec::rec_bot_ok(sig, rid, x));
        assert(xf =~= crate::dom_rec::bot_fields(sig, rid));
        assert(crate::dom_rec::apps(crate::dom_rec::apps(xs[mi], xf), Seq::<Cpt>::empty()) == crate::dom_rec::apps(xs[mi], xf));
        if sh.rposj(p).len() > 0 {
            let k = sh.rposj(p)[0] as int;
            assert(crate::dom_rec::rec_field(sig, rid, p, k));
        }
    } else {
        assert(x.last() == Cpt::Nd(NdKey::Con(sh.ind, p as nat, sm), xf));
        crate::dom_rec_ty::rec_ihs_len(sig, rid, x, nf);
    }
    let bt = body_top(sig, rid, p, xs);
    assert forall|i: int| 0 <= i < bt.len() implies #[trigger] wf(bt[i]) by {
        if i < nf { assert(bt[i] == xf[i]); } else { assert(bt[i] == hs[i - nf]); }
    }
}

/// A smashed structure's rebuilt major at bottom fields: the structure's
/// fields are type parameters, never recursive, so there are no
/// recursive results.
pub proof fn rebuilt_bot_ihs(sig: Sig, rid: u64, p: int, xs: Seq<Cpt>)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        0 <= p < crate::dom_rec_ty::rshape(sig, rid).nmin(),
        xs.len() == crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()
            + crate::dom_rec_ty::rshape(sig, rid).fields[p].len(),
        crate::dom_code::cval(crate::dom_rec_ty::rshape(sig, rid).ind, p as nat,
            crate::dom_code::smash(sig, crate::dom_rec_ty::rshape(sig, rid).ind),
            xs.subrange((crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int, xs.len() as int)) is Bot,
    ensures
        p == 0,
        sig.ienv.recs[rid].rules.len() == 1,
        forall|k: int| 0 <= k < crate::dom_rec_ty::rshape(sig, rid).fields[p].len() ==> !#[trigger] crate::dom_rec::rec_field(sig, rid, p, k),
        crate::dom_rec::rec_ihs(sig, rid, rebuilt(sig, rid, p, xs), crate::dom_rec_ty::rshape(sig, rid).fields[p].len())
            == Seq::<Cpt>::empty(),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    assert(crate::ti_syntax::struct_of(sig, sh.ind));
    reveal(crate::ti_syntax::struct_of);
    assert(crate::dom_code::canon_shape(sig, sh.ind) == sh);
    assert(sh.nmin() == 1);
    assert(rd.rules.len() == sh.nmin());
    assert forall|k: int| 0 <= k < sh.fields[p].len() implies !#[trigger] crate::dom_rec::rec_field(sig, rid, p, k) by {
        assert(crate::rec_canon::psimple(sig, sh.ind, sh.pdoms, sh.np, k as nat, sh.fields[0][k]));
        crate::ti_valid::psimple_not_direct(sig, sh.ind, sh.pdoms, sh.us(), sh.np, sh.ni, k as nat, sh.fields[0][k]);
    }
    let x = rebuilt(sig, rid, p, xs);
    assert(!crate::dom_rec::rec_ok(sig, rid, x));
    assert(crate::dom_rec::rec_ihs(sig, rid, x, sh.fields[p].len()) == Seq::<Cpt>::empty());
}

/// ONE ARGUMENT of the body: below what it holds at most.
#[verifier::spinoff_prover]
pub proof fn body_arg_bound(ss: Sig, sig: Sig, rid: u64, lv: Seq<LevelSpec>, l: LevelSpec, p: int, xs: Seq<Cpt>, i: int, w: Cpt)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        rec_wired(sig),
        crate::dom_rec_end::rec_hyps(sig, rid),
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::dom_model::sem_const(sig, rid, lv),
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(sig, rid, lv),
            crate::ti_syntax::dty_at(sig, rid, lv), crate::ti_syntax::sort(l))),
        0 <= p < crate::dom_rec_ty::rshape(sig, rid).nmin(),
        xs.len() == crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()
            + crate::dom_rec_ty::rshape(sig, rid).fields[p].len(),
        crate::dom_code::aw(xs),
        0 <= i < body_args(sig, rid, lv, p).len(),
        mem(sig, body_args(sig, rid, lv, p)[i], crate::dom_tele::exts(bot_env(), xs), w),
    ensures
        le(w, body_top(sig, rid, p, xs)[i]),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + 1 + nmin) as int;
    let nf = sh.fields[p].len();
    rebuilt_facts(sig, rid, p, xs);
    major_form(sig, rid, lv);
    let env = crate::dom_tele::exts(bot_env(), xs);
    let args = body_args(sig, rid, lv, p);
    let x = rebuilt(sig, rid, p, xs);
    let xf = xs.subrange(pre, xs.len() as int);
    let top = body_top(sig, rid, p, xs);
    reveal(mem);
    if i < nf {
        let v = (nf - 1 - i) as nat;
        assert(args[i] == ExprSpec::Var(v));
        let wt = choose|wt: Wit| #[trigger] mem_w(sig, ExprSpec::Var(v), env, w, wt);
        crate::dom_rec_ty::exts_at(bot_env(), xs, v);
        assert(top[i] == xf[i] && xf[i] == xs[pre + i]);
    } else {
        let r = i - nf;
        let rp = sh.rposj(p);
        crate::dom_rec_ty::rec_ihs_at(sig, rid, x, nf);
        crate::dom_rec_ty::rec_pos_facts(sh.fields[p], sh.ind, sh.us(), np, sh.ni, nf);
        let k = rp[r];
        assert(args[i] == ihterm(sig, rid, lv, p, r));
        let iargs = crate::rec_canon::vars(1 + nmin + nf, np) + seq![ExprSpec::Var(nmin + nf)]
            + crate::rec_canon::vars(nf, nmin) + seq![ExprSpec::Var((nf - 1 - k) as nat)];
        let ih = crate::dom_rec::ih_in(rd, x, xf[k as int]);
        assert(ih =~= xs.subrange(0, pre).push(xf[k as int]));
        assert forall|j: int| 0 <= j < iargs.len() implies #[trigger] iargs[j] is Var && env(iargs[j]->Var_0) == ih[j] by {
            crate::dom_rec_ty::exts_at(bot_env(), xs, iargs[j]->Var_0);
            if j == pre {
                assert(xs[pre + k] == xf[k as int]);
            }
        }
        assert forall|j: int| 0 <= j < ih.len() implies #[trigger] wf(ih[j]) by {
            if j < pre { assert(ih[j] == xs[j]); } else { assert(ih[j] == xf[k as int]); }
        }
        assert(iargs.len() == crate::dom_rec_ty::rtds(sig, rid, lv).len());
        ih_bound(ss, sig, rid, lv, l, iargs, env, ih, w);
        assert(x.last()->Nd_1 == xf);
        assert(top[i] == crate::dom_rec::rec_ihs(sig, rid, x, nf)[r]);
    }
}

/// THE RULE'S BODY: its members lie below the code function at the head
/// inputs and the major rebuilt from the field inputs.
#[verifier::spinoff_prover]
pub proof fn body_bound(ss: Sig, sig: Sig, rid: u64, lv: Seq<LevelSpec>, l: LevelSpec, p: int, xs: Seq<Cpt>, y: Cpt)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        rec_wired(sig),
        crate::dom_rec_end::rec_hyps(sig, rid),
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::dom_model::sem_const(sig, rid, lv),
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(sig, rid, lv),
            crate::ti_syntax::dty_at(sig, rid, lv), crate::ti_syntax::sort(l))),
        0 <= p < crate::dom_rec_ty::rshape(sig, rid).nmin(),
        xs.len() == crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()
            + crate::dom_rec_ty::rshape(sig, rid).fields[p].len(),
        crate::dom_code::aw(xs),
        mem(sig, rule_body(sig, rid, lv, p), crate::dom_tele::exts(bot_env(), xs), y),
    ensures
        le(y, crate::dom_rec::recval(sig, rid, rebuilt(sig, rid, p, xs))),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + 1 + nmin) as int;
    let nf = sh.fields[p].len();
    let mi = (np + 1 + p) as int;
    rebuilt_facts(sig, rid, p, xs);
    let env = crate::dom_tele::exts(bot_env(), xs);
    let x = rebuilt(sig, rid, p, xs);
    let xf = xs.subrange(pre, xs.len() as int);
    let hs = crate::dom_rec::rec_ihs(sig, rid, x, nf);
    assert(x[mi] == xs[mi]);
    let rv = crate::dom_rec::recval(sig, rid, x);
    assert(rv == crate::dom_rec::apps(crate::dom_rec::apps(xs[mi], xf), hs));
    crate::dom_rec_ty::apps_concat(xs[mi], xf, hs);
    let v0 = (nmin - 1 - p + nf) as nat;
    let args = body_args(sig, rid, lv, p);
    assert(rule_body(sig, rid, lv, p) == spine_app(ExprSpec::Var(v0), args));
    let (hw, wb) = crate::dom_bound::spine_mem(sig, ExprSpec::Var(v0), args, env, y);
    reveal(mem);
    let w0 = choose|w: Wit| #[trigger] mem_w(sig, ExprSpec::Var(v0), env, hw, w);
    crate::dom_rec_ty::exts_at(bot_env(), xs, v0);
    let full = body_top(sig, rid, p, xs);
    assert forall|i: int| 0 <= i < wb.len() implies le(#[trigger] wb[i], full[i]) by {
        assert(mem(sig, args[i], env, wb[i]));
        body_arg_bound(ss, sig, rid, lv, l, p, xs, i, wb[i]);
    }
    assert(full == xf + hs);
    assert(xs.len() - 1 - v0 == mi);
    assert(le(hw, xs[mi]));
    assert forall|i: int| 0 <= i < wb.len() implies #[trigger] wf(wb[i]) by {
        assert(mem(sig, args[i], env, wb[i]));
    }
    assert forall|i: int| 0 <= i < full.len() implies #[trigger] wf(full[i]) by {}
    crate::dom_rec::apps_mono(hw, xs[mi], wb, full);
    le_trans(y, crate::dom_rec::apps(hw, wb), crate::dom_rec::apps(xs[mi], full));
}

/// The bottom environment fits every context.
pub proof fn bot_fits(sig: Sig, g: crate::ti_syntax::Ctx)
    ensures
        crate::dom_sound::fits_env(sig, g, bot_env()),
{
    crate::dom_sound::typed_basic();
    assert forall|i: nat| i < g.len() implies #[trigger] crate::dom_sound::fits_var(sig, g, bot_env(), i) by {
        mem_bot(sig, crate::ti_syntax::var_ty(g, i), bot_env());
        reveal(mem);
        assert(crate::dom_sound::fits_at(sig, g, bot_env(), i, Cpt::Bot));
    }
}

/// What the right-in-left direction assumes of the fragment beyond the
/// recursor's scope: a non-Prop inductive whose parameters are type
/// parameters and whose closed field types are ranked below it, semantic at
/// the recursor's instance and at the major's constructor's own, the two
/// equivalent (Iota's level condition).
pub open spec fn r2l_ok(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int, clv: Seq<LevelSpec>) -> bool {
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let us = crate::dom_rec_ty::rinst(sig, rid, lv);
    &&& crate::dom_rec_ty::rec_scope(sig, rid)
    &&& crate::ti_syntax::iota_ok(sig)
    &&& 0 <= p < sh.nmin()
    &&& lv.len() == sig.ienv.recs[rid].uparams.len()
    &&& clv.len() == sig.consts[sh.ind].lps.len()
    &&& crate::conv_cr::levs_eq(us, clv)
    &&& crate::dom_model::sem_const(sig, rid, lv)
    &&& crate::dom_model::sem_const(sig, sh.ind, us)
    &&& crate::dom_model::sem_const(sig, sh.ind, clv)
    &&& crate::dom_model::sem_const(sig, sh.ctors[p], clv)
    &&& crate::dom_code::prop_ok(sig, sh.ind) && crate::dom_code::fields_blind(sig, sh.ind) && crate::dom_levels::sig_lps(sig)
    &&& crate::dom_code::fields_typed(sig, sh.ind)
    &&& forall|q: int| 0 <= q < sh.np ==> (#[trigger] sh.pdoms[q]) is Sort
    &&& forall|k: int| 0 <= k < sh.fields[p].len() && !isrec(sig, rid, p, k) && crate::rec_canon::simple_ty(sig, sh.ind, sh.fields[p][k]) ==>
        crate::dom_canon::ranked(sig, #[trigger] sh.fields[p][k], crate::dom_code::rk(sig, sh.ind))
}

/// A sort's members at equivalent levels are the same.
pub proof fn sort_mem_lv(sig: Sig, l1: LevelSpec, l2: LevelSpec, rho: Env, a: Cpt)
    requires
        crate::conv_cr::lev_eq(l1, l2),
    ensures
        mem(sig, ExprSpec::Sort(l1), rho, a) == mem(sig, ExprSpec::Sort(l2), rho, a),
{
    reveal(mem);
    assert(crate::ti_syntax::is_zero(l1) == crate::ti_syntax::is_zero(l2)) by {
        if crate::ti_syntax::is_zero(l1) {
            assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(l2, r) == 0 by {
                assert(crate::level_model::interp(l1, r) == 0);
            }
        }
        if crate::ti_syntax::is_zero(l2) {
            assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(l1, r) == 0 by {
                assert(crate::level_model::interp(l2, r) == 0);
            }
        }
    }
    if mem(sig, ExprSpec::Sort(l1), rho, a) {
        assert(mem_w(sig, ExprSpec::Sort(l2), rho, a, crate::dom_model::Wit::Nil));
    }
    if mem(sig, ExprSpec::Sort(l2), rho, a) {
        assert(mem_w(sig, ExprSpec::Sort(l1), rho, a, crate::dom_model::Wit::Nil));
    }
}

/// The parameters' values typed along their sorts at one instance are
/// typed along them at an equivalent one.
pub proof fn chain_pdoms_lv(sig: Sig, rid: u64, us: Seq<LevelSpec>, us2: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        forall|q: int| 0 <= q < crate::dom_rec_ty::rshape(sig, rid).np ==> (#[trigger] crate::dom_rec_ty::rshape(sig, rid).pdoms[q]) is Sort,
        us.len() == crate::dom_rec_ty::rshape(sig, rid).lps.len(),
        crate::conv_cr::levs_eq(us, us2),
        crate::dom_tele::chain_ok(sig, pdoms_at(sig, rid, us), bot_env(), dps, pv),
    ensures
        crate::dom_tele::chain_ok(sig, pdoms_at(sig, rid, us2), bot_env(), dps, pv),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    crate::dom_rec_ty::scope_ctor_ind(sig, rid);
    crate::dom_ctor_bound::ctor_shape_ind(sig, sh.ind);
    let (pd, pd2) = (pdoms_at(sig, rid, us), pdoms_at(sig, rid, us2));
    assert forall|i: int| 0 <= i < pd2.len() implies #[trigger] crate::dom_sound::dfit(sig, pd2[i],
        crate::dom_tele::exts(bot_env(), pv.subrange(0, i)), dps[i], pv[i]) by {
        let env = crate::dom_tele::exts(bot_env(), pv.subrange(0, i));
        assert(crate::dom_sound::dfit(sig, pd[i], env, dps[i], pv[i]));
        let l0 = sh.pdoms[i]->Sort_0;
        assert(sh.pdoms[i] == ExprSpec::Sort(l0));
        let (l1, l2) = (crate::level_model::subst_level_spec(l0, sh.lps, us), crate::level_model::subst_level_spec(l0, sh.lps, us2));
        assert(pd[i] == ExprSpec::Sort(l1) && pd2[i] == ExprSpec::Sort(l2));
        crate::ti_ls2::ll_pair(l0, l0, sh.lps, us, us2);
        sort_mem_lv(sig, l1, l2, env, dps[i]);
    }
}

/// The rule chain's parameter inputs, typed along the declared domains.
pub proof fn r2l_pv(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int, clv: Seq<LevelSpec>, ds: Seq<Cpt>, xs: Seq<Cpt>)
    requires
        r2l_ok(sig, rid, lv, p, clv),
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0,
            (crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int) + ftds(sig, rid, lv, p),
            bot_env(), ds, xs),
    ensures ({
        let np = crate::dom_rec_ty::rshape(sig, rid).np as int;
        crate::dom_tele::chain_ok(sig, pdoms_at(sig, rid, crate::dom_rec_ty::rinst(sig, rid, lv)), bot_env(), ds.subrange(0, np), xs.subrange(0, np))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + 1 + nmin) as int;
    let tds = crate::dom_rec_ty::rtds(sig, rid, lv);
    let tl = tds.subrange(0, pre) + ftds(sig, rid, lv, p);
    let lm = crate::rec_canon::elim_level(sig, rid, crate::rec_canon::rec_ind(sig, rid));
    major_form(sig, rid, lv);
    crate::dom_rec_ty::scope_ctor_ind(sig, rid);
    crate::dom_ctor_bound::ctor_shape_ind(sig, sh.ind);
    assert(sh.pdoms.len() == np);
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(1 + nmin, np));
    let pd = pdoms_at(sig, rid, crate::dom_rec_ty::rinst(sig, rid, lv));
    crate::dom_rec_ty::rec_elp_pdoms(sig, rid);
    assert forall|i: int| 0 <= i < np implies #[trigger] crate::dom_sound::dfit(sig, pd[i],
        crate::dom_tele::exts(bot_env(), xs.subrange(0, np as int).subrange(0, i)), ds.subrange(0, np as int)[i], xs.subrange(0, np as int)[i]) by {
        assert(crate::dom_sound::dfit(sig, tl[i], crate::dom_tele::exts(bot_env(), xs.subrange(0, i)), ds[i], xs[i]));
        assert((sh.head_doms(lm) + seq![major])[i] == sh.pdoms[i]);
        assert(tl[i] == tds[i]);
        assert(tds[i] == crate::expr_model::subst_expr_levels(sh.pdoms[i], rd.uparams, lv));
        crate::dom_rec_ty::rinst_id(sig, rid, lv, sh.pdoms[i]);
        assert(xs.subrange(0, np as int).subrange(0, i) =~= xs.subrange(0, i));
    }
}

/// An interpreted recursor's inductive ranks below it.
pub proof fn r2l_ind_below(sig: Sig, rid: u64, lv: Seq<LevelSpec>)
    requires
        crate::dom_rec_end::rec_hyps(sig, rid),
        lv.len() == sig.ienv.recs[rid].uparams.len(),
    ensures
        crate::dom_code::rk(sig, crate::dom_rec_ty::rshape(sig, rid).ind) < crate::dom_code::rk(sig, rid),
        crate::ti_syntax::iota_ok(sig),
{
    reveal(crate::dom_rec_end::sig_rec);
    reveal(crate::dom_rec_end::rec_interp);
    assert(crate::dom_rec_end::rec_model(sig, rid));
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    assert(crate::dom_model::sem_const(sig, sh.ind, sig.consts[sh.ind].lps.map_values(|n: u64| LevelSpec::Param(n))));
    crate::dom_rec_ty::ind_below_rec(sig, rid, lv);
}

/// A closed field's input: typed at a member of its closed type at the
/// constructor's instance (the type's two instances convert, so have the
/// same members).
#[verifier::spinoff_prover]
pub proof fn r2l_closed_field(ss: Sig, sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int, clv: Seq<LevelSpec>, ds: Seq<Cpt>, xs: Seq<Cpt>, k: int)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        ss == crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, rid)),
        crate::dom_rec_end::rec_hyps(sig, rid),
        r2l_ok(sig, rid, lv, p, clv),
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0,
            (crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int) + ftds(sig, rid, lv, p),
            bot_env(), ds, xs),
        0 <= k < crate::dom_rec_ty::rshape(sig, rid).fields[p].len(),
        !isrec(sig, rid, p, k),
        !ispvar(sig, rid, p, k),
        crate::rec_canon::simple_ty(sig, crate::dom_rec_ty::rshape(sig, rid).ind, crate::dom_rec_ty::rshape(sig, rid).fields[p][k]),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let i = (sh.np + 1 + sh.nmin() + k) as int;
        &&& mem(sig, crate::iota_sr::cfu(sig, rid, p, k, clv), bot_env(), ds[i]) && typed(ds[i], Cpt::U) && typed(xs[i], ds[i])
        &&& crate::dom_canon::ranked(sig, sh.fields[p][k], crate::dom_code::rk(sig, sh.ind))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + 1 + nmin) as int;
    let tl = crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0, pre) + ftds(sig, rid, lv, p);
    let ff = ftds(sig, rid, lv, p);
    let i = pre + k;
    let us = crate::dom_rec_ty::rinst(sig, rid, lv);
    let env = crate::dom_tele::exts(bot_env(), xs.subrange(0, i));
    assert(crate::dom_sound::dfit(sig, tl[i], env, ds[i], xs[i]));
    assert(tl[i] == ff[k]);
    let f = sh.fields[p][k];
    let (fu, fu2) = (crate::iota_sr::cfu(sig, rid, p, k, us), crate::iota_sr::cfu(sig, rid, p, k, clv));
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::dom_rec_ty::rec_lps_sub(sig, rid);
    simple_closed(sig, sh.ind, f);
    crate::dom_rec_ty::rec_elp_parts(sig, rid, p);
    crate::dom_rec_ty::rinst_id(sig, rid, lv, f);
    crate::ti_level::ls_lift((1 + nmin) as nat, k as nat, f, rd.uparams, lv);
    crate::ti_level::ls_nlbv(f, sh.lps, us);
    crate::ti_level::ls_nlbv(f, sh.lps, clv);
    crate::subst_algebra::lift_closed((1 + nmin) as nat, k as nat, fu);
    assert(ff[k] == fu);
    crate::dom_model::mem_closed_env(sig, fu, env, ds[i]);
    crate::dom_model::mem_closed_env(sig, fu, bot_env(), ds[i]);
    // the two instances of the closed type convert, so have the same members
    crate::dom_rec_end::rec_canon_ok(sig, rid);
    crate::dom_lift::field_facts(sig, sh.ind, p, k);
    // the field is typed below its inductive's rank, below the recursor's
    let ri = crate::dom_code::rk(sig, sh.ind);
    let s0 = crate::ti_strip::strip_below(sig, ri);
    r2l_ind_below(sig, rid, lv);
    crate::dom_sound::oracle_down(sig, ri, crate::dom_code::rk(sig, rid));
    let l = choose|l: LevelSpec| #[trigger] crate::ti_syntax::derivable(s0, crate::ti_syntax::eq(Seq::empty(), f, f, crate::ti_syntax::sort(l)));
    crate::dom_levels::sig_lps_below(sig, ri, sh.lps, us);
    crate::dom_levels::sig_lps_below(sig, ri, sh.lps, clv);
    crate::ti_ls2::ls_pair_nil(s0, f, f, crate::ti_syntax::sort(l), sh.lps, us, clv);
    let te = crate::expr_model::subst_expr_levels(crate::ti_syntax::sort(l), sh.lps, us);
    let d = crate::ti_sub::get(s0, crate::ti_syntax::eq(Seq::empty(), fu, fu2, te));
    assert(crate::dom_sound::fits_env(sig, Seq::empty(), bot_env())) by {
        assert forall|j: nat| #[trigger] wf(bot_env()(j)) by {
            crate::dom_sound::typed_basic();
            typed_wf(Cpt::Bot, Cpt::U);
        }
    }
    crate::dom_sound::oracle_use(s0, sig, d, bot_env());
    assert(crate::dom_sound::sem_eq(sig, fu, fu2, bot_env()));
    assert(mem(sig, fu2, bot_env(), ds[i]));
}

/// A parameter-typed field's input: typed at a code below its parameter's
/// value.
#[verifier::spinoff_prover]
pub proof fn r2l_pvar_field(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int, clv: Seq<LevelSpec>, ds: Seq<Cpt>, xs: Seq<Cpt>, k: int)
    requires
        r2l_ok(sig, rid, lv, p, clv),
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0,
            (crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int) + ftds(sig, rid, lv, p),
            bot_env(), ds, xs),
        0 <= k < crate::dom_rec_ty::rshape(sig, rid).fields[p].len(),
        ispvar(sig, rid, p, k),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let i = (sh.np + 1 + sh.nmin() + k) as int;
        &&& wf(ds[i]) && le(ds[i], xs[pvq(sig, rid, p, k)]) && typed(ds[i], Cpt::U) && typed(xs[i], ds[i])
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + 1 + nmin) as int;
    let tl = crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0, pre) + ftds(sig, rid, lv, p);
    let ff = ftds(sig, rid, lv, p);
    let i = pre + k;
    let env = crate::dom_tele::exts(bot_env(), xs.subrange(0, i));
    assert(crate::dom_sound::dfit(sig, tl[i], env, ds[i], xs[i]));
    assert(tl[i] == ff[k]);
    let v = sh.fields[p][k]->Var_0;
    let iv = (v + 1 + nmin) as nat;
    assert(sh.field_at(p, k, (1 + nmin) as nat) == ExprSpec::Var(iv));
    assert(crate::expr_model::subst_expr_levels(ExprSpec::Var(iv), rd.uparams, lv) == ExprSpec::Var(iv));
    assert(ff[k] == ExprSpec::Var(iv));
    crate::dom_adeq_base::mem_var(sig, iv, env, ds[i]);
    crate::dom_rec_ty::exts_at(bot_env(), xs.subrange(0, i), iv);
    assert(xs.subrange(0, i)[i - 1 - iv] == xs[pvq(sig, rid, p, k)]);
}

/// A recursive field's input: typed at the inductive's canonical code at
/// the parameters' values.
#[verifier::spinoff_prover]
pub proof fn r2l_rec_field(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int, clv: Seq<LevelSpec>, ds: Seq<Cpt>, xs: Seq<Cpt>, k: int)
    requires
        r2l_ok(sig, rid, lv, p, clv),
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0,
            (crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int) + ftds(sig, rid, lv, p),
            bot_env(), ds, xs),
        0 <= k < crate::dom_rec_ty::rshape(sig, rid).fields[p].len(),
        isrec(sig, rid, p, k),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        typed(xs[(sh.np + 1 + sh.nmin() + k) as int], crate::dom_code::canon_code(sig, sh.ind, crate::dom_rec_ty::rinst(sig, rid, lv),
            xs.subrange(0, sh.np as int)))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + 1 + nmin) as int;
    let tl = crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0, pre) + ftds(sig, rid, lv, p);
    let ff = ftds(sig, rid, lv, p);
    let i = pre + k;
    let env = crate::dom_tele::exts(bot_env(), xs.subrange(0, i));
    assert(crate::dom_sound::dfit(sig, tl[i], env, ds[i], xs[i]));
    assert(tl[i] == ff[k]);
    crate::dom_rec_shape::occ_form(sh, p, k, (1 + nmin) as nat, rd.uparams, lv);
    assert((k as nat + (1 + nmin) as nat) == (k + 1 + nmin) as nat);
    assert forall|j: nat| #[trigger] wf(env(j)) by {
        crate::dom_rec_ty::exts_at(bot_env(), xs.subrange(0, i), j);
        if j < i {
            assert(crate::dom_sound::dfit(sig, tl[i - 1 - j], crate::dom_tele::exts(bot_env(), xs.subrange(0, i - 1 - j)), ds[i - 1 - j], xs[i - 1 - j]));
            typed_wf(xs[i - 1 - j], ds[i - 1 - j]);
            assert(xs.subrange(0, i)[i - 1 - j] == xs[i - 1 - j]);
        }
    }
    r2l_pv(sig, rid, lv, p, clv, ds, xs);
    let pv = xs.subrange(0, np as int);
    assert forall|q: int| 0 <= q < np implies #[trigger] le(env((k + 1 + nmin + np - 1 - q) as nat), pv[q]) by {
        crate::dom_rec_ty::exts_at(bot_env(), xs.subrange(0, i), (k + 1 + nmin + np - 1 - q) as nat);
        assert(xs.subrange(0, i)[q] == pv[q]);
        assert(wf(pv[q]));
        le_refl(pv[q]);
    }
    typed_at_pv(sig, rid, crate::dom_rec_ty::rinst(sig, rid, lv), (k + 1 + nmin) as nat, env, xs[i], ds[i], ds.subrange(0, np as int), pv);
}

/// THE FIELD INPUTS of a typed chain along the rule's binders are what the
/// A field over the parameters: a member of its type at the parameters'
/// values and the earlier fields.
pub proof fn r2l_ps_field(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int, clv: Seq<LevelSpec>, ds: Seq<Cpt>, xs: Seq<Cpt>, k: int)
    requires
        crate::dom_rec_end::rec_hyps(sig, rid),
        r2l_ok(sig, rid, lv, p, clv),
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0,
            (crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int) + ftds(sig, rid, lv, p),
            bot_env(), ds, xs),
        0 <= k < crate::dom_rec_ty::rshape(sig, rid).fields[p].len(),
        !isrec(sig, rid, p, k),
        !ispvar(sig, rid, p, k),
        !crate::rec_canon::simple_ty(sig, crate::dom_rec_ty::rshape(sig, rid).ind, crate::dom_rec_ty::rshape(sig, rid).fields[p][k]),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let pre = (sh.np + 1 + sh.nmin()) as int;
        let i = pre + k;
        let (pv, xf) = (xs.subrange(0, sh.np as int), xs.subrange(pre, xs.len() as int));
        &&& mem(sig, crate::iota_sr::cfu(sig, rid, p, k, crate::dom_rec_ty::rinst(sig, rid, lv)),
                crate::dom_tele::exts(bot_env(), pv + xf.subrange(0, k)), ds[i])
        &&& typed(ds[i], Cpt::U) && typed(xs[i], ds[i])
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + 1 + nmin) as int;
    let tl = crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0, pre) + ftds(sig, rid, lv, p);
    let ff = ftds(sig, rid, lv, p);
    let i = pre + k;
    let (pv, xf) = (xs.subrange(0, np as int), xs.subrange(pre, xs.len() as int));
    let e1 = crate::dom_tele::exts(bot_env(), xs.subrange(0, i));
    let e2 = crate::dom_tele::exts(bot_env(), pv + xf.subrange(0, k));
    assert(crate::dom_sound::dfit(sig, tl[i], e1, ds[i], xs[i]));
    assert(tl[i] == ff[k]);
    let f = sh.fields[p][k];
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::dom_canon::canon_fields(sig, sh.ind, p, k);
    // over the parameters, so without level parameters
    crate::dom_rec_end::rec_canon_ok(sig, rid);
    crate::dom_rec_ty::rec_lps_sub(sig, rid);
    crate::dom_rec_ty::rec_elp_parts(sig, rid, p);
    crate::dom_rec_ty::rinst_id(sig, rid, lv, f);
    let fu = crate::iota_sr::cfu(sig, rid, p, k, crate::dom_rec_ty::rinst(sig, rid, lv));
    crate::iota_sr::ps_field_at(sig, rid, p, k, crate::dom_rec_ty::rinst(sig, rid, lv));
    assert(crate::expr_model::subst_expr_levels(f, rd.uparams, lv) == fu);
    crate::ti_level::ls_lift((1 + nmin) as nat, k as nat, f, rd.uparams, lv);
    assert(ff[k] == crate::subst_algebra::lift((1 + nmin) as nat, k as nat, fu));
    crate::subst_algebra::lift_zero(k as nat, fu);
    assert forall|j: nat| j < np implies #[trigger] e1(j + (k as nat) + ((1 + nmin) as nat)) == e2(j + (k as nat) + 0) by {
        crate::dom_rec_ty::exts_at(bot_env(), xs.subrange(0, i), (j + k + 1 + nmin) as nat);
        crate::dom_rec_ty::exts_at(bot_env(), pv + xf.subrange(0, k), (j + k) as nat);
        assert((pv + xf.subrange(0, k))[np - 1 - j] == xs[np - 1 - j]);
    }
    crate::dom_psimple::ps_mem_transfer(sig, sh.ind, sh.pdoms, np, k as nat, fu, (1 + nmin) as nat, 0, e1, e2, ds[i]);
}

/// constructor step needs, at the chain's parameter inputs.
#[verifier::spinoff_prover]
pub proof fn r2l_fields(ss: Sig, sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int, clv: Seq<LevelSpec>, ds: Seq<Cpt>, xs: Seq<Cpt>)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        ss == crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, rid)),
        crate::dom_rec_end::rec_hyps(sig, rid),
        r2l_ok(sig, rid, lv, p, clv),
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0,
            (crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int) + ftds(sig, rid, lv, p),
            bot_env(), ds, xs),
    ensures ({
        let np = crate::dom_rec_ty::rshape(sig, rid).np as int;
        let pre = (crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int;
        cf_fields_ok(sig, rid, p, clv, ds.subrange(0, np), xs.subrange(0, np), xs.subrange(pre, xs.len() as int), ds.subrange(pre, ds.len() as int))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + 1 + nmin) as int;
    let tl = crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0, pre) + ftds(sig, rid, lv, p);
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    assert(sh.fields[p].len() == rd.rules[p].nfields);
    r2l_pv(sig, rid, lv, p, clv, ds, xs);
    let xf = xs.subrange(pre, xs.len() as int);
    let ak = ds.subrange(pre, ds.len() as int);
    let pv = xs.subrange(0, np as int);
    let us = crate::dom_rec_ty::rinst(sig, rid, lv);
    // the parameters, at their sorts at the constructor's instance
    crate::dom_rec_ty::rec_lps_sub(sig, rid);
    chain_pdoms_lv(sig, rid, us, clv, ds.subrange(0, np as int), pv);
    crate::dom_rec_end::rec_canon_ok(sig, rid);
    assert forall|k: int| 0 <= k < xf.len() implies #[trigger] wf(xf[k]) by {
        assert(crate::dom_sound::dfit(sig, tl[pre + k], crate::dom_tele::exts(bot_env(), xs.subrange(0, pre + k)), ds[pre + k], xs[pre + k]));
        typed_wf(xs[pre + k], ds[pre + k]);
    }
    assert forall|k: int| 0 <= k < xf.len() && !isrec(sig, rid, p, k) && !ispvar(sig, rid, p, k)
        && crate::rec_canon::simple_ty(sig, sh.ind, sh.fields[p][k]) implies
        mem(sig, crate::iota_sr::cfu(sig, rid, p, k, clv), bot_env(), #[trigger] ak[k]) && typed(ak[k], Cpt::U) && typed(xf[k], ak[k])
        && crate::dom_canon::ranked(sig, sh.fields[p][k], crate::dom_code::rk(sig, sh.ind)) by {
        r2l_closed_field(ss, sig, rid, lv, p, clv, ds, xs, k);
    }
    assert forall|k: int| 0 <= k < xf.len() && !isrec(sig, rid, p, k) && !ispvar(sig, rid, p, k)
        && !crate::rec_canon::simple_ty(sig, sh.ind, sh.fields[p][k]) implies
        mem(sig, crate::iota_sr::cfu(sig, rid, p, k, clv), crate::dom_tele::exts(bot_env(), pv + xf.subrange(0, k)), #[trigger] ak[k])
        && typed(ak[k], Cpt::U) && typed(xf[k], ak[k]) by {
        r2l_ps_mem(ss, sig, rid, lv, p, clv, ds, xs, k);
    }
    r2l_fields_b(ss, sig, rid, lv, p, clv, ds, xs);
    assert(crate::dom_code::aw(xf));
    assert(crate::dom_tele::chain_ok(sig, pdoms_at(sig, rid, clv), bot_env(), ds.subrange(0, np as int), pv));
}

/// `r2l_fields`' parameter-typed and recursive fields.
#[verifier::spinoff_prover]
proof fn r2l_fields_b(ss: Sig, sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int, clv: Seq<LevelSpec>, ds: Seq<Cpt>, xs: Seq<Cpt>)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        ss == crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, rid)),
        crate::dom_rec_end::rec_hyps(sig, rid),
        r2l_ok(sig, rid, lv, p, clv),
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0,
            (crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int) + ftds(sig, rid, lv, p),
            bot_env(), ds, xs),
    ensures ({
        let np = crate::dom_rec_ty::rshape(sig, rid).np as int;
        let pre = (crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int;
        let pv = xs.subrange(0, np);
        let xf = xs.subrange(pre, xs.len() as int);
        let ak = ds.subrange(pre, ds.len() as int);
        &&& forall|k: int| 0 <= k < xf.len() && ispvar(sig, rid, p, k) ==>
            wf(#[trigger] ak[k]) && le(ak[k], pv[pvq(sig, rid, p, k)]) && typed(ak[k], Cpt::U) && typed(xf[k], ak[k])
        &&& forall|k: int| 0 <= k < xf.len() && isrec(sig, rid, p, k) ==>
            typed(#[trigger] xf[k], crate::dom_code::canon_code(sig, crate::dom_rec_ty::rshape(sig, rid).ind, clv, pv))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + 1 + nmin) as int;
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    assert(sh.fields[p].len() == rd.rules[p].nfields);
    r2l_pv(sig, rid, lv, p, clv, ds, xs);
    let xf = xs.subrange(pre, xs.len() as int);
    let ak = ds.subrange(pre, ds.len() as int);
    let pv = xs.subrange(0, np as int);
    let us = crate::dom_rec_ty::rinst(sig, rid, lv);
    crate::dom_rec_ty::rec_lps_sub(sig, rid);
    crate::dom_rec_end::rec_canon_ok(sig, rid);
    assert forall|k: int| 0 <= k < xf.len() && ispvar(sig, rid, p, k) implies
        wf(#[trigger] ak[k]) && le(ak[k], pv[pvq(sig, rid, p, k)]) && typed(ak[k], Cpt::U) && typed(xf[k], ak[k]) by {
        r2l_pvar_field(sig, rid, lv, p, clv, ds, xs, k);
        typed_wf(ak[k], Cpt::U);
        crate::dom_canon::canon_fields(sig, sh.ind, p, k);
        assert(pv[pvq(sig, rid, p, k)] == xs[pvq(sig, rid, p, k)]);
    }
    assert forall|k: int| 0 <= k < xf.len() && isrec(sig, rid, p, k) implies
        typed(#[trigger] xf[k], crate::dom_code::canon_code(sig, sh.ind, clv, pv)) by {
        r2l_rec_field(sig, rid, lv, p, clv, ds, xs, k);
        crate::dom_code::canon_lveq(sig, sh.ind, us, clv, pv);
    }
}

/// `r2l_fields`' case of a field over the parameters.
#[verifier::spinoff_prover]
proof fn r2l_ps_mem(ss: Sig, sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int, clv: Seq<LevelSpec>, ds: Seq<Cpt>, xs: Seq<Cpt>, k: int)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        ss == crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, rid)),
        crate::dom_rec_end::rec_hyps(sig, rid),
        r2l_ok(sig, rid, lv, p, clv),
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0,
            (crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int) + ftds(sig, rid, lv, p),
            bot_env(), ds, xs),
        0 <= k < xs.len() - (crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()),
        !isrec(sig, rid, p, k),
        !ispvar(sig, rid, p, k),
        !crate::rec_canon::simple_ty(sig, crate::dom_rec_ty::rshape(sig, rid).ind, crate::dom_rec_ty::rshape(sig, rid).fields[p][k]),
    ensures ({
        let np = crate::dom_rec_ty::rshape(sig, rid).np as int;
        let pre = (crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int;
        let (pv, xf, ak) = (xs.subrange(0, np), xs.subrange(pre, xs.len() as int), ds.subrange(pre, ds.len() as int));
        &&& mem(sig, crate::iota_sr::cfu(sig, rid, p, k, clv), crate::dom_tele::exts(bot_env(), pv + xf.subrange(0, k)), ak[k])
        &&& typed(ak[k], Cpt::U) && typed(xf[k], ak[k])
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + 1 + nmin) as int;
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    assert(sh.fields[p].len() == rd.rules[p].nfields);
    r2l_pv(sig, rid, lv, p, clv, ds, xs);
    let xf = xs.subrange(pre, xs.len() as int);
    let ak = ds.subrange(pre, ds.len() as int);
    let pv = xs.subrange(0, np as int);
    let us = crate::dom_rec_ty::rinst(sig, rid, lv);
    crate::dom_rec_ty::rec_lps_sub(sig, rid);
    chain_pdoms_lv(sig, rid, us, clv, ds.subrange(0, np as int), pv);
    crate::dom_rec_end::rec_canon_ok(sig, rid);
        r2l_ps_field(sig, rid, lv, p, clv, ds, xs, k);
        crate::dom_rec_ty::scope_ctor(sig, rid, p);
        crate::dom_canon::canon_fields(sig, sh.ind, p, k);
        // from the recursor's instance to the constructor's, through the
        // field's lowering over the parameters
        crate::iota_sr::ps_field_at(sig, rid, p, k, us);
        crate::iota_sr::ps_field_at(sig, rid, p, k, clv);
        crate::dom_lift::pfield_facts(sig, sh.ind, p, k);
        let (fu, fu2) = (crate::iota_sr::cfu(sig, rid, p, k, us), crate::iota_sr::cfu(sig, rid, p, k, clv));
        let e = crate::rec_canon::plow(sh.fields[p][k], k as nat);
        let env = crate::dom_tele::exts(bot_env(), pv + xf.subrange(0, k));
        let env2 = crate::dom_tele::exts(bot_env(), pv);
        let kn = k as nat;
        assert forall|i: nat| i < np implies #[trigger] env2(i) == env(i + kn) by {
            crate::dom_rec_ty::exts_at(bot_env(), pv, i);
            crate::dom_rec_ty::exts_at(bot_env(), pv + xf.subrange(0, k), i + kn);
            assert((pv + xf.subrange(0, k))[np - 1 - i] == pv[np - 1 - i]);
        }
        crate::dom_psimple::ps_mem_plow(sig, sh.ind, sh.pdoms, np, k as nat, fu, env, env2, ak[k]);
        crate::dom_psimple::ps_mem_plow(sig, sh.ind, sh.pdoms, np, k as nat, fu2, env, env2, ak[k]);
        let s0 = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, sh.ind));
        r2l_ind_below(sig, rid, lv);
        crate::dom_sound::oracle_down(sig, crate::dom_code::rk(sig, sh.ind), crate::dom_code::rk(sig, rid));
        let l0 = choose|l: LevelSpec| #[trigger] crate::ti_syntax::derivable(s0, crate::ti_syntax::eq(sh.pdoms, e, e, crate::ti_syntax::sort(l)));
        assert(crate::ti_level::gls(sh.pdoms, sig.consts[sh.ind].lps, us) =~= pdoms_at(sig, rid, us));
        crate::dom_psimple::ps_mem_lv(s0, sig, sh.ind, us, clv, e, l0, ds.subrange(0, np as int), pv, ak[k]);
}

/// A CONSTRUCTOR NODE over field values typed as the constructor step
/// asks is a member of the constructor application whose arguments have
/// the parameters' values and the fields above them as members.
#[verifier::spinoff_prover]
pub proof fn con_major(sig: Sig, rid: u64, p: int, clv: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>,
    xf: Seq<Cpt>, ak: Seq<Cpt>, cargs: Seq<ExprSpec>, rho: Env, wl: Seq<Cpt>)
    requires
        cf_fields_ok(sig, rid, p, clv, dps, pv, xf, ak),
        crate::dom_code::canon_sr(sig, crate::dom_rec_ty::rshape(sig, rid).ind),
        crate::dom_model::sem_const(sig, crate::dom_rec_ty::rshape(sig, rid).ctors[p], clv),
        cargs.len() == crate::dom_rec_ty::rshape(sig, rid).np + xf.len(),
        wl.len() == xf.len(),
        forall|q: int| 0 <= q < crate::dom_rec_ty::rshape(sig, rid).np ==> mem(sig, #[trigger] cargs[q], rho, pv[q]),
        forall|k: int| 0 <= k < xf.len() ==> mem(sig, cargs[crate::dom_rec_ty::rshape(sig, rid).np + k], rho, #[trigger] wl[k])
            && le(xf[k], wl[k]),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        mem(sig, spine_app(ExprSpec::Const(sh.ctors[p], clv), cargs), rho, crate::dom_code::cval(sh.ind, p as nat, crate::dom_code::smash(sig, sh.ind), xf))
    }),
{
    crate::dom_rec_ty::rec_scope_ind(sig, rid);
    con_major_s(sig, crate::dom_rec_ty::rshape(sig, rid), p, clv, dps, pv, xf, ak, cargs, rho, wl);
}

/// THE REBUILT MAJOR is a member of the constructor application, its
/// parameter arguments having the parameters' values as members.
#[verifier::spinoff_prover]
pub proof fn r2l_major(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int, clv: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>,
    xf: Seq<Cpt>, ak: Seq<Cpt>, cargs: Seq<ExprSpec>, rho: Env, wl: Seq<Cpt>)
    requires
        r2l_ok(sig, rid, lv, p, clv),
        cf_fields_ok(sig, rid, p, clv, dps, pv, xf, ak),
        cargs.len() == crate::dom_rec_ty::rshape(sig, rid).np + xf.len(),
        wl.len() == xf.len(),
        forall|q: int| 0 <= q < crate::dom_rec_ty::rshape(sig, rid).np ==> mem(sig, #[trigger] cargs[q], rho, pv[q]),
        forall|k: int| 0 <= k < xf.len() ==> mem(sig, cargs[crate::dom_rec_ty::rshape(sig, rid).np + k], rho, #[trigger] wl[k])
            && le(xf[k], wl[k]),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        mem(sig, spine_app(ExprSpec::Const(sh.ctors[p], clv), cargs), rho, crate::dom_code::cval(sh.ind, p as nat, crate::dom_code::smash(sig, sh.ind), xf))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let (ind, np) = (sh.ind, sh.np);
    let c = sh.ctors[p];
    let (ac, v) = cf_step(sig, rid, p, clv, dps, pv, xf, ak);
    typed_wf(v, ac);
    le_refl(v);
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    assert(crate::dom_code::canon_ok(sig, ind));
    assert(crate::dom_model::ctor_of(sig, ind, c));
    assert(crate::dom_model::code_ok(sig, c, clv, ac, v));
    assert(crate::dom_sem::sem_mem(sig, c, clv, v, ac, v));
    crate::dom_sem::mem_sem(sig, c, clv, rho, v);
    let ws = pv + xf;
    ind_pv_mem_wf(sig, rid, clv, dps, pv, xf, 0);
    assert forall|i: int| 0 <= i < cargs.len() implies #[trigger] mem(sig, cargs[i], rho, ws[i]) && wf(ws[i]) by {
        if i < np {
            assert(ws[i] == pv[i]);
        } else {
            let k = i - np;
            assert(ws[i] == xf[k]);
            assert(wl[k] == wl[k]);
            assert(mem(sig, cargs[np + k], rho, wl[k]) && le(xf[k], wl[k]));
            mem_down_e(sig, cargs[i], rho, wl[k], xf[k]);
        }
    }
    let val = crate::dom_code::cval(ind, p as nat, crate::dom_code::smash(sig, ind), xf);
    crate::dom_code::cval_wf(ind, p as nat, crate::dom_code::smash(sig, ind), xf);
    crate::dom_bound::spine_mem_intro(sig, ExprSpec::Const(c, clv), cargs, rho, v, ws, val);
}

/// IOTA, RIGHT IN LEFT, without extra arguments: a member of the rule
/// applied to the head arguments and the fields is a member of the
/// recursor applied up to its major, a constructor application of exact
/// THE REBUILT INPUTS FIT the recursor's telescope: the heads as walked,
/// the rebuilt major at the canonical code at the parameters' values.
#[verifier::spinoff_prover]
pub proof fn r2l_fit(ss: Sig, sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int, clv: Seq<LevelSpec>, ds: Seq<Cpt>, xs: Seq<Cpt>)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        ss == crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, rid)),
        crate::dom_rec_end::rec_hyps(sig, rid),
        r2l_ok(sig, rid, lv, p, clv),
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0,
            (crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int) + ftds(sig, rid, lv, p),
            bot_env(), ds, xs),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let pre = (sh.np + 1 + sh.nmin()) as int;
        let x = rebuilt(sig, rid, p, xs);
        let dsx = ds.subrange(0, pre).push(crate::dom_code::canon_code(sig, sh.ind, crate::dom_rec_ty::rinst(sig, rid, lv),
            xs.subrange(0, sh.np as int)));
        let tds = crate::dom_rec_ty::rtds(sig, rid, lv);
        &&& x.len() == tds.len() && dsx.len() == tds.len()
        &&& forall|i: int| 0 <= i < tds.len() ==> #[trigger] crate::dom_sound::dfit(sig, tds[i],
            crate::dom_tele::exts(bot_env(), x.subrange(0, i)), dsx[i], x[i])
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + 1 + nmin) as int;
    let tl = crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0, pre) + ftds(sig, rid, lv, p);
    r2l_fields(ss, sig, rid, lv, p, clv, ds, xs);
    r2l_pv(sig, rid, lv, p, clv, ds, xs);
    let us = crate::dom_rec_ty::rinst(sig, rid, lv);
    let xf = xs.subrange(pre, xs.len() as int);
    let ak = ds.subrange(pre, ds.len() as int);
    let (dps, pv) = (ds.subrange(0, np as int), xs.subrange(0, np as int));
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] wf(xs[i]) by {
        assert(crate::dom_sound::dfit(sig, tl[i], crate::dom_tele::exts(bot_env(), xs.subrange(0, i)), ds[i], xs[i]));
        typed_wf(xs[i], ds[i]);
    }
    rebuilt_facts(sig, rid, p, xs);
    let x = rebuilt(sig, rid, p, xs);
    let maj = crate::dom_code::cval(sh.ind, p as nat, crate::dom_code::smash(sig, sh.ind), xf);
    let dcan = crate::dom_code::canon_code(sig, sh.ind, us, pv);
    cf_val_typed(sig, rid, p, clv, dps, pv, xf, ak);
    crate::ti_ls2::levs_eq_sym(us, clv);
    crate::dom_code::canon_lveq(sig, sh.ind, clv, us, pv);
    let tds = crate::dom_rec_ty::rtds(sig, rid, lv);
    major_form(sig, rid, lv);
    let dsx = ds.subrange(0, pre).push(dcan);
    let envm = crate::dom_tele::exts(bot_env(), xs.subrange(0, pre));
    assert forall|j: nat| #[trigger] wf(envm(j)) by {
        crate::dom_rec_ty::exts_at(bot_env(), xs.subrange(0, pre), j);
    }
    assert forall|q: int| 0 <= q < np implies #[trigger] le(pv[q], envm((1 + nmin + np - 1 - q) as nat)) by {
        crate::dom_rec_ty::exts_at(bot_env(), xs.subrange(0, pre), (1 + nmin + np - 1 - q) as nat);
        assert(xs.subrange(0, pre)[q] == pv[q]);
        assert(wf(envm((1 + nmin + np - 1 - q) as nat)));
        le_refl(pv[q]);
    }
    ind_pv_mem(sig, rid, us, (1 + nmin) as nat, envm, dps, pv);
    assert forall|i: int| 0 <= i < tds.len() implies #[trigger] crate::dom_sound::dfit(sig, tds[i],
        crate::dom_tele::exts(bot_env(), x.subrange(0, i)), dsx[i], x[i]) by {
        assert(x.subrange(0, i) =~= xs.subrange(0, i));
        if i < pre {
            assert(crate::dom_sound::dfit(sig, tl[i], crate::dom_tele::exts(bot_env(), xs.subrange(0, i)), ds[i], xs[i]));
            assert(tl[i] == tds[i] && dsx[i] == ds[i] && x[i] == xs[i]);
        } else {
            assert(x[i] == maj && dsx[i] == dcan);
        }
    }
}

/// arity.
#[verifier::spinoff_prover]
pub proof fn iota_core_r2l(ss: Sig, sig: Sig, rid: u64, lv: Seq<LevelSpec>, l: LevelSpec, p: int, clv: Seq<LevelSpec>,
    g: crate::ti_syntax::Ctx, tb: ExprSpec, a0: Seq<ExprSpec>, cargs: Seq<ExprSpec>, rho: Env, r: Cpt)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        ss == crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, rid)),
        rec_wired(sig),
        crate::dom_rec_end::rec_hyps(sig, rid),
        r2l_ok(sig, rid, lv, p, clv),
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(sig, rid, lv),
            crate::ti_syntax::dty_at(sig, rid, lv), crate::ti_syntax::sort(l))),
        crate::expr_model::nlbv(sig.ienv.recs[rid].rules[p].rhs) == 0,
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(g,
            crate::expr_model::subst_expr_levels(sig.ienv.recs[rid].rules[p].rhs, sig.ienv.recs[rid].uparams, lv),
            crate::expr_model::subst_expr_levels(sig.ienv.recs[rid].rules[p].rhs, sig.ienv.recs[rid].uparams, lv), tb)),
        forall|i: nat| #[trigger] wf(rho(i)),
        a0.len() == crate::dom_rec_ty::rshape(sig, rid).np + 2 + crate::dom_rec_ty::rshape(sig, rid).nmin(),
        a0.last() == spine_app(ExprSpec::Const(crate::dom_rec_ty::rshape(sig, rid).ctors[p], clv), cargs),
        cargs.len() == crate::dom_rec_ty::rshape(sig, rid).np + crate::dom_rec_ty::rshape(sig, rid).fields[p].len(),
        forall|q: int| 0 <= q < crate::dom_rec_ty::rshape(sig, rid).np ==> #[trigger] crate::dom_sound::sem_eq(sig, a0[q], cargs[q], rho),
        mem(sig, spine_app(spine_app(crate::expr_model::subst_expr_levels(sig.ienv.recs[rid].rules[p].rhs, sig.ienv.recs[rid].uparams, lv),
            a0.subrange(0, (crate::dom_rec_ty::rshape(sig, rid).np + 1 + crate::dom_rec_ty::rshape(sig, rid).nmin()) as int)),
            cargs.subrange(crate::dom_rec_ty::rshape(sig, rid).np as int, cargs.len() as int)), rho, r),
    ensures
        mem(sig, spine_app(ExprSpec::Const(rid, lv), a0), rho, r),
{
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + 1 + nmin) as int;
    let nf = sh.fields[p].len();
    let body = crate::expr_model::subst_expr_levels(rd.rules[p].rhs, rd.uparams, lv);
    let heads = a0.subrange(0, pre);
    let fargs = cargs.subrange(np as int, cargs.len() as int);
    spine_concat(body, heads, fargs);
    let (hb, wl) = crate::dom_bound::spine_mem(sig, body, heads + fargs, rho, r);
    crate::dom_rec_shape::nlbv_sl(rd.rules[p].rhs, rd.uparams, lv);
    crate::dom_model::mem_closed_env(sig, body, rho, hb);
    rule_split(sig, rid, lv, p);
    let tl = crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0, pre) + ftds(sig, rid, lv, p);
    bot_fits(sig, g);
    assert forall|i: int| 0 <= i < wl.len() implies #[trigger] wf(wl[i]) by {
        assert(mem(sig, (heads + fargs)[i], rho, wl[i]));
    }
    // the rule's lambda, walked
    let (xs, ds, y) = crate::dom_tele::lam_apps(ss, sig, g, tl, rule_body(sig, rid, lv, p), tb, bot_env(), hb, wl);
    body_bound(ss, sig, rid, lv, l, p, xs, y);
    let x = rebuilt(sig, rid, p, xs);
    rebuilt_facts(sig, rid, p, xs);
    // the major
    let xf = xs.subrange(pre, xs.len() as int);
    let ak = ds.subrange(pre, ds.len() as int);
    r2l_fields(ss, sig, rid, lv, p, clv, ds, xs);
    let (dps, pv) = (ds.subrange(0, np as int), xs.subrange(0, np as int));
    // the constructor's own parameters have the recursor's parameters' values
    assert forall|q: int| 0 <= q < np implies mem(sig, #[trigger] cargs[q], rho, pv[q]) by {
        assert(mem(sig, (heads + fargs)[q], rho, wl[q]));
        assert((heads + fargs)[q] == a0[q]);
        assert(crate::dom_sound::sem_eq(sig, a0[q], cargs[q], rho));
        assert(mem(sig, cargs[q], rho, wl[q]));
        assert(pv[q] == xs[q]);
        mem_down_e(sig, cargs[q], rho, wl[q], xs[q]);
    }
    let wf2 = wl.subrange(pre, wl.len() as int);
    assert forall|k: int| 0 <= k < xf.len() implies mem(sig, cargs[np + k], rho, #[trigger] wf2[k]) && le(xf[k], wf2[k]) by {
        assert(mem(sig, (heads + fargs)[pre + k], rho, wl[pre + k]));
        assert((heads + fargs)[pre + k] == cargs[np + k]);
        assert(wf2[k] == wl[pre + k] && xf[k] == xs[pre + k]);
    }
    r2l_major(sig, rid, lv, p, clv, dps, pv, xf, ak, cargs, rho, wf2);
    let maj = crate::dom_code::cval(sh.ind, p as nat, crate::dom_code::smash(sig, sh.ind), xf);
    // the recursor's step at the rebuilt inputs
    let dcan = crate::dom_code::canon_code(sig, sh.ind, crate::dom_rec_ty::rinst(sig, rid, lv), pv);
    let tds = crate::dom_rec_ty::rtds(sig, rid, lv);
    let dsx = ds.subrange(0, pre).push(dcan);
    r2l_fit(ss, sig, rid, lv, p, clv, ds, xs);
    let (ar, sr) = crate::dom_rec_ty::rec_step(ss, sig, rid, lv, l, bot_env(), dsx, x);
    typed_wf(sr, ar);
    le_refl(sr);
    assert(rsem(sig, rid, lv, sr, ar, sr));
    assert(mem(sig, ExprSpec::Const(rid, lv), rho, sr));
    // the recursor's arguments
    assert forall|i: int| 0 <= i < a0.len() implies #[trigger] mem(sig, a0[i], rho, x[i]) && wf(x[i]) by {
        if i < pre {
            assert(mem(sig, (heads + fargs)[i], rho, wl[i]));
            assert((heads + fargs)[i] == a0[i] && x[i] == xs[i]);
            mem_down_e(sig, a0[i], rho, wl[i], xs[i]);
        } else {
            assert(x[i] == maj && a0[i] == a0.last());
        }
    }
    let rv = crate::dom_rec::recval(sig, rid, x);
    crate::dom_rec::recval_wf(sig, rid, x);
    crate::dom_bound::spine_mem_intro(sig, ExprSpec::Const(rid, lv), a0, rho, sr, x, rv);
    le_trans(r, crate::dom_rec::apps(hb, wl), y);
    le_trans(r, y, rv);
    mem_down_e(sig, spine_app(ExprSpec::Const(rid, lv), a0), rho, rv, r);
}

pub open spec fn ispvar_s(sig: Sig, sh: crate::rec_canon::IndShape, p: int, k: int) -> bool {
    crate::rec_canon::pvar_field(sh.pdoms, sh.np, k as nat, sh.fields[p][k])
}

pub open spec fn pvq_s(sig: Sig, sh: crate::rec_canon::IndShape, p: int, k: int) -> int {
    (k + sh.np - 1 - sh.fields[p][k]->Var_0) as int
}

pub open spec fn pdoms_at_s(sig: Sig, sh: crate::rec_canon::IndShape, cl: Seq<LevelSpec>) -> Seq<ExprSpec> {
    crate::dom_rec_shape::sls(sh.pdoms, sh.lps, cl)
}

pub open spec fn cf_fields_ok_s(sig: Sig, sh: crate::rec_canon::IndShape, p: int, cl: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>, xf: Seq<Cpt>, ak: Seq<Cpt>) -> bool {
    &&& 0 <= p < sh.nmin()
    &&& cl.len() == sig.consts[sh.ind].lps.len()
    &&& crate::dom_model::sem_const(sig, sh.ind, cl)
    &&& crate::dom_code::prop_ok(sig, sh.ind) && crate::dom_code::fields_blind(sig, sh.ind) && crate::dom_levels::sig_lps(sig)
    &&& crate::dom_code::fields_typed(sig, sh.ind)
    &&& crate::dom_tele::chain_ok(sig, pdoms_at_s(sig, sh, cl), bot_env(), dps, pv)
    &&& xf.len() == sh.fields[p].len()
    &&& ak.len() == xf.len()
    &&& crate::dom_code::aw(xf)
    &&& forall|k: int| 0 <= k < xf.len() && !isrec_s(sh, p, k) && !ispvar_s(sig, sh, p, k)
        && crate::rec_canon::simple_ty(sig, sh.ind, sh.fields[p][k]) ==>
        mem(sig, crate::iota_sr::cfu_s(sh, p, k, cl), bot_env(), #[trigger] ak[k]) && typed(ak[k], Cpt::U) && typed(xf[k], ak[k])
        && crate::dom_canon::ranked(sig, sh.fields[p][k], crate::dom_code::rk(sig, sh.ind))
    &&& forall|k: int| 0 <= k < xf.len() && !isrec_s(sh, p, k) && !ispvar_s(sig, sh, p, k)
        && !crate::rec_canon::simple_ty(sig, sh.ind, sh.fields[p][k]) ==>
        mem(sig, crate::iota_sr::cfu_s(sh, p, k, cl), crate::dom_tele::exts(bot_env(), pv + xf.subrange(0, k)), #[trigger] ak[k])
        && typed(ak[k], Cpt::U) && typed(xf[k], ak[k])
    &&& forall|k: int| 0 <= k < xf.len() && ispvar_s(sig, sh, p, k) ==>
        wf(#[trigger] ak[k]) && le(ak[k], pv[pvq_s(sig, sh, p, k)]) && typed(ak[k], Cpt::U) && typed(xf[k], ak[k])
    &&& forall|k: int| 0 <= k < xf.len() && isrec_s(sh, p, k) ==>
        typed(#[trigger] xf[k], crate::dom_code::canon_code(sig, sh.ind, cl, pv))
}

pub open spec fn cf_ds_s(sig: Sig, sh: crate::rec_canon::IndShape, p: int, cl: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>, ak: Seq<Cpt>) -> Seq<Cpt> {
    let dcan = crate::dom_code::canon_code(sig, sh.ind, cl, pv);
    dps + Seq::new(ak.len(), |k: int| if isrec_s(sh, p, k) { dcan } else { ak[k] })
}



pub proof fn pdoms_at_facts_s(sig: Sig, sh: crate::rec_canon::IndShape, p: int, cl: Seq<LevelSpec>)
    requires
        crate::dom_rec_ty::ind_scope(sig, sh),
        0 <= p < sh.nmin(),
        cl.len() == sig.consts[sh.ind].lps.len(),
    ensures ({
        let tds = ctds_s(sig, sh, p, cl);
        &&& pdoms_at_s(sig, sh, cl).len() == sh.np
        &&& sh.lps == sig.consts[sh.ind].lps
        &&& crate::ti_syntax::dty_at(sig, sh.ctors[p], cl) == crate::iota_sr::ctel_s(sig, sh, p, cl)
        &&& cbody_s(sig, sh, p, cl) == spine_app(ExprSpec::Const(sh.ind, cl), crate::rec_canon::vars(sh.fields[p].len(), sh.np))
        &&& !(cbody_s(sig, sh, p, cl) is Bind)
        &&& tds.len() == sh.np + sh.fields[p].len()
        &&& forall|q: int| 0 <= q < sh.np ==> #[trigger] tds[q] == pdoms_at_s(sig, sh, cl)[q]
        &&& forall|k: int| 0 <= k < sh.fields[p].len() ==> #[trigger] tds[sh.np + k] == crate::iota_sr::cfu_s(sh, p, k, cl)
    }),
{
    reveal(crate::dom_code::ind_side);
    crate::dom_rec_ty::scope_ctor_s(sig, sh, p);
    crate::dom_ctor_bound::ctor_shape(sig, sh.ind, p);
    crate::iota_sr::ctor_at_s(sig, sh, p, cl);
    ctor_ty_split_s(sig, sh, p, cl);
    let tds = ctds_s(sig, sh, p, cl);
    assert forall|q: int| 0 <= q < sh.np implies #[trigger] tds[q] == pdoms_at_s(sig, sh, cl)[q] by {
        assert(tds[q] == crate::dom_rel::ptype(sig, sh.ind, cl, q));
    }
}

#[verifier::spinoff_prover]
pub proof fn cf_chain_s(sig: Sig, sh: crate::rec_canon::IndShape, p: int, cl: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>, xf: Seq<Cpt>, ak: Seq<Cpt>)
    requires
        crate::dom_rec_ty::ind_scope(sig, sh),
        cf_fields_ok_s(sig, sh, p, cl, dps, pv, xf, ak),
    ensures ({
        let xsc = pv + xf;
        &&& crate::dom_tele::chain_ok(sig, ctds_s(sig, sh, p, cl), bot_env(), cf_ds_s(sig, sh, p, cl, dps, pv, ak), xsc)
        &&& mem(sig, cbody_s(sig, sh, p, cl), crate::dom_tele::exts(bot_env(), xsc),
                crate::dom_code::canon_code(sig, sh.ind, cl, pv))
    }),
{
    let (ind, np) = (sh.ind, sh.np);
    let nf = xf.len();
    pdoms_at_facts_s(sig, sh, p, cl);
    let tds = ctds_s(sig, sh, p, cl);
    let dsc = cf_ds_s(sig, sh, p, cl, dps, pv, ak);
    let xsc = pv + xf;
    crate::dom_rec_ty::scope_ctor_s(sig, sh, p);
    assert(pv.len() == np && dps.len() == np);
    assert forall|i: int| 0 <= i < tds.len() implies #[trigger] crate::dom_sound::dfit(sig, tds[i],
        crate::dom_tele::exts(bot_env(), xsc.subrange(0, i)), dsc[i], xsc[i]) by {
        let env = crate::dom_tele::exts(bot_env(), xsc.subrange(0, i));
        if i < np {
            assert(xsc.subrange(0, i) =~= pv.subrange(0, i));
            assert(dsc[i] == dps[i] && xsc[i] == pv[i] && tds[i] == pdoms_at_s(sig, sh, cl)[i]);
            assert(crate::dom_sound::dfit(sig, pdoms_at_s(sig, sh, cl)[i], crate::dom_tele::exts(bot_env(), pv.subrange(0, i)), dps[i], pv[i]));
        } else {
            let k = i - np;
            let fu = crate::iota_sr::cfu_s(sh, p, k, cl);
            assert(tds[np + k] == fu);
            assert(xsc[i] == xf[k]);
            assert forall|j: nat| #[trigger] wf(env(j)) by {
                crate::dom_rec_ty::exts_at(bot_env(), xsc.subrange(0, i), j);
                ind_pv_mem_wf_s(sig, sh, cl, dps, pv, xf, j);
            }
            crate::dom_canon::canon_fields(sig, ind, p, k);
            if isrec_s(sh, p, k) {
                crate::iota_sr::cfu_direct_s(sig, sh, p, k, cl);
                assert forall|q: int| 0 <= q < np implies #[trigger] le(pv[q], env((k + np - 1 - q) as nat)) by {
                    crate::dom_rec_ty::exts_at(bot_env(), xsc.subrange(0, i), (k + np - 1 - q) as nat);
                    assert(xsc[q] == pv[q]);
                    le_refl(pv[q]);
                }
                ind_pv_mem_s(sig, sh, cl, k as nat, env, dps, pv);
            } else if ispvar_s(sig, sh, p, k) {
                let v = sh.fields[p][k]->Var_0;
                let q = pvq_s(sig, sh, p, k);
                assert(fu == sh.fields[p][k]);
                crate::dom_rec_ty::exts_at(bot_env(), xsc.subrange(0, i), v);
                assert(xsc[q] == pv[q]);
                crate::dom_adeq_base::mem_var(sig, v, env, ak[k]);
            } else if !crate::rec_canon::simple_ty(sig, ind, sh.fields[p][k]) {
                assert(xsc.subrange(0, i) =~= pv + xf.subrange(0, k));
            } else {
                simple_closed(sig, ind, sh.fields[p][k]);
                crate::ti_level::ls_nlbv(sh.fields[p][k], sh.lps, cl);
                crate::dom_model::mem_closed_env(sig, fu, env, ak[k]);
                crate::dom_model::mem_closed_env(sig, fu, bot_env(), ak[k]);
            }
        }
    }
    let envf = crate::dom_tele::exts(bot_env(), xsc);
    assert forall|j: nat| #[trigger] wf(envf(j)) by {
        crate::dom_rec_ty::exts_at(bot_env(), xsc, j);
        ind_pv_mem_wf_s(sig, sh, cl, dps, pv, xf, j);
    }
    assert forall|q: int| 0 <= q < np implies #[trigger] le(pv[q], envf((nf + np - 1 - q) as nat)) by {
        crate::dom_rec_ty::exts_at(bot_env(), xsc, (nf + np - 1 - q) as nat);
        assert(xsc[q] == pv[q]);
        le_refl(pv[q]);
    }
    ind_pv_mem_s(sig, sh, cl, nf as nat, envf, dps, pv);
}

proof fn ind_pv_mem_wf_s(sig: Sig, sh: crate::rec_canon::IndShape, cl: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>, xf: Seq<Cpt>, j: nat)
    requires
        crate::dom_tele::chain_ok(sig, pdoms_at_s(sig, sh, cl), bot_env(), dps, pv),
        crate::dom_code::aw(xf),
    ensures
        forall|i: int| 0 <= i < (pv + xf).len() ==> #[trigger] wf((pv + xf)[i]),
{
    assert forall|i: int| 0 <= i < (pv + xf).len() implies #[trigger] wf((pv + xf)[i]) by {
        if i < pv.len() {
            assert(crate::dom_sound::dfit(sig, pdoms_at_s(sig, sh, cl)[i],
                crate::dom_tele::exts(bot_env(), pv.subrange(0, i)), dps[i], pv[i]));
            typed_wf(pv[i], dps[i]);
        }
    }
}

#[verifier::spinoff_prover]
proof fn cf_ps_typed_s(sig: Sig, sh: crate::rec_canon::IndShape, p: int, cl: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>, xf: Seq<Cpt>, ak: Seq<Cpt>, k: int)
    requires
        crate::ti_syntax::iota_ok(sig),
        crate::dom_rec_ty::ind_scope(sig, sh),
        cf_fields_ok_s(sig, sh, p, cl, dps, pv, xf, ak),
        0 <= k < xf.len(),
        !isrec_s(sh, p, k),
        !ispvar_s(sig, sh, p, k),
        !crate::rec_canon::simple_ty(sig, sh.ind, sh.fields[p][k]),
    ensures ({
        let pe = crate::dom_code::fpe(pv, sh.np, k as nat);
        let cv = crate::dom_code::ceval(sig, crate::dom_code::rk(sig, sh.ind), sh.ind, Seq::empty(), pe, sh.fields[p][k]);
        typed(xf[k], cv)
    }),
{
    let (ind, np) = (sh.ind, sh.np);
    let e = sh.fields[p][k];
    let pe = crate::dom_code::fpe(pv, np, k as nat);
    let cv = crate::dom_code::ceval(sig, crate::dom_code::rk(sig, ind), ind, Seq::empty(), pe, e);
    crate::dom_rec_ty::scope_ctor_s(sig, sh, p);
    crate::dom_lift::pfield_facts(sig, ind, p, k);
    // the field at the instance: over the parameters, blind, ranked alike
    let fu = crate::iota_sr::cfu_s(sh, p, k, cl);
    crate::iota_sr::ps_field_at_s(sig, sh, p, k, cl);
    crate::dom_canon::sl_kinds(sig, ind, sh.pdoms, np, k as nat, e, crate::dom_code::rk(sig, ind), sh.lps, cl);
    crate::dom_code::blind_sl(sig, e, sh.lps, cl);
    assert forall|i: int| 0 <= i < pv.len() implies #[trigger] wf(pv[i]) && typed(pv[i], Cpt::U) by {
        let pd = pdoms_at_s(sig, sh, cl)[i];
        assert(crate::dom_sound::dfit(sig, pd, crate::dom_tele::exts(bot_env(), pv.subrange(0, i)), dps[i], pv[i]));
        typed_wf(pv[i], dps[i]);
        let l0 = sh.pdoms[i]->Sort_0;
        assert(sh.pdoms[i] == ExprSpec::Sort(l0));
        assert(pd == ExprSpec::Sort(crate::level_model::subst_level_spec(l0, sh.lps, cl)));
        crate::dom_canon::sort_mem_typed(sig, crate::level_model::subst_level_spec(l0, sh.lps, cl),
            crate::dom_tele::exts(bot_env(), pv.subrange(0, i)), dps[i], pv[i]);
    }
    let env = crate::dom_tele::exts(bot_env(), pv + xf.subrange(0, k));
    assert forall|i: nat| #[trigger] wf(env(i)) by {
        crate::dom_rec_ty::exts_at(bot_env(), pv + xf.subrange(0, k), i);
    }
    assert forall|q: int| 0 <= q < np implies le(env((k as nat + np - 1 - q) as nat), #[trigger] pe[q]) by {
        crate::dom_rec_ty::exts_at(bot_env(), pv + xf.subrange(0, k), (k as nat + np - 1 - q) as nat);
        assert((pv + xf.subrange(0, k))[q] == pv[q]);
        assert(pe[q] == pv[q]);
        le_refl(pv[q]);
    }
    crate::dom_code::fpe_aw(pv, np, k as nat);
    crate::dom_canon::ps_bound(sig, ind, sh.pdoms, np, k as nat, Seq::empty(), pe, fu, env, ak[k]);
    crate::dom_code::ceval_sl(sig, crate::dom_code::rk(sig, ind), ind, Seq::empty(), pe, e, sh.lps, cl);
    crate::dom_sound::typed_basic();
    assert forall|q: int| 0 <= q < np && sh.pdoms[q] is Sort implies typed(#[trigger] pe[q], Cpt::U) by {
        assert(pe[q] == pv[q]);
        assert(0 <= q < pv.len());
        assert(wf(pv[q]));
        assert(wf(pv[q]) && typed(pv[q], Cpt::U));
    }
    crate::dom_canon::ps_ceval_typed(sig, crate::dom_code::rk(sig, ind), ind, Seq::empty(), sh.pdoms, np, k as nat, pe, e);
    typed_weak(xf[k], ak[k], cv);
}

/// AT A PROP STRUCTURE every field value is bottom: each field is a proof
/// (`rec_canon::pprop`), typed at its code, which is a proposition.
#[verifier::spinoff_prover]
pub proof fn cf_prop_bot_s(sig: Sig, sh: crate::rec_canon::IndShape, p: int, cl: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>, xf: Seq<Cpt>, ak: Seq<Cpt>)
    requires
        crate::ti_syntax::iota_ok(sig),
        crate::dom_rec_ty::ind_scope(sig, sh),
        cf_fields_ok_s(sig, sh, p, cl, dps, pv, xf, ak),
        !crate::dom_code::never_prop(sig, sh.ind),
    ensures
        crate::dom_code::smash(sig, sh.ind),
        forall|k: int| 0 <= k < xf.len() ==> (#[trigger] xf[k]) is Bot,
{
    let (ind, np) = (sh.ind, sh.np);
    let r = crate::dom_code::rk(sig, ind);
    reveal(crate::dom_code::prop_ok);
    assert(crate::dom_code::canon_shape(sig, ind) == sh);
    assert(crate::dom_code::smash(sig, ind) && crate::rec_canon::shape_props(sh));
    crate::dom_ctor_bound::ctor_shape(sig, ind, p);
    assert(sh.pdoms.len() == np && pv.len() == np);
    assert forall|i: int| 0 <= i < pv.len() implies #[trigger] wf(pv[i]) by {
        assert(crate::dom_sound::dfit(sig, pdoms_at_s(sig, sh, cl)[i], crate::dom_tele::exts(bot_env(), pv.subrange(0, i)), dps[i], pv[i]));
        typed_wf(pv[i], dps[i]);
    }
    reveal(crate::rec_canon::shape_props);
    crate::dom_sound::typed_basic();
    // the parameters' values: types, propositions at sort zero
    assert forall|q: int| 0 <= q < np && sh.pdoms[q] is Sort implies typed(#[trigger] pv[q], Cpt::U)
        && (crate::ti_syntax::is_zero(sh.pdoms[q]->Sort_0) ==> typed(pv[q], Cpt::Prop)) by {
        let l0 = sh.pdoms[q]->Sort_0;
        let pd = pdoms_at_s(sig, sh, cl)[q];
        assert(crate::dom_sound::dfit(sig, pd, crate::dom_tele::exts(bot_env(), pv.subrange(0, q)), dps[q], pv[q]));
        let l1 = crate::level_model::subst_level_spec(l0, sh.lps, cl);
        assert(pd == ExprSpec::Sort(l1));
        crate::dom_canon::sort_mem_typed(sig, l1, crate::dom_tele::exts(bot_env(), pv.subrange(0, q)), dps[q], pv[q]);
        if crate::ti_syntax::is_zero(l0) {
            assert(crate::rec_canon::stable_lvl(l0)) by { reveal(crate::rec_canon::stable_lvl); }
            crate::dom_code::scode_sl(l0, sh.lps, cl);
            crate::dom_canon::prop_param_typed(sig, l1, crate::dom_tele::exts(bot_env(), pv.subrange(0, q)), dps[q], pv[q]);
        }
    }
    assert forall|k: int| 0 <= k < xf.len() implies (#[trigger] xf[k]) is Bot by {
        let e = sh.fields[p][k];
        let pe = crate::dom_code::fpe(pv, np, k as nat);
        let cv = crate::dom_code::ceval(sig, r, ind, cl, pe, e);
        assert(crate::rec_canon::pprop(sh.pdoms, np, k as nat, e));
        crate::dom_canon::pprop_not_head(sig, ind, sh.pdoms, sh.us(), np, sh.ni, k as nat, e);
        crate::dom_canon::canon_fields(sig, ind, p, k);
        crate::dom_code::fpe_aw(pv, np, k as nat);
        assert forall|q: int| 0 <= q < np && sh.pdoms[q] is Sort implies typed(#[trigger] pe[q], Cpt::U) by {
            assert(pe[q] == pv[q]);
        }
        assert forall|q: int| 0 <= q < np && sh.pdoms[q] is Sort && crate::ti_syntax::is_zero(sh.pdoms[q]->Sort_0)
            implies typed(#[trigger] pe[q], Cpt::Prop) by {
            assert(pe[q] == pv[q]);
        }
        crate::dom_canon::pprop_code(sig, r, ind, cl, sh.pdoms, np, k as nat, pe, e);
        crate::dom_canon::ps_ceval_typed(sig, r, ind, cl, sh.pdoms, np, k as nat, pe, e);
        if ispvar_s(sig, sh, p, k) {
            let q = pvq_s(sig, sh, p, k);
            crate::dom_lift::cf_var(sig, ind, pv, p, k);
            crate::dom_code::ceval_blind(sig, r, ind, Seq::empty(), cl, pe, e);
            assert(cv == pv[q]);
            typed_weak(xf[k], ak[k], cv);
        } else {
            cf_ps_typed_s(sig, sh, p, cl, dps, pv, xf, ak, k);
            crate::dom_code::ceval_blind(sig, r, ind, Seq::empty(), cl, pe, e);
        }
        crate::dom_canon::typed_prop_bot(xf[k], cv);
    }
}

#[verifier::spinoff_prover]
pub proof fn cf_val_typed_s(sig: Sig, sh: crate::rec_canon::IndShape, p: int, cl: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>, xf: Seq<Cpt>, ak: Seq<Cpt>)
    requires
        crate::ti_syntax::iota_ok(sig),
        crate::dom_rec_ty::ind_scope(sig, sh),
        cf_fields_ok_s(sig, sh, p, cl, dps, pv, xf, ak),
    ensures ({
        typed(crate::dom_code::cval(sh.ind, p as nat, crate::dom_code::smash(sig, sh.ind), xf), crate::dom_code::canon_code(sig, sh.ind, cl, pv))
    }),
{
    let (ind, np) = (sh.ind, sh.np);
    let nf = xf.len();
    let r = crate::dom_code::rk(sig, ind);
    let l = ind_ty_plain_s(sig, sh, cl);
    assert forall|i: int| 0 <= i < pv.len() implies #[trigger] wf(pv[i]) by {
        assert(crate::dom_sound::dfit(sig, pdoms_at_s(sig, sh, cl)[i], crate::dom_tele::exts(bot_env(), pv.subrange(0, i)), dps[i], pv[i]));
        typed_wf(pv[i], dps[i]);
    }
    crate::dom_canon::chain_sparams(sig, ind, cl, pdoms_at_s(sig, sh, cl), l, dps, pv);
    crate::dom_canon::canon_typed(sig, ind, cl, pv);
    let dcan = crate::dom_code::canon_code(sig, ind, cl, pv);
    typed_wf(dcan, Cpt::U);
    let sm = crate::dom_code::smash(sig, ind);
    let val = crate::dom_code::cval(ind, p as nat, sm, xf);
    if !crate::dom_code::never_prop(sig, ind) {
        cf_prop_bot_s(sig, sh, p, cl, dps, pv, xf, ak);
    }
    if val is Bot {
        let n0 = cstage(dcan, Cpt::U);
        typed_up(dcan, Cpt::U, n0);
        assert(has_type(n0, val, dcan));
        typed_down(val, dcan, n0);
        return;
    }
    assert(val == Cpt::Nd(NdKey::Con(ind, p as nat, sm), xf));
    crate::dom_code::wf_nd(NdKey::Con(ind, p as nat, sm), xf);
    parts_lower(val);
    let n = cstage(val, dcan) + cstage(dcan, Cpt::U) + 2;
    typed_up(dcan, Cpt::U, n);
    let blocks = crate::dom_code::cblocks(sig, ind, cl, pv, sh.nmin());
    crate::dom_rec_ty::scope_ctor_s(sig, sh, p);
    crate::dom_code::cblocks_at(sig, ind, cl, pv, sh.nmin());
    crate::dom_code::centries_at(sig, ind, cl, pv, p as nat, nf);
    let ts = dcan->Nd_1;
    assert(ts.last() == Cpt::Nd(NdKey::Tag(2), blocks));
    let es = crate::dom_typing::tbl(ts)[p]->Nd_1;
    assert forall|k: int| 0 <= k < nf implies (#[trigger] xf[k]) is Bot
        || (es[k] == crate::dom_typing::rmark() && has_type(n, xf[k], dcan))
        || (crate::dom_typing::is_centry(es[k]) && has_type(n, xf[k], crate::dom_typing::ecode(es[k]))) by {
        assert(es[k] == crate::dom_code::centry_at(sig, ind, cl, pv, p as nat, k as nat));
        assert(ht(xf[k]) < ht(val));
        crate::dom_canon::canon_fields(sig, ind, p, k);
        if isrec_s(sh, p, k) {
            typed_up(xf[k], dcan, n);
        } else {
            let e = sh.fields[p][k];
            let pe = crate::dom_code::fpe(pv, np, k as nat);
            let cv = crate::dom_code::ceval(sig, r, ind, cl, pe, e);
            assert(crate::dom_typing::ecode(es[k]) == cv);
            crate::dom_code::fpe_aw(pv, np, k as nat);
            crate::dom_code::ceval_wf(sig, r, ind, cl, pe, e);
            crate::dom_typing::tbl_lower(dcan);
            if ispvar_s(sig, sh, p, k) {
                // a parameter-typed field: below its parameter's value
                let q = pvq_s(sig, sh, p, k);
                crate::dom_lift::cf_var(sig, ind, pv, p, k);
                crate::dom_code::ceval_blind(sig, r, ind, Seq::empty(), cl, pe, e);
                assert(cv == pv[q]);
                assert(typed(pv[q], Cpt::U));
                typed_weak(xf[k], ak[k], cv);
            } else if !crate::rec_canon::simple_ty(sig, ind, e) {
                // a type over the parameters: below its code at their values
                cf_ps_typed_s(sig, sh, p, cl, dps, pv, xf, ak, k);
                crate::dom_code::ceval_blind(sig, r, ind, Seq::empty(), cl, pe, e);
            } else {
                let fu = crate::iota_sr::cfu_s(sh, p, k, cl);
                crate::dom_lift::field_facts(sig, ind, p, k);
                crate::dom_canon::sl_kinds(sig, ind, sh.pdoms, np, k as nat, e, r, sh.lps, cl);
                crate::dom_code::blind_sl(sig, e, sh.lps, cl);
                crate::dom_canon::closed_bound(sig, ind, cl, pe, fu, bot_env(), ak[k]);
                crate::dom_code::ceval_sl(sig, r, ind, cl, pe, e, sh.lps, cl);
                crate::dom_sound::typed_basic();
                crate::dom_canon::ceval_typed(sig, r, ind, cl, pe, e);
                typed_weak(xf[k], ak[k], cv);
            }
            typed_up(xf[k], cv, n);
        }
    }
    crate::dom_code::never_prop_not(sig, ind, cl);
    assert(has_type(n, val, dcan));
    typed_down(val, dcan, n);
}

#[verifier::spinoff_prover]
pub proof fn cf_step_s(sig: Sig, sh: crate::rec_canon::IndShape, p: int, clv: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>, xf: Seq<Cpt>, ak: Seq<Cpt>) -> (r: (Cpt, Cpt))
    requires
        crate::ti_syntax::iota_ok(sig),
        crate::dom_rec_ty::ind_scope(sig, sh),
        cf_fields_ok_s(sig, sh, p, clv, dps, pv, xf, ak),
    ensures ({
        let c = sh.ctors[p];
        &&& mem(sig, crate::ti_syntax::dty_at(sig, c, clv), bot_env(), r.0)
        &&& typed(r.0, Cpt::U)
        &&& typed(r.1, r.0)
        &&& cf_fun(sh.ind, p as nat, crate::dom_code::smash(sig, sh.ind), sh.np, crate::ti_syntax::dty_at(sig, c, clv), Seq::empty(), 0, r.1)
        &&& le(crate::dom_code::cval(sh.ind, p as nat, crate::dom_code::smash(sig, sh.ind), xf), crate::dom_rec::apps(r.1, pv + xf))
    }),
{
    let (ind, np) = (sh.ind, sh.np);
    let nf = xf.len();
    pdoms_at_facts_s(sig, sh, p, clv);
    ctor_ty_split_s(sig, sh, p, clv);
    let tds = ctds_s(sig, sh, p, clv);
    let cb = cbody_s(sig, sh, p, clv);
    let l = ind_ty_plain_s(sig, sh, clv);
    crate::dom_canon::chain_sparams(sig, ind, clv, pdoms_at_s(sig, sh, clv), l, dps, pv);
    ind_pv_mem_wf_s(sig, sh, clv, dps, pv, xf, 0);
    assert forall|i: int| 0 <= i < pv.len() implies #[trigger] wf(pv[i]) by {
        assert((pv + xf)[i] == pv[i]);
    }
    crate::dom_canon::canon_typed(sig, ind, clv, pv);
    let dcan = crate::dom_code::canon_code(sig, ind, clv, pv);
    let dsc = cf_ds_s(sig, sh, p, clv, dps, pv, ak);
    let xsc = pv + xf;
    cf_chain_s(sig, sh, p, clv, dps, pv, xf, ak);
    crate::dom_tele::pichain_mem(sig, tds, cb, bot_env(), dsc, xsc, dcan);
    let a = crate::dom_tele::pichain(dsc, xsc, dcan);
    let sm = crate::dom_code::smash(sig, ind);
    let val = crate::dom_code::cval(ind, p as nat, sm, xf);
    cf_val_typed_s(sig, sh, p, clv, dps, pv, xf, ak);
    assert forall|i: int| 0 <= i < dsc.len() implies #[trigger] typed(xsc[i], dsc[i]) by {
        assert(crate::dom_sound::dfit(sig, tds[i], crate::dom_tele::exts(bot_env(), xsc.subrange(0, i)), dsc[i], xsc[i]));
    }
    crate::dom_tele::lamchain_typed(dsc, xsc, dcan, val);
    let v = crate::dom_tele::lamchain(xsc, val);
    assert(cacc(Seq::empty(), xsc, 0, np) =~= xf);
    le_refl(val);
    assert(crate::dom_compact::le(val, Cpt::Nd(NdKey::Con(ind, p as nat, sm), xf)));
    crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, clv), crate::rec_canon::vars(nf, np));
    lamchain_cf(ind, p as nat, crate::dom_code::smash(sig, ind), np, tds, cb, Seq::empty(), 0, xsc, val);
    typed_wf(v, a);
    crate::dom_tele::lamchain_apps(xsc, val);
    (a, v)
}

pub proof fn ind_ty_plain_s(sig: Sig, sh: crate::rec_canon::IndShape, cl: Seq<LevelSpec>) -> (l: LevelSpec)
    requires
        crate::dom_rec_ty::ind_scope(sig, sh),
    ensures ({
        &&& crate::ti_syntax::dty_at(sig, sh.ind, cl) == crate::rec_canon::binds(BinderKind::Pi, pdoms_at_s(sig, sh, cl), ExprSpec::Sort(l))
        &&& sh.pdoms.len() == sh.np
    }),
{
    let ind = sh.ind;
    let ti = sig.consts[ind].ty;
    reveal(crate::dom_code::ind_side);
    crate::dom_ctor_bound::ctor_shape_ind(sig, ind);
    reveal(crate::dom_code::ind_side);
    assert(sh.idoms.len() == 0);
    assert(sh.pdoms + sh.idoms =~= sh.pdoms);
    let b = crate::rec_canon::tbody(ti, sh.np + sh.ni);
    assert(ti == crate::rec_canon::binds(BinderKind::Pi, sh.pdoms, b));
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms, b, sh.lps, cl);
    let l0 = b->Sort_0;
    assert(b == ExprSpec::Sort(l0));
    crate::level_model::subst_level_spec(l0, sh.lps, cl)
}

pub proof fn ind_pv_mem_s(sig: Sig, sh: crate::rec_canon::IndShape, cl: Seq<LevelSpec>, from: nat, env: Env, dps: Seq<Cpt>, pv: Seq<Cpt>)
    requires
        crate::dom_rec_ty::ind_scope(sig, sh),
        crate::dom_model::sem_const(sig, sh.ind, cl),
        crate::dom_tele::chain_ok(sig, pdoms_at_s(sig, sh, cl), bot_env(), dps, pv),
        forall|i: nat| #[trigger] wf(env(i)),
        forall|q: int| 0 <= q < sh.np
            ==> #[trigger] le(pv[q], env((from + sh.np - 1 - q) as nat)),
    ensures ({
        &&& mem(sig, spine_app(ExprSpec::Const(sh.ind, cl), crate::rec_canon::vars(from, sh.np)), env,
                crate::dom_code::canon_code(sig, sh.ind, cl, pv))
        &&& typed(crate::dom_code::canon_code(sig, sh.ind, cl, pv), Cpt::U)
        &&& crate::dom_code::aw(pv)
    }),
{
    let (ind, np) = (sh.ind, sh.np);
    let l = ind_ty_plain_s(sig, sh, cl);
    let pd = pdoms_at_s(sig, sh, cl);
    assert forall|i: int| 0 <= i < pv.len() implies #[trigger] wf(pv[i]) by {
        assert(crate::dom_sound::dfit(sig, pd[i], crate::dom_tele::exts(bot_env(), pv.subrange(0, i)), dps[i], pv[i]));
        typed_wf(pv[i], dps[i]);
    }
    let (ai, vi) = crate::dom_canon::tf_step(sig, ind, cl, pd, l, dps, pv);
    typed_wf(vi, ai);
    le_refl(vi);
    assert(crate::dom_sem::sem_mem(sig, ind, cl, vi, ai, vi));
    crate::dom_sem::mem_sem(sig, ind, cl, env, vi);
    let args = crate::rec_canon::vars(from, np);
    let ws = Seq::new(np, |q: int| env((from + np - 1 - q) as nat));
    assert forall|i: int| 0 <= i < args.len() implies #[trigger] mem(sig, args[i], env, ws[i]) && wf(ws[i]) by {
        var_mem(sig, (from + np - 1 - i) as nat, env);
    }
    assert forall|i: int| 0 <= i < pv.len() implies #[trigger] wf(pv[i]) && le(pv[i], ws[i]) by {}
    assert forall|i: int| 0 <= i < ws.len() implies #[trigger] wf(ws[i]) by {}
    crate::dom_rec::apps_mono(vi, vi, pv, ws);
    let c = crate::dom_code::canon_code(sig, ind, cl, pv);
    crate::dom_code::canon_wf(sig, ind, cl, pv);
    le_trans(c, crate::dom_rec::apps(vi, pv), crate::dom_rec::apps(vi, ws));
    crate::dom_bound::spine_mem_intro(sig, ExprSpec::Const(ind, cl), args, env, vi, ws, c);
    crate::dom_canon::chain_sparams(sig, ind, cl, pd, l, dps, pv);
    crate::dom_canon::canon_typed(sig, ind, cl, pv);
}

#[verifier::spinoff_prover]
pub proof fn typed_at_pv_s(sig: Sig, sh: crate::rec_canon::IndShape, cl: Seq<LevelSpec>, from: nat, env: Env, x: Cpt, d: Cpt, dps: Seq<Cpt>, pv: Seq<Cpt>)
    requires
        crate::dom_rec_ty::ind_scope(sig, sh),
        crate::dom_model::sem_const(sig, sh.ind, cl),
        crate::dom_tele::chain_ok(sig, pdoms_at_s(sig, sh, cl), bot_env(), dps, pv),
        forall|i: nat| #[trigger] wf(env(i)),
        forall|q: int| 0 <= q < sh.np
            ==> #[trigger] le(env((from + sh.np - 1 - q) as nat), pv[q]),
        mem(sig, spine_app(ExprSpec::Const(sh.ind, cl),
            crate::rec_canon::vars(from, sh.np)), env, d),
        typed(x, d),
    ensures ({
        typed(x, crate::dom_code::canon_code(sig, sh.ind, cl, pv))
    }),
{
    let (ind, np) = (sh.ind, sh.np);
    let l = ind_ty_plain_s(sig, sh, cl);
    let pd = pdoms_at_s(sig, sh, cl);
    assert forall|i: int| 0 <= i < pv.len() implies #[trigger] wf(pv[i]) by {
        assert(crate::dom_sound::dfit(sig, pd[i], crate::dom_tele::exts(bot_env(), pv.subrange(0, i)), dps[i], pv[i]));
        typed_wf(pv[i], dps[i]);
    }
    crate::dom_canon::chain_sparams(sig, ind, cl, pd, l, dps, pv);
    crate::dom_canon::canon_typed(sig, ind, cl, pv);
    let cb = crate::dom_code::canon_code(sig, ind, cl, pv);
    typed_wf(x, d);
    if d is Bot {
        let n = cstage(x, d);
        typed_up(x, d, n);
        ty_of_bot(n, x);
        crate::dom_tele::bot_typed(cb);
        return;
    }
    let args = crate::rec_canon::vars(from, np);
    crate::dom_rec_shape::tarity_binds(pd, ExprSpec::Sort(l));
    tbody_binds(pd, ExprSpec::Sort(l));
    let ws = crate::dom_bound::tf_spine(sig, ind, cl, args, env, d);
    assert forall|i: int| 0 <= i < ws.len() implies #[trigger] wf(ws[i]) && le(ws[i], pv[i]) by {
        crate::dom_bound::args_w_at(sig, args, env, ws, i);
        assert(args[i] == ExprSpec::Var((from + np - 1 - i) as nat));
        crate::dom_adeq_base::mem_var(sig, (from + np - 1 - i) as nat, env, ws[i]);
        le_trans(ws[i], env((from + np - 1 - i) as nat), pv[i]);
    }
    let cw = crate::dom_code::canon_code(sig, ind, cl, ws);
    crate::dom_code::canon_mono(sig, ind, cl, ws, pv);
    crate::dom_code::canon_wf(sig, ind, cl, pv);
    le_trans(d, cw, cb);
    typed_weak(x, d, cb);
}

#[verifier::spinoff_prover]
pub proof fn con_major_s(sig: Sig, sh: crate::rec_canon::IndShape, p: int, clv: Seq<LevelSpec>, dps: Seq<Cpt>, pv: Seq<Cpt>,
    xf: Seq<Cpt>, ak: Seq<Cpt>, cargs: Seq<ExprSpec>, rho: Env, wl: Seq<Cpt>)
    requires
        crate::dom_rec_ty::ind_scope(sig, sh),
        cf_fields_ok_s(sig, sh, p, clv, dps, pv, xf, ak),
        crate::dom_code::canon_sr(sig, sh.ind),
        crate::dom_model::sem_const(sig, sh.ctors[p], clv),
        cargs.len() == sh.np + xf.len(),
        wl.len() == xf.len(),
        forall|q: int| 0 <= q < sh.np ==> mem(sig, #[trigger] cargs[q], rho, pv[q]),
        forall|k: int| 0 <= k < xf.len() ==> mem(sig, cargs[sh.np + k], rho, #[trigger] wl[k])
            && le(xf[k], wl[k]),
    ensures ({
        mem(sig, spine_app(ExprSpec::Const(sh.ctors[p], clv), cargs), rho, crate::dom_code::cval(sh.ind, p as nat, crate::dom_code::smash(sig, sh.ind), xf))
    }),
{
    reveal(crate::dom_code::ind_side);
    let (ind, np) = (sh.ind, sh.np);
    let c = sh.ctors[p];
    let (ac, v) = cf_step_s(sig, sh, p, clv, dps, pv, xf, ak);
    typed_wf(v, ac);
    le_refl(v);
    crate::dom_rec_ty::scope_ctor_s(sig, sh, p);
    assert(crate::dom_model::code_ok(sig, c, clv, ac, v));
    assert(crate::dom_sem::sem_mem(sig, c, clv, v, ac, v));
    crate::dom_sem::mem_sem(sig, c, clv, rho, v);
    let ws = pv + xf;
    ind_pv_mem_wf_s(sig, sh, clv, dps, pv, xf, 0);
    assert forall|i: int| 0 <= i < cargs.len() implies #[trigger] mem(sig, cargs[i], rho, ws[i]) && wf(ws[i]) by {
        if i < np {
            assert(ws[i] == pv[i]);
        } else {
            let k = i - np;
            assert(ws[i] == xf[k]);
            assert(wl[k] == wl[k]);
            assert(mem(sig, cargs[np + k], rho, wl[k]) && le(xf[k], wl[k]));
            mem_down_e(sig, cargs[i], rho, wl[k], xf[k]);
        }
    }
    let val = crate::dom_code::cval(ind, p as nat, crate::dom_code::smash(sig, ind), xf);
    crate::dom_code::cval_wf(ind, p as nat, crate::dom_code::smash(sig, ind), xf);
    crate::dom_bound::spine_mem_intro(sig, ExprSpec::Const(c, clv), cargs, rho, v, ws, val);
}

} // verus!
