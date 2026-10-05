//! THE RECURSOR'S TYPING (step 3 of the S6.4c/d plan in
//! docs/TYPED_TARGET.md): minor premise `p`, typed at a member of its type,
//! applied to a value's fields and then to anything at the recursive
//! fields, is typed at a code below the motive's value applied to the
//! value. The minor's type ends in the motive at the constructor applied to
//! the parameters and fields; `tele_apps` types the application at a
//! member of that body, and `motive_bound` puts the member below the
//! motive at the value.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_model::*;
#[cfg(verus_only)]
use crate::dom_sound::fits_env;
#[cfg(verus_only)]
use crate::dom_tele::{exts, tele_apps};
#[cfg(verus_only)]
use crate::dom_bound::{motive_bound, flds, args_w};
#[cfg(verus_only)]
use crate::ti_syntax::{Sig, Ctx, derivable, eq, sort, dty_at, pi};
#[cfg(verus_only)]
use crate::dom_typing::{ty_of_bot, prop_is_type};
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::rec_canon::{binds, tarity, vars};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Looking a variable up in an extended environment.
pub proof fn exts_at(rho: Env, ws: Seq<Cpt>, i: nat)
    ensures
        exts(rho, ws)(i) == if i < ws.len() { ws[ws.len() - 1 - i] } else { rho((i - ws.len()) as nat) },
    decreases ws.len(),
{
    if ws.len() > 0 {
        let r = ws.drop_first();
        exts_at(ext(rho, ws[0]), r, i);
        if i >= r.len() {
            let j = (i - r.len()) as nat;
            if j == 0 {
                assert(i == ws.len() - 1);
            }
        } else {
            assert(r[r.len() - 1 - i] == ws[ws.len() - 1 - i]);
        }
    }
}

/// The body of a minor premise's type: the motive (at `Var(km)`) at the
/// constructor `c` applied to the parameters and the `nf` fields, under
/// `nr` hypotheses.
pub open spec fn minor_body(km: nat, c: u64, us: Seq<LevelSpec>, pvars: Seq<ExprSpec>, nf: nat, nr: nat) -> ExprSpec {
    ExprSpec::App(Box::new(ExprSpec::Var(km)),
        Box::new(spine_app(ExprSpec::Const(c, us), pvars + crate::rec_canon::vars(nr, nf))))
}

/// THE MINOR'S OUTPUT IS TYPED BELOW THE MOTIVE AT THE VALUE.
pub proof fn minor_out(ss: Sig, sig: Sig, g: Ctx, fds: Seq<ExprSpec>, ihs: Seq<ExprSpec>, km: nat, c: u64, us: Seq<LevelSpec>,
    pvars: Seq<ExprSpec>, l: LevelSpec, rho: Env, d: Cpt, xn: Cpt, fs: Seq<Cpt>, hs: Seq<Cpt>) -> (e: Cpt)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        derivable(ss, eq(g, binds(BinderKind::Pi, fds + ihs, minor_body(km, c, us, pvars, fds.len(), ihs.len())),
            binds(BinderKind::Pi, fds + ihs, minor_body(km, c, us, pvars, fds.len(), ihs.len())), sort(l))),
        fits_env(sig, g, rho),
        mem(sig, binds(BinderKind::Pi, fds + ihs, minor_body(km, c, us, pvars, fds.len(), ihs.len())), rho, d),
        typed(d, Cpt::U),
        typed(xn, d),
        fs.len() == fds.len(),
        hs.len() == ihs.len(),
        crate::dom_code::aw(fs),
        crate::dom_code::aw(hs),
        km >= fds.len() + ihs.len(),
        sig.consts.contains_key(c),
        sig.consts[c].val is None,
        sig.ienv.ctor_ind.contains_key(c),
        ctor_of(sig, sig.ienv.ctor_ind[c], c),
        pvars.len() == crate::dom_code::canon_shape(sig, sig.ienv.ctor_ind[c]).np,
        pvars.len() + fds.len() == tarity(dty_at(sig, c, us)),
    ensures
        typed(crate::dom_rec::apps(xn, fs + hs), e),
        typed(e, Cpt::U),
        le(e, app(rho((km - fds.len() - ihs.len()) as nat),
            Cpt::Nd(NdKey::Con(sig.ienv.ctor_ind[c], ctor_pos(sig, sig.ienv.ctor_ind[c], c) as nat), fs))),
{
    let (nf, nr) = (fds.len(), ihs.len());
    let ind = sig.ienv.ctor_ind[c];
    let pc = ctor_pos(sig, ind, c) as nat;
    let np = pvars.len();
    let ws = fs + hs;
    assert forall|i: int| 0 <= i < ws.len() implies #[trigger] wf(ws[i]) by {
        if i < nf {
            assert(ws[i] == fs[i]);
        } else {
            assert(ws[i] == hs[i - nf]);
        }
    }
    let body = minor_body(km, c, us, pvars, nf, nr);
    let (ws2, e, _l2, _dcs) = tele_apps(ss, sig, g, fds + ihs, body, l, rho, d, xn, ws);
    let rho2 = exts(rho, ws2);
    let args = pvars + crate::rec_canon::vars(nr, nf);
    let wa = motive_bound(sig, km, c, us, args, rho2, e);
    exts_at(rho, ws2, km);
    // the fields' witnesses lie below the fields
    let fl = flds(wa, np);
    assert forall|i: int| 0 <= i < nf implies le(#[trigger] fl[i], fs[i]) && wf(fl[i]) by {
        let v = (nr + nf - 1 - i) as nat;
        assert(args[np + i] == ExprSpec::Var(v));
        assert(mem(sig, args[np + i], rho2, wa[np + i]));
        reveal(mem);
        let w = choose|w: Wit| #[trigger] mem_w(sig, ExprSpec::Var(v), rho2, wa[np + i], w);
        exts_at(rho, ws2, v);
        assert(ws2[ws2.len() - 1 - v] == ws2[i]);
        assert(le(ws2[i], ws[i]) && ws[i] == fs[i]);
        assert(fl[i] == wa[np + i]);
        le_trans(fl[i], ws2[i], fs[i]);
    }
    crate::dom_sem::nd_le(NdKey::Con(ind, pc), fl, fs);
    crate::dom_code::wf_nd(NdKey::Con(ind, pc), fl);
    crate::dom_code::wf_nd(NdKey::Con(ind, pc), fs);
    let m = rho((km - nf - nr) as nat);
    assert(wf(m));
    le_refl(m);
    crate::dom_sound::app_mono(m, m, Cpt::Nd(NdKey::Con(ind, pc), fl), Cpt::Nd(NdKey::Con(ind, pc), fs));
    le_trans(e, app(m, Cpt::Nd(NdKey::Con(ind, pc), fl)), app(m, Cpt::Nd(NdKey::Con(ind, pc), fs)));
    e
}

/// AN APPROXIMATION APPLIED THROUGH THE TELESCOPE lies below the code
/// function at the inputs.
pub proof fn rf_apps(sig: Sig, rid: u64, ds: Seq<ExprSpec>, body: ExprSpec, p: Seq<Cpt>, v: Cpt, ws: Seq<Cpt>)
    requires
        rf_fun(sig, rid, binds(BinderKind::Pi, ds, body), p, v),
        !(body is Bind && body->Bind_0 == BinderKind::Pi),
        wf(v),
        crate::dom_code::aw(p),
        crate::dom_code::aw(ws),
        ws.len() == ds.len(),
    ensures
        le(crate::dom_rec::apps(v, ws), crate::dom_rec::recval(sig, rid, p + ws)),
    decreases ds.len(),
{
    if ds.len() == 0 {
        assert(p + ws =~= p);
        assert(crate::dom_rec::apps(v, ws) == v);
        if v is Bot {
            reveal_with_fuel(le_set, 1);
        }
        return;
    }
    let (ta, rest) = (ds[0], ds.drop_first());
    let tb = binds(BinderKind::Pi, rest, body);
    assert(binds(BinderKind::Pi, ds, body) == ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb)));
    crate::dom_tele::apps_front(v, ws);
    let w0 = ws[0];
    assert(wf(w0));
    let v2 = app(v, w0);
    let wr = ws.drop_first();
    assert forall|i: int| 0 <= i < wr.len() implies #[trigger] wf(wr[i]) by {
        assert(wr[i] == ws[i + 1]);
    }
    assert forall|i: int| 0 <= i < p.len() + 1 implies #[trigger] wf(p.push(w0)[i]) by {
        if i < p.len() { assert(p.push(w0)[i] == p[i]); }
    }
    if v is Lam {
        appk_wf(v, w0, true);
        crate::dom_rec::rf_app(sig, rid, ta, tb, p, v, w0);
    } else {
        assert(v is Bot);
        assert(v2 == Cpt::Bot);
    }
    rf_apps(sig, rid, rest, body, p.push(w0), v2, wr);
    assert(p.push(w0) + wr =~= p + ws);
}

/// A CHAIN'S LAMBDA APPROXIMATES the recursor's code function when its
/// output does.
pub proof fn lamchain_rf(sig: Sig, rid: u64, tds: Seq<ExprSpec>, body: ExprSpec, p: Seq<Cpt>, xs: Seq<Cpt>, out: Cpt)
    requires
        xs.len() == tds.len(),
        !(body is Bind && body->Bind_0 == BinderKind::Pi),
        le(out, crate::dom_rec::recval(sig, rid, p + xs)),
    ensures
        rf_fun(sig, rid, binds(BinderKind::Pi, tds, body), p, crate::dom_tele::lamchain(xs, out)),
    decreases tds.len(),
{
    if tds.len() == 0 {
        assert(p + xs =~= p);
        return;
    }
    if out is Bot {
        return;
    }
    let (t2, x2) = (tds.drop_first(), xs.drop_first());
    assert(p.push(xs[0]) + x2 =~= p + xs);
    lamchain_rf(sig, rid, t2, body, p.push(xs[0]), x2, out);
    let l2 = crate::dom_tele::lamchain(x2, out);
    let f = seq![(xs[0], l2)];
    assert(f[0] == (xs[0], l2));
    assert(binds(BinderKind::Pi, tds, body) == ExprSpec::Bind(BinderKind::Pi, Box::new(tds[0]), Box::new(binds(BinderKind::Pi, t2, body))));
    assert(crate::dom_tele::lamchain(xs, out) == Cpt::Lam(f));
}

/// Applying to two sequences in turn.
pub proof fn apps_concat(u: Cpt, a: Seq<Cpt>, b: Seq<Cpt>)
    ensures
        crate::dom_rec::apps(crate::dom_rec::apps(u, a), b) == crate::dom_rec::apps(u, a + b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        apps_concat(u, a, b.drop_last());
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

/// The recursive results follow the rule's recursive fields.
pub proof fn rec_ihs_len(sig: Sig, rid: u64, ins: Seq<Cpt>, k: nat)
    requires
        crate::dom_rec::rec_ok(sig, rid, ins),
        k <= ins.last()->Nd_1.len(),
        crate::rec_canon::shape_of(sig, sig.ienv.recs[rid], crate::rec_canon::rec_ind(sig, rid)).fields[ins.last()->Nd_0->Con_1 as int].len()
            == ins.last()->Nd_1.len(),
    ensures ({
        let sh = crate::rec_canon::shape_of(sig, sig.ienv.recs[rid], crate::rec_canon::rec_ind(sig, rid));
        let p = ins.last()->Nd_0->Con_1 as int;
        crate::dom_rec::rec_ihs(sig, rid, ins, k).len()
            == crate::rec_canon::rec_pos(sh.fields[p], sh.ind, sh.us(), sh.np, sh.ni, k).len()
    }),
    decreases k,
{
    if k > 0 {
        rec_ihs_len(sig, rid, ins, (k - 1) as nat);
    }
}

/// The motive's value at the major is in the recursor type's body.
pub proof fn app_var_mem(sig: Sig, i: nat, j: nat, rho: Env)
    requires
        wf(rho(i)),
        wf(rho(j)),
        wf(app(rho(i), rho(j))),
    ensures
        mem(sig, ExprSpec::App(Box::new(ExprSpec::Var(i)), Box::new(ExprSpec::Var(j))), rho, app(rho(i), rho(j))),
{
    reveal(mem);
    le_refl(rho(i));
    le_refl(rho(j));
    le_refl(app(rho(i), rho(j)));
    assert(mem_w(sig, ExprSpec::Var(i), rho, rho(i), Wit::Nil));
    assert(mem_w(sig, ExprSpec::Var(j), rho, rho(j), Wit::Nil));
    assert(mem_w(sig, ExprSpec::App(Box::new(ExprSpec::Var(i)), Box::new(ExprSpec::Var(j))), rho, app(rho(i), rho(j)),
        Wit::Ap(rho(i), rho(j), Box::new(Wit::Nil), Box::new(Wit::Nil))));
}

/// A RECURSOR IN THE FIRST STAGE'S SCOPE: canonical, without indices,
/// with distinct constructors, and the only canonical recursor of its
/// inductive.
pub open spec fn rec_scope(sig: Sig, rid: u64) -> bool {
    let sh = crate::rec_canon::shape_of(sig, sig.ienv.recs[rid], crate::rec_canon::rec_ind(sig, rid));
    &&& crate::rec_canon::rec_canon(sig, rid)
    &&& sh.ni == 0
    &&& forall|j1: int, j2: int| #![trigger sh.ctors[j1], sh.ctors[j2]]
        0 <= j1 < sh.nmin() && 0 <= j2 < sh.nmin() && sh.ctors[j1] == sh.ctors[j2] ==> j1 == j2
    &&& forall|r2: u64| #[trigger] crate::rec_canon::rec_canon(sig, r2) && crate::rec_canon::rec_ind(sig, r2) == crate::rec_canon::rec_ind(sig, rid)
        ==> r2 == rid
    &&& !sig.ienv.ctor_ind.contains_key(sh.ind) && !sig.ienv.recs.contains_key(sh.ind)
    &&& forall|i: int, j: int| #![trigger sig.ienv.recs[rid].uparams[i], sig.ienv.recs[rid].uparams[j]]
        0 <= i < sig.ienv.recs[rid].uparams.len() && 0 <= j < sig.ienv.recs[rid].uparams.len()
        && sig.ienv.recs[rid].uparams[i] == sig.ienv.recs[rid].uparams[j] ==> i == j
}

/// A recursor in scope is its inductive's canonical recursor.
pub proof fn scope_canon(sig: Sig, rid: u64)
    requires
        rec_scope(sig, rid),
    ensures
        crate::dom_code::has_canon(sig, rshape(sig, rid).ind),
        crate::dom_code::canon_shape(sig, rshape(sig, rid).ind) == rshape(sig, rid),
{
    let ind = crate::rec_canon::rec_ind(sig, rid);
    assert(crate::rec_canon::rec_canon(sig, rid) && crate::rec_canon::rec_ind(sig, rid) == ind);
    assert(crate::dom_code::has_canon(sig, ind));
    let r2 = crate::dom_code::canon_rec(sig, ind);
    assert(crate::rec_canon::rec_canon(sig, r2) && crate::rec_canon::rec_ind(sig, r2) == ind);
    assert(r2 == rid);
}

/// The recursor's shape.
pub open spec fn rshape(sig: Sig, rid: u64) -> crate::rec_canon::IndShape {
    crate::rec_canon::shape_of(sig, sig.ienv.recs[rid], crate::rec_canon::rec_ind(sig, rid))
}

/// The recursor's type's domains at a level instance.
pub open spec fn rtds(sig: Sig, rid: u64, ls: Seq<LevelSpec>) -> Seq<ExprSpec> {
    let sh = rshape(sig, rid);
    let lm = crate::rec_canon::elim_level(sig, rid, crate::rec_canon::rec_ind(sig, rid));
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), vars(1 + sh.nmin(), sh.np));
    crate::dom_rec_shape::sls(sh.head_doms(lm) + seq![major], sig.ienv.recs[rid].uparams, ls)
}

/// Its body: the motive at the major.
pub open spec fn rbody(sig: Sig, rid: u64) -> ExprSpec {
    ExprSpec::App(Box::new(ExprSpec::Var(rshape(sig, rid).nmin() + 1)), Box::new(ExprSpec::Var(0)))
}

/// The instantiated type splits into its domains and body.
pub proof fn rec_ty_split(sig: Sig, rid: u64, ls: Seq<LevelSpec>)
    requires
        rec_scope(sig, rid),
    ensures
        dty_at(sig, rid, ls) == binds(BinderKind::Pi, rtds(sig, rid, ls), rbody(sig, rid)),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let lm = crate::rec_canon::elim_level(sig, rid, crate::rec_canon::rec_ind(sig, rid));
    let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
    let idx = Seq::new(ni, |k: int| crate::subst_algebra::lift(1 + nmin, k as nat, sh.idoms[k]));
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), vars(1 + nmin + ni, np) + vars(0, ni));
    let body = spine_app(ExprSpec::Var(nmin + ni + 1), vars(1, ni).push(ExprSpec::Var(0)));
    assert(idx =~= Seq::<ExprSpec>::empty());
    assert(vars(0, ni) =~= Seq::<ExprSpec>::empty());
    assert(vars(1 + nmin + ni, np) + vars(0, ni) =~= vars(1 + nmin, np));
    assert(sh.head_doms(lm) + idx + seq![major] =~= sh.head_doms(lm) + seq![major]);
    assert(vars(1, ni).push(ExprSpec::Var(0)) =~= seq![ExprSpec::Var(0)]);
    assert(body == ExprSpec::App(Box::new(ExprSpec::Var(nmin + 1)), Box::new(ExprSpec::Var(0)))) by {
        let a = seq![ExprSpec::Var(0)];
        assert(a.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
        assert(a[0] == ExprSpec::Var(0));
        reveal_with_fuel(spine_app, 2);
    }
    assert(sig.consts[rid].ty == sh.rec_ty(lm));
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.head_doms(lm) + seq![major], body, rd.uparams, ls);
    assert(crate::expr_model::subst_expr_levels(body, rd.uparams, ls) == body) by {
        assert(crate::expr_model::subst_expr_levels(ExprSpec::Var(nmin + 1), rd.uparams, ls) == ExprSpec::Var(nmin + 1));
        assert(crate::expr_model::subst_expr_levels(ExprSpec::Var(0), rd.uparams, ls) == ExprSpec::Var(0));
    }
}

/// A constructor of a recursor in scope: of its canonical shape, at its
/// position.
pub proof fn scope_ctor(sig: Sig, rid: u64, p: int)
    requires
        rec_scope(sig, rid),
        0 <= p < rshape(sig, rid).nmin(),
    ensures ({
        let sh = rshape(sig, rid);
        let c = sh.ctors[p];
        &&& crate::dom_code::canon_shape(sig, sh.ind) == sh
        &&& sig.ienv.ctor_ind.contains_key(c) && sig.ienv.ctor_ind[c] == sh.ind
        &&& ctor_of(sig, sh.ind, c)
        &&& ctor_pos(sig, sh.ind, c) == p
        &&& sig.consts.contains_key(c) && sig.consts[c].val is None
    }),
{
    let sh = rshape(sig, rid);
    let ind = crate::rec_canon::rec_ind(sig, rid);
    let c = sh.ctors[p];
    assert(sh.ind == ind);
    assert(crate::dom_code::has_canon(sig, ind));
    let r2 = crate::dom_code::canon_rec(sig, ind);
    assert(crate::rec_canon::rec_canon(sig, r2) && crate::rec_canon::rec_ind(sig, r2) == ind);
    assert(r2 == rid);
    assert(crate::dom_code::canon_shape(sig, ind) == sh);
    assert(0 <= p < crate::dom_code::canon_shape(sig, ind).nmin() && crate::dom_code::canon_shape(sig, ind).ctors[p] == c);
    assert(ctor_of(sig, ind, c));
    let p2 = ctor_pos(sig, ind, c);
    assert(0 <= p2 < sh.nmin() && sh.ctors[p2] == c);
}

/// The inductive of a recursor in scope: canonical, of the recursor's
/// shape, an axiom, neither a constructor nor a recursor.
pub proof fn scope_ctor_ind(sig: Sig, rid: u64)
    requires
        rec_scope(sig, rid),
    ensures ({
        let sh = rshape(sig, rid);
        &&& crate::dom_code::has_canon(sig, sh.ind)
        &&& crate::dom_code::canon_shape(sig, sh.ind) == sh
        &&& sig.consts.contains_key(sh.ind) && sig.consts[sh.ind].val is None
        &&& !sig.ienv.ctor_ind.contains_key(sh.ind) && !sig.ienv.recs.contains_key(sh.ind)
    }),
{
    let sh = rshape(sig, rid);
    let ind = crate::rec_canon::rec_ind(sig, rid);
    assert(sh.ind == ind);
    assert(crate::dom_code::has_canon(sig, ind));
    let r2 = crate::dom_code::canon_rec(sig, ind);
    assert(crate::rec_canon::rec_canon(sig, r2) && crate::rec_canon::rec_ind(sig, r2) == ind);
    assert(r2 == rid);
    crate::dom_ctor_bound::ctor_shape_ind(sig, ind);
}

/// A constructor application is not a binder.
pub proof fn spine_const_nonbind(c: u64, us: Seq<LevelSpec>, args: Seq<ExprSpec>)
    ensures
        !(spine_app(ExprSpec::Const(c, us), args) is Bind),
{
}

/// THE MINOR'S OUTPUT, for the recursor at a chain of inputs.
#[verifier::spinoff_prover]
pub proof fn rec_minor(ss: Sig, sig: Sig, rid: u64, ls: Seq<LevelSpec>, l: LevelSpec, rho0: Env, ds: Seq<Cpt>, xs: Seq<Cpt>) -> (e: Cpt)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        rec_scope(sig, rid),
        derivable(ss, eq(Seq::empty(), dty_at(sig, rid, ls), dty_at(sig, rid, ls), sort(l))),
        forall|i: nat| #[trigger] wf(rho0(i)),
        crate::dom_tele::chain_ok(sig, rtds(sig, rid, ls), rho0, ds, xs),
        crate::dom_rec::rec_ok(sig, rid, xs),
    ensures
        typed(crate::dom_rec::recval(sig, rid, xs), e),
        typed(e, Cpt::U),
        le(e, app(xs[rshape(sig, rid).np as int], xs.last())),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let ind = crate::rec_canon::rec_ind(sig, rid);
    let lm = crate::rec_canon::elim_level(sig, rid, ind);
    let (np, nmin) = (sh.np, sh.nmin());
    let tds = rtds(sig, rid, ls);
    rec_ty_split(sig, rid, ls);
    let v = xs.last();
    let p = v->Nd_0->Con_1 as int;
    let fs = v->Nd_1;
    let nf = fs.len();
    let c = sh.ctors[p];
    scope_ctor(sig, rid, p);
    assert(sh.fields[p].len() == rd.rules[p].nfields);
    let mi = np + 1 + p;
    let minor = xs[mi];
    let hs = crate::dom_rec::rec_ihs(sig, rid, xs, nf);
    assert(crate::dom_rec::recval(sig, rid, xs) == crate::dom_rec::apps(crate::dom_rec::apps(minor, fs), hs));
    apps_concat(minor, fs, hs);
    rec_ihs_len(sig, rid, xs, nf);
    let nr = hs.len();
    assert(nr == sh.rposj(p).len());
    // the minor's type at the instance
    assert(sh.head_doms(lm)[mi] == sh.minor_ty(p));
    assert(tds[mi] == crate::expr_model::subst_expr_levels(sh.minor_ty(p), rd.uparams, ls));
    let (f2, i2) = crate::dom_rec_shape::minor_shape(sh, p, rd.uparams, ls);
    let us2 = crate::level_model::subst_levels_spec(sh.us(), rd.uparams, ls);
    let km = (p + nf + nr) as nat;
    let pvars = vars((1 + p + nf + nr) as nat, np);
    // its typing context, and the chain's environment there
    let li = crate::dom_tele::tele_prefix(ss, sig, Seq::empty(), tds, rbody(sig, rid), l, rho0, ds, xs, mi);
    let g = Seq::<ExprSpec>::empty() + tds.subrange(0, mi);
    let rho = crate::dom_tele::exts(rho0, xs.subrange(0, mi));
    assert(crate::dom_sound::dfit(sig, tds[mi], crate::dom_tele::exts(rho0, xs.subrange(0, mi)), ds[mi], xs[mi]));
    // the constructor's arity
    let tc = sig.consts[c].ty;
    assert(tc == binds(BinderKind::Pi, sh.pdoms + sh.fields[p], crate::rec_canon::tbody(tc, np + nf)));
    spine_const_nonbind(ind, sh.us(), vars(nf, np) + sh.tss[p]);
    crate::dom_rec_shape::tarity_binds(sh.pdoms + sh.fields[p], crate::rec_canon::tbody(tc, np + nf));
    crate::dom_rec_shape::tarity_sl(tc, sig.consts[c].lps, us2);
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] wf(xs[i]) by {
        assert(crate::dom_sound::dfit(sig, tds[i], crate::dom_tele::exts(rho0, xs.subrange(0, i)), ds[i], xs[i]));
        typed_wf(xs[i], ds[i]);
    }
    assert(forall|i: int| 0 <= i < fs.len() ==> #[trigger] wf(fs[i])) by {
        assert(wf(xs[xs.len() - 1]));
    }
    crate::dom_rec::rec_ihs_wf(sig, rid, xs, nf);
    let e = minor_out(ss, sig, g, f2, i2, km, c, us2, pvars, li, rho, ds[mi], minor, fs, hs);
    exts_at(rho0, xs.subrange(0, mi), p as nat);
    assert(v == Cpt::Nd(NdKey::Con(ind, p as nat), fs));
    e
}

/// THE MOTIVE AT THE MAJOR is a type, in the recursor type's body.
#[verifier::spinoff_prover]
pub proof fn rec_motive(ss: Sig, sig: Sig, rid: u64, ls: Seq<LevelSpec>, l: LevelSpec, rho0: Env, ds: Seq<Cpt>, xs: Seq<Cpt>)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        rec_scope(sig, rid),
        derivable(ss, eq(Seq::empty(), dty_at(sig, rid, ls), dty_at(sig, rid, ls), sort(l))),
        forall|i: nat| #[trigger] wf(rho0(i)),
        crate::dom_tele::chain_ok(sig, rtds(sig, rid, ls), rho0, ds, xs),
    ensures
        typed(app(xs[rshape(sig, rid).np as int], xs.last()), Cpt::U),
        mem(sig, rbody(sig, rid), crate::dom_tele::exts(rho0, xs), app(xs[rshape(sig, rid).np as int], xs.last())),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let ind = crate::rec_canon::rec_ind(sig, rid);
    let lm = crate::rec_canon::elim_level(sig, rid, ind);
    let (np, nmin) = (sh.np, sh.nmin());
    let tds = rtds(sig, rid, ls);
    rec_ty_split(sig, rid, ls);
    let (xm, v) = (xs[np as int], xs.last());
    let tv = app(xm, v);
    // the motive's domain at the instance: a Pi into a sort
    let ia = crate::rec_canon::ind_app(sh.ind, sh.us(), vars(sh.ni, np) + vars(0, sh.ni));
    assert(sh.idoms.len() == 0);
    assert(sh.motive_ty(lm) == ExprSpec::Bind(BinderKind::Pi, Box::new(ia), Box::new(ExprSpec::Sort(lm))));
    assert(sh.head_doms(lm)[np as int] == sh.motive_ty(lm));
    let ta = crate::expr_model::subst_expr_levels(ia, rd.uparams, ls);
    let lm2 = crate::level_model::subst_level_spec(lm, rd.uparams, ls);
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), vars(1 + nmin, np));
    assert((sh.head_doms(lm) + seq![major])[np as int] == sh.motive_ty(lm));
    assert(crate::expr_model::subst_expr_levels(sh.motive_ty(lm), rd.uparams, ls)
        == ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(crate::expr_model::subst_expr_levels(ExprSpec::Sort(lm), rd.uparams, ls))));
    assert(tds[np as int] == pi(ta, ExprSpec::Sort(lm2)));
    let li = crate::dom_tele::tele_prefix(ss, sig, Seq::empty(), tds, rbody(sig, rid), l, rho0, ds, xs, np as int);
    let g = Seq::<ExprSpec>::empty() + tds.subrange(0, np as int);
    let rho = crate::dom_tele::exts(rho0, xs.subrange(0, np as int));
    assert(crate::dom_sound::dfit(sig, tds[np as int], rho, ds[np as int], xm));
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] wf(xs[i]) by {
        assert(crate::dom_sound::dfit(sig, tds[i], crate::dom_tele::exts(rho0, xs.subrange(0, i)), ds[i], xs[i]));
        typed_wf(xs[i], ds[i]);
    }
    assert(wf(xs[xs.len() - 1]));
    let (w2, r1, _l2, _a0) = crate::dom_tele::tele_step(ss, sig, g, ta, ExprSpec::Sort(lm2), li, rho, ds[np as int], xm, v);
    reveal(mem);
    let wr = choose|w: Wit| #[trigger] mem_w(sig, ExprSpec::Sort(lm2), ext(rho, w2), r1, w);
    assert(r1 is Bot || r1 == sortc(lm2));
    crate::dom_sound::typed_basic();
    if r1 is Bot {
        let n = cstage(tv, r1);
        typed_up(tv, r1, n);
        ty_of_bot(n, tv);
    } else if r1 is Prop {
        let n = cstage(tv, r1);
        typed_up(tv, r1, n);
        prop_is_type(n, tv);
        typed_down(tv, Cpt::U, n);
    }
    // in the body, under the chain's environment
    let rho2 = crate::dom_tele::exts(rho0, xs);
    exts_at(rho0, xs, nmin + 1);
    exts_at(rho0, xs, 0);
    assert(xs.len() == np + nmin + 2);
    typed_wf(tv, Cpt::U);
    app_var_mem(sig, nmin + 1, 0, rho2);
}

/// THE STEP APPROXIMATION: at a typed chain of inputs whose major has a
/// rule, the single-chain lambda ending in the code function's value is
/// typed at a member of the recursor's type, approximates the code
/// function, and applied along the chain gives at least that value.
#[verifier::spinoff_prover]
pub proof fn rec_step(ss: Sig, sig: Sig, rid: u64, ls: Seq<LevelSpec>, l: LevelSpec, rho0: Env, ds: Seq<Cpt>, xs: Seq<Cpt>) -> (r: (Cpt, Cpt))
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        rec_scope(sig, rid),
        derivable(ss, eq(Seq::empty(), dty_at(sig, rid, ls), dty_at(sig, rid, ls), sort(l))),
        forall|i: nat| #[trigger] wf(rho0(i)),
        crate::dom_tele::chain_ok(sig, rtds(sig, rid, ls), rho0, ds, xs),
        crate::dom_rec::rec_ok(sig, rid, xs),
    ensures
        mem(sig, dty_at(sig, rid, ls), rho0, r.0),
        typed(r.0, Cpt::U),
        typed(r.1, r.0),
        rf_fun(sig, rid, dty_at(sig, rid, ls), Seq::empty(), r.1),
        le(crate::dom_rec::recval(sig, rid, xs), crate::dom_rec::apps(r.1, xs)),
{
    let np = rshape(sig, rid).np;
    let rv = crate::dom_rec::recval(sig, rid, xs);
    let e = rec_minor(ss, sig, rid, ls, l, rho0, ds, xs);
    rec_motive(ss, sig, rid, ls, l, rho0, ds, xs);
    let tv = app(xs[np as int], xs.last());
    typed_weak(rv, e, tv);
    rec_ty_split(sig, rid, ls);
    let tds = rtds(sig, rid, ls);
    crate::dom_tele::pichain_mem(sig, tds, rbody(sig, rid), rho0, ds, xs, tv);
    let a = crate::dom_tele::pichain(ds, xs, tv);
    assert forall|i: int| 0 <= i < ds.len() implies #[trigger] typed(xs[i], ds[i]) by {
        assert(crate::dom_sound::dfit(sig, tds[i], crate::dom_tele::exts(rho0, xs.subrange(0, i)), ds[i], xs[i]));
    }
    crate::dom_tele::lamchain_typed(ds, xs, tv, rv);
    let sa = crate::dom_tele::lamchain(xs, rv);
    le_refl(rv);
    assert(Seq::<Cpt>::empty() + xs =~= xs);
    lamchain_rf(sig, rid, tds, rbody(sig, rid), Seq::empty(), xs, rv);
    typed_wf(sa, a);
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] wf(xs[i]) by {
        assert(typed(xs[i], ds[i]));
        typed_wf(xs[i], ds[i]);
    }
    crate::dom_tele::lamchain_apps(xs, rv);
    (a, sa)
}

/// The recursive results, one by one: the code function at each recursive
/// field, in the rule's order.
pub proof fn rec_ihs_at(sig: Sig, rid: u64, ins: Seq<Cpt>, k: nat)
    requires
        crate::dom_rec::rec_ok(sig, rid, ins),
        k <= ins.last()->Nd_1.len(),
        rshape(sig, rid).fields[ins.last()->Nd_0->Con_1 as int].len() == ins.last()->Nd_1.len(),
    ensures ({
        let sh = rshape(sig, rid);
        let p = ins.last()->Nd_0->Con_1 as int;
        let rp = crate::rec_canon::rec_pos(sh.fields[p], sh.ind, sh.us(), sh.np, sh.ni, k);
        let hs = crate::dom_rec::rec_ihs(sig, rid, ins, k);
        &&& hs.len() == rp.len()
        &&& forall|r: int| 0 <= r < rp.len() ==> #[trigger] rp[r] < k
            && hs[r] == crate::dom_rec::recval(sig, rid, crate::dom_rec::ih_in(sig.ienv.recs[rid], ins, ins.last()->Nd_1[rp[r] as int]))
    }),
    decreases k,
{
    if k > 0 {
        rec_ihs_at(sig, rid, ins, (k - 1) as nat);
        let sh = rshape(sig, rid);
        let p = ins.last()->Nd_0->Con_1 as int;
        let rp0 = crate::rec_canon::rec_pos(sh.fields[p], sh.ind, sh.us(), sh.np, sh.ni, (k - 1) as nat);
        let rp = crate::rec_canon::rec_pos(sh.fields[p], sh.ind, sh.us(), sh.np, sh.ni, k);
        let hs0 = crate::dom_rec::rec_ihs(sig, rid, ins, (k - 1) as nat);
        let hs = crate::dom_rec::rec_ihs(sig, rid, ins, k);
        assert forall|r: int| 0 <= r < rp.len() implies #[trigger] rp[r] < k
            && hs[r] == crate::dom_rec::recval(sig, rid, crate::dom_rec::ih_in(sig.ienv.recs[rid], ins, ins.last()->Nd_1[rp[r] as int])) by {
            if r < rp0.len() {
                assert(rp[r] == rp0[r] && hs[r] == hs0[r]);
            }
        }
    }
}

/// The recursive positions are positions of direct occurrences.
pub proof fn rec_pos_facts(fs: Seq<ExprSpec>, ind: u64, us: Seq<LevelSpec>, np: nat, ni: nat, n: nat)
    requires
        n <= fs.len(),
    ensures
        forall|r: int| 0 <= r < crate::rec_canon::rec_pos(fs, ind, us, np, ni, n).len() ==>
            #[trigger] crate::rec_canon::rec_pos(fs, ind, us, np, ni, n)[r] < n
            && crate::rec_canon::direct_occ(fs[crate::rec_canon::rec_pos(fs, ind, us, np, ni, n)[r] as int], ind, us, np, ni,
                crate::rec_canon::rec_pos(fs, ind, us, np, ni, n)[r]),
    decreases n,
{
    if n > 0 {
        rec_pos_facts(fs, ind, us, np, ni, (n - 1) as nat);
        let prev = crate::rec_canon::rec_pos(fs, ind, us, np, ni, (n - 1) as nat);
        let cur = crate::rec_canon::rec_pos(fs, ind, us, np, ni, n);
        assert forall|r: int| 0 <= r < cur.len() implies #[trigger] cur[r] < n
            && crate::rec_canon::direct_occ(fs[cur[r] as int], ind, us, np, ni, cur[r]) by {
            if r < prev.len() {
                assert(cur[r] == prev[r]);
            }
        }
    }
}

} // verus!
