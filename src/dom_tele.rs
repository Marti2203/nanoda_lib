//! APPLYING THROUGH A TELESCOPE (step 3 of the S6.4c/d plan in
//! docs/TYPED_TARGET.md): a function typed at a member of a derivable Pi
//! type's denotation, applied to any argument, is typed at the codomain at
//! the argument's projection onto its inputs, and that codomain lies in
//! the body's denotation under the extended environment, which fits the
//! extended context. The projection is typed at the domain and leaves the
//! application unchanged, so no domain match is needed.
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
use crate::dom_sound::{fits_env, fits_ext, dfit, body_jc, cod_in_body, sound, sound_ok, typed_basic};
#[cfg(verus_only)]
use crate::ti_syntax::{Sig, Ctx, derivable, eq, sort, pi};
#[cfg(verus_only)]
use crate::ti_gen::{gen, gmark, typ};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Bottom is typed at every type.
pub proof fn bot_typed(a: Cpt)
    requires
        typed(a, Cpt::U),
    ensures
        typed(Cpt::Bot, a),
{
    let n = cstage(a, Cpt::U) + 1;
    typed_up(a, Cpt::U, n);
    typed_wf(a, Cpt::U);
    assert(stg(n, Cpt::Bot));
    assert(has_type(n, Cpt::Bot, a));
    typed_down(Cpt::Bot, a, n);
}

/// A Pi type's domain is a type.
pub proof fn pi_dom_type(a: Cpt)
    requires
        typed(a, Cpt::U),
        a is Pi,
    ensures
        typed(*a->Pi_0, Cpt::U),
{
    let n = cstage(a, Cpt::U);
    typed_up(a, Cpt::U, n);
    assert(has_type((n - 1) as nat, *a->Pi_0, Cpt::U));
    typed_down(*a->Pi_0, Cpt::U, (n - 1) as nat);
}

/// The body of a derivable Pi type is join-closed under every fitting
/// extension, from its derivation's soundness.
pub proof fn pi_body_jc(sig: Sig, g: Ctx, ta: ExprSpec, tb: ExprSpec, l2: LevelSpec, rho: Env)
    requires
        typ(sig, g.push(ta), tb, l2),
        fits_env(sig, g, rho),
    ensures
        body_jc(sig, ta, tb, rho),
{
    let d = crate::ti_sub::get(sig, eq(g.push(ta), tb, tb, sort(l2)));
    assert forall|x: Cpt, a: Cpt| #[trigger] dfit(sig, ta, rho, a, x) implies jc(sig, tb, ext(rho, x)) by {
        fits_ext(sig, g, rho, ta, a, x);
        sound(sig, d, ext(rho, x));
    }
}

/// ONE STEP: the argument's projection, the codomain there, and the
/// extended environment.
pub proof fn tele_step(sig: Sig, g: Ctx, ta: ExprSpec, tb: ExprSpec, l: LevelSpec, rho: Env, d: Cpt, u: Cpt, w: Cpt)
    -> (r: (Cpt, Cpt, LevelSpec, Cpt))
    requires
        derivable(sig, eq(g, pi(ta, tb), pi(ta, tb), sort(l))),
        fits_env(sig, g, rho),
        mem(sig, pi(ta, tb), rho, d),
        typed(d, Cpt::U),
        typed(u, d),
        wf(w),
    ensures
        wf(r.0),
        le(r.0, w),
        app(u, w) == app(u, r.0),
        typed(app(u, w), r.1),
        typed(r.1, Cpt::U),
        mem(sig, tb, ext(rho, r.0), r.1),
        fits_env(sig, g.push(ta), ext(rho, r.0)),
        typ(sig, g.push(ta), tb, r.2),
        dfit(sig, ta, rho, r.3, r.0),
{
    let dd = crate::ti_sub::get(sig, eq(g, pi(ta, tb), pi(ta, tb), sort(l)));
    gen(sig, dd);
    let (l1, l2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(ta, tb, l1, l2)
        && typ(sig, g, ta, l1) && typ(sig, g.push(ta), tb, l2) && crate::ti_chain::tchain(sig, g, sort(l), sort(crate::ti_syntax::imax(l1, l2)));
    typed_wf(u, d);
    typed_wf(d, Cpt::U);
    typed_basic();
    reveal(mem);
    if d is Bot {
        typed_up(u, d, cstage(u, d));
        ty_of_bot(cstage(u, d), u);
        mem_bot(sig, ta, rho);
        mem_bot(sig, tb, ext(rho, Cpt::Bot));
        fits_ext(sig, g, rho, ta, Cpt::Bot, Cpt::Bot);
        le_refl(Cpt::Bot);
        return (Cpt::Bot, Cpt::Bot, l2, Cpt::Bot);
    }
    // the member lies below a generator, whose domain is in the domain's
    // denotation
    let wit = choose|wit: Wit| #[trigger] mem_w(sig, pi(ta, tb), rho, d, wit);
    assert(pi(ta, tb) == ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb)));
    let (a, gen_) = match wit {
        Wit::Gen(a, gen_, wa, _) => {
            assert(mem_w(sig, ta, rho, a, *wa));
            (a, gen_)
        },
        _ => {
            assert(false);
            (Cpt::Bot, Cpt::Bot)
        },
    };
    assert(le(d, gen_) && gen_ is Pi && *gen_->Pi_0 == a && mem(sig, ta, rho, a));
    head_le(d, gen_);
    let a0 = *d->Pi_0;
    pi_dom_le(d, gen_);
    parts_lower(d);
    assert(wf(a0));
    mem_down_e(sig, ta, rho, a, a0);
    pi_dom_type(d);
    // the argument, projected onto the function's inputs
    let n = cstage(u, d) + cstage(d, Cpt::U) + 2;
    typed_up(u, d, n);
    typed_up(d, Cpt::U, n);
    ty_inv(n, u, d);
    let w2 = if u is Lam { crate::dom_proj::proj(u, w) } else { Cpt::Bot };
    if u is Lam {
        crate::dom_proj::proj_props(u, w);
        crate::dom_proj::proj_typed(n, u, d, w);
        typed_down(w2, a0, (n - 1) as nat);
    } else {
        assert(u is Bot);
        bot_typed(a0);
        le_refl(Cpt::Bot);
        assert(app(u, w) == Cpt::Bot && app(u, w2) == Cpt::Bot);
    }
    // the codomain, in the body's denotation
    pi_body_jc(sig, g, ta, tb, l2, rho);
    cod_in_body(sig, ta, tb, rho, d, w2, a0);
    crate::dom_proj::app_typed_at(n, u, d, w2);
    typed_down(app(u, w2), cod(d, w2), (n - 1) as nat);
    typed_down(cod(d, w2), Cpt::U, (n - 1) as nat);
    fits_ext(sig, g, rho, ta, a0, w2);
    (w2, cod(d, w2), l2, a0)
}

/// The environment extended by `ws` in order, the last innermost.
pub open spec fn exts(rho: Env, ws: Seq<Cpt>) -> Env
    decreases ws.len(),
{
    if ws.len() == 0 { rho } else { exts(ext(rho, ws[0]), ws.drop_first()) }
}

/// Applying to a sequence, from the front.
pub proof fn apps_front(u: Cpt, ws: Seq<Cpt>)
    requires
        ws.len() > 0,
    ensures
        crate::dom_rec::apps(u, ws) == crate::dom_rec::apps(app(u, ws[0]), ws.drop_first()),
    decreases ws.len(),
{
    let v = app(u, ws[0]);
    if ws.len() > 1 {
        let init = ws.drop_last();
        apps_front(u, init);
        assert(init[0] == ws[0]);
        let r = ws.drop_first();
        assert(r.drop_last() =~= init.drop_first());
        assert(r.last() == ws.last());
        assert(crate::dom_rec::apps(v, r) == app(crate::dom_rec::apps(v, r.drop_last()), r.last()));
        assert(crate::dom_rec::apps(u, ws) == app(crate::dom_rec::apps(u, init), ws.last()));
    } else {
        assert(ws.drop_first() =~= Seq::<Cpt>::empty());
        assert(ws.drop_last() =~= Seq::<Cpt>::empty());
        assert(crate::dom_rec::apps(u, ws.drop_last()) == u);
        assert(crate::dom_rec::apps(v, ws.drop_first()) == v);
    }
}

/// THROUGH A TELESCOPE: the arguments' projections, the codomain after
/// all of them, and the extended environment.
pub proof fn tele_apps(sig: Sig, g: Ctx, ds: Seq<ExprSpec>, body: ExprSpec, l: LevelSpec, rho: Env, d: Cpt, u: Cpt, ws: Seq<Cpt>)
    -> (r: (Seq<Cpt>, Cpt, LevelSpec, Seq<Cpt>))
    requires
        ws.len() == ds.len(),
        derivable(sig, eq(g, crate::rec_canon::binds(BinderKind::Pi, ds, body), crate::rec_canon::binds(BinderKind::Pi, ds, body), sort(l))),
        fits_env(sig, g, rho),
        mem(sig, crate::rec_canon::binds(BinderKind::Pi, ds, body), rho, d),
        typed(d, Cpt::U),
        typed(u, d),
        crate::dom_code::aw(ws),
    ensures
        r.0.len() == ws.len(),
        crate::dom_sem::pre_le(r.0, ws),
        crate::dom_code::aw(r.0),
        crate::dom_rec::apps(u, ws) == crate::dom_rec::apps(u, r.0),
        typed(crate::dom_rec::apps(u, ws), r.1),
        typed(r.1, Cpt::U),
        mem(sig, body, exts(rho, r.0), r.1),
        fits_env(sig, g + ds, exts(rho, r.0)),
        typ(sig, g + ds, body, r.2),
        r.3.len() == ds.len(),
        forall|i: int| 0 <= i < ds.len() ==> #[trigger] dfit(sig, ds[i], exts(rho, r.0.subrange(0, i)), r.3[i], r.0[i]),
    decreases ds.len(),
{
    if ds.len() == 0 {
        assert(g + ds =~= g);
        assert(crate::rec_canon::binds(BinderKind::Pi, ds, body) == body);
        return (Seq::empty(), d, l, Seq::empty());
    }
    let (ta, rest) = (ds[0], ds.drop_first());
    let tb = crate::rec_canon::binds(BinderKind::Pi, rest, body);
    assert(crate::rec_canon::binds(BinderKind::Pi, ds, body) == pi(ta, tb));
    let (w2, d2, l2, a0) = tele_step(sig, g, ta, tb, l, rho, d, u, ws[0]);
    assert(wf(ws[0]));
    let u2 = app(u, ws[0]);
    let wr = ws.drop_first();
    assert forall|i: int| 0 <= i < wr.len() implies #[trigger] wf(wr[i]) by {
        assert(wr[i] == ws[i + 1]);
    }
    let (ws2r, e, l3, dsr) = tele_apps(sig, g.push(ta), rest, body, l2, ext(rho, w2), d2, u2, wr);
    let dcs = seq![a0] + dsr;
    let ws2 = seq![w2] + ws2r;
    assert(ws2[0] == w2 && ws2.drop_first() =~= ws2r);
    apps_front(u, ws);
    apps_front(u, ws2);
    assert(g.push(ta) + rest =~= g + ds);
    assert forall|i: int| 0 <= i < ws2.len() implies le(#[trigger] ws2[i], ws[i]) by {
        if i > 0 {
            assert(ws2[i] == ws2r[i - 1] && ws[i] == wr[i - 1]);
        }
    }
    assert forall|i: int| 0 <= i < ws2.len() implies #[trigger] wf(ws2[i]) by {
        if i > 0 {
            assert(ws2[i] == ws2r[i - 1]);
        }
    }
    assert forall|i: int| 0 <= i < ds.len() implies #[trigger] dfit(sig, ds[i], exts(rho, ws2.subrange(0, i)), dcs[i], ws2[i]) by {
        if i == 0 {
            assert(ws2.subrange(0, 0) =~= Seq::<Cpt>::empty());
        } else {
            assert(dfit(sig, rest[i - 1], exts(ext(rho, w2), ws2r.subrange(0, i - 1)), dsr[i - 1], ws2r[i - 1]));
            let pre = ws2.subrange(0, i);
            assert(pre[0] == w2 && pre.drop_first() =~= ws2r.subrange(0, i - 1));
            assert(rest[i - 1] == ds[i] && dcs[i] == dsr[i - 1] && ws2[i] == ws2r[i - 1]);
        }
    }
    (ws2, e, l3, dcs)
}

/// A Pi code along one chain of inputs: domain `ds[i]`, one entry at
/// `xs[i]`, ending in `c`.
pub open spec fn pichain(ds: Seq<Cpt>, xs: Seq<Cpt>, c: Cpt) -> Cpt
    decreases ds.len(),
{
    if ds.len() == 0 || xs.len() == 0 {
        c
    } else {
        Cpt::Pi(Box::new(ds[0]), seq![(xs[0], pichain(ds.drop_first(), xs.drop_first(), c))])
    }
}

/// A lambda along one chain of inputs, ending in `out` (bottom when `out`
/// is: a lambda must have an output above bottom).
pub open spec fn lamchain(xs: Seq<Cpt>, out: Cpt) -> Cpt
    decreases xs.len(),
{
    if xs.len() == 0 || out is Bot {
        out
    } else {
        Cpt::Lam(seq![(xs[0], lamchain(xs.drop_first(), out))])
    }
}

/// The chain's domains are members of the telescope's domains, types,
/// with the inputs typed at them.
pub open spec fn chain_ok(sig: Sig, tds: Seq<ExprSpec>, rho: Env, ds: Seq<Cpt>, xs: Seq<Cpt>) -> bool {
    &&& ds.len() == tds.len()
    &&& xs.len() == tds.len()
    &&& forall|i: int| 0 <= i < tds.len() ==> #[trigger] dfit(sig, tds[i], exts(rho, xs.subrange(0, i)), ds[i], xs[i])
}

proof fn chain_ok_rest(sig: Sig, tds: Seq<ExprSpec>, rho: Env, ds: Seq<Cpt>, xs: Seq<Cpt>)
    requires
        chain_ok(sig, tds, rho, ds, xs),
        tds.len() > 0,
    ensures
        chain_ok(sig, tds.drop_first(), ext(rho, xs[0]), ds.drop_first(), xs.drop_first()),
        dfit(sig, tds[0], rho, ds[0], xs[0]),
{
    assert(dfit(sig, tds[0], exts(rho, xs.subrange(0, 0)), ds[0], xs[0]));
    assert(xs.subrange(0, 0) =~= Seq::<Cpt>::empty());
    let (t2, d2, x2) = (tds.drop_first(), ds.drop_first(), xs.drop_first());
    assert forall|i: int| 0 <= i < t2.len() implies #[trigger] dfit(sig, t2[i], exts(ext(rho, xs[0]), x2.subrange(0, i)), d2[i], x2[i]) by {
        assert(dfit(sig, tds[i + 1], exts(rho, xs.subrange(0, i + 1)), ds[i + 1], xs[i + 1]));
        let pre = xs.subrange(0, i + 1);
        assert(pre[0] == xs[0] && pre.drop_first() =~= x2.subrange(0, i));
    }
}

/// A CHAIN'S PI CODE is a member of the telescope and a type.
pub proof fn pichain_mem(sig: Sig, tds: Seq<ExprSpec>, body: ExprSpec, rho: Env, ds: Seq<Cpt>, xs: Seq<Cpt>, c: Cpt)
    requires
        chain_ok(sig, tds, rho, ds, xs),
        mem(sig, body, exts(rho, xs), c),
        typed(c, Cpt::U),
    ensures
        mem(sig, crate::rec_canon::binds(BinderKind::Pi, tds, body), rho, pichain(ds, xs, c)),
        typed(pichain(ds, xs, c), Cpt::U),
    decreases tds.len(),
{
    if tds.len() == 0 {
        assert(xs =~= Seq::<Cpt>::empty());
        return;
    }
    chain_ok_rest(sig, tds, rho, ds, xs);
    let (t2, d2, x2) = (tds.drop_first(), ds.drop_first(), xs.drop_first());
    let rho2 = ext(rho, xs[0]);
    pichain_mem(sig, t2, body, rho2, d2, x2, c);
    let inner = pichain(d2, x2, c);
    let (d0, x0) = (ds[0], xs[0]);
    let pc = Cpt::Pi(Box::new(d0), seq![(x0, inner)]);
    assert(pichain(ds, xs, c) == pc);
    typed_wf(d0, Cpt::U);
    typed_wf(x0, d0);
    typed_wf(inner, Cpt::U);
    compat_refl(inner);
    assert(seq![(x0, inner)][0] == (x0, inner));
    assert(fun_ok(seq![(x0, inner)]));
    assert(wf(pc));
    // typed
    let n = ht(pc) + cstage(d0, Cpt::U) + cstage(x0, d0) + cstage(inner, Cpt::U) + 2;
    typed_up(d0, Cpt::U, (n - 1) as nat);
    typed_up(x0, d0, (n - 1) as nat);
    typed_up(inner, Cpt::U, (n - 1) as nat);
    assert(stg(n, pc));
    assert(has_type(n, pc, Cpt::U));
    typed_down(pc, Cpt::U, n);
    // a member: its own generator
    reveal(mem);
    let wa = choose|w: Wit| #[trigger] mem_w(sig, tds[0], rho, d0, w);
    let wi = choose|w: Wit| #[trigger] mem_w(sig, crate::rec_canon::binds(BinderKind::Pi, t2, body), rho2, inner, w);
    le_refl(pc);
    let ws = seq![wi];
    assert(gsteps(pc)[0] == (x0, inner) && ws[0] == wi);
    assert(entries_ok(sig, crate::rec_canon::binds(BinderKind::Pi, t2, body), rho, d0, pc, ws));
    assert(crate::rec_canon::binds(BinderKind::Pi, tds, body)
        == ExprSpec::Bind(BinderKind::Pi, Box::new(tds[0]), Box::new(crate::rec_canon::binds(BinderKind::Pi, t2, body))));
    assert(mem_w(sig, crate::rec_canon::binds(BinderKind::Pi, tds, body), rho, pc, Wit::Gen(d0, pc, Box::new(wa), ws)));
}

/// A CHAIN'S LAMBDA is typed at the chain's Pi code.
pub proof fn lamchain_typed(ds: Seq<Cpt>, xs: Seq<Cpt>, c: Cpt, out: Cpt)
    requires
        ds.len() == xs.len(),
        forall|i: int| 0 <= i < ds.len() ==> #[trigger] typed(xs[i], ds[i]),
        typed(pichain(ds, xs, c), Cpt::U),
        typed(out, c),
    ensures
        typed(lamchain(xs, out), pichain(ds, xs, c)),
        (lamchain(xs, out) is Bot) == (out is Bot),
    decreases ds.len(),
{
    let p = pichain(ds, xs, c);
    if ds.len() == 0 {
        return;
    }
    let (d2, x2) = (ds.drop_first(), xs.drop_first());
    let (d0, x0) = (ds[0], xs[0]);
    let pi2 = pichain(d2, x2, c);
    assert(p == Cpt::Pi(Box::new(d0), seq![(x0, pi2)]));
    let n0 = cstage(p, Cpt::U);
    typed_up(p, Cpt::U, n0);
    let g0 = seq![(x0, pi2)];
    assert(g0[0] == (x0, pi2));
    assert(has_type((n0 - 1) as nat, g0[0].0, d0) && has_type((n0 - 1) as nat, g0[0].1, Cpt::U));
    typed_down(pi2, Cpt::U, (n0 - 1) as nat);
    assert forall|i: int| 0 <= i < d2.len() implies #[trigger] typed(x2[i], d2[i]) by {
        assert(typed(xs[i + 1], ds[i + 1]));
    }
    lamchain_typed(d2, x2, c, out);
    let l2 = lamchain(x2, out);
    if out is Bot {
        crate::dom_tele::bot_typed(p);
        return;
    }
    let lc = Cpt::Lam(seq![(x0, l2)]);
    assert(lamchain(xs, out) == lc);
    assert(typed(x0, d0));
    typed_wf(x0, d0);
    typed_wf(l2, pi2);
    typed_wf(p, Cpt::U);
    compat_refl(l2);
    let f0 = seq![(x0, l2)];
    assert(f0[0] == (x0, l2));
    assert(fun_ok(f0));
    assert(!(f0[0].1 is Bot));
    assert(forall|k: int| 0 <= k < f0.len() ==> wf(#[trigger] f0[k].0) && wf(f0[k].1));
    assert(wf(lc));
    // the entry's output, at the codomain above the chain's next Pi
    assert(steps(p, false).contains((x0, pi2)));
    entry_appk(p, (x0, pi2), false);
    let cd = cod(p, x0);
    crate::dom_sound::cod_typed_at(p, x0, n0);
    typed_down(cd, Cpt::U, (n0 - 1) as nat);
    typed_weak(l2, pi2, cd);
    parts_lower(p);
    assert(has_type((n0 - 1) as nat, d0, Cpt::U));
    typed_down(d0, Cpt::U, (n0 - 1) as nat);
    let n = ht(lc) + ht(p) + cstage(d0, Cpt::U) + cstage(x0, d0) + cstage(l2, cd) + 3;
    typed_up(d0, Cpt::U, (n - 1) as nat);
    typed_up(x0, d0, (n - 1) as nat);
    typed_up(l2, cd, (n - 1) as nat);
    assert(stg(n, lc) && stg(n, p));
    assert(has_type(n, lc, p));
    typed_down(lc, p, n);
}

/// ALONG A CHAIN, each domain is typed in its prefix context, where the
/// chain's environment fits.
pub proof fn tele_prefix(sig: Sig, g: Ctx, tds: Seq<ExprSpec>, body: ExprSpec, l: LevelSpec, rho: Env,
    ds: Seq<Cpt>, xs: Seq<Cpt>, i: int) -> (li: LevelSpec)
    requires
        derivable(sig, eq(g, crate::rec_canon::binds(BinderKind::Pi, tds, body), crate::rec_canon::binds(BinderKind::Pi, tds, body), sort(l))),
        fits_env(sig, g, rho),
        chain_ok(sig, tds, rho, ds, xs),
        0 <= i < tds.len(),
    ensures
        typ(sig, g + tds.subrange(0, i), tds[i], li),
        fits_env(sig, g + tds.subrange(0, i), exts(rho, xs.subrange(0, i))),
    decreases i,
{
    let (ta, rest) = (tds[0], tds.drop_first());
    let tb = crate::rec_canon::binds(BinderKind::Pi, rest, body);
    assert(crate::rec_canon::binds(BinderKind::Pi, tds, body) == pi(ta, tb));
    let dd = crate::ti_sub::get(sig, eq(g, pi(ta, tb), pi(ta, tb), sort(l)));
    gen(sig, dd);
    let (l1, l2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(ta, tb, l1, l2)
        && typ(sig, g, ta, l1) && typ(sig, g.push(ta), tb, l2) && crate::ti_chain::tchain(sig, g, sort(l), sort(crate::ti_syntax::imax(l1, l2)));
    if i == 0 {
        assert(g + tds.subrange(0, 0) =~= g);
        assert(xs.subrange(0, 0) =~= Seq::<Cpt>::empty());
        return l1;
    }
    chain_ok_rest(sig, tds, rho, ds, xs);
    fits_ext(sig, g, rho, ta, ds[0], xs[0]);
    let li = tele_prefix(sig, g.push(ta), rest, body, l2, ext(rho, xs[0]), ds.drop_first(), xs.drop_first(), i - 1);
    assert(g.push(ta) + rest.subrange(0, i - 1) =~= g + tds.subrange(0, i));
    assert(rest[i - 1] == tds[i]);
    let pre = xs.subrange(0, i);
    assert(pre[0] == xs[0] && pre.drop_first() =~= xs.drop_first().subrange(0, i - 1));
    li
}

/// A chain's lambda, applied along its chain, gives at least its output.
pub proof fn lamchain_apps(xs: Seq<Cpt>, out: Cpt)
    requires
        crate::dom_code::aw(xs),
        wf(lamchain(xs, out)),
    ensures
        le(out, crate::dom_rec::apps(lamchain(xs, out), xs)),
    decreases xs.len(),
{
    if xs.len() == 0 {
        assert(crate::dom_rec::apps(out, xs) == out);
        le_refl(out);
        return;
    }
    if out is Bot {
        return;
    }
    let (x0, x2) = (xs[0], xs.drop_first());
    let l2 = lamchain(x2, out);
    let lc = Cpt::Lam(seq![(x0, l2)]);
    assert(lamchain(xs, out) == lc);
    assert(seq![(x0, l2)][0] == (x0, l2));
    assert(steps(lc, true).contains((x0, l2)));
    entry_appk(lc, (x0, l2), true);
    assert(wf(l2));
    assert forall|i: int| 0 <= i < x2.len() implies #[trigger] wf(x2[i]) by {
        assert(x2[i] == xs[i + 1]);
    }
    lamchain_apps(x2, out);
    apps_front(lc, xs);
    appk_wf(lc, x0, true);
    assert forall|i: int| 0 <= i < x2.len() implies le(#[trigger] x2[i], x2[i]) by {
        le_refl(x2[i]);
    }
    crate::dom_rec::apps_mono(l2, app(lc, x0), x2, x2);
    le_trans(out, crate::dom_rec::apps(l2, x2), crate::dom_rec::apps(app(lc, x0), x2));
}

} // verus!
