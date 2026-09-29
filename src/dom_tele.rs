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
use crate::dom_sound::{fits_env, fits_ext, dfit, body_jc, cod_in_body, sound, sound_ok, typed_basic, sel_below_gen};
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
pub proof fn pi_body_jc(ss: Sig, sig: Sig, g: Ctx, ta: ExprSpec, tb: ExprSpec, l2: LevelSpec, rho: Env)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        typ(ss, g.push(ta), tb, l2),
        fits_env(sig, g, rho),
    ensures
        body_jc(sig, ta, tb, rho),
{
    let d = crate::ti_sub::get(ss, eq(g.push(ta), tb, tb, sort(l2)));
    assert forall|x: Cpt, a: Cpt| #[trigger] dfit(sig, ta, rho, a, x) implies jc(sig, tb, ext(rho, x)) by {
        fits_ext(sig, g, rho, ta, a, x);
        crate::dom_sound::oracle_use(ss, sig, d, ext(rho, x));
    }
}

/// ONE STEP: the argument's projection, the codomain there, and the
/// extended environment.
pub proof fn tele_step(ss: Sig, sig: Sig, g: Ctx, ta: ExprSpec, tb: ExprSpec, l: LevelSpec, rho: Env, d: Cpt, u: Cpt, w: Cpt)
    -> (r: (Cpt, Cpt, LevelSpec, Cpt))
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        derivable(ss, eq(g, pi(ta, tb), pi(ta, tb), sort(l))),
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
        typ(ss, g.push(ta), tb, r.2),
        dfit(sig, ta, rho, r.3, r.0),
{
    let dd = crate::ti_sub::get(ss, eq(g, pi(ta, tb), pi(ta, tb), sort(l)));
    gen(ss, dd);
    let (l1, l2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(ta, tb, l1, l2)
        && typ(ss, g, ta, l1) && typ(ss, g.push(ta), tb, l2) && crate::ti_chain::tchain(ss, g, sort(l), sort(crate::ti_syntax::imax(l1, l2)));
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
    pi_body_jc(ss, sig, g, ta, tb, l2, rho);
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
pub proof fn tele_apps(ss: Sig, sig: Sig, g: Ctx, ds: Seq<ExprSpec>, body: ExprSpec, l: LevelSpec, rho: Env, d: Cpt, u: Cpt, ws: Seq<Cpt>)
    -> (r: (Seq<Cpt>, Cpt, LevelSpec, Seq<Cpt>))
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        ws.len() == ds.len(),
        derivable(ss, eq(g, crate::rec_canon::binds(BinderKind::Pi, ds, body), crate::rec_canon::binds(BinderKind::Pi, ds, body), sort(l))),
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
        typ(ss, g + ds, body, r.2),
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
    let (w2, d2, l2, a0) = tele_step(ss, sig, g, ta, tb, l, rho, d, u, ws[0]);
    assert(wf(ws[0]));
    let u2 = app(u, ws[0]);
    let wr = ws.drop_first();
    assert forall|i: int| 0 <= i < wr.len() implies #[trigger] wf(wr[i]) by {
        assert(wr[i] == ws[i + 1]);
    }
    let (ws2r, e, l3, dsr) = tele_apps(ss, sig, g.push(ta), rest, body, l2, ext(rho, w2), d2, u2, wr);
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
pub proof fn tele_prefix(ss: Sig, sig: Sig, g: Ctx, tds: Seq<ExprSpec>, body: ExprSpec, l: LevelSpec, rho: Env,
    ds: Seq<Cpt>, xs: Seq<Cpt>, i: int) -> (li: LevelSpec)
    requires
        derivable(ss, eq(g, crate::rec_canon::binds(BinderKind::Pi, tds, body), crate::rec_canon::binds(BinderKind::Pi, tds, body), sort(l))),
        fits_env(sig, g, rho),
        chain_ok(sig, tds, rho, ds, xs),
        0 <= i < tds.len(),
    ensures
        typ(ss, g + tds.subrange(0, i), tds[i], li),
        fits_env(sig, g + tds.subrange(0, i), exts(rho, xs.subrange(0, i))),
    decreases i,
{
    let (ta, rest) = (tds[0], tds.drop_first());
    let tb = crate::rec_canon::binds(BinderKind::Pi, rest, body);
    assert(crate::rec_canon::binds(BinderKind::Pi, tds, body) == pi(ta, tb));
    let dd = crate::ti_sub::get(ss, eq(g, pi(ta, tb), pi(ta, tb), sort(l)));
    gen(ss, dd);
    let (l1, l2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(ta, tb, l1, l2)
        && typ(ss, g, ta, l1) && typ(ss, g.push(ta), tb, l2) && crate::ti_chain::tchain(ss, g, sort(l), sort(crate::ti_syntax::imax(l1, l2)));
    if i == 0 {
        assert(g + tds.subrange(0, 0) =~= g);
        assert(xs.subrange(0, 0) =~= Seq::<Cpt>::empty());
        return l1;
    }
    chain_ok_rest(sig, tds, rho, ds, xs);
    fits_ext(sig, g, rho, ta, ds[0], xs[0]);
    let li = tele_prefix(ss, sig, g.push(ta), rest, body, l2, ext(rho, xs[0]), ds.drop_first(), xs.drop_first(), i - 1);
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

/// A CHAIN'S LAMBDA is a member of a lambda telescope whose body holds its
/// output.
pub proof fn lamchain_mem(sig: Sig, tds: Seq<ExprSpec>, body: ExprSpec, rho: Env, ds: Seq<Cpt>, xs: Seq<Cpt>, out: Cpt)
    requires
        chain_ok(sig, tds, rho, ds, xs),
        mem(sig, body, exts(rho, xs), out),
        wf(out),
    ensures
        mem(sig, crate::rec_canon::binds(BinderKind::Lam, tds, body), rho, lamchain(xs, out)),
        wf(lamchain(xs, out)),
        (lamchain(xs, out) is Bot) == (out is Bot),
    decreases tds.len(),
{
    reveal(mem);
    if tds.len() == 0 {
        assert(xs =~= Seq::<Cpt>::empty());
        return;
    }
    let t = crate::rec_canon::binds(BinderKind::Lam, tds, body);
    if out is Bot {
        mem_bot(sig, t, rho);
        return;
    }
    chain_ok_rest(sig, tds, rho, ds, xs);
    let (t2, d2, x2) = (tds.drop_first(), ds.drop_first(), xs.drop_first());
    let rho2 = ext(rho, xs[0]);
    lamchain_mem(sig, t2, body, rho2, d2, x2, out);
    let inner = lamchain(x2, out);
    let (d0, x0) = (ds[0], xs[0]);
    let lc = Cpt::Lam(seq![(x0, inner)]);
    assert(lamchain(xs, out) == lc);
    typed_wf(x0, d0);
    compat_refl(inner);
    let f0 = seq![(x0, inner)];
    assert(f0[0] == (x0, inner));
    assert(fun_ok(f0));
    assert(!(f0[0].1 is Bot));
    assert(wf(lc));
    let wa = choose|w: Wit| #[trigger] mem_w(sig, tds[0], rho, d0, w);
    let wi = choose|w: Wit| #[trigger] mem_w(sig, crate::rec_canon::binds(BinderKind::Lam, t2, body), rho2, inner, w);
    le_refl(lc);
    let ws = seq![wi];
    assert(gsteps(lc)[0] == (x0, inner) && ws[0] == wi);
    assert(entries_ok(sig, crate::rec_canon::binds(BinderKind::Lam, t2, body), rho, d0, lc, ws));
    assert(t == ExprSpec::Bind(BinderKind::Lam, Box::new(tds[0]), Box::new(crate::rec_canon::binds(BinderKind::Lam, t2, body))));
    assert(mem_w(sig, t, rho, lc, Wit::Gen(d0, lc, Box::new(wa), ws)));
}

/// ONE STEP AT A FITTING ARGUMENT: no projection needed.
pub proof fn tele_step_fit(ss: Sig, sig: Sig, g: Ctx, ta: ExprSpec, tb: ExprSpec, l: LevelSpec, rho: Env, d: Cpt, u: Cpt, w: Cpt, ax: Cpt)
    -> (l2: LevelSpec)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        derivable(ss, eq(g, pi(ta, tb), pi(ta, tb), sort(l))),
        fits_env(sig, g, rho),
        mem(sig, pi(ta, tb), rho, d),
        typed(d, Cpt::U),
        typed(u, d),
        dfit(sig, ta, rho, ax, w),
    ensures
        typed(app(u, w), cod(d, w)),
        typed(cod(d, w), Cpt::U),
        mem(sig, tb, ext(rho, w), cod(d, w)),
        fits_env(sig, g.push(ta), ext(rho, w)),
        typ(ss, g.push(ta), tb, l2),
{
    let dd = crate::ti_sub::get(ss, eq(g, pi(ta, tb), pi(ta, tb), sort(l)));
    gen(ss, dd);
    let (l1, l2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(ta, tb, l1, l2)
        && typ(ss, g, ta, l1) && typ(ss, g.push(ta), tb, l2) && crate::ti_chain::tchain(ss, g, sort(l), sort(crate::ti_syntax::imax(l1, l2)));
    typed_wf(u, d);
    typed_wf(d, Cpt::U);
    typed_wf(w, ax);
    typed_basic();
    fits_ext(sig, g, rho, ta, ax, w);
    reveal(mem);
    if d is Bot {
        typed_up(u, d, cstage(u, d));
        ty_of_bot(cstage(u, d), u);
        assert(cod(d, w) == Cpt::Bot);
        assert(app(u, w) == Cpt::Bot);
        mem_bot(sig, tb, ext(rho, w));
        return l2;
    }
    let wit = choose|wit: Wit| #[trigger] mem_w(sig, pi(ta, tb), rho, d, wit);
    assert(pi(ta, tb) == ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb)));
    let gen_ = match wit {
        Wit::Gen(_, gen_, _, _) => gen_,
        _ => {
            assert(false);
            Cpt::Bot
        },
    };
    head_le(d, gen_);
    pi_body_jc(ss, sig, g, ta, tb, l2, rho);
    cod_in_body(sig, ta, tb, rho, d, w, ax);
    let n = cstage(u, d) + cstage(d, Cpt::U) + 2;
    typed_up(u, d, n);
    typed_up(d, Cpt::U, n);
    crate::dom_proj::app_typed_at(n, u, d, w);
    typed_down(app(u, w), cod(d, w), (n - 1) as nat);
    typed_down(cod(d, w), Cpt::U, (n - 1) as nat);
    l2
}

/// THROUGH A TELESCOPE, MIXED: arguments marked `fit` are typed at the
/// given domain members whatever the earlier values, and pass unchanged;
/// the others are projected.
pub proof fn tele_mix(ss: Sig, sig: Sig, g: Ctx, ds: Seq<ExprSpec>, body: ExprSpec, l: LevelSpec, rho: Env, d: Cpt, u: Cpt,
    ws: Seq<Cpt>, fit: Seq<bool>, axs: Seq<Cpt>) -> (r: (Seq<Cpt>, Seq<Cpt>))
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        ws.len() == ds.len(),
        fit.len() == ds.len(),
        axs.len() == ds.len(),
        derivable(ss, eq(g, crate::rec_canon::binds(BinderKind::Pi, ds, body), crate::rec_canon::binds(BinderKind::Pi, ds, body), sort(l))),
        fits_env(sig, g, rho),
        mem(sig, crate::rec_canon::binds(BinderKind::Pi, ds, body), rho, d),
        typed(d, Cpt::U),
        typed(u, d),
        crate::dom_code::aw(ws),
        forall|i: int, vals: Seq<Cpt>| 0 <= i < ds.len() && fit[i] && vals.len() == i
            ==> #[trigger] dfit(sig, ds[i], exts(rho, vals), axs[i], ws[i]),
    ensures
        r.0.len() == ws.len(),
        crate::dom_sem::pre_le(r.0, ws),
        crate::dom_code::aw(r.0),
        crate::dom_rec::apps(u, ws) == crate::dom_rec::apps(u, r.0),
        chain_ok(sig, ds, rho, r.1, r.0),
        forall|i: int| 0 <= i < ds.len() && fit[i] ==> #[trigger] r.0[i] == ws[i],
    decreases ds.len(),
{
    if ds.len() == 0 {
        assert(chain_ok(sig, ds, rho, Seq::empty(), Seq::empty()));
        return (Seq::empty(), Seq::empty());
    }
    let (ta, rest) = (ds[0], ds.drop_first());
    let tb = crate::rec_canon::binds(BinderKind::Pi, rest, body);
    assert(crate::rec_canon::binds(BinderKind::Pi, ds, body) == pi(ta, tb));
    let w0 = ws[0];
    assert(wf(w0));
    let (x0, d2, l2, a0) = if fit[0] {
        assert(dfit(sig, ds[0], exts(rho, Seq::<Cpt>::empty()), axs[0], ws[0]));
        let l2 = tele_step_fit(ss, sig, g, ta, tb, l, rho, d, u, w0, axs[0]);
        le_refl(w0);
        (w0, cod(d, w0), l2, axs[0])
    } else {
        let (w2, dd, l2, a0) = tele_step(ss, sig, g, ta, tb, l, rho, d, u, w0);
        (w2, dd, l2, a0)
    };
    let u2 = app(u, w0);
    let wr = ws.drop_first();
    assert forall|i: int| 0 <= i < wr.len() implies #[trigger] wf(wr[i]) by {
        assert(wr[i] == ws[i + 1]);
    }
    let (fr, ar) = (fit.drop_first(), axs.drop_first());
    let rho2 = ext(rho, x0);
    assert forall|i: int, vals: Seq<Cpt>| 0 <= i < rest.len() && fr[i] && vals.len() == i
        implies #[trigger] dfit(sig, rest[i], exts(rho2, vals), ar[i], wr[i]) by {
        let v2 = seq![x0] + vals;
        assert(v2[0] == x0 && v2.drop_first() =~= vals);
        assert(dfit(sig, ds[i + 1], exts(rho, v2), axs[i + 1], ws[i + 1]));
    }
    let (xr, dr) = tele_mix(ss, sig, g.push(ta), rest, body, l2, rho2, d2, u2, wr, fr, ar);
    let xs2 = seq![x0] + xr;
    let dcs = seq![a0] + dr;
    assert(xs2[0] == x0 && xs2.drop_first() =~= xr);
    apps_front(u, ws);
    apps_front(u, xs2);
    assert forall|i: int| 0 <= i < xs2.len() implies le(#[trigger] xs2[i], ws[i]) && wf(xs2[i]) by {
        if i > 0 {
            assert(xs2[i] == xr[i - 1] && ws[i] == wr[i - 1]);
        }
    }
    assert forall|i: int| 0 <= i < xs2.len() implies #[trigger] wf(xs2[i]) by {
        assert(le(xs2[i], ws[i]) && wf(xs2[i]));
    }
    assert forall|i: int| 0 <= i < ds.len() implies #[trigger] dfit(sig, ds[i], exts(rho, xs2.subrange(0, i)), dcs[i], xs2[i]) by {
        if i == 0 {
            assert(xs2.subrange(0, 0) =~= Seq::<Cpt>::empty());
        } else {
            assert(dfit(sig, rest[i - 1], exts(rho2, xr.subrange(0, i - 1)), dr[i - 1], xr[i - 1]));
            let pre = xs2.subrange(0, i);
            assert(pre[0] == x0 && pre.drop_first() =~= xr.subrange(0, i - 1));
            assert(rest[i - 1] == ds[i] && dcs[i] == dr[i - 1] && xs2[i] == xr[i - 1]);
        }
    }
    assert forall|i: int| 0 <= i < ds.len() && fit[i] implies #[trigger] xs2[i] == ws[i] by {
        if i > 0 {
            assert(fr[i - 1] == fit[i]);
            assert(xr[i - 1] == wr[i - 1]);
        }
    }
    (xs2, dcs)
}

/// ONE LAMBDA STEP: a member of a derivable lambda's denotation applied to
/// any argument lies below a member of the body's denotation at the join
/// of the generator's inputs below the argument, which is typed at the
/// domain member.
#[verifier::spinoff_prover]
pub proof fn lam_step(ss: Sig, sig: Sig, g: Ctx, ta: ExprSpec, b: ExprSpec, t: ExprSpec, rho: Env, lu: Cpt, w: Cpt)
    -> (r: (Cpt, Cpt, Cpt, ExprSpec))
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        derivable(ss, eq(g, ExprSpec::Bind(BinderKind::Lam, Box::new(ta), Box::new(b)), ExprSpec::Bind(BinderKind::Lam, Box::new(ta), Box::new(b)), t)),
        fits_env(sig, g, rho),
        mem(sig, ExprSpec::Bind(BinderKind::Lam, Box::new(ta), Box::new(b)), rho, lu),
        wf(w),
    ensures
        wf(r.0),
        le(r.0, w),
        dfit(sig, ta, rho, r.2, r.0),
        le(app(lu, w), r.1),
        mem(sig, b, ext(rho, r.0), r.1),
        fits_env(sig, g.push(ta), ext(rho, r.0)),
        derivable(ss, eq(g.push(ta), b, b, r.3)),
{
    let lm = ExprSpec::Bind(BinderKind::Lam, Box::new(ta), Box::new(b));
    let dd = crate::ti_sub::get(ss, eq(g, lm, lm, t));
    gen(ss, dd);
    let (bt, l1, l2) = choose|bt: ExprSpec, l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(bt, b, l1, l2)
        && typ(ss, g, ta, l1) && derivable(ss, eq(g.push(ta), b, b, bt)) && typ(ss, g.push(ta), bt, l2)
        && crate::ti_chain::tchain(ss, g, t, pi(ta, bt));
    let db = crate::ti_sub::get(ss, eq(g.push(ta), b, b, bt));
    assert forall|x: Cpt, a: Cpt| #[trigger] dfit(sig, ta, rho, a, x) implies jc(sig, b, ext(rho, x)) by {
        fits_ext(sig, g, rho, ta, a, x);
        crate::dom_sound::oracle_use(ss, sig, db, ext(rho, x));
    }
    typed_basic();
    reveal(mem);
    let wl = choose|wt: Wit| #[trigger] mem_w(sig, lm, rho, lu, wt);
    mem_wf(sig, lm, rho, lu, wl);
    if lu is Bot {
        mem_bot(sig, ta, rho);
        mem_bot(sig, b, ext(rho, Cpt::Bot));
        fits_ext(sig, g, rho, ta, Cpt::Bot, Cpt::Bot);
        le_refl(Cpt::Bot);
        assert(app(lu, w) == Cpt::Bot);
        return (Cpt::Bot, Cpt::Bot, Cpt::Bot, bt);
    }
    let (a, gen_, ws) = match wl {
        Wit::Gen(a, gen_, wa, ws) => {
            assert(mem_w(sig, ta, rho, a, *wa));
            (a, gen_, ws)
        },
        _ => {
            assert(false);
            (Cpt::Bot, Cpt::Bot, Seq::empty())
        },
    };
    assert(le(lu, gen_) && gen_ is Lam && typed(a, Cpt::U) && mem(sig, ta, rho, a) && entries_ok(sig, b, rho, a, gen_, ws));
    let f = gen_->Lam_0;
    parts_lower(gen_);
    // the inputs below the argument, joined: typed at the domain member
    let s = crate::dom_proj::ins_sel(f, w, f.len() as int);
    let hb = ht(gen_);
    assert forall|y: Cpt| #[trigger] s.contains(y) implies wf(y) && typed(y, a) && le(y, w) && ht(y) <= hb by {
        crate::dom_proj::ins_sel_mem(f, w, f.len() as int, y);
        let i = choose|i: int| 0 <= i < f.len() && #[trigger] f[i].0 == y && le(f[i].0, w);
        assert(gsteps(gen_)[i] == f[i]);
        assert(typed(f[i].0, a));
        typed_wf(y, a);
    }
    assert forall|y: Cpt, z: Cpt| #[trigger] s.contains(y) && #[trigger] s.contains(z) implies compat(y, z) by {
        ub_compat(y, z, w);
    }
    assert(pw(s));
    pw_coh(s, hb);
    assert(fits(s, hb)) by {
        assert forall|i: int| 0 <= i < s.len() implies ht(#[trigger] s[i]) <= hb by {
            assert(s.contains(s[i]));
        }
    }
    let x = jall(s);
    jall_lub(s, hb, w);
    typed_wf(a, Cpt::U);
    let n = hb + ht(a) + cstage(a, Cpt::U) + 2;
    typed_up(a, Cpt::U, n);
    assert forall|y: Cpt| #[trigger] s.contains(y) implies has_type(n, y, a) by {
        typed_up(y, a, n);
    }
    ty_jall(n, s, s.len() as int, a);
    typed_down(x, a, n);
    typed_wf(x, a);
    // the selected outputs, in the body at the joined input
    let ev = ext(rho, x);
    assert(dfit(sig, ta, rho, a, x));
    assert(jc(sig, b, ev));
    let tg = seq![gen_];
    assert(tg[0] == gen_);
    let sm = selk(tg, w, ht(gen_), true);
    assert forall|y: Cpt| #[trigger] sm.contains(y) implies mem(sig, b, ev, y) by {
        sel_lam_mem(tg, w, ht(gen_), 1, y);
        let k = choose|k: int| 0 <= k < f.len() && #[trigger] f[k].1 == y && le(f[k].0, w);
        assert(gsteps(gen_)[k] == f[k]);
        assert(mem_w(sig, b, ext(rho, f[k].0), y, ws[k]));
        crate::dom_proj::ins_sel_mem(f, w, f.len() as int, f[k].0);
        assert(s.contains(f[k].0));
        jall_ub(s, hb, f[k].0);
        assert forall|q: nat| #[trigger] le(ext(rho, f[k].0)(q), ev(q)) by {
            if q > 0 {
                le_refl(rho((q - 1) as nat));
            }
        }
        mem_env_mono(sig, b, ext(rho, f[k].0), ev, y, ws[k]);
    }
    assert forall|y: Cpt| #[trigger] sm.contains(y) implies wf(y) by {
        let wy = choose|w3: Wit| #[trigger] mem_w(sig, b, ev, y, w3);
        mem_wf(sig, b, ev, y, wy);
    }
    assert forall|y: Cpt, z: Cpt| #[trigger] sm.contains(y) && #[trigger] sm.contains(z) implies compat(y, z) by {
        jc_elim(sig, b, ev, y, z);
    }
    assert forall|i: int| 0 <= i < sm.len() implies #[trigger] mem(sig, b, ev, sm[i]) by {
        assert(sm.contains(sm[i]));
    }
    jall_mem(sig, b, ev, sm, sm.len() as int);
    head_le(lu, gen_);
    sel_below_gen(lu, gen_, w, true);
    fits_ext(sig, g, rho, ta, a, x);
    (x, jall(sm), a, bt)
}

/// THROUGH A LAMBDA TELESCOPE: a member applied to any arguments lies below
/// a member of the body under the environment of typed inputs below them.
pub proof fn lam_apps(ss: Sig, sig: Sig, g: Ctx, tds: Seq<ExprSpec>, body: ExprSpec, t: ExprSpec, rho: Env, lu: Cpt, ws: Seq<Cpt>)
    -> (r: (Seq<Cpt>, Seq<Cpt>, Cpt))
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        ws.len() == tds.len(),
        derivable(ss, eq(g, crate::rec_canon::binds(BinderKind::Lam, tds, body), crate::rec_canon::binds(BinderKind::Lam, tds, body), t)),
        fits_env(sig, g, rho),
        mem(sig, crate::rec_canon::binds(BinderKind::Lam, tds, body), rho, lu),
        crate::dom_code::aw(ws),
    ensures
        r.0.len() == ws.len(),
        crate::dom_sem::pre_le(r.0, ws),
        crate::dom_code::aw(r.0),
        chain_ok(sig, tds, rho, r.1, r.0),
        le(crate::dom_rec::apps(lu, ws), r.2),
        mem(sig, body, exts(rho, r.0), r.2),
    decreases tds.len(),
{
    reveal(mem);
    let lb = crate::rec_canon::binds(BinderKind::Lam, tds, body);
    let wl = choose|wt: Wit| #[trigger] mem_w(sig, lb, rho, lu, wt);
    mem_wf(sig, lb, rho, lu, wl);
    if tds.len() == 0 {
        assert(crate::dom_rec::apps(lu, ws) == lu);
        le_refl(lu);
        assert(chain_ok(sig, tds, rho, Seq::empty(), Seq::empty()));
        return (Seq::empty(), Seq::empty(), lu);
    }
    let (ta, rest) = (tds[0], tds.drop_first());
    let tb = crate::rec_canon::binds(BinderKind::Lam, rest, body);
    assert(lb == ExprSpec::Bind(BinderKind::Lam, Box::new(ta), Box::new(tb)));
    let w0 = ws[0];
    assert(wf(w0));
    let (x0, y0, a0, bt) = lam_step(ss, sig, g, ta, tb, t, rho, lu, w0);
    let wr = ws.drop_first();
    assert forall|i: int| 0 <= i < wr.len() implies #[trigger] wf(wr[i]) by {
        assert(wr[i] == ws[i + 1]);
    }
    let (xr, dr, y) = lam_apps(ss, sig, g.push(ta), rest, body, bt, ext(rho, x0), y0, wr);
    let xs = seq![x0] + xr;
    let dcs = seq![a0] + dr;
    assert(xs[0] == x0 && xs.drop_first() =~= xr);
    apps_front(lu, ws);
    let wy = choose|w3: Wit| #[trigger] mem_w(sig, tb, ext(rho, x0), y0, w3);
    mem_wf(sig, tb, ext(rho, x0), y0, wy);
    if lu is Lam {
        appk_wf(lu, w0, true);
    }
    assert forall|i: int| 0 <= i < wr.len() implies le(#[trigger] wr[i], wr[i]) by {
        le_refl(wr[i]);
    }
    crate::dom_rec::apps_mono(app(lu, w0), y0, wr, wr);
    le_trans(crate::dom_rec::apps(lu, ws), crate::dom_rec::apps(y0, wr), y);
    assert forall|i: int| 0 <= i < xs.len() implies le(#[trigger] xs[i], ws[i]) && wf(xs[i]) by {
        if i > 0 {
            assert(xs[i] == xr[i - 1] && ws[i] == wr[i - 1]);
        }
    }
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] wf(xs[i]) by {
        assert(le(xs[i], ws[i]) && wf(xs[i]));
    }
    assert forall|i: int| 0 <= i < tds.len() implies #[trigger] dfit(sig, tds[i], exts(rho, xs.subrange(0, i)), dcs[i], xs[i]) by {
        if i == 0 {
            assert(xs.subrange(0, 0) =~= Seq::<Cpt>::empty());
        } else {
            assert(dfit(sig, rest[i - 1], exts(ext(rho, x0), xr.subrange(0, i - 1)), dr[i - 1], xr[i - 1]));
            let pre = xs.subrange(0, i);
            assert(pre[0] == x0 && pre.drop_first() =~= xr.subrange(0, i - 1));
            assert(rest[i - 1] == tds[i] && dcs[i] == dr[i - 1] && xs[i] == xr[i - 1]);
        }
    }
    (xs, dcs, y)
}

/// THE REST OF A DERIVABLE TELESCOPE is derivable in the prefix context.
pub proof fn tele_rest(sig: Sig, g: Ctx, tds: Seq<ExprSpec>, body: ExprSpec, l: LevelSpec, i: int) -> (li: LevelSpec)
    requires
        derivable(sig, eq(g, crate::rec_canon::binds(BinderKind::Pi, tds, body), crate::rec_canon::binds(BinderKind::Pi, tds, body), sort(l))),
        0 <= i <= tds.len(),
    ensures
        derivable(sig, eq(g + tds.subrange(0, i),
            crate::rec_canon::binds(BinderKind::Pi, tds.subrange(i, tds.len() as int), body),
            crate::rec_canon::binds(BinderKind::Pi, tds.subrange(i, tds.len() as int), body), sort(li))),
    decreases i,
{
    if i == 0 {
        assert(g + tds.subrange(0, 0) =~= g);
        assert(tds.subrange(0, tds.len() as int) =~= tds);
        return l;
    }
    let (ta, rest) = (tds[0], tds.drop_first());
    let tb = crate::rec_canon::binds(BinderKind::Pi, rest, body);
    assert(crate::rec_canon::binds(BinderKind::Pi, tds, body) == pi(ta, tb));
    let dd = crate::ti_sub::get(sig, eq(g, pi(ta, tb), pi(ta, tb), sort(l)));
    gen(sig, dd);
    let (l1, l2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(ta, tb, l1, l2)
        && typ(sig, g, ta, l1) && typ(sig, g.push(ta), tb, l2) && crate::ti_chain::tchain(sig, g, sort(l), sort(crate::ti_syntax::imax(l1, l2)));
    let li = tele_rest(sig, g.push(ta), rest, body, l2, i - 1);
    assert(g.push(ta) + rest.subrange(0, i - 1) =~= g + tds.subrange(0, i));
    assert(rest.subrange(i - 1, rest.len() as int) =~= tds.subrange(i, tds.len() as int));
    li
}

/// A Pi member's domain is in the domain's denotation.
pub proof fn pi_dom_mem(sig: Sig, ta: ExprSpec, tb: ExprSpec, rho: Env, d: Cpt)
    requires
        mem(sig, pi(ta, tb), rho, d),
        d is Pi,
        wf(d),
    ensures
        mem(sig, ta, rho, *d->Pi_0),
{
    reveal(mem);
    let wit = choose|wit: Wit| #[trigger] mem_w(sig, pi(ta, tb), rho, d, wit);
    assert(pi(ta, tb) == ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb)));
    match wit {
        Wit::Gen(a, gen_, wa, _) => {
            assert(mem_w(sig, ta, rho, a, *wa));
            head_le(d, gen_);
            pi_dom_le(d, gen_);
            parts_lower(d);
            mem_down_e(sig, ta, rho, a, *d->Pi_0);
        },
        _ => {
            assert(false);
        },
    }
}

/// A chain's environment fits the chain's context.
pub proof fn chain_fits(sig: Sig, g: Ctx, tds: Seq<ExprSpec>, rho: Env, ds: Seq<Cpt>, xs: Seq<Cpt>)
    requires
        chain_ok(sig, tds, rho, ds, xs),
        fits_env(sig, g, rho),
    ensures
        fits_env(sig, g + tds, exts(rho, xs)),
    decreases tds.len(),
{
    if tds.len() == 0 {
        assert(g + tds =~= g);
        return;
    }
    chain_ok_rest(sig, tds, rho, ds, xs);
    fits_ext(sig, g, rho, tds[0], ds[0], xs[0]);
    chain_fits(sig, g.push(tds[0]), tds.drop_first(), ext(rho, xs[0]), ds.drop_first(), xs.drop_first());
    assert(g.push(tds[0]) + tds.drop_first() =~= g + tds);
}

/// One more value, innermost.
pub proof fn exts_push(rho: Env, ws: Seq<Cpt>, w: Cpt)
    ensures
        exts(rho, ws.push(w)) == ext(exts(rho, ws), w),
    decreases ws.len(),
{
    if ws.len() == 0 {
        assert(ws.push(w).drop_first() =~= Seq::<Cpt>::empty());
        assert(ws.push(w)[0] == w);
        reveal_with_fuel(exts, 2);
    } else {
        exts_push(ext(rho, ws[0]), ws.drop_first(), w);
        assert(ws.push(w).drop_first() =~= ws.drop_first().push(w));
        assert(ws.push(w)[0] == ws[0]);
    }
}

/// A chain one longer.
pub proof fn chain_push(sig: Sig, tds: Seq<ExprSpec>, rho: Env, ds: Seq<Cpt>, xs: Seq<Cpt>, t: ExprSpec, d: Cpt, x: Cpt)
    requires
        chain_ok(sig, tds, rho, ds, xs),
        dfit(sig, t, exts(rho, xs), d, x),
    ensures
        chain_ok(sig, tds.push(t), rho, ds.push(d), xs.push(x)),
{
    let (t2, d2, x2) = (tds.push(t), ds.push(d), xs.push(x));
    assert forall|i: int| 0 <= i < t2.len() implies #[trigger] dfit(sig, t2[i], exts(rho, x2.subrange(0, i)), d2[i], x2[i]) by {
        assert(x2.subrange(0, i) =~= xs.subrange(0, i) || i == xs.len());
        if i < tds.len() {
            assert(x2.subrange(0, i) =~= xs.subrange(0, i));
            assert(t2[i] == tds[i] && d2[i] == ds[i] && x2[i] == xs[i]);
        } else {
            assert(x2.subrange(0, i) =~= xs);
        }
    }
}

} // verus!
