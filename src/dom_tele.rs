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
    -> (r: (Cpt, Cpt, LevelSpec))
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
        return (Cpt::Bot, Cpt::Bot, l2);
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
    (w2, cod(d, w2), l2)
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
    -> (r: (Seq<Cpt>, Cpt, LevelSpec))
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
    decreases ds.len(),
{
    if ds.len() == 0 {
        assert(g + ds =~= g);
        assert(crate::rec_canon::binds(BinderKind::Pi, ds, body) == body);
        let d0 = crate::ti_sub::get(sig, eq(g, body, body, sort(l)));
        return (Seq::empty(), d, l);
    }
    let (ta, rest) = (ds[0], ds.drop_first());
    let tb = crate::rec_canon::binds(BinderKind::Pi, rest, body);
    assert(crate::rec_canon::binds(BinderKind::Pi, ds, body) == pi(ta, tb));
    let (w2, d2, l2) = tele_step(sig, g, ta, tb, l, rho, d, u, ws[0]);
    assert(wf(ws[0]));
    let u2 = app(u, ws[0]);
    let wr = ws.drop_first();
    assert forall|i: int| 0 <= i < wr.len() implies #[trigger] wf(wr[i]) by {
        assert(wr[i] == ws[i + 1]);
    }
    let (ws2r, e, l3) = tele_apps(sig, g.push(ta), rest, body, l2, ext(rho, w2), d2, u2, wr);
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
    (ws2, e, l3)
}

} // verus!
