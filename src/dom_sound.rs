//! SOUNDNESS OF THE DOMAIN MODEL (typed inversion, stage 4; the paper's
//! Theorem 2.31): under an environment fitting the context, convertible
//! terms denote the same set, every element of a term's denotation lies
//! below one typed by an element of its type's denotation, and the
//! denotation is closed under joins.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::dom_model::*;
#[cfg(verus_only)]
use crate::ti_syntax::{Ctx, var_ty, is_zero, Deriv, Rule, Jd, valid, concl, step_ok, prems};
#[cfg(verus_only)]
use crate::ti_meta::valid_prems;
#[cfg(verus_only)]
use crate::subst_algebra::{inst, lift, lift_zero};
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The `i`-th variable's value is typed by `a`, a type in the denotation
/// of its declared type.
pub open spec fn fits_at(sig: Sig, g: Ctx, rho: Env, i: nat, a: Cpt) -> bool {
    mem(sig, var_ty(g, i), rho, a) && typed(a, Cpt::U) && typed(rho(i), a)
}

/// The `i`-th variable's value is typed within its declared type.
pub open spec fn fits_var(sig: Sig, g: Ctx, rho: Env, i: nat) -> bool {
    exists|a: Cpt| #[trigger] fits_at(sig, g, rho, i, a)
}

/// THE ENVIRONMENT FITS THE CONTEXT (the paper's Def 2.30).
pub open spec fn fits_env(sig: Sig, g: Ctx, rho: Env) -> bool {
    &&& forall|i: nat| #[trigger] wf(rho(i))
    &&& forall|i: nat| i < g.len() ==> #[trigger] fits_var(sig, g, rho, i)
}

pub proof fn typed_basic()
    ensures
        typed(Cpt::Bot, Cpt::Bot),
        typed(Cpt::Bot, Cpt::U),
        typed(Cpt::U, Cpt::U),
        typed(Cpt::Prop, Cpt::U),
        typed(Cpt::Bot, Cpt::Prop),
{
    reveal(mem);
    reveal(typed);
    assert(has_type(1, Cpt::U, Cpt::U));
    assert(has_type(1, Cpt::Bot, Cpt::U));
    assert(has_type(1, Cpt::Bot, Cpt::Bot));
    assert(has_type(1, Cpt::Prop, Cpt::U));
    assert(has_type(1, Cpt::Bot, Cpt::Prop));
}

/// (L1) An environment extended by an element typed at a type in the
/// domain's denotation fits the extended context.
pub proof fn fits_ext(sig: Sig, g: Ctx, rho: Env, ta: ExprSpec, a: Cpt, x: Cpt)
    requires
        fits_env(sig, g, rho),
        mem(sig, ta, rho, a),
        typed(a, Cpt::U),
        typed(x, a),
    ensures
        fits_env(sig, g.push(ta), ext(rho, x)),
{
    use crate::ti_meta::var_ty_push;
    typed_wf(x, a);
    assert forall|i: nat| #[trigger] wf(ext(rho, x)(i)) by {
        if i > 0 {
            assert(wf(rho((i - 1) as nat)));
        }
    }
    assert forall|i: nat| i < g.push(ta).len() implies #[trigger] fits_var(sig, g.push(ta), ext(rho, x), i) by {
        var_ty_push(g, ta, i);
        if i == 0 {
            mem_lift1(sig, ta, rho, x, a);
            assert(fits_at(sig, g.push(ta), ext(rho, x), 0, a));
        } else {
            let k = (i - 1) as nat;
            assert(fits_var(sig, g, rho, k));
            let ak = choose|a2: Cpt| #[trigger] fits_at(sig, g, rho, k, a2);
            mem_lift1(sig, var_ty(g, k), rho, x, ak);
            assert(fits_at(sig, g.push(ta), ext(rho, x), i, ak));
        }
    }
}

/// (L5) Instantiating the first variable with `x` is covered by the
/// environment extended with an element of `x`'s denotation.
pub proof fn covers_inst(sig: Sig, x: ExprSpec, rho: Env, v: Cpt)
    requires
        mem(sig, x, rho, v),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        covers(sig, crate::ti_subst::isub(0, x), rho, ext(rho, v)),
{
    reveal(mem);
    reveal(typed);
    assert forall|i: nat| #[trigger] mem(sig, crate::ti_subst::isub(0, x)(i), rho, ext(rho, v)(i)) by {
        if i == 0 {
            lift_zero(0, x);
        } else {
            let k = (i - 1) as nat;
            le_refl(rho(k));
            assert(mem_w(sig, ExprSpec::Var(k), rho, rho(k), Wit::Nil));
        }
    }
}

pub proof fn jc_inst(sig: Sig, x: ExprSpec, rho: Env)
    requires
        jc(sig, x, rho),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        forall|i: nat| #[trigger] jc(sig, crate::ti_subst::isub(0, x)(i), rho),
{
    assert forall|i: nat| #[trigger] jc(sig, crate::ti_subst::isub(0, x)(i), rho) by {
        if i == 0 {
            lift_zero(0, x);
        } else {
            jc_var(sig, (i - 1) as nat, rho);
        }
    }
}

/// (L6) Application is monotone in both arguments.
pub proof fn app_mono(w: Cpt, w2: Cpt, v: Cpt, v2: Cpt)
    requires
        wf(w),
        wf(w2),
        wf(v),
        wf(v2),
        le(w, w2),
        le(v, v2),
    ensures
        le(crate::dom_compact::app(w, v), crate::dom_compact::app(w2, v2)),
{
    if w is Lam {
        head_le(w, w2);
        appk_mono_fun(w, w2, v, true);
        appk_mono_arg(w2, v, v2, true);
        le_trans(crate::dom_compact::app(w, v), crate::dom_compact::app(w2, v), crate::dom_compact::app(w2, v2));
    } else {
        assert(crate::dom_compact::app(w, v) == Cpt::Bot);
    }
}

/// A Pi code that is a type has codomains that are types.
pub proof fn cod_typed_at(p: Cpt, v: Cpt, n: nat)
    requires
        has_type(n, p, Cpt::U),
        p is Pi,
        wf(v),
    ensures
        n >= 2,
        has_type((n - 1) as nat, cod(p, v), Cpt::U),
{
    let t = seq![p];
    assert(t[0] == p);
    let g = p->Pi_1;
    parts_lower(p);
    assert(n >= 2);
    appk_wf(p, v, false);
    let sm = selk(t, v, ht(p), false);
    assert forall|y: Cpt| #[trigger] sm.contains(y) implies has_type((n - 1) as nat, y, Cpt::U) by {
        sel_pi_mem(t, v, ht(p), 1, y);
        let q = choose|q: int| 0 <= q < g.len() && #[trigger] g[q].1 == y && le(g[q].0, v);
    }
    assert(stg((n - 1) as nat, Cpt::U));
    assert(has_type((n - 1) as nat, Cpt::U, Cpt::U));
    ty_jall((n - 1) as nat, sm, sm.len() as int, Cpt::U);
}

/// (L4) APPLYING A TYPED LAMBDA: the result is typed at the codomain.
pub proof fn app_typed(fw: Cpt, p: Cpt, v: Cpt)
    requires
        fw is Lam,
        p is Pi,
        typed(fw, p),
        typed(p, Cpt::U),
        wf(v),
    ensures
        typed(crate::dom_compact::app(fw, v), cod(p, v)),
        typed(cod(p, v), Cpt::U),
{
    let n = cstage(fw, p) + cstage(p, Cpt::U) + 2;
    typed_up(fw, p, n);
    typed_up(p, Cpt::U, n);
    let m = (n - 1) as nat;
    cod_typed_at(p, v, n);
    let t = seq![fw];
    assert(t[0] == fw);
    let f = fw->Lam_0;
    parts_lower(fw);
    appk_wf(fw, v, true);
    let sm = selk(t, v, ht(fw), true);
    assert forall|y: Cpt| #[trigger] sm.contains(y) implies has_type(m, y, cod(p, v)) by {
        sel_lam_mem(t, v, ht(fw), 1, y);
        let q = choose|q: int| 0 <= q < f.len() && #[trigger] f[q].1 == y && le(f[q].0, v);
        assert(has_type(m, f[q].0, *p->Pi_0) && has_type(m, y, cod(p, f[q].0)));
        cod_typed_at(p, f[q].0, n);
        appk_mono_arg(p, f[q].0, v, false);
        ty_weak(m, y, cod(p, f[q].0), cod(p, v));
    }
    ty_jall(m, sm, sm.len() as int, cod(p, v));
    typed_down(crate::dom_compact::app(fw, v), cod(p, v), m);
    typed_down(cod(p, v), Cpt::U, m);
}

/// `u` lies below an element `v` of `m` typed by a type `a` in `t`.
pub open spec fn tyd_at(sig: Sig, m: ExprSpec, rho: Env, t: ExprSpec, u: Cpt, v: Cpt, a: Cpt) -> bool {
    mem(sig, m, rho, v) && le(u, v) && mem(sig, t, rho, a) && typed(a, Cpt::U) && typed(v, a)
}

#[verifier::opaque]
pub open spec fn tyd_w(sig: Sig, m: ExprSpec, rho: Env, t: ExprSpec, u: Cpt) -> bool {
    exists|v: Cpt, a: Cpt| #[trigger] tyd_at(sig, m, rho, t, u, v, a)
}

/// Every element of `m` lies below one typed within `t` (the paper's
/// `[[m]] : [[t]]`).
pub open spec fn tyd(sig: Sig, m: ExprSpec, rho: Env, t: ExprSpec) -> bool {
    forall|u: Cpt| #[trigger] mem(sig, m, rho, u) ==> tyd_w(sig, m, rho, t, u)
}

pub open spec fn sem_eq(sig: Sig, m: ExprSpec, n: ExprSpec, rho: Env) -> bool {
    forall|u: Cpt| #[trigger] mem(sig, m, rho, u) == mem(sig, n, rho, u)
}

/// What soundness says of `m == n : t` under `rho`.
pub open spec fn sound_ok(sig: Sig, m: ExprSpec, n: ExprSpec, t: ExprSpec, rho: Env) -> bool {
    sem_eq(sig, m, n, rho) && tyd(sig, m, rho, t) && jc(sig, m, rho)
}

/// Bottom is typed below itself anywhere.
pub proof fn tyd_bot(sig: Sig, m: ExprSpec, rho: Env, t: ExprSpec)
    ensures
        tyd_w(sig, m, rho, t, Cpt::Bot),
{
    reveal(mem);
    reveal(typed);
    mem_bot(sig, m, rho);
    mem_bot(sig, t, rho);
    typed_basic();
    le_refl(Cpt::Bot);
    assert(tyd_at(sig, m, rho, t, Cpt::Bot, Cpt::Bot, Cpt::Bot));
    tyd_w_intro(sig, m, rho, t, Cpt::Bot, Cpt::Bot, Cpt::Bot);
}

pub proof fn tyd_w_intro(sig: Sig, m: ExprSpec, rho: Env, t: ExprSpec, u: Cpt, v: Cpt, a: Cpt)
    requires
        tyd_at(sig, m, rho, t, u, v, a),
    ensures
        tyd_w(sig, m, rho, t, u),
{
    reveal(tyd_w);
}

pub proof fn tyd_w_elim(sig: Sig, m: ExprSpec, rho: Env, t: ExprSpec, u: Cpt) -> (r: (Cpt, Cpt))
    requires
        tyd_w(sig, m, rho, t, u),
    ensures
        tyd_at(sig, m, rho, t, u, r.0, r.1),
{
    reveal(tyd_w);
    choose|v: Cpt, a: Cpt| #[trigger] tyd_at(sig, m, rho, t, u, v, a)
}

/// Equal denotations share typing and join-closure.
pub proof fn sound_transfer(sig: Sig, m: ExprSpec, n: ExprSpec, t: ExprSpec, t2: ExprSpec, rho: Env)
    requires
        sem_eq(sig, m, n, rho),
        sem_eq(sig, t, t2, rho),
        tyd(sig, m, rho, t),
        jc(sig, m, rho),
    ensures
        tyd(sig, n, rho, t2),
        jc(sig, n, rho),
{
    assert forall|u: Cpt| #[trigger] mem(sig, n, rho, u) implies tyd_w(sig, n, rho, t2, u) by {
        assert(mem(sig, m, rho, u));
        let (v, a) = tyd_w_elim(sig, m, rho, t, u);
        assert(mem(sig, m, rho, v) && mem(sig, t, rho, a));
        tyd_w_intro(sig, n, rho, t2, u, v, a);
    }
    assert forall|u1: Cpt, u2: Cpt| mem(sig, n, rho, u1) && mem(sig, n, rho, u2) implies #[trigger] jc_pair(sig, n, rho, u1, u2) by {
        assert(mem(sig, m, rho, u1) && mem(sig, m, rho, u2));
        jc_elim(sig, m, rho, u1, u2);
        assert(mem(sig, m, rho, join(u1, u2)));
    }
    jc_intro(sig, n, rho);
}

/// A proposition's inhabitants are bottom, stage-free.
pub proof fn below_prop_bot_sf(v: Cpt, a: Cpt, a2: Cpt)
    requires
        typed(v, a),
        le(a, a2),
        typed(a2, Cpt::Prop),
    ensures
        v is Bot,
{
    reveal(mem);
    reveal(typed);
    let n = cstage(v, a) + cstage(a2, Cpt::Prop);
    typed_up(v, a, n);
    typed_up(a2, Cpt::Prop, n);
    below_prop_bot(n, v, a, a2);
}

pub proof fn prop_is_type_sf(v: Cpt)
    requires
        typed(v, Cpt::Prop),
    ensures
        typed(v, Cpt::U),
{
    reveal(mem);
    reveal(typed);
    prop_is_type(cstage(v, Cpt::Prop), v);
}

/// (L2) A TYPE ELEMENT: an element of a type's denotation lies below one
/// that is a type (and, at a proposition sort, bottom or a proposition).
pub proof fn type_elem(sig: Sig, t: ExprSpec, rho: Env, l: LevelSpec, a: Cpt) -> (a2: Cpt)
    requires
        tyd(sig, t, rho, ExprSpec::Sort(l)),
        mem(sig, t, rho, a),
    ensures
        mem(sig, t, rho, a2),
        le(a, a2),
        typed(a2, Cpt::U),
        is_zero(l) ==> (a2 is Bot || typed(a2, Cpt::Prop)),
{
    reveal(mem);
    reveal(typed);
    assert(tyd_w(sig, t, rho, ExprSpec::Sort(l), a));
    let (v, s) = tyd_w_elim(sig, t, rho, ExprSpec::Sort(l), a);
    let ws = choose|w: Wit| #[trigger] mem_w(sig, ExprSpec::Sort(l), rho, s, w);
    typed_basic();
    if s is Bot {
        ty_of_bot(cstage(v, s), v);
    } else if s is Prop {
        prop_is_type_sf(v);
    }
    v
}

pub proof fn sem_eq_refl(sig: Sig, m: ExprSpec, rho: Env)
    ensures
        sem_eq(sig, m, m, rho),
{
}

pub proof fn sound_sym(sig: Sig, m: ExprSpec, n: ExprSpec, t: ExprSpec, rho: Env)
    requires
        sound_ok(sig, n, m, t, rho),
    ensures
        sound_ok(sig, m, n, t, rho),
{
    assert(sem_eq(sig, m, n, rho));
    sound_transfer(sig, n, m, t, t, rho);
}

pub proof fn sound_trans(sig: Sig, m: ExprSpec, mid: ExprSpec, n: ExprSpec, t: ExprSpec, rho: Env)
    requires
        sound_ok(sig, m, mid, t, rho),
        sound_ok(sig, mid, n, t, rho),
    ensures
        sound_ok(sig, m, n, t, rho),
{
    assert(sem_eq(sig, m, n, rho));
}

pub proof fn sound_conv(sig: Sig, m: ExprSpec, n: ExprSpec, a: ExprSpec, b: ExprSpec, rho: Env)
    requires
        sound_ok(sig, m, n, a, rho),
        sem_eq(sig, a, b, rho),
    ensures
        sound_ok(sig, m, n, b, rho),
{
    sound_transfer(sig, m, m, a, b, rho);
}

/// VARIABLES: the value is the typed top of the variable's denotation.
pub proof fn sound_var(sig: Sig, g: Ctx, i: nat, rho: Env)
    requires
        fits_env(sig, g, rho),
        i < g.len(),
    ensures
        sound_ok(sig, ExprSpec::Var(i), ExprSpec::Var(i), var_ty(g, i), rho),
{
    let m = ExprSpec::Var(i);
    assert(wf(rho(i)));
    jc_var(sig, i, rho);
    assert(fits_var(sig, g, rho, i));
    let a = choose|a: Cpt| #[trigger] fits_at(sig, g, rho, i, a);
    assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) implies tyd_w(sig, m, rho, var_ty(g, i), u) by {
        reveal(mem);
        let w = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
        le_refl(rho(i));
        assert(mem_w(sig, m, rho, rho(i), Wit::Nil));
        assert(tyd_at(sig, m, rho, var_ty(g, i), u, rho(i), a));
        tyd_w_intro(sig, m, rho, var_ty(g, i), u, rho(i), a);
    }
}

/// UNIVERSES: a sort's denotation is {bottom, its code}.
pub proof fn sound_univ(sig: Sig, l: LevelSpec, l2: LevelSpec, rho: Env)
    requires
        crate::conv_cr::lev_eq(l, l2),
    ensures
        sound_ok(sig, ExprSpec::Sort(l), ExprSpec::Sort(l2), ExprSpec::Sort(crate::ti_syntax::succ(l)), rho),
{
    reveal(mem);
    let m = ExprSpec::Sort(l);
    let t = ExprSpec::Sort(crate::ti_syntax::succ(l));
    assert(is_zero(l) == is_zero(l2)) by {
        if is_zero(l) {
            assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(l2, r) == 0 by {
                assert(crate::level_model::interp(l, r) == crate::level_model::interp(l2, r));
            }
        }
        if is_zero(l2) {
            assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(l, r) == 0 by {
                assert(crate::level_model::interp(l, r) == crate::level_model::interp(l2, r));
            }
        }
    }
    assert(!is_zero(crate::ti_syntax::succ(l))) by {
        let r = Map::<nat, nat>::empty();
        assert(crate::level_model::interp(crate::ti_syntax::succ(l), r) > 0);
    }
    let c = sortc(l);
    typed_basic();
    assert(sem_eq(sig, m, ExprSpec::Sort(l2), rho)) by {
        assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) == mem(sig, ExprSpec::Sort(l2), rho, u) by {
            if mem(sig, m, rho, u) {
                let w = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
                assert(mem_w(sig, ExprSpec::Sort(l2), rho, u, w));
            }
            if mem(sig, ExprSpec::Sort(l2), rho, u) {
                let w = choose|w: Wit| #[trigger] mem_w(sig, ExprSpec::Sort(l2), rho, u, w);
                assert(mem_w(sig, m, rho, u, w));
            }
        }
    }
    assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) implies tyd_w(sig, m, rho, t, u) by {
        let w = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
        assert(mem_w(sig, m, rho, c, Wit::Nil));
        assert(mem_w(sig, t, rho, Cpt::U, Wit::Nil));
        le_refl(c);
        if u is Bot {
            assert(le(u, c));
        }
        assert(tyd_at(sig, m, rho, t, u, c, Cpt::U));
        tyd_w_intro(sig, m, rho, t, u, c, Cpt::U);
    }
    assert forall|u1: Cpt, u2: Cpt| mem(sig, m, rho, u1) && mem(sig, m, rho, u2) implies #[trigger] jc_pair(sig, m, rho, u1, u2) by {
        let w1 = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u1, w);
        let w2 = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u2, w);
        assert(mem_w(sig, m, rho, join(u1, u2), Wit::Nil));
    }
    jc_intro(sig, m, rho);
}

/// PROOF IRRELEVANCE: a proposition's inhabitants denote {bottom}.
pub proof fn prop_denot_bot(sig: Sig, m: ExprSpec, a: ExprSpec, l: LevelSpec, rho: Env, u: Cpt)
    requires
        is_zero(l),
        tyd(sig, a, rho, ExprSpec::Sort(l)),
        tyd(sig, m, rho, a),
        mem(sig, m, rho, u),
    ensures
        u is Bot,
{
    let (v, aa) = tyd_w_elim(sig, m, rho, a, u);
    let a2 = type_elem(sig, a, rho, l, aa);
    if a2 is Bot {
        reveal(typed);
        assert(le(aa, a2));
        typed_wf(v, aa);
        if !(aa is Bot) {
            head_le(aa, a2);
        }
        ty_of_bot(cstage(v, aa), v);
    } else {
        below_prop_bot_sf(v, aa, a2);
    }
    reveal(mem);
    let w = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
    mem_wf(sig, m, rho, u, w);
    if !(u is Bot) {
        head_le(u, v);
    }
}

pub proof fn sound_irr(sig: Sig, m: ExprSpec, n: ExprSpec, a: ExprSpec, l: LevelSpec, rho: Env)
    requires
        is_zero(l),
        sound_ok(sig, a, a, ExprSpec::Sort(l), rho),
        sound_ok(sig, m, m, a, rho),
        sound_ok(sig, n, n, a, rho),
    ensures
        sound_ok(sig, m, n, a, rho),
{
    assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) == mem(sig, n, rho, u) by {
        mem_bot(sig, m, rho);
        mem_bot(sig, n, rho);
        reveal(mem);
        if mem(sig, m, rho, u) {
            prop_denot_bot(sig, m, a, l, rho, u);
            assert(mem_w(sig, n, rho, u, bot_w(n)));
        }
        if mem(sig, n, rho, u) {
            prop_denot_bot(sig, n, a, l, rho, u);
            assert(mem_w(sig, m, rho, u, bot_w(m)));
        }
    }
}

/// `x` is typed by a type `a` in the denotation of the domain `ta`.
pub open spec fn dfit(sig: Sig, ta: ExprSpec, rho: Env, a: Cpt, x: Cpt) -> bool {
    mem(sig, ta, rho, a) && typed(a, Cpt::U) && typed(x, a)
}

/// The body is join-closed under every fitting extension.
pub open spec fn body_jc(sig: Sig, ta: ExprSpec, body: ExprSpec, rho: Env) -> bool {
    forall|x: Cpt, a: Cpt| #[trigger] dfit(sig, ta, rho, a, x) ==> jc(sig, body, ext(rho, x))
}

/// The generator's shape for a binder kind.
pub open spec fn gen_shape(bk: BinderKind, a: Cpt, gen: Cpt) -> bool {
    if bk == BinderKind::Pi { gen is Pi && *gen->Pi_0 == a } else { gen is Lam }
}

/// MERGING TWO GENERATORS of a binder's denotation into one above both.
#[verifier::spinoff_prover]
pub proof fn merge_gen(sig: Sig, 
    bk: BinderKind, ta: ExprSpec, body: ExprSpec, l: LevelSpec, rho: Env,
    a1: Cpt, gen1: Cpt, ws1: Seq<Wit>, a2: Cpt, gen2: Cpt, ws2: Seq<Wit>,
) -> (r: (Cpt, Cpt, Wit))
    requires
        jc(sig, ta, rho),
        tyd(sig, ta, rho, ExprSpec::Sort(l)),
        body_jc(sig, ta, body, rho),
        mem(sig, ta, rho, a1),
        mem(sig, ta, rho, a2),
        typed(a1, Cpt::U),
        typed(a2, Cpt::U),
        gen_shape(bk, a1, gen1),
        gen_shape(bk, a2, gen2),
        entries_ok(sig, body, rho, a1, gen1, ws1),
        entries_ok(sig, body, rho, a2, gen2, ws2),
        bk == BinderKind::Lam ==> exists|k: int| 0 <= k < gen1->Lam_0.len() && !(#[trigger] gen1->Lam_0[k].1 is Bot),
    ensures
        le(gen1, r.1),
        le(gen2, r.1),
        wf(r.1),
        mem_w(sig, ExprSpec::Bind(bk, Box::new(ta), Box::new(body)), rho, r.1, r.2),
{
    let lam = bk == BinderKind::Lam;
    jc_elim(sig, ta, rho, a1, a2);
    typed_wf(a1, Cpt::U);
    typed_wf(a2, Cpt::U);
    join_ub(a1, a2);
    let a = type_elem(sig, ta, rho, l, join(a1, a2));
    le_trans(a1, join(a1, a2), a);
    le_trans(a2, join(a1, a2), a);
    typed_wf(a, Cpt::U);
    let g1 = gsteps(gen1);
    let g2 = gsteps(gen2);
    let gg = g1 + g2;
    let big = if lam { Cpt::Lam(gg) } else { Cpt::Pi(Box::new(a), gg) };
    assert(gsteps(big) == gg);
    assert(steps(big, lam) == gg);
    assert(steps(gen1, lam) == g1);
    assert(steps(gen2, lam) == g2);
    let ws = ws1 + ws2;
    // every entry: typed at the merged domain, output in the body at its input
    assert forall|i: int| 0 <= i < gg.len() implies typed(#[trigger] gg[i].0, a) && mem_w(sig, body, ext(rho, gg[i].0), gg[i].1, ws[i]) by {
        if i < g1.len() {
            assert(gg[i] == g1[i] && ws[i] == ws1[i]);
            assert(typed(g1[i].0, a1));
            typed_weak(g1[i].0, a1, a);
        } else {
            let k = i - g1.len();
            assert(gg[i] == g2[k] && ws[i] == ws2[k]);
            assert(typed(g2[k].0, a2));
            typed_weak(g2[k].0, a2, a);
        }
    }
    // well formed: entries, the function condition, a non-bottom output
    assert forall|k: int| 0 <= k < gg.len() implies wf(#[trigger] gg[k].0) && wf(gg[k].1) by {
        typed_wf(gg[k].0, a);
        mem_wf(sig, body, ext(rho, gg[k].0), gg[k].1, ws[k]);
    }
    fok_iff(gg);
    assert forall|e1: (Cpt, Cpt), e2: (Cpt, Cpt)| #[trigger] gg.contains(e1) && #[trigger] gg.contains(e2) && compat(e1.0, e2.0)
        implies compat(e1.1, e2.1) by {
        let i = choose|i: int| 0 <= i < gg.len() && gg[i] == e1;
        let j = choose|j: int| 0 <= j < gg.len() && gg[j] == e2;
        let x12 = join(e1.0, e2.0);
        typed_wf(e1.0, a);
        typed_wf(e2.0, a);
        typed_join(e1.0, e2.0, a);
        join_ub(e1.0, e2.0);
        compat_symm(e1.0, e2.0);
        assert(dfit(sig, ta, rho, a, x12));
        assert(jc(sig, body, ext(rho, x12)));
        assert forall|q: nat| #[trigger] le(ext(rho, e1.0)(q), ext(rho, x12)(q)) by {
            if q > 0 {
                le_refl(rho((q - 1) as nat));
            }
        }
        assert forall|q: nat| #[trigger] le(ext(rho, e2.0)(q), ext(rho, x12)(q)) by {
            if q > 0 {
                le_refl(rho((q - 1) as nat));
            }
        }
        mem_env_mono(sig, body, ext(rho, e1.0), ext(rho, x12), e1.1, ws[i]);
        mem_env_mono(sig, body, ext(rho, e2.0), ext(rho, x12), e2.1, ws[j]);
        reveal(mem);
        jc_elim(sig, body, ext(rho, x12), e1.1, e2.1);
    }
    if lam {
        let k = choose|k: int| 0 <= k < gen1->Lam_0.len() && !(#[trigger] gen1->Lam_0[k].1 is Bot);
        assert(gg[k] == g1[k]);
    }
    assert(wf(big));
    // above both
    assert(gg == Seq::<(Cpt, Cpt)>::empty() + g1 + g2);
    gen_below(gen1, big, lam, Seq::empty(), g2);
    assert(gg == g1 + g2 + Seq::<(Cpt, Cpt)>::empty());
    gen_below(gen2, big, lam, g1, Seq::empty());
    // in the denotation
    reveal(mem);
    let wa = choose|w: Wit| #[trigger] mem_w(sig, ta, rho, a, w);
    assert(entries_ok(sig, body, rho, a, big, ws));
    le_refl(big);
    let wit = Wit::Gen(a, big, Box::new(wa), ws);
    assert(mem_w(sig, ExprSpec::Bind(bk, Box::new(ta), Box::new(body)), rho, big, wit));
    (a, big, wit)
}

/// One pair of a binder's denotation joins inside it.
#[verifier::spinoff_prover]
proof fn jc_bind_pair(sig: Sig, bk: BinderKind, ta: ExprSpec, body: ExprSpec, l: LevelSpec, rho: Env, u1: Cpt, u2: Cpt)
    requires
        jc(sig, ta, rho),
        tyd(sig, ta, rho, ExprSpec::Sort(l)),
        body_jc(sig, ta, body, rho),
        mem(sig, ExprSpec::Bind(bk, Box::new(ta), Box::new(body)), rho, u1),
        mem(sig, ExprSpec::Bind(bk, Box::new(ta), Box::new(body)), rho, u2),
    ensures
        jc_pair(sig, ExprSpec::Bind(bk, Box::new(ta), Box::new(body)), rho, u1, u2),
{
    let m = ExprSpec::Bind(bk, Box::new(ta), Box::new(body));
    reveal(mem);
    let w1 = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u1, w);
    let w2 = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u2, w);
    if u1 is Bot {
        assert(join(u1, u2) == u2);
        return;
    }
    if u2 is Bot {
        assert(join(u1, u2) == u1);
        return;
    }
    if let (Wit::Gen(a1, gen1, wa1, ws1), Wit::Gen(a2, gen2, wa2, ws2)) = (w1, w2) {
        assert(mem_w(sig, ta, rho, a1, *wa1) && mem_w(sig, ta, rho, a2, *wa2));
        if bk == BinderKind::Lam {
            head_le(u1, gen1);
            below_lam_nonbot(u1, gen1);
        }
        let (a, big, wit) = merge_gen(sig, bk, ta, body, l, rho, a1, gen1, ws1, a2, gen2, ws2);
        le_trans(u1, gen1, big);
        le_trans(u2, gen2, big);
        ub_compat(u1, u2, big);
        join_ub(u1, u2);
        join_lub(u1, u2, big);
        mem_down(sig, m, rho, big, join(u1, u2), wit);
    }
}

/// A BINDER'S DENOTATION IS JOIN-CLOSED when its domain is a join-closed
/// type and its body is join-closed under every fitting extension.
pub proof fn jc_binder(sig: Sig, bk: BinderKind, ta: ExprSpec, body: ExprSpec, l: LevelSpec, rho: Env)
    requires
        jc(sig, ta, rho),
        tyd(sig, ta, rho, ExprSpec::Sort(l)),
        body_jc(sig, ta, body, rho),
    ensures
        jc(sig, ExprSpec::Bind(bk, Box::new(ta), Box::new(body)), rho),
{
    let m = ExprSpec::Bind(bk, Box::new(ta), Box::new(body));
    assert forall|u1: Cpt, u2: Cpt| mem(sig, m, rho, u1) && mem(sig, m, rho, u2) implies #[trigger] jc_pair(sig, m, rho, u1, u2) by {
        jc_bind_pair(sig, bk, ta, body, l, rho, u1, u2);
    }
    jc_intro(sig, m, rho);
}

/// Bodies agree under every fitting extension.
pub open spec fn body_eq(sig: Sig, ta: ExprSpec, b: ExprSpec, b2: ExprSpec, rho: Env) -> bool {
    forall|x: Cpt, a: Cpt| #[trigger] dfit(sig, ta, rho, a, x) ==> sem_eq(sig, b, b2, ext(rho, x))
}

/// One direction of `bind_sem_eq`.
#[verifier::spinoff_prover]
proof fn bind_sub(sig: Sig, bk: BinderKind, ta: ExprSpec, b: ExprSpec, ta2: ExprSpec, b2: ExprSpec, rho: Env, u: Cpt)
    requires
        sem_eq(sig, ta, ta2, rho),
        body_eq(sig, ta, b, b2, rho),
        mem(sig, ExprSpec::Bind(bk, Box::new(ta), Box::new(b)), rho, u),
    ensures
        mem(sig, ExprSpec::Bind(bk, Box::new(ta2), Box::new(b2)), rho, u),
{
    let m = ExprSpec::Bind(bk, Box::new(ta), Box::new(b));
    let m2 = ExprSpec::Bind(bk, Box::new(ta2), Box::new(b2));
    reveal(mem);
    let w = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
    if u is Bot {
        assert(mem_w(sig, m2, rho, u, Wit::Nil));
    } else if let Wit::Gen(a, gen, wa, ws) = w {
        assert(mem_w(sig, ta, rho, a, *wa));
        assert(mem(sig, ta, rho, a));
        assert(mem(sig, ta, rho, a) == mem(sig, ta2, rho, a));
        assert(mem(sig, ta2, rho, a));
        let wa2 = choose|v: Wit| #[trigger] mem_w(sig, ta2, rho, a, v);
        let st = gsteps(gen);
        assert(entries_ok(sig, b, rho, a, gen, ws));
        assert forall|i: int| 0 <= i < ws.len() implies #[trigger] mem(sig, b2, ext(rho, st[i].0), st[i].1) by {
            assert(dfit(sig, ta, rho, a, st[i].0));
            assert(sem_eq(sig, b, b2, ext(rho, st[i].0)));
            assert(mem_w(sig, b, ext(rho, st[i].0), st[i].1, ws[i]));
            assert(mem(sig, b, ext(rho, st[i].0), st[i].1));
        }
        let ws2 = Seq::new(ws.len(), |i: int| choose|v: Wit| #[trigger] mem_w(sig, b2, ext(rho, st[i].0), st[i].1, v));
        assert forall|i: int| 0 <= i < ws2.len() implies
            typed(#[trigger] gsteps(gen)[i].0, a) && mem_w(sig, b2, ext(rho, gsteps(gen)[i].0), gsteps(gen)[i].1, ws2[i]) by {
            assert(mem(sig, b2, ext(rho, st[i].0), st[i].1));
        }
        assert(entries_ok(sig, b2, rho, a, gen, ws2));
        assert(mem_w(sig, m2, rho, u, Wit::Gen(a, gen, Box::new(wa2), ws2)));
    }
}

/// BINDERS WITH EQUAL DOMAINS AND BODIES DENOTE THE SAME.
pub proof fn bind_sem_eq(sig: Sig, bk: BinderKind, ta: ExprSpec, b: ExprSpec, ta2: ExprSpec, b2: ExprSpec, rho: Env)
    requires
        sem_eq(sig, ta, ta2, rho),
        body_eq(sig, ta, b, b2, rho),
    ensures
        sem_eq(sig, ExprSpec::Bind(bk, Box::new(ta), Box::new(b)), ExprSpec::Bind(bk, Box::new(ta2), Box::new(b2)), rho),
{
    let m = ExprSpec::Bind(bk, Box::new(ta), Box::new(b));
    let m2 = ExprSpec::Bind(bk, Box::new(ta2), Box::new(b2));
    assert(sem_eq(sig, ta2, ta, rho));
    assert forall|x: Cpt, a: Cpt| #[trigger] dfit(sig, ta2, rho, a, x) implies sem_eq(sig, b2, b, ext(rho, x)) by {
        assert(dfit(sig, ta, rho, a, x));
    }
    assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) == mem(sig, m2, rho, u) by {
        if mem(sig, m, rho, u) {
            bind_sub(sig, bk, ta, b, ta2, b2, rho, u);
        }
        if mem(sig, m2, rho, u) {
            bind_sub(sig, bk, ta2, b2, ta, b, rho, u);
        }
    }
}

/// The body is typed within `t` under every fitting extension.
pub open spec fn body_tyd(sig: Sig, ta: ExprSpec, body: ExprSpec, t: ExprSpec, rho: Env) -> bool {
    forall|x: Cpt, a: Cpt| #[trigger] dfit(sig, ta, rho, a, x) ==> tyd(sig, body, ext(rho, x), t)
}

/// A chosen typed element above `u` (when one exists).
pub open spec fn tw(sig: Sig, m: ExprSpec, rho: Env, t: ExprSpec, u: Cpt) -> (Cpt, Cpt) {
    choose|v: Cpt, a: Cpt| #[trigger] tyd_at(sig, m, rho, t, u, v, a)
}

/// RAISING A GENERATOR: each output replaced by the typed element above
/// it that the body's soundness provides.
#[verifier::spinoff_prover]
pub proof fn raise_gen(sig: Sig, bk: BinderKind, ta: ExprSpec, body: ExprSpec, t: ExprSpec, rho: Env, u: Cpt, a: Cpt, gen: Cpt, ws: Seq<Wit>)
    -> (r: (Cpt, Wit))
    requires
        mem(sig, ta, rho, a),
        typed(a, Cpt::U),
        gen_shape(bk, a, gen),
        entries_ok(sig, body, rho, a, gen, ws),
        wf(u),
        !(u is Bot),
        le(u, gen),
        body_jc(sig, ta, body, rho),
        body_tyd(sig, ta, body, t, rho),
    ensures
        le(gen, r.0),
        wf(r.0),
        gen_shape(bk, a, r.0),
        mem_w(sig, ExprSpec::Bind(bk, Box::new(ta), Box::new(body)), rho, r.0, r.1),
        gsteps(r.0).len() == gsteps(gen).len(),
        forall|i: int| 0 <= i < gsteps(gen).len() ==> #[trigger] gsteps(r.0)[i] == (gsteps(gen)[i].0,
            tw(sig, body, ext(rho, gsteps(gen)[i].0), t, gsteps(gen)[i].1).0),
        forall|i: int| 0 <= i < gsteps(gen).len() ==> #[trigger] tyd_at(sig, body, ext(rho, gsteps(gen)[i].0), t, gsteps(gen)[i].1,
            tw(sig, body, ext(rho, gsteps(gen)[i].0), t, gsteps(gen)[i].1).0, tw(sig, body, ext(rho, gsteps(gen)[i].0), t, gsteps(gen)[i].1).1),
{
    let lam = bk == BinderKind::Lam;
    let g = gsteps(gen);
    let n = g.len();
    // the typed elements above each output
    assert forall|i: int| 0 <= i < n implies #[trigger] tyd_at(sig, body, ext(rho, g[i].0), t, g[i].1,
        tw(sig, body, ext(rho, g[i].0), t, g[i].1).0, tw(sig, body, ext(rho, g[i].0), t, g[i].1).1) by {
        assert(dfit(sig, ta, rho, a, g[i].0));
        assert(tyd(sig, body, ext(rho, g[i].0), t));
        reveal(mem);
        assert(mem_w(sig, body, ext(rho, g[i].0), g[i].1, ws[i]));
        assert(mem(sig, body, ext(rho, g[i].0), g[i].1));
        let (v, aa) = tyd_w_elim(sig, body, ext(rho, g[i].0), t, g[i].1);
    }
    let g2 = Seq::new(n, |i: int| (g[i].0, tw(sig, body, ext(rho, g[i].0), t, g[i].1).0));
    let big = if lam { Cpt::Lam(g2) } else { Cpt::Pi(Box::new(a), g2) };
    assert(gsteps(big) == g2);
    assert(steps(big, lam) == g2 && steps(gen, lam) == g);
    reveal(mem);
    // witnesses for the raised outputs
    assert forall|i: int| 0 <= i < n implies #[trigger] mem(sig, body, ext(rho, g2[i].0), g2[i].1) by {
        assert(tyd_at(sig, body, ext(rho, g[i].0), t, g[i].1, tw(sig, body, ext(rho, g[i].0), t, g[i].1).0, tw(sig, body, ext(rho, g[i].0), t, g[i].1).1));
    }
    let ws2 = Seq::new(n, |i: int| choose|w: Wit| #[trigger] mem_w(sig, body, ext(rho, g2[i].0), g2[i].1, w));
    assert forall|i: int| 0 <= i < n implies typed(#[trigger] g2[i].0, a) && mem_w(sig, body, ext(rho, g2[i].0), g2[i].1, ws2[i]) by {
        assert(entries_ok(sig, body, rho, a, gen, ws));
        assert(typed(g[i].0, a));
        assert(mem(sig, body, ext(rho, g2[i].0), g2[i].1));
    }
    // well formed
    assert forall|k: int| 0 <= k < n implies wf(#[trigger] g2[k].0) && wf(g2[k].1) by {
        typed_wf(g2[k].0, a);
        mem_wf(sig, body, ext(rho, g2[k].0), g2[k].1, ws2[k]);
    }
    fok_iff(g2);
    assert forall|e1: (Cpt, Cpt), e2: (Cpt, Cpt)| #[trigger] g2.contains(e1) && #[trigger] g2.contains(e2) && compat(e1.0, e2.0)
        implies compat(e1.1, e2.1) by {
        let i = choose|i: int| 0 <= i < n && g2[i] == e1;
        let j = choose|j: int| 0 <= j < n && g2[j] == e2;
        let x12 = join(e1.0, e2.0);
        typed_wf(e1.0, a);
        typed_wf(e2.0, a);
        typed_join(e1.0, e2.0, a);
        join_ub(e1.0, e2.0);
        assert(dfit(sig, ta, rho, a, x12));
        assert(jc(sig, body, ext(rho, x12)));
        assert forall|q: nat| #[trigger] le(ext(rho, e1.0)(q), ext(rho, x12)(q)) by {
            if q > 0 {
                le_refl(rho((q - 1) as nat));
            }
        }
        assert forall|q: nat| #[trigger] le(ext(rho, e2.0)(q), ext(rho, x12)(q)) by {
            if q > 0 {
                le_refl(rho((q - 1) as nat));
            }
        }
        mem_env_mono(sig, body, ext(rho, e1.0), ext(rho, x12), e1.1, ws2[i]);
        mem_env_mono(sig, body, ext(rho, e2.0), ext(rho, x12), e2.1, ws2[j]);
        jc_elim(sig, body, ext(rho, x12), e1.1, e2.1);
    }
    if lam {
        head_le(u, gen);
        below_lam_nonbot(u, gen);
        let k = choose|k: int| 0 <= k < gen->Lam_0.len() && !(#[trigger] gen->Lam_0[k].1 is Bot);
        assert(tyd_at(sig, body, ext(rho, g[k].0), t, g[k].1, g2[k].1, tw(sig, body, ext(rho, g[k].0), t, g[k].1).1));
        mem_wf(sig, body, ext(rho, g[k].0), g[k].1, ws[k]);
        if g2[k].1 is Bot {
            head_le(g[k].1, g2[k].1);
        }
        assert(big->Lam_0[k].1 == g2[k].1);
        assert(!(big->Lam_0[k].1 is Bot));
    }
    typed_wf(a, Cpt::U);
    assert(fun_ok(g2));
    assert(wf(big));
    // above the generator
    assert forall|k: int| 0 <= k < n implies g2[k].0 == #[trigger] g[k].0 && le(g[k].1, g2[k].1) by {
        assert(tyd_at(sig, body, ext(rho, g[k].0), t, g[k].1, tw(sig, body, ext(rho, g[k].0), t, g[k].1).0, tw(sig, body, ext(rho, g[k].0), t, g[k].1).1));
    }
    if !lam {
        le_refl(a);
    }
    gen_raise(gen, big, lam);
    // in the denotation
    let wa = choose|w: Wit| #[trigger] mem_w(sig, ta, rho, a, w);
    assert(entries_ok(sig, body, rho, a, big, ws2));
    le_refl(big);
    let wit = Wit::Gen(a, big, Box::new(wa), ws2);
    assert(mem_w(sig, ExprSpec::Bind(bk, Box::new(ta), Box::new(body)), rho, big, wit));
    (big, wit)
}

/// `imax l1 l2` is zero everywhere only if `l2` is.
pub proof fn imax_zero(l1: LevelSpec, l2: LevelSpec)
    requires
        is_zero(crate::ti_syntax::imax(l1, l2)),
    ensures
        is_zero(l2),
{
    assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(l2, r) == 0 by {
        assert(crate::level_model::interp(crate::ti_syntax::imax(l1, l2), r) == 0);
    }
}

/// An element typed within a sort's denotation is typed by that sort's
/// code (or is bottom).
pub proof fn typed_in_sort(sig: Sig, v: Cpt, s: Cpt, l: LevelSpec, rho: Env)
    requires
        typed(v, s),
        mem(sig, ExprSpec::Sort(l), rho, s),
    ensures
        typed(v, sortc(l)),
        typed(v, Cpt::U),
        is_zero(l) ==> typed(v, Cpt::Prop),
{
    reveal(mem);
    let w = choose|w: Wit| #[trigger] mem_w(sig, ExprSpec::Sort(l), rho, s, w);
    typed_basic();
    if s is Bot {
        reveal(typed);
        ty_of_bot(cstage(v, s), v);
    } else if s is Prop {
        prop_is_type_sf(v);
    }
}

/// THE PI RULE, TYPING: a Pi's denotation lies below Pi codes typed by the
/// sort `imax l1 l2`.
#[verifier::spinoff_prover]
pub proof fn sound_pi_ty(sig: Sig, ta: ExprSpec, b: ExprSpec, l1: LevelSpec, l2: LevelSpec, rho: Env)
    requires
        body_jc(sig, ta, b, rho),
        body_tyd(sig, ta, b, ExprSpec::Sort(l2), rho),
    ensures
        tyd(sig, ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(b)), rho, ExprSpec::Sort(crate::ti_syntax::imax(l1, l2))),
{
    let m = ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(b));
    let st = ExprSpec::Sort(crate::ti_syntax::imax(l1, l2));
    let c = sortc(crate::ti_syntax::imax(l1, l2));
    assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) implies tyd_w(sig, m, rho, st, u) by {
        if u is Bot {
            tyd_bot(sig, m, rho, st);
        } else {
            reveal(mem);
            let w = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
            if let Wit::Gen(a, gen, wa, ws) = w {
                assert(mem_w(sig, ta, rho, a, *wa));
                let (big, wit) = raise_gen(sig, BinderKind::Pi, ta, b, ExprSpec::Sort(l2), rho, u, a, gen, ws);
                let g = gsteps(gen);
                let g2 = gsteps(big);
                let n = ht(big) + 1;
                parts_lower(big);
                typed_basic();
                if is_zero(crate::ti_syntax::imax(l1, l2)) {
                    imax_zero(l1, l2);
                }
                let outc = if is_zero(crate::ti_syntax::imax(l1, l2)) { Cpt::Prop } else { Cpt::U };
                typed_up(a, Cpt::U, (n - 1) as nat);
                assert forall|k: int| 0 <= k < g2.len() implies has_type((n - 1) as nat, #[trigger] g2[k].0, a)
                    && has_type((n - 1) as nat, g2[k].1, outc) by {
                    assert(g2[k] == (g[k].0, tw(sig, b, ext(rho, g[k].0), ExprSpec::Sort(l2), g[k].1).0));
                    let (v, s) = tw(sig, b, ext(rho, g[k].0), ExprSpec::Sort(l2), g[k].1);
                    assert(tyd_at(sig, b, ext(rho, g[k].0), ExprSpec::Sort(l2), g[k].1, v, s));
                    assert(entries_ok(sig, b, rho, a, gen, ws));
                    assert(typed(g[k].0, a));
                    typed_up(g[k].0, a, (n - 1) as nat);
                    typed_in_sort(sig, v, s, l2, ext(rho, g[k].0));
                    typed_up(v, outc, (n - 1) as nat);
                }
                assert(stg(n, c));
                assert(has_type(n, big, c));
                typed_down(big, c, n);
                le_trans(u, gen, big);
                assert(mem(sig, m, rho, big));
                assert(mem_w(sig, st, rho, c, Wit::Nil));
                assert(tyd_at(sig, m, rho, st, u, big, c));
                tyd_w_intro(sig, m, rho, st, u, big, c);
            }
        }
    }
}

/// THE LAMBDA RULE, TYPING: a lambda's denotation lies below lambdas typed
/// by Pi codes in the Pi type's denotation.
#[verifier::spinoff_prover]
pub proof fn sound_lam_ty(sig: Sig, ta: ExprSpec, bd: ExprSpec, tb: ExprSpec, rho: Env)
    requires
        body_jc(sig, ta, bd, rho),
        body_tyd(sig, ta, bd, tb, rho),
        body_jc(sig, ta, tb, rho),
    ensures
        tyd(sig, ExprSpec::Bind(BinderKind::Lam, Box::new(ta), Box::new(bd)), rho, ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb))),
{
    let m = ExprSpec::Bind(BinderKind::Lam, Box::new(ta), Box::new(bd));
    let pt = ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb));
    assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) implies tyd_w(sig, m, rho, pt, u) by {
        if u is Bot {
            tyd_bot(sig, m, rho, pt);
        } else {
            reveal(mem);
            let w = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
            if let Wit::Gen(a, gen, wa, ws) = w {
                assert(mem_w(sig, ta, rho, a, *wa));
                let (big, wit) = raise_gen(sig, BinderKind::Lam, ta, bd, tb, rho, u, a, gen, ws);
                let g = gsteps(gen);
                let g2 = gsteps(big);
                let nn = g.len();
                assert(entries_ok(sig, bd, rho, a, gen, ws));
                // the Pi code: same inputs, the outputs' types
                let gt = Seq::new(nn, |i: int| (g[i].0, tw(sig, bd, ext(rho, g[i].0), tb, g[i].1).1));
                let p = Cpt::Pi(Box::new(a), gt);
                assert forall|i: int| 0 <= i < nn implies #[trigger] tyd_at(sig, bd, ext(rho, g[i].0), tb, g[i].1, g2[i].1, gt[i].1) by {
                    assert(g2[i] == (g[i].0, tw(sig, bd, ext(rho, g[i].0), tb, g[i].1).0));
                }
                assert forall|i: int| 0 <= i < nn implies #[trigger] mem(sig, tb, ext(rho, gt[i].0), gt[i].1) by {
                    assert(tyd_at(sig, bd, ext(rho, g[i].0), tb, g[i].1, g2[i].1, gt[i].1));
                }
                let wsb = Seq::new(nn, |i: int| choose|v: Wit| #[trigger] mem_w(sig, tb, ext(rho, gt[i].0), gt[i].1, v));
                assert forall|k: int| 0 <= k < nn implies wf(#[trigger] gt[k].0) && wf(gt[k].1) && typed(gt[k].0, a)
                    && typed(gt[k].1, Cpt::U) && mem_w(sig, tb, ext(rho, gt[k].0), gt[k].1, wsb[k]) by {
                    assert(typed(g[k].0, a));
                    typed_wf(g[k].0, a);
                    assert(tyd_at(sig, bd, ext(rho, g[k].0), tb, g[k].1, g2[k].1, gt[k].1));
                    typed_wf(gt[k].1, Cpt::U);
                    assert(mem(sig, tb, ext(rho, gt[k].0), gt[k].1));
                }
                fok_iff(gt);
                assert forall|e1: (Cpt, Cpt), e2: (Cpt, Cpt)| #[trigger] gt.contains(e1) && #[trigger] gt.contains(e2) && compat(e1.0, e2.0)
                    implies compat(e1.1, e2.1) by {
                    let i = choose|i: int| 0 <= i < nn && gt[i] == e1;
                    let j = choose|j: int| 0 <= j < nn && gt[j] == e2;
                    let x12 = join(e1.0, e2.0);
                    typed_join(e1.0, e2.0, a);
                    join_ub(e1.0, e2.0);
                    assert(dfit(sig, ta, rho, a, x12));
                    assert(jc(sig, tb, ext(rho, x12)));
                    assert forall|q: nat| #[trigger] le(ext(rho, e1.0)(q), ext(rho, x12)(q)) by {
                        if q > 0 {
                            le_refl(rho((q - 1) as nat));
                        }
                    }
                    assert forall|q: nat| #[trigger] le(ext(rho, e2.0)(q), ext(rho, x12)(q)) by {
                        if q > 0 {
                            le_refl(rho((q - 1) as nat));
                        }
                    }
                    mem_env_mono(sig, tb, ext(rho, e1.0), ext(rho, x12), e1.1, wsb[i]);
                    mem_env_mono(sig, tb, ext(rho, e2.0), ext(rho, x12), e2.1, wsb[j]);
                    jc_elim(sig, tb, ext(rho, x12), e1.1, e2.1);
                }
                typed_wf(a, Cpt::U);
                assert(wf(p));
                // the Pi code is in the Pi type's denotation
                assert(entries_ok(sig, tb, rho, a, p, wsb));
                le_refl(p);
                assert(mem_w(sig, pt, rho, p, Wit::Gen(a, p, wa, wsb)));
                // typings at one stage
                let n = ht(p) + ht(big) + 2;
                parts_lower(p);
                parts_lower(big);
                typed_basic();
                typed_up(a, Cpt::U, (n - 1) as nat);
                assert forall|k: int| 0 <= k < nn implies has_type((n - 1) as nat, #[trigger] gt[k].0, a)
                    && has_type((n - 1) as nat, gt[k].1, Cpt::U) by {
                    typed_up(gt[k].0, a, (n - 1) as nat);
                    typed_up(gt[k].1, Cpt::U, (n - 1) as nat);
                }
                assert(stg(n, p) && stg(n, Cpt::U));
                assert(has_type(n, p, Cpt::U));
                typed_down(p, Cpt::U, n);
                assert forall|k: int| 0 <= k < nn implies has_type((n - 1) as nat, #[trigger] g2[k].0, a)
                    && has_type((n - 1) as nat, g2[k].1, cod(p, g2[k].0)) by {
                    assert(tyd_at(sig, bd, ext(rho, g[k].0), tb, g[k].1, g2[k].1, gt[k].1));
                    assert(g2[k].0 == g[k].0);
                    typed_up(g2[k].0, a, (n - 1) as nat);
                    typed_up(g2[k].1, gt[k].1, (n - 1) as nat);
                    assert(gt.contains(gt[k]));
                    assert(steps(p, false) == gt);
                    entry_appk(p, gt[k], false);
                    cod_typed_at(p, gt[k].0, n);
                    ty_weak((n - 1) as nat, g2[k].1, gt[k].1, cod(p, g2[k].0));
                }
                assert(stg(n, big));
                assert(has_type(n, big, p));
                typed_down(big, p, n);
                le_trans(u, gen, big);
                assert(mem(sig, m, rho, big));
                assert(mem(sig, pt, rho, p));
                assert(tyd_at(sig, m, rho, pt, u, big, p));
                tyd_w_intro(sig, m, rho, pt, u, big, p);
            }
        }
    }
}

pub proof fn app_sem_eq(sig: Sig, f: ExprSpec, x: ExprSpec, f2: ExprSpec, x2: ExprSpec, rho: Env)
    requires
        sem_eq(sig, f, f2, rho),
        sem_eq(sig, x, x2, rho),
    ensures
        sem_eq(sig, ExprSpec::App(Box::new(f), Box::new(x)), ExprSpec::App(Box::new(f2), Box::new(x2)), rho),
{
    let m = ExprSpec::App(Box::new(f), Box::new(x));
    let m2 = ExprSpec::App(Box::new(f2), Box::new(x2));
    assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) == mem(sig, m2, rho, u) by {
        reveal(mem);
        if mem(sig, m, rho, u) {
            let w = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
            if let Wit::Ap(wf_, wx, w1, w2) = w {
                assert(mem_w(sig, f, rho, wf_, *w1) && mem_w(sig, x, rho, wx, *w2));
                assert(mem(sig, f, rho, wf_) && mem(sig, x, rho, wx));
                assert(mem(sig, f, rho, wf_) == mem(sig, f2, rho, wf_));
                assert(mem(sig, x, rho, wx) == mem(sig, x2, rho, wx));
                let v1 = choose|v: Wit| #[trigger] mem_w(sig, f2, rho, wf_, v);
                let v2 = choose|v: Wit| #[trigger] mem_w(sig, x2, rho, wx, v);
                assert(mem_w(sig, m2, rho, u, Wit::Ap(wf_, wx, Box::new(v1), Box::new(v2))));
            }
        }
        if mem(sig, m2, rho, u) {
            let w = choose|w: Wit| #[trigger] mem_w(sig, m2, rho, u, w);
            if let Wit::Ap(wf_, wx, w1, w2) = w {
                assert(mem_w(sig, f2, rho, wf_, *w1) && mem_w(sig, x2, rho, wx, *w2));
                assert(mem(sig, f2, rho, wf_) && mem(sig, x2, rho, wx));
                assert(mem(sig, f, rho, wf_) == mem(sig, f2, rho, wf_));
                assert(mem(sig, x, rho, wx) == mem(sig, x2, rho, wx));
                let v1 = choose|v: Wit| #[trigger] mem_w(sig, f, rho, wf_, v);
                let v2 = choose|v: Wit| #[trigger] mem_w(sig, x, rho, wx, v);
                assert(mem_w(sig, m, rho, u, Wit::Ap(wf_, wx, Box::new(v1), Box::new(v2))));
            }
        }
    }
}

/// Application is well formed.
pub proof fn app_wf(w: Cpt, v: Cpt)
    requires
        wf(w),
        wf(v),
    ensures
        wf(crate::dom_compact::app(w, v)),
{
    if w is Lam {
        appk_wf(w, v, true);
    }
}

#[verifier::spinoff_prover]
proof fn app_jc_pair(sig: Sig, f: ExprSpec, x: ExprSpec, rho: Env, u1: Cpt, u2: Cpt)
    requires
        jc(sig, f, rho),
        jc(sig, x, rho),
        mem(sig, ExprSpec::App(Box::new(f), Box::new(x)), rho, u1),
        mem(sig, ExprSpec::App(Box::new(f), Box::new(x)), rho, u2),
    ensures
        jc_pair(sig, ExprSpec::App(Box::new(f), Box::new(x)), rho, u1, u2),
{
    let m = ExprSpec::App(Box::new(f), Box::new(x));
    reveal(mem);
    let w1 = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u1, w);
    let w2 = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u2, w);
    if let (Wit::Ap(f1, x1, a1, b1), Wit::Ap(f2, x2, a2, b2)) = (w1, w2) {
        assert(mem_w(sig, f, rho, f1, *a1) && mem_w(sig, f, rho, f2, *a2) && mem_w(sig, x, rho, x1, *b1) && mem_w(sig, x, rho, x2, *b2));
        assert(mem(sig, f, rho, f1) && mem(sig, f, rho, f2) && mem(sig, x, rho, x1) && mem(sig, x, rho, x2));
        jc_elim(sig, f, rho, f1, f2);
        jc_elim(sig, x, rho, x1, x2);
        mem_wf(sig, f, rho, f1, *a1);
        mem_wf(sig, f, rho, f2, *a2);
        mem_wf(sig, x, rho, x1, *b1);
        mem_wf(sig, x, rho, x2, *b2);
        let fw = join(f1, f2);
        let xv = join(x1, x2);
        join_ub(f1, f2);
        join_ub(x1, x2);
        app_wf(fw, xv);
        app_mono(f1, fw, x1, xv);
        app_mono(f2, fw, x2, xv);
        let top = crate::dom_compact::app(fw, xv);
        le_trans(u1, crate::dom_compact::app(f1, x1), top);
        le_trans(u2, crate::dom_compact::app(f2, x2), top);
        ub_compat(u1, u2, top);
        join_ub(u1, u2);
        join_lub(u1, u2, top);
        let wfw = choose|v: Wit| #[trigger] mem_w(sig, f, rho, fw, v);
        let wxv = choose|v: Wit| #[trigger] mem_w(sig, x, rho, xv, v);
        assert(mem_w(sig, m, rho, join(u1, u2), Wit::Ap(fw, xv, Box::new(wfw), Box::new(wxv))));
    }
}

pub proof fn app_jc(sig: Sig, f: ExprSpec, x: ExprSpec, rho: Env)
    requires
        jc(sig, f, rho),
        jc(sig, x, rho),
    ensures
        jc(sig, ExprSpec::App(Box::new(f), Box::new(x)), rho),
{
    let m = ExprSpec::App(Box::new(f), Box::new(x));
    assert forall|u1: Cpt, u2: Cpt| mem(sig, m, rho, u1) && mem(sig, m, rho, u2) implies #[trigger] jc_pair(sig, m, rho, u1, u2) by {
        app_jc_pair(sig, f, x, rho, u1, u2);
    }
    jc_intro(sig, m, rho);
}

/// A Pi code's codomain at a typed argument lies in the body's
/// denotation at that argument.
#[verifier::spinoff_prover]
pub proof fn cod_in_body(sig: Sig, ta: ExprSpec, tb: ExprSpec, rho: Env, p: Cpt, v: Cpt, ax: Cpt)
    requires
        mem(sig, ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb)), rho, p),
        wf(p),
        p is Pi,
        dfit(sig, ta, rho, ax, v),
        body_jc(sig, ta, tb, rho),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        mem(sig, tb, ext(rho, v), cod(p, v)),
{
    reveal(mem);
    let mpi = ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb));
    let w = choose|w: Wit| #[trigger] mem_w(sig, mpi, rho, p, w);
    typed_wf(v, ax);
    if let Wit::Gen(a, gen, wa, ws) = w {
        let g = gen->Pi_1;
        assert(entries_ok(sig, tb, rho, a, gen, ws));
        let ev = ext(rho, v);
        assert(jc(sig, tb, ev));
        let tg = seq![gen];
        assert(tg[0] == gen);
        let sm = selk(tg, v, ht(gen), false);
        assert forall|y: Cpt| #[trigger] sm.contains(y) implies mem(sig, tb, ev, y) by {
            sel_pi_mem(tg, v, ht(gen), 1, y);
            let k = choose|k: int| 0 <= k < g.len() && #[trigger] g[k].1 == y && le(g[k].0, v);
            assert(gsteps(gen)[k] == g[k]);
            assert(mem_w(sig, tb, ext(rho, g[k].0), y, ws[k]));
            assert forall|q: nat| #[trigger] le(ext(rho, g[k].0)(q), ev(q)) by {
                if q > 0 {
                    le_refl(rho((q - 1) as nat));
                }
            }
            mem_env_mono(sig, tb, ext(rho, g[k].0), ev, y, ws[k]);
        }
        assert forall|y: Cpt| #[trigger] sm.contains(y) implies wf(y) by {
            let wy = choose|w2: Wit| #[trigger] mem_w(sig, tb, ev, y, w2);
            mem_wf(sig, tb, ev, y, wy);
        }
        assert forall|y: Cpt, z: Cpt| #[trigger] sm.contains(y) && #[trigger] sm.contains(z) implies compat(y, z) by {
            jc_elim(sig, tb, ev, y, z);
        }
        assert(pw(sm));
        selk_fits(gen, v, false);
        pw_coh(sm, dec(ht(gen)));
        assert forall|i: int| 0 <= i < sm.len() implies #[trigger] mem(sig, tb, ev, sm[i]) by {
            assert(sm.contains(sm[i]));
        }
        jall_mem(sig, tb, ev, sm, sm.len() as int);
        let j = jall(sm);
        jall_fits(sm, dec(ht(gen)), sm.len() as int);
        // the Pi code's own selection lies below that join
        appk_wf(p, v, false);
        let sp = selk(seq![p], v, ht(p), false);
        let tp = seq![p];
        assert(tp[0] == p);
        assert forall|z: Cpt| #[trigger] sp.contains(z) implies le(z, j) by {
            sel_pi_mem(tp, v, ht(p), 1, z);
            let q = choose|q: int| 0 <= q < p->Pi_1.len() && #[trigger] p->Pi_1[q].1 == z && le(p->Pi_1[q].0, v);
            let e = p->Pi_1[q];
            assert(p->Pi_1.contains(e));
            head_le(p, gen);
            entry_le(p, gen, e, false);
            sel_mono(tg, e.0, v, ht(gen));
            selk_fits(gen, e.0, false);
            le_set_sub(z, selk(tg, e.0, ht(gen), false), sm, dec(ht(gen)), dec(ht(gen)));
            le_set_jall(z, sm, dec(ht(gen)));
            assert(seq![j][0] == j);
            le_set_budget(z, seq![j], dec(ht(gen)), ht(j));
        }
        selk_fits(p, v, false);
        jall_lub(sp, dec(ht(p)), j);
        let wj = choose|w2: Wit| #[trigger] mem_w(sig, tb, ev, j, w2);
        mem_wf(sig, tb, ev, j, wj);
        mem_down_e(sig, tb, ev, j, cod(p, v));
    }
}

/// A Pi code's codomain at an argument's element lies in the instance.
pub proof fn cod_in_inst(sig: Sig, ta: ExprSpec, tb: ExprSpec, x: ExprSpec, rho: Env, p: Cpt, v: Cpt, ax: Cpt)
    requires
        mem(sig, ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb)), rho, p),
        wf(p),
        p is Pi,
        dfit(sig, ta, rho, ax, v),
        mem(sig, x, rho, v),
        body_jc(sig, ta, tb, rho),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        mem(sig, inst(0, x, tb), rho, cod(p, v)),
{
    use crate::ti_subst::{isub, inst_is_psub};
    cod_in_body(sig, ta, tb, rho, p, v, ax);
    let ev = ext(rho, v);
    covers_inst(sig, x, rho, v);
    reveal(mem);
    let wj = choose|w2: Wit| #[trigger] mem_w(sig, tb, ev, cod(p, v), w2);
    mem_psub_back(sig, tb, isub(0, x), rho, ev, cod(p, v), wj);
    inst_is_psub(0, x, tb);
}

/// THE APPLICATION RULE, TYPING.
#[verifier::spinoff_prover]
pub proof fn sound_app_ty(sig: Sig, f: ExprSpec, x: ExprSpec, ta: ExprSpec, tb: ExprSpec, rho: Env)
    requires
        tyd(sig, f, rho, ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb))),
        tyd(sig, x, rho, ta),
        body_jc(sig, ta, tb, rho),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        tyd(sig, ExprSpec::App(Box::new(f), Box::new(x)), rho, inst(0, x, tb)),
{
    let m = ExprSpec::App(Box::new(f), Box::new(x));
    let pt = ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb));
    let t = inst(0, x, tb);
    assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) implies tyd_w(sig, m, rho, t, u) by {
        if u is Bot {
            tyd_bot(sig, m, rho, t);
        } else {
            reveal(mem);
            let w = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
            if let Wit::Ap(fw, xv, w1, w2) = w {
                assert(mem_w(sig, f, rho, fw, *w1) && mem_w(sig, x, rho, xv, *w2));
                assert(mem(sig, f, rho, fw) && mem(sig, x, rho, xv));
                mem_wf(sig, f, rho, fw, *w1);
                mem_wf(sig, x, rho, xv, *w2);
                let (fw2, p) = tyd_w_elim(sig, f, rho, pt, fw);
                let (xv2, ax) = tyd_w_elim(sig, x, rho, ta, xv);
                typed_wf(fw2, p);
                typed_wf(xv2, ax);
                app_mono(fw, fw2, xv, xv2);
                let top = crate::dom_compact::app(fw2, xv2);
                le_trans(u, crate::dom_compact::app(fw, xv), top);
                if !(fw2 is Lam) {
                    assert(top == Cpt::Bot);
                    head_le(u, top);
                }
                reveal(typed);
                ty_inv(cstage(fw2, p), fw2, p);
                app_typed(fw2, p, xv2);
                assert(dfit(sig, ta, rho, ax, xv2));
                cod_in_inst(sig, ta, tb, x, rho, p, xv2, ax);
                app_wf(fw2, xv2);
                le_refl(top);
                let wf2 = choose|v: Wit| #[trigger] mem_w(sig, f, rho, fw2, v);
                let wx2 = choose|v: Wit| #[trigger] mem_w(sig, x, rho, xv2, v);
                assert(mem_w(sig, m, rho, top, Wit::Ap(fw2, xv2, Box::new(wf2), Box::new(wx2))));
                assert(tyd_at(sig, m, rho, t, u, top, cod(p, xv2)));
                tyd_w_intro(sig, m, rho, t, u, top, cod(p, xv2));
            }
        }
    }
}

/// An element of `body[x]` comes from `body` at a typed argument above an
/// element of `x`.
#[verifier::spinoff_prover]
pub proof fn inst_elem(sig: Sig, x: ExprSpec, body: ExprSpec, ta: ExprSpec, rho: Env, u: Cpt) -> (r: (Cpt, Cpt))
    requires
        mem(sig, inst(0, x, body), rho, u),
        tyd(sig, x, rho, ta),
        jc(sig, x, rho),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        mem(sig, x, rho, r.0),
        dfit(sig, ta, rho, r.1, r.0),
        mem(sig, body, ext(rho, r.0), u),
{
    use crate::ti_subst::{psub, isub, inst_is_psub};
    inst_is_psub(0, x, body);
    reveal(mem);
    let w = choose|w: Wit| #[trigger] mem_w(sig, psub(body, isub(0, x)), rho, u, w);
    jc_inst(sig, x, rho);
    let rr = mem_psub_fwd(sig, body, isub(0, x), rho, u, w);
    assert(mem(sig, isub(0, x)(0), rho, rr(0)));
    lift_zero(0, x);
    assert(mem(sig, x, rho, rr(0)));
    let (v2, ax) = tyd_w_elim(sig, x, rho, ta, rr(0));
    assert forall|i: nat| #[trigger] le(rr(i), ext(rho, v2)(i)) by {
        if i > 0 {
            assert(mem(sig, isub(0, x)(i), rho, rr(i)));
            let wv = choose|w2: Wit| #[trigger] mem_w(sig, ExprSpec::Var((i - 1) as nat), rho, rr(i), w2);
        }
    }
    let wb = choose|w2: Wit| #[trigger] mem_w(sig, body, rr, u, w2);
    mem_env_mono(sig, body, rr, ext(rho, v2), u, wb);
    (v2, ax)
}

/// What `body` denotes at an element of `x`, `body[x]` denotes.
pub proof fn inst_back(sig: Sig, x: ExprSpec, body: ExprSpec, rho: Env, v: Cpt, u: Cpt)
    requires
        mem(sig, x, rho, v),
        mem(sig, body, ext(rho, v), u),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        mem(sig, inst(0, x, body), rho, u),
{
    use crate::ti_subst::{psub, isub, inst_is_psub};
    covers_inst(sig, x, rho, v);
    reveal(mem);
    let w = choose|w: Wit| #[trigger] mem_w(sig, body, ext(rho, v), u, w);
    mem_psub_back(sig, body, isub(0, x), rho, ext(rho, v), u, w);
    inst_is_psub(0, x, body);
}

/// The selection of an element below a generator lies below the join of
/// the generator's own (coherent) selection.
pub proof fn sel_below_gen(w: Cpt, gen: Cpt, v: Cpt, lam: bool)
    requires
        wf(w),
        wf(v),
        kind(w, lam),
        kind(gen, lam),
        le(w, gen),
        pw(selk(seq![gen], v, ht(gen), lam)),
    ensures
        le(appk(w, v, lam), jall(selk(seq![gen], v, ht(gen), lam))),
{
    let tg = seq![gen];
    assert(tg[0] == gen);
    let sm = selk(tg, v, ht(gen), lam);
    let j = jall(sm);
    selk_fits(gen, v, lam);
    pw_coh(sm, dec(ht(gen)));
    jall_fits(sm, dec(ht(gen)), sm.len() as int);
    appk_wf(w, v, lam);
    let sw = selk(seq![w], v, ht(w), lam);
    let tw_ = seq![w];
    assert(tw_[0] == w);
    let h = steps(w, lam);
    assert forall|z: Cpt| #[trigger] sw.contains(z) implies le(z, j) by {
        if lam {
            sel_lam_mem(tw_, v, ht(w), 1, z);
        } else {
            sel_pi_mem(tw_, v, ht(w), 1, z);
        }
        let q = choose|q: int| 0 <= q < h.len() && #[trigger] h[q].1 == z && le(h[q].0, v);
        let e = h[q];
        assert(h.contains(e));
        entry_le(w, gen, e, lam);
        sel_mono(tg, e.0, v, ht(gen));
        selk_fits(gen, e.0, lam);
        le_set_sub(z, selk(tg, e.0, ht(gen), lam), sm, dec(ht(gen)), dec(ht(gen)));
        le_set_jall(z, sm, dec(ht(gen)));
        assert(seq![j][0] == j);
        le_set_budget(z, seq![j], dec(ht(gen)), ht(j));
    }
    selk_fits(w, v, lam);
    jall_lub(sw, dec(ht(w)), j);
}

/// A lambda's application at a typed argument lies in the body's
/// denotation at that argument.
#[verifier::spinoff_prover]
pub proof fn lam_in_body(sig: Sig, ta: ExprSpec, body: ExprSpec, rho: Env, fw: Cpt, v2: Cpt, ax: Cpt)
    requires
        mem(sig, ExprSpec::Bind(BinderKind::Lam, Box::new(ta), Box::new(body)), rho, fw),
        fw is Lam,
        dfit(sig, ta, rho, ax, v2),
        body_jc(sig, ta, body, rho),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        mem(sig, body, ext(rho, v2), crate::dom_compact::app(fw, v2)),
{
    let lm = ExprSpec::Bind(BinderKind::Lam, Box::new(ta), Box::new(body));
    reveal(mem);
    let w1 = choose|w: Wit| #[trigger] mem_w(sig, lm, rho, fw, w);
    mem_wf(sig, lm, rho, fw, w1);
    typed_wf(v2, ax);
    if let Wit::Gen(a, gen, wa, ws) = w1 {
        let ev = ext(rho, v2);
        assert(jc(sig, body, ev));
        assert(entries_ok(sig, body, rho, a, gen, ws));
        let tg = seq![gen];
        assert(tg[0] == gen);
        let g = gen->Lam_0;
        let sm = selk(tg, v2, ht(gen), true);
        assert forall|y: Cpt| #[trigger] sm.contains(y) implies mem(sig, body, ev, y) by {
            sel_lam_mem(tg, v2, ht(gen), 1, y);
            let k = choose|k: int| 0 <= k < g.len() && #[trigger] g[k].1 == y && le(g[k].0, v2);
            assert(gsteps(gen)[k] == g[k]);
            assert(mem_w(sig, body, ext(rho, g[k].0), y, ws[k]));
            assert forall|q: nat| #[trigger] le(ext(rho, g[k].0)(q), ev(q)) by {
                if q > 0 {
                    le_refl(rho((q - 1) as nat));
                }
            }
            mem_env_mono(sig, body, ext(rho, g[k].0), ev, y, ws[k]);
        }
        assert forall|y: Cpt| #[trigger] sm.contains(y) implies wf(y) by {
            let wy = choose|w3: Wit| #[trigger] mem_w(sig, body, ev, y, w3);
            mem_wf(sig, body, ev, y, wy);
        }
        assert forall|y: Cpt, z: Cpt| #[trigger] sm.contains(y) && #[trigger] sm.contains(z) implies compat(y, z) by {
            jc_elim(sig, body, ev, y, z);
        }
        assert forall|i: int| 0 <= i < sm.len() implies #[trigger] mem(sig, body, ev, sm[i]) by {
            assert(sm.contains(sm[i]));
        }
        jall_mem(sig, body, ev, sm, sm.len() as int);
        let j = jall(sm);
        head_le(fw, gen);
        sel_below_gen(fw, gen, v2, true);
        appk_wf(fw, v2, true);
        let wj = choose|w3: Wit| #[trigger] mem_w(sig, body, ev, j, w3);
        mem_wf(sig, body, ev, j, wj);
        mem_down_e(sig, body, ev, j, crate::dom_compact::app(fw, v2));
    }
}

/// BETA, forward: an application of a lambda denotes into the instance.
#[verifier::spinoff_prover]
pub proof fn beta_fwd(sig: Sig, ta: ExprSpec, body: ExprSpec, x: ExprSpec, rho: Env, u: Cpt)
    requires
        tyd(sig, x, rho, ta),
        body_jc(sig, ta, body, rho),
        forall|i: nat| #[trigger] wf(rho(i)),
        mem(sig, ExprSpec::App(Box::new(ExprSpec::Bind(BinderKind::Lam, Box::new(ta), Box::new(body))), Box::new(x)), rho, u),
    ensures
        mem(sig, inst(0, x, body), rho, u),
{
    let lm = ExprSpec::Bind(BinderKind::Lam, Box::new(ta), Box::new(body));
    let m = ExprSpec::App(Box::new(lm), Box::new(x));
    let nn = inst(0, x, body);
    reveal(mem);
    let w = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
    mem_bot(sig, nn, rho);
    if let Wit::Ap(fw, xv, w1, w2) = w {
        assert(mem_w(sig, lm, rho, fw, *w1) && mem_w(sig, x, rho, xv, *w2));
        mem_wf(sig, lm, rho, fw, *w1);
        mem_wf(sig, x, rho, xv, *w2);
        if !(fw is Lam) {
            assert(crate::dom_compact::app(fw, xv) == Cpt::Bot);
            if !(u is Bot) {
                head_le(u, Cpt::Bot);
            }
            return;
        }
        assert(mem(sig, x, rho, xv));
        let (v2, ax) = tyd_w_elim(sig, x, rho, ta, xv);
        typed_wf(v2, ax);
        assert(dfit(sig, ta, rho, ax, v2));
        assert(mem(sig, lm, rho, fw));
        lam_in_body(sig, ta, body, rho, fw, v2, ax);
        appk_mono_arg(fw, xv, v2, true);
        le_trans(u, crate::dom_compact::app(fw, xv), crate::dom_compact::app(fw, v2));
        inst_back(sig, x, body, rho, v2, crate::dom_compact::app(fw, v2));
        mem_down_e(sig, nn, rho, crate::dom_compact::app(fw, v2), u);
    }
}

/// BETA, backward: an element of the instance comes from a one-entry lambda
/// applied at a typed argument.
#[verifier::spinoff_prover]
pub proof fn beta_bwd(sig: Sig, ta: ExprSpec, body: ExprSpec, x: ExprSpec, rho: Env, u: Cpt)
    requires
        tyd(sig, x, rho, ta),
        jc(sig, x, rho),
        forall|i: nat| #[trigger] wf(rho(i)),
        mem(sig, inst(0, x, body), rho, u),
    ensures
        mem(sig, ExprSpec::App(Box::new(ExprSpec::Bind(BinderKind::Lam, Box::new(ta), Box::new(body))), Box::new(x)), rho, u),
{
    let lm = ExprSpec::Bind(BinderKind::Lam, Box::new(ta), Box::new(body));
    let m = ExprSpec::App(Box::new(lm), Box::new(x));
    let (v2, ax) = inst_elem(sig, x, body, ta, rho, u);
    reveal(mem);
    mem_bot(sig, m, rho);
    if u is Bot {
        return;
    }
    typed_wf(v2, ax);
    let wu = choose|w: Wit| #[trigger] mem_w(sig, body, ext(rho, v2), u, w);
    mem_wf(sig, body, ext(rho, v2), u, wu);
    let f = seq![(v2, u)];
    let lf = Cpt::Lam(f);
    assert(f[0] == (v2, u));
    compat_refl(u);
    assert(fun_ok(f));
    assert(wf(f[0].0) && wf(f[0].1));
    assert(forall|k: int| 0 <= k < f.len() ==> wf(#[trigger] f[k].0) && wf(f[k].1));
    assert(!(f[0].1 is Bot));
    assert(wf(lf));
    let wa = choose|w: Wit| #[trigger] mem_w(sig, ta, rho, ax, w);
    assert(entries_ok(sig, body, rho, ax, lf, seq![wu]));
    le_refl(lf);
    assert(mem_w(sig, lm, rho, lf, Wit::Gen(ax, lf, Box::new(wa), seq![wu])));
    assert(steps(lf, true).contains((v2, u)));
    entry_appk(lf, (v2, u), true);
    let wx = choose|w: Wit| #[trigger] mem_w(sig, x, rho, v2, w);
    assert(mem_w(sig, m, rho, u, Wit::Ap(lf, v2, Box::new(Wit::Gen(ax, lf, Box::new(wa), seq![wu])), Box::new(wx))));
}

/// An instance is typed within the instantiated type.
#[verifier::spinoff_prover]
pub proof fn inst_tyd(sig: Sig, ta: ExprSpec, body: ExprSpec, tb: ExprSpec, x: ExprSpec, rho: Env)
    requires
        tyd(sig, x, rho, ta),
        jc(sig, x, rho),
        body_tyd(sig, ta, body, tb, rho),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        tyd(sig, inst(0, x, body), rho, inst(0, x, tb)),
{
    let nb = inst(0, x, body);
    let nt = inst(0, x, tb);
    assert forall|u: Cpt| #[trigger] mem(sig, nb, rho, u) implies tyd_w(sig, nb, rho, nt, u) by {
        let (v2, ax) = inst_elem(sig, x, body, ta, rho, u);
        assert(dfit(sig, ta, rho, ax, v2));
        assert(tyd(sig, body, ext(rho, v2), tb));
        let (u2, b2) = tyd_w_elim(sig, body, ext(rho, v2), tb, u);
        inst_back(sig, x, body, rho, v2, u2);
        inst_back(sig, x, tb, rho, v2, b2);
        assert(tyd_at(sig, nb, rho, nt, u, u2, b2));
        tyd_w_intro(sig, nb, rho, nt, u, u2, b2);
    }
}

#[verifier::spinoff_prover]
proof fn inst_jc_pair(sig: Sig, ta: ExprSpec, body: ExprSpec, x: ExprSpec, rho: Env, u1: Cpt, u2: Cpt)
    requires
        tyd(sig, x, rho, ta),
        jc(sig, x, rho),
        body_jc(sig, ta, body, rho),
        forall|i: nat| #[trigger] wf(rho(i)),
        mem(sig, inst(0, x, body), rho, u1),
        mem(sig, inst(0, x, body), rho, u2),
    ensures
        jc_pair(sig, inst(0, x, body), rho, u1, u2),
{
    let (v1, a1) = inst_elem(sig, x, body, ta, rho, u1);
    let (v2, a2) = inst_elem(sig, x, body, ta, rho, u2);
    jc_elim(sig, x, rho, v1, v2);
    typed_wf(v1, a1);
    typed_wf(v2, a2);
    join_ub(v1, v2);
    let (vv, av) = tyd_w_elim(sig, x, rho, ta, join(v1, v2));
    le_trans(v1, join(v1, v2), vv);
    le_trans(v2, join(v1, v2), vv);
    assert(dfit(sig, ta, rho, av, vv));
    let ev = ext(rho, vv);
    assert(jc(sig, body, ev));
    reveal(mem);
    let w1 = choose|w: Wit| #[trigger] mem_w(sig, body, ext(rho, v1), u1, w);
    let w2 = choose|w: Wit| #[trigger] mem_w(sig, body, ext(rho, v2), u2, w);
    assert forall|q: nat| #[trigger] le(ext(rho, v1)(q), ev(q)) by {
        if q > 0 {
            le_refl(rho((q - 1) as nat));
        }
    }
    assert forall|q: nat| #[trigger] le(ext(rho, v2)(q), ev(q)) by {
        if q > 0 {
            le_refl(rho((q - 1) as nat));
        }
    }
    mem_env_mono(sig, body, ext(rho, v1), ev, u1, w1);
    mem_env_mono(sig, body, ext(rho, v2), ev, u2, w2);
    jc_elim(sig, body, ev, u1, u2);
    inst_back(sig, x, body, rho, vv, join(u1, u2));
}

/// An instance is join-closed.
pub proof fn inst_jc(sig: Sig, ta: ExprSpec, body: ExprSpec, x: ExprSpec, rho: Env)
    requires
        tyd(sig, x, rho, ta),
        jc(sig, x, rho),
        body_jc(sig, ta, body, rho),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        jc(sig, inst(0, x, body), rho),
{
    let nb = inst(0, x, body);
    assert forall|u1: Cpt, u2: Cpt| mem(sig, nb, rho, u1) && mem(sig, nb, rho, u2) implies #[trigger] jc_pair(sig, nb, rho, u1, u2) by {
        inst_jc_pair(sig, ta, body, x, rho, u1, u2);
    }
    jc_intro(sig, nb, rho);
}

/// THE BETA RULE.
pub proof fn sound_beta(sig: Sig, ta: ExprSpec, body: ExprSpec, tb: ExprSpec, x: ExprSpec, rho: Env)
    requires
        tyd(sig, x, rho, ta),
        jc(sig, x, rho),
        body_jc(sig, ta, body, rho),
        body_tyd(sig, ta, body, tb, rho),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        sound_ok(sig, ExprSpec::App(Box::new(ExprSpec::Bind(BinderKind::Lam, Box::new(ta), Box::new(body))), Box::new(x)),
            inst(0, x, body), inst(0, x, tb), rho),
{
    let m = ExprSpec::App(Box::new(ExprSpec::Bind(BinderKind::Lam, Box::new(ta), Box::new(body))), Box::new(x));
    let nb = inst(0, x, body);
    assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) == mem(sig, nb, rho, u) by {
        if mem(sig, m, rho, u) {
            beta_fwd(sig, ta, body, x, rho, u);
        }
        if mem(sig, nb, rho, u) {
            beta_bwd(sig, ta, body, x, rho, u);
        }
    }
    inst_tyd(sig, ta, body, tb, x, rho);
    inst_jc(sig, ta, body, x, rho);
    assert(sem_eq(sig, nb, m, rho));
    sem_eq_refl(sig, inst(0, x, tb), rho);
    sound_transfer(sig, nb, m, inst(0, x, tb), inst(0, x, tb), rho);
}

/// A typed lambda's inputs are typed at the Pi code's domain.
pub proof fn lam_entry_typed(u: Cpt, p: Cpt, k: int)
    requires
        typed(u, p),
        u is Lam,
        p is Pi,
        0 <= k < u->Lam_0.len(),
    ensures
        typed(u->Lam_0[k].0, *p->Pi_0),
{
    reveal(typed);
    let c = cstage(u, p);
    assert(has_type((c - 1) as nat, u->Lam_0[k].0, *p->Pi_0));
    typed_down(u->Lam_0[k].0, *p->Pi_0, (c - 1) as nat);
}

pub open spec fn eta_app(m: ExprSpec) -> ExprSpec {
    ExprSpec::App(Box::new(lift(1, 0, m)), Box::new(ExprSpec::Var(0)))
}

/// The eta premise: the two sides applied to the fresh variable agree
/// under every fitting extension.
pub open spec fn eta_body(sig: Sig, ta: ExprSpec, m: ExprSpec, n: ExprSpec, rho: Env) -> bool {
    forall|x: Cpt, a: Cpt| #[trigger] dfit(sig, ta, rho, a, x) ==> sem_eq(sig, eta_app(m), eta_app(n), ext(rho, x))
}

/// The witness on the other side of the eta premise, at one input.
pub open spec fn eta_pick(sig: Sig, n: ExprSpec, rho: Env, x: Cpt, z: Cpt) -> (Cpt, Cpt) {
    choose|nk: Cpt, vk: Cpt| mem(sig, n, rho, nk) && wf(nk) && wf(vk) && le(vk, x) && #[trigger] le(z, crate::dom_compact::app(nk, vk))
}

/// One input of the typed lambda crosses the eta premise.
proof fn eta_cross(sig: Sig, ta: ExprSpec, m: ExprSpec, n: ExprSpec, rho: Env, u2: Cpt, a: Cpt, x: Cpt)
    requires
        eta_body(sig, ta, m, n, rho),
        dfit(sig, ta, rho, a, x),
        mem(sig, m, rho, u2),
        wf(u2),
    ensures
        ({
            let (nk, vk) = eta_pick(sig, n, rho, x, crate::dom_compact::app(u2, x));
            mem(sig, n, rho, nk) && wf(nk) && wf(vk) && le(vk, x) && le(crate::dom_compact::app(u2, x), crate::dom_compact::app(nk, vk))
        }),
{
    let ex = ext(rho, x);
    let z = crate::dom_compact::app(u2, x);
    typed_wf(x, a);
    mem_lift1(sig, m, rho, x, u2);
    reveal(mem);
    let wl = choose|w: Wit| #[trigger] mem_w(sig, lift(1, 0, m), ex, u2, w);
    le_refl(x);
    assert(mem_w(sig, ExprSpec::Var(0), ex, x, Wit::Nil));
    app_wf(u2, x);
    le_refl(z);
    assert(mem_w(sig, eta_app(m), ex, z, Wit::Ap(u2, x, Box::new(wl), Box::new(Wit::Nil))));
    assert(sem_eq(sig, eta_app(m), eta_app(n), ex));
    assert(mem(sig, eta_app(m), ex, z));
    assert(mem(sig, eta_app(n), ex, z));
    let w = choose|w: Wit| #[trigger] mem_w(sig, eta_app(n), ex, z, w);
    if let Wit::Ap(nk, vk, w1, w2) = w {
        assert(mem_w(sig, lift(1, 0, n), ex, nk, *w1));
        mem_lift1(sig, n, rho, x, nk);
        assert(mem(sig, n, rho, nk));
        mem_wf(sig, lift(1, 0, n), ex, nk, *w1);
        assert(mem_w(sig, ExprSpec::Var(0), ex, vk, *w2));
        assert(mem(sig, n, rho, nk) && wf(nk) && wf(vk) && le(vk, x) && le(z, crate::dom_compact::app(nk, vk)));
    }
}

/// ETA, one inclusion: an element of `m` is an element of `n`.
#[verifier::spinoff_prover]
pub proof fn eta_sub(sig: Sig, ta: ExprSpec, tb: ExprSpec, m: ExprSpec, n: ExprSpec, rho: Env, u: Cpt)
    requires
        tyd(sig, m, rho, ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb))),
        jc(sig, n, rho),
        eta_body(sig, ta, m, n, rho),
        mem(sig, m, rho, u),
    ensures
        mem(sig, n, rho, u),
{
    let pt = ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb));
    mem_bot(sig, n, rho);
    reveal(mem);
    let wu = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
    mem_wf(sig, m, rho, u, wu);
    if u is Bot {
        return;
    }
    let (u2, p) = tyd_w_elim(sig, m, rho, pt, u);
    typed_wf(u2, p);
    head_le(u, u2);
    if p is Bot {
        reveal(typed);
        ty_of_bot(cstage(u2, p), u2);
    }
    let wp = choose|w: Wit| #[trigger] mem_w(sig, pt, rho, p, w);
    if let Wit::Gen(a, gen, wa, ws) = wp {
        head_le(p, gen);
        assert(mem_w(sig, ta, rho, a, *wa));
        assert(mem(sig, ta, rho, a));
        assert(typed(a, Cpt::U));
        reveal(typed);
        ty_inv(cstage(u2, p), u2, p);
        assert(u2 is Lam);
        let f = u2->Lam_0;
        let kk = f.len();
        pi_dom_le(p, gen);
        // every input fits the domain, and crosses the eta premise
        assert forall|k: int| 0 <= k < kk implies #[trigger] dfit(sig, ta, rho, a, f[k].0) by {
            lam_entry_typed(u2, p, k);
            typed_weak(f[k].0, *p->Pi_0, a);
        }
        let ns = Seq::new(kk, |k: int| eta_pick(sig, n, rho, f[k].0, crate::dom_compact::app(u2, f[k].0)).0);
        let vs = Seq::new(kk, |k: int| eta_pick(sig, n, rho, f[k].0, crate::dom_compact::app(u2, f[k].0)).1);
        assert forall|k: int| 0 <= k < kk implies mem(sig, n, rho, #[trigger] ns[k]) && wf(ns[k]) && wf(vs[k]) && le(vs[k], f[k].0)
            && le(crate::dom_compact::app(u2, f[k].0), crate::dom_compact::app(ns[k], vs[k])) by {
            assert(dfit(sig, ta, rho, a, f[k].0));
            eta_cross(sig, ta, m, n, rho, u2, a, f[k].0);
        }
        // join the other side's witnesses
        assert forall|y: Cpt| #[trigger] ns.contains(y) implies wf(y) by {
            let k = choose|k: int| 0 <= k < kk && ns[k] == y;
        }
        assert forall|y: Cpt, z: Cpt| #[trigger] ns.contains(y) && #[trigger] ns.contains(z) implies compat(y, z) by {
            let i = choose|i: int| 0 <= i < kk && ns[i] == y;
            let j = choose|j: int| 0 <= j < kk && ns[j] == z;
            jc_elim(sig, n, rho, y, z);
        }
        mxh_fits(ns);
        let b = mxh(ns, ns.len() as int);
        pw_coh(ns, b);
        jall_mem(sig, n, rho, ns, ns.len() as int);
        let nj = jall(ns);
        jall_pw(ns, ns.len() as int);
        // each output is below the joined witness applied at its input
        assert forall|k: int| 0 <= k < kk implies le(#[trigger] f[k].1, crate::dom_compact::app(nj, f[k].0)) by {
            assert(ns.contains(ns[k]));
            jall_ub(ns, b, ns[k]);
            assert(dfit(sig, ta, rho, a, f[k].0));
            typed_wf(f[k].0, a);
            app_mono(ns[k], nj, vs[k], f[k].0);
            assert(f.contains(f[k]));
            assert(steps(u2, true) == f);
            entry_appk(u2, f[k], true);
            le_trans(f[k].1, crate::dom_compact::app(u2, f[k].0), crate::dom_compact::app(ns[k], vs[k]));
            le_trans(f[k].1, crate::dom_compact::app(ns[k], vs[k]), crate::dom_compact::app(nj, f[k].0));
        }
        // the joined witness is a lambda: the typed lambda has a non-bottom output
        let k0 = choose|k: int| 0 <= k < kk && !(#[trigger] f[k].1 is Bot);
        if !(nj is Lam) {
            assert(crate::dom_compact::app(nj, f[k0].0) == Cpt::Bot);
            head_le(f[k0].1, Cpt::Bot);
        }
        // so the lambda lies below it
        let tn = seq![nj];
        assert(tn[0] == nj);
        assert forall|k: int| 0 <= k < kk implies
            le_set(#[trigger] f[k].1, sel_lam(tn, f[k].0, ht(nj), 1), dec(ht(nj))) by {
            assert(dfit(sig, ta, rho, a, f[k].0));
            typed_wf(f[k].0, a);
            appk_wf(nj, f[k].0, true);
            selk_fits(nj, f[k].0, true);
            let sk = selk(tn, f[k].0, ht(nj), true);
            le_set_jall(f[k].1, sk, dec(ht(nj)));
            let jj = jall(sk);
            assert(seq![jj][0] == jj);
            le_set_budget(f[k].1, seq![jj], ht(jj), dec(ht(nj)));
        }
        assert(le(u2, nj));
        le_trans(u, u2, nj);
        mem_down_e(sig, n, rho, nj, u);
    }
}

/// THE ETA RULE.
pub proof fn sound_eta(sig: Sig, ta: ExprSpec, tb: ExprSpec, m: ExprSpec, n: ExprSpec, rho: Env)
    requires
        sound_ok(sig, m, m, ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb)), rho),
        sound_ok(sig, n, n, ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb)), rho),
        eta_body(sig, ta, m, n, rho),
    ensures
        sound_ok(sig, m, n, ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb)), rho),
{
    assert forall|x: Cpt, a: Cpt| #[trigger] dfit(sig, ta, rho, a, x) implies sem_eq(sig, eta_app(n), eta_app(m), ext(rho, x)) by {
        assert(sem_eq(sig, eta_app(m), eta_app(n), ext(rho, x)));
    }
    assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) == mem(sig, n, rho, u) by {
        if mem(sig, m, rho, u) {
            eta_sub(sig, ta, tb, m, n, rho, u);
        }
        if mem(sig, n, rho, u) {
            eta_sub(sig, ta, tb, n, m, rho, u);
        }
    }
}

/// Soundness at `sig` of the derivations of a syntax signature `ss`, one
/// derivation and environment at a time.
pub open spec fn sound_at(ss: Sig, sig: Sig, d: Deriv, rho: Env) -> bool {
    valid(ss, d) && concl(d) is Eq && fits_env(sig, concl(d)->Eq_0, rho)
        ==> sound_ok(sig, concl(d)->Eq_1, concl(d)->Eq_2, concl(d)->Eq_3, rho)
}

/// A SOUNDNESS ORACLE: every derivation of `ss` is sound at `sig`. The
/// telescope lemmas take it instead of calling `sound`, so soundness's
/// Iota case can hand them the recursor-stripped signature's derivations.
#[verifier::opaque]
pub open spec fn sound_oracle(ss: Sig, sig: Sig) -> bool {
    forall|d: Deriv, rho: Env| #[trigger] sound_at(ss, sig, d, rho)
}

pub proof fn oracle_use(ss: Sig, sig: Sig, d: Deriv, rho: Env)
    requires
        sound_oracle(ss, sig),
        valid(ss, d),
        concl(d) is Eq,
        fits_env(sig, concl(d)->Eq_0, rho),
    ensures
        sound_ok(sig, concl(d)->Eq_1, concl(d)->Eq_2, concl(d)->Eq_3, rho),
{
    reveal(sound_oracle);
    assert(sound_at(ss, sig, d, rho));
}

/// An oracle below a rank is one below any lower rank: those
/// derivations are derivations below it (`ti_strip::iota_ok_below`).
pub proof fn oracle_down(sig: Sig, r1: int, r2: int)
    requires
        sound_oracle(crate::ti_strip::strip_below(sig, r2), sig),
        r1 <= r2 || r1 <= 0,
        crate::ti_syntax::iota_ok(sig),
    ensures
        sound_oracle(crate::ti_strip::strip_below(sig, r1), sig),
{
    let (s1, s2) = (crate::ti_strip::strip_below(sig, r1), crate::ti_strip::strip_below(sig, r2));
    reveal(sound_oracle);
    crate::ti_strip::iota_ok_below(sig, r2);
    assert(crate::ti_valid::sig_ext(s1, s2));
    assert forall|d: Deriv, rho: Env| #[trigger] sound_at(s1, sig, d, rho) by {
        if valid(s1, d) && concl(d) is Eq && fits_env(sig, concl(d)->Eq_0, rho) {
            crate::ti_valid::d_ext(s1, s2, d);
            assert(sound_at(s2, sig, d, rho));
        }
    }
}

/// The soundness theorem, as an oracle.
pub proof fn sound_all(sig: Sig)
    requires
        crate::dom_rec_end::sig_sr(sig),
    ensures
        sound_oracle(sig, sig),
{
    reveal(sound_oracle);
    assert forall|d: Deriv, rho: Env| #[trigger] sound_at(sig, sig, d, rho) by {
        if valid(sig, d) && concl(d) is Eq && fits_env(sig, concl(d)->Eq_0, rho) {
            sound(sig, d, rho);
        }
    }
}

/// SOUNDNESS OF THE MODEL (the paper's Theorem 2.31): under a fitting
/// environment, a derivation's sides denote the same join-closed set,
/// typed within its type.
/// Rule ProjIota's parameter premises are sound.
proof fn sound_pjs(sig: Sig, d: Deriv, rho: Env)
    requires
        crate::dom_rec_end::sig_sr(sig),
        valid(sig, d),
        concl(d) is Eq,
        d->Node_0 is ProjIota,
        fits_env(sig, concl(d)->Eq_0, rho),
    ensures
        crate::dom_proj_sound::pjs_sound(sig, concl(d)->Eq_1, rho),
    decreases crate::ti_strip::irank(sig, d), d, 0int,
{
    valid_prems(sig, d);
    crate::ti_strip::irank_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (g, m) = (j->Eq_0, j->Eq_1);
    reveal(crate::ti_syntax::proj_iota_ok);
    reveal(crate::ti_syntax::proj_pjs);
    let x = *m->Proj_1;
    let h = crate::beta_model::spine_head(x);
    let s = sig.ienv.ctor_ind[h->Const_0];
    let sh = crate::dom_code::canon_shape(sig, s);
    let args = crate::beta_model::spine_args(x);
    if args.len() >= sh.np && forall|q: int| 0 <= q < sh.np ==> crate::rec_canon::pdom_ok(#[trigger] sh.pdoms[q]) {
        let pj = crate::ti_syntax::proj_pjs(sig, g, m);
        reveal(crate::ti_syntax::proj_fire);
        crate::ti_syntax::struct_of_basic(sig, s);
        crate::dom_ctor_bound::ctor_shape_ind(sig, s);
        assert forall|q: int| 0 <= q < sh.np implies #[trigger] crate::dom_model::jc(sig, args[q], rho)
            && crate::dom_proj_sound::tyd_sort(sig, args[q], rho) by {
            let t = crate::expr_model::subst_expr_levels(sh.pdoms[q], sig.consts[s].lps, h->Const_1);
            assert(pj[q] == crate::ti_syntax::eq(g, args[q], args[q], t));
            assert(concl(ps[5 + q]) == pj[q]);
            sound(sig, ps[5 + q], rho);
            let lq = crate::rec_canon::pdom_lvl(t);
            crate::rec_canon::pdom_facts(sh.pdoms[q], sig.consts[s].lps, h->Const_1);
            crate::dom_code::canon_aliases_at(sig, s);
            crate::dom_code::pdoms_alias_at(sig, s, q);
            crate::dom_adeq_syn::pdom_alias_sl(sig, sh.pdoms[q], sig.consts[s].lps, h->Const_1);
            assert forall|u: Cpt| #[trigger] mem(sig, t, rho, u) == mem(sig, ExprSpec::Sort(lq), rho, u) by {
                pdom_mem(sig, t, rho, u);
            }
            sound_transfer(sig, args[q], args[q], t, ExprSpec::Sort(lq), rho);
            assert(crate::dom_sound::tyd(sig, args[q], rho, ExprSpec::Sort(lq)));
        }
    }
}

/// A definition's members are its value's (closed, so read anywhere).
pub proof fn mem_const_def(sig: Sig, c: u64, ls: Seq<LevelSpec>, rho: Env, u: Cpt)
    requires
        crate::dom_model::unfolds(sig, c, ls),
        crate::expr_model::nlbv(crate::ti_syntax::dval(sig, c, ls)) == 0,
    ensures
        mem(sig, ExprSpec::Const(c, ls), rho, u) ==> mem(sig, crate::ti_syntax::dval(sig, c, ls), rho, u),
        mem(sig, crate::ti_syntax::dval(sig, c, ls), rho, u) ==> mem(sig, ExprSpec::Const(c, ls), rho, u),
{
    let v = crate::ti_syntax::dval(sig, c, ls);
    crate::dom_model::mem_closed_env(sig, v, rho, u);
    reveal(mem);
    if mem(sig, ExprSpec::Const(c, ls), rho, u) {
        let w = choose|w: Wit| #[trigger] mem_w(sig, ExprSpec::Const(c, ls), rho, u, w);
        if u is Bot {
            crate::dom_model::mem_bot(sig, v, rho);
        } else {
            assert(!crate::dom_model::sem_const(sig, c, ls));
            assert(mem_w(sig, v, crate::dom_model::bot_env(), u, w));
        }
    }
    if mem(sig, v, rho, u) {
        let w = choose|w: Wit| #[trigger] mem_w(sig, v, crate::dom_model::bot_env(), u, w);
        crate::dom_model::mem_wf(sig, v, crate::dom_model::bot_env(), u, w);
        assert(mem_w(sig, ExprSpec::Const(c, ls), rho, u, w));
    }
}

/// A SOUND PARAMETER'S DOMAIN HAS ITS SORT'S MEMBERS: a sort alias's members
/// are its identity's, which apply to a sort's members as the sort
/// (`beta_fwd`, `beta_bwd`).
pub proof fn pdom_mem(sig: Sig, e: ExprSpec, rho: Env, a: Cpt)
    requires
        crate::rec_canon::pdom_ok(e),
        crate::dom_adeq_syn::pdom_alias(sig, e),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        mem(sig, e, rho, a) == mem(sig, crate::ti_syntax::sort(crate::rec_canon::pdom_lvl(e)), rho, a),
{
    if e is Sort {
        return;
    }
    let c = e->App_0->Const_0;
    let lu = e->App_0->Const_1[0];
    let l = e->App_1->Sort_0;
    let s = crate::ti_syntax::sort(l);
    let su = crate::ti_syntax::sort(lu);
    let cc = ExprSpec::Const(c, seq![lu]);
    assert(e->App_0->Const_1 =~= seq![lu]);
    assert(e == crate::dom_rel::sapp(cc, s));
    // the alias unfolds to the identity on its sort
    let p = sig.consts[c].lps[0];
    let v = crate::ti_syntax::lam(su, ExprSpec::Var(0));
    assert(crate::ti_syntax::dval(sig, c, seq![lu]) == v) by {
        reveal_with_fuel(crate::expr_model::subst_expr_levels, 3);
        assert(crate::level_model::find_level_idx(seq![p], p) == Some(0nat));
    }
    assert(crate::expr_model::nlbv(v) == 0) by { reveal_with_fuel(crate::expr_model::nlbv, 3); }
    assert(crate::ti_syntax::crank(sig, v) == 0) by { reveal_with_fuel(crate::ti_syntax::crank, 3); }
    assert(crate::dom_model::unfolds(sig, c, seq![lu]));
    // the sort typed at the alias's domain
    sound_univ(sig, l, l, rho);
    assert(crate::conv_cr::lev_eq(crate::ti_syntax::succ(l), lu)) by {
        assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(crate::ti_syntax::succ(l), r) == crate::level_model::interp(lu, r) by {
            assert(crate::level_model::interp(lu, r) == crate::level_model::interp(crate::ti_syntax::succ(l), r));
        }
    }
    sound_univ(sig, crate::ti_syntax::succ(l), lu, rho);
    sound_conv(sig, s, s, crate::ti_syntax::sort(crate::ti_syntax::succ(l)), su, rho);
    assert(body_jc(sig, su, ExprSpec::Var(0), rho)) by {
        assert forall|x: Cpt, a0: Cpt| #[trigger] dfit(sig, su, rho, a0, x) implies jc(sig, ExprSpec::Var(0), ext(rho, x)) by {
            crate::dom_model::typed_wf(x, a0);
            crate::dom_model::jc_var(sig, 0, ext(rho, x));
        }
    }
    assert(crate::subst_algebra::inst(0, s, ExprSpec::Var(0)) == s) by {
        reveal_with_fuel(crate::subst_algebra::inst, 2);
    }
    let bapp = ExprSpec::App(Box::new(v), Box::new(s));
    assert(bapp == crate::dom_rel::sapp(v, s));
    if mem(sig, e, rho, a) {
        let (uf, ux) = crate::dom_adeq::app_parts(sig, cc, s, rho, a);
        mem_const_def(sig, c, seq![lu], rho, uf);
        crate::dom_adeq::mem_app_intro(sig, v, s, rho, uf, ux);
        crate::dom_model::mem_down_e(sig, bapp, rho, crate::dom_compact::app(uf, ux), a);
        beta_fwd(sig, su, ExprSpec::Var(0), s, rho, a);
    }
    if mem(sig, s, rho, a) {
        beta_bwd(sig, su, ExprSpec::Var(0), s, rho, a);
        let (uf, ux) = crate::dom_adeq::app_parts(sig, v, s, rho, a);
        mem_const_def(sig, c, seq![lu], rho, uf);
        crate::dom_adeq::mem_app_intro(sig, cc, s, rho, uf, ux);
        crate::dom_model::mem_down_e(sig, e, rho, crate::dom_compact::app(uf, ux), a);
    }
}

pub proof fn sound(sig: Sig, d: Deriv, rho: Env)
    requires
        crate::dom_rec_end::sig_sr(sig),
        valid(sig, d),
        concl(d) is Eq,
        fits_env(sig, concl(d)->Eq_0, rho),
    ensures
        sound_ok(sig, concl(d)->Eq_1, concl(d)->Eq_2, concl(d)->Eq_3, rho),
    decreases crate::ti_strip::irank(sig, d), d, 1int,
{
    valid_prems(sig, d);
    crate::ti_strip::irank_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    match rule {
        Rule::Var(i) => {
            sound_var(sig, g, i, rho);
        },
        Rule::Univ(l, l2) => {
            sound_univ(sig, l, l2, rho);
        },
        Rule::Sym => {
            sound(sig, ps[0], rho);
            sound_sym(sig, m, n, a, rho);
        },
        Rule::Trans => {
            sound(sig, ps[0], rho);
            sound(sig, ps[1], rho);
            sound_trans(sig, m, concl(ps[0])->Eq_2, n, a, rho);
        },
        Rule::Conv(l) => {
            sound(sig, ps[0], rho);
            sound(sig, ps[1], rho);
            sound_conv(sig, m, n, concl(ps[0])->Eq_3, a, rho);
        },
        Rule::Irr(l) => {
            sound(sig, ps[0], rho);
            sound(sig, ps[1], rho);
            sound(sig, ps[2], rho);
            sound_irr(sig, m, n, a, l, rho);
        },
        Rule::PiCong(_, _) => sound_pi_d(sig, d, rho),
        Rule::LamCong(_, _) => sound_lam_d(sig, d, rho),
        Rule::AppCong(_, _) => sound_app_d(sig, d, rho),
        Rule::Beta(_, _) => sound_beta_d(sig, d, rho),
        Rule::Zeta(_) => sound_zeta_d(sig, d, rho),
        Rule::Eta(..) => sound_eta_d(sig, d, rho),
        Rule::ConstAx(_) | Rule::Local(_) => sound_leaf_d(sig, d, rho),
        Rule::ConstDef(_) | Rule::Delta(_) => sound_def_d(sig, d, rho),
        Rule::LitUnf(_) => {
            // a literal denotes what it unfolds to
            sound(sig, ps[2], rho);
            crate::dom_model::mem_lit(sig, m->NatLit_0, rho);
            assert(sem_eq(sig, n, m, rho));
            assert(sem_eq(sig, a, a, rho));
            sound_transfer(sig, n, m, a, a, rho);
        },
        Rule::ProjCong(_) => {
            reveal(crate::ti_syntax::proj_cong_ok);
            sound(sig, ps[0], rho);
            crate::dom_proj_sound::sound_proj_cong(sig, m->Proj_0, *m->Proj_1, *n->Proj_1, concl(ps[0])->Eq_3, a, rho);
        },
        Rule::ProjIota(l) => {
            reveal(crate::ti_syntax::proj_iota_ok);
            sound(sig, ps[0], rho);
            sound(sig, ps[1], rho);
            sound(sig, ps[3], rho);
            sound(sig, ps[4], rho);
            sound_pjs(sig, d, rho);
            crate::dom_proj_sound::sound_proj_iota(sig, m, n, a, concl(ps[2])->Eq_3, l, rho);
        },
        Rule::RecEta(_) => sound_reta_d(sig, d, rho),
        Rule::StructEta(_) => {
            reveal(crate::ti_syntax::struct_eta_ok);
            sound(sig, ps[0], rho);
            sound(sig, ps[1], rho);
            assert forall|k: int| 0 <= k < crate::ti_syntax::struct_nf(sig, a) implies
                #[trigger] crate::dom_sound::sem_eq(sig, ExprSpec::Proj(k as usize, Box::new(m)), ExprSpec::Proj(k as usize, Box::new(n)), rho) by {
                sound(sig, ps[3 + k], rho);
            }
            crate::dom_proj_sound::sound_seta(sig, m, n, a, rho);
        },
        Rule::Iota(l) => if crate::ti_syntax::iota_prop(sig, m) {
            // a proposition motive's: proof irrelevance
            crate::ti_syntax::prop_zero(sig, m, l);
            sound(sig, ps[0], rho);
            sound(sig, ps[1], rho);
            sound(sig, ps[2], rho);
            sound_irr(sig, m, n, a, l, rho);
        } else {
            sound(sig, ps[0], rho);
            // the derivations below the recursor's rank fire only lower
            // recursors
            let rr = crate::dom_code::rk(sig, crate::beta_model::spine_head(m)->Const_0);
            let ss = crate::ti_strip::strip_below(sig, rr);
            assert(crate::beta_model::spine_head(m) is Const) by {
                assert(crate::beta_model::rec_ready(sig.ienv, m));
            }
            crate::ti_strip::irank_prems(sig, d);
            reveal(sound_oracle);
            assert forall|d2: Deriv, rho2: Env| #[trigger] sound_at(ss, sig, d2, rho2) by {
                if valid(ss, d2) && concl(d2) is Eq && fits_env(sig, concl(d2)->Eq_0, rho2) {
                    crate::ti_strip::strip_below_valid(sig, rr, d2);
                    sound(sig, d2, rho2);
                }
            }
            crate::ti_meta::mk_d(sig, ps[0]);
            crate::ti_meta::mk_d(sig, ps[1]);
            // the parameter premises: the recursor's parameters and the
            // constructor's own denote alike
            reveal(crate::ti_syntax::iota_pjs);
            crate::ti_syntax::fire_interp(sig, m);
            let rd = sig.ienv.recs[crate::beta_model::spine_head(m)->Const_0];
            let args = crate::beta_model::spine_args(m);
            let cargs = crate::beta_model::spine_args(args[rd.major_idx as int]);
            assert forall|q: int| 0 <= q < rd.num_params implies #[trigger] sem_eq(sig, args[q], cargs[q], rho) by {
                let pj = crate::ti_syntax::iota_pjs(sig, g, m);
                assert(concl(ps[3 + q]) == pj[q]);
                sound(sig, ps[3 + q], rho);
            }
            assert(crate::ti_syntax::iota_lv(sig, m));
            crate::dom_iota_sound::sound_iota(sig, g, m, a, rho);
        },
        Rule::RedG(_) | Rule::LitTy(_) | Rule::ProjG(_) => {
            reveal(crate::ti_syntax::iota_ok);
            reveal(crate::ti_syntax::proj_g_ok);
        },
        _ => {},
    }
}

/// The recursor's eta step: the redex denotes as the redex at the major's
/// eta expansion, whose rule instance is the step's result.
#[verifier::spinoff_prover]
proof fn sound_reta_d(sig: Sig, d: Deriv, rho: Env)
    requires
        crate::dom_rec_end::sig_sr(sig),
        valid(sig, d),
        concl(d) is Eq,
        fits_env(sig, concl(d)->Eq_0, rho),
        d->Node_0 is RecEta,
    ensures
        sound_ok(sig, concl(d)->Eq_1, concl(d)->Eq_2, concl(d)->Eq_3, rho),
    decreases crate::ti_strip::irank(sig, d), d, 0int,
{
    valid_prems(sig, d);
    crate::ti_strip::irank_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (g, m, n, a) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
    let l = rule->RecEta_0;
    reveal(crate::ti_syntax::rec_eta_ok);
    sound(sig, ps[0], rho);
    sound(sig, ps[1], rho);
    sound(sig, ps[2], rho);
    sound(sig, ps[3], rho);
    sound(sig, ps[4], rho);
    if crate::ti_syntax::iota_prop(sig, m) {
        crate::ti_syntax::prop_zero(sig, m, l);
        sound_irr(sig, m, n, a, l, rho);
    } else {
        // the derivations below the recursor's rank fire only lower
        // recursors
        let rr = crate::dom_code::rk(sig, crate::beta_model::spine_head(m)->Const_0);
        let ss = crate::ti_strip::strip_below(sig, rr);
        assert(crate::ti_hred::rec_major(sig, m));
        crate::ti_strip::irank_prems(sig, d);
        reveal(sound_oracle);
        assert forall|d2: Deriv, rho2: Env| #[trigger] sound_at(ss, sig, d2, rho2) by {
            if valid(ss, d2) && concl(d2) is Eq && fits_env(sig, concl(d2)->Eq_0, rho2) {
                crate::ti_strip::strip_below_valid(sig, rr, d2);
                sound(sig, d2, rho2);
            }
        }
        crate::ti_meta::mk_d(sig, ps[1]);
        crate::ti_meta::mk_d(sig, ps[4]);
        sound_reta(sig, g, m, a, rho);
    }
}

#[verifier::spinoff_prover]
proof fn sound_pi_d(sig: Sig, d: Deriv, rho: Env)
    requires
        crate::dom_rec_end::sig_sr(sig),
        valid(sig, d),
        concl(d) is Eq,
        fits_env(sig, concl(d)->Eq_0, rho),
        d->Node_0 is PiCong,
    ensures
        sound_ok(sig, concl(d)->Eq_1, concl(d)->Eq_2, concl(d)->Eq_3, rho),
    decreases crate::ti_strip::irank(sig, d), d, 0int,
{
    valid_prems(sig, d);
    crate::ti_strip::irank_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::PiCong(l1, l2) = rule {
        let (ta, b) = (*m->Bind_1, *m->Bind_2);
        let (ta2, b2) = (*n->Bind_1, *n->Bind_2);
        sound(sig, ps[0], rho);
        assert forall|x: Cpt, aa: Cpt| #[trigger] dfit(sig, ta, rho, aa, x) implies sound_ok(sig, b, b2, ExprSpec::Sort(l2), ext(rho, x)) by {
            fits_ext(sig, g, rho, ta, aa, x);
            sound(sig, ps[1], ext(rho, x));
        }
        assert forall|x: Cpt, aa: Cpt| #[trigger] dfit(sig, ta, rho, aa, x) implies sem_eq(sig, b, b2, ext(rho, x)) by {
            assert(sound_ok(sig, b, b2, ExprSpec::Sort(l2), ext(rho, x)));
        }
        assert forall|x: Cpt, aa: Cpt| #[trigger] dfit(sig, ta, rho, aa, x) implies jc(sig, b, ext(rho, x)) by {
            assert(sound_ok(sig, b, b2, ExprSpec::Sort(l2), ext(rho, x)));
        }
        assert forall|x: Cpt, aa: Cpt| #[trigger] dfit(sig, ta, rho, aa, x) implies tyd(sig, b, ext(rho, x), ExprSpec::Sort(l2)) by {
            assert(sound_ok(sig, b, b2, ExprSpec::Sort(l2), ext(rho, x)));
        }
        bind_sem_eq(sig, BinderKind::Pi, ta, b, ta2, b2, rho);
        sound_pi_ty(sig, ta, b, l1, l2, rho);
        jc_binder(sig, BinderKind::Pi, ta, b, l1, rho);
    }
}

#[verifier::spinoff_prover]
proof fn sound_lam_d(sig: Sig, d: Deriv, rho: Env)
    requires
        crate::dom_rec_end::sig_sr(sig),
        valid(sig, d),
        concl(d) is Eq,
        fits_env(sig, concl(d)->Eq_0, rho),
        d->Node_0 is LamCong,
    ensures
        sound_ok(sig, concl(d)->Eq_1, concl(d)->Eq_2, concl(d)->Eq_3, rho),
    decreases crate::ti_strip::irank(sig, d), d, 0int,
{
    valid_prems(sig, d);
    crate::ti_strip::irank_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::LamCong(l1, l2) = rule {
        let (ta, bd) = (*m->Bind_1, *m->Bind_2);
        let (ta2, bd2) = (*n->Bind_1, *n->Bind_2);
        let tb = *a->Bind_2;
        sound(sig, ps[0], rho);
        assert forall|x: Cpt, aa: Cpt| #[trigger] dfit(sig, ta, rho, aa, x) implies sound_ok(sig, tb, tb, ExprSpec::Sort(l2), ext(rho, x)) by {
            fits_ext(sig, g, rho, ta, aa, x);
            sound(sig, ps[1], ext(rho, x));
        }
        assert forall|x: Cpt, aa: Cpt| #[trigger] dfit(sig, ta, rho, aa, x) implies sound_ok(sig, bd, bd2, tb, ext(rho, x)) by {
            fits_ext(sig, g, rho, ta, aa, x);
            sound(sig, ps[2], ext(rho, x));
        }
        assert forall|x: Cpt, aa: Cpt| #[trigger] dfit(sig, ta, rho, aa, x) implies sem_eq(sig, bd, bd2, ext(rho, x)) && jc(sig, bd, ext(rho, x))
            && tyd(sig, bd, ext(rho, x), tb) && jc(sig, tb, ext(rho, x)) by {
            assert(sound_ok(sig, bd, bd2, tb, ext(rho, x)));
            assert(sound_ok(sig, tb, tb, ExprSpec::Sort(l2), ext(rho, x)));
        }
        bind_sem_eq(sig, BinderKind::Lam, ta, bd, ta2, bd2, rho);
        sound_lam_ty(sig, ta, bd, tb, rho);
        jc_binder(sig, BinderKind::Lam, ta, bd, l1, rho);
    }
}

#[verifier::spinoff_prover]
proof fn sound_app_d(sig: Sig, d: Deriv, rho: Env)
    requires
        crate::dom_rec_end::sig_sr(sig),
        valid(sig, d),
        concl(d) is Eq,
        fits_env(sig, concl(d)->Eq_0, rho),
        d->Node_0 is AppCong,
    ensures
        sound_ok(sig, concl(d)->Eq_1, concl(d)->Eq_2, concl(d)->Eq_3, rho),
    decreases crate::ti_strip::irank(sig, d), d, 0int,
{
    valid_prems(sig, d);
    crate::ti_strip::irank_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::AppCong(l1, l2) = rule {
        let pt = concl(ps[0])->Eq_3;
        let (ta, tb) = (*pt->Bind_1, *pt->Bind_2);
        let (f, x0) = (*m->App_0, *m->App_1);
        let (f2, x2) = (*n->App_0, *n->App_1);
        sound(sig, ps[0], rho);
        sound(sig, ps[1], rho);
        assert forall|x: Cpt, aa: Cpt| #[trigger] dfit(sig, ta, rho, aa, x) implies sound_ok(sig, tb, tb, ExprSpec::Sort(l2), ext(rho, x)) by {
            fits_ext(sig, g, rho, ta, aa, x);
            sound(sig, ps[3], ext(rho, x));
        }
        assert forall|x: Cpt, aa: Cpt| #[trigger] dfit(sig, ta, rho, aa, x) implies jc(sig, tb, ext(rho, x)) by {
            assert(sound_ok(sig, tb, tb, ExprSpec::Sort(l2), ext(rho, x)));
        }
        assert(pt == ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb)));
        app_sem_eq(sig, f, x0, f2, x2, rho);
        sound_app_ty(sig, f, x0, ta, tb, rho);
        app_jc(sig, f, x0, rho);
    }
}

#[verifier::spinoff_prover]
proof fn sound_beta_d(sig: Sig, d: Deriv, rho: Env)
    requires
        crate::dom_rec_end::sig_sr(sig),
        valid(sig, d),
        concl(d) is Eq,
        fits_env(sig, concl(d)->Eq_0, rho),
        d->Node_0 is Beta,
    ensures
        sound_ok(sig, concl(d)->Eq_1, concl(d)->Eq_2, concl(d)->Eq_3, rho),
    decreases crate::ti_strip::irank(sig, d), d, 0int,
{
    valid_prems(sig, d);
    crate::ti_strip::irank_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::Beta(l1, l2) = rule {
        let (fl, x0) = (*m->App_0, *m->App_1);
        let (ta, bd) = (*fl->Bind_1, *fl->Bind_2);
        let tb = concl(ps[1])->Eq_3;
        sound(sig, ps[2], rho);
        assert forall|x: Cpt, aa: Cpt| #[trigger] dfit(sig, ta, rho, aa, x) implies sound_ok(sig, bd, bd, tb, ext(rho, x)) by {
            fits_ext(sig, g, rho, ta, aa, x);
            sound(sig, ps[1], ext(rho, x));
        }
        assert forall|x: Cpt, aa: Cpt| #[trigger] dfit(sig, ta, rho, aa, x) implies jc(sig, bd, ext(rho, x)) && tyd(sig, bd, ext(rho, x), tb) by {
            assert(sound_ok(sig, bd, bd, tb, ext(rho, x)));
        }
        assert(fl == ExprSpec::Bind(BinderKind::Lam, Box::new(ta), Box::new(bd)));
        sound_beta(sig, ta, bd, tb, x0, rho);
    }
}

#[verifier::spinoff_prover]
proof fn sound_eta_d(sig: Sig, d: Deriv, rho: Env)
    requires
        crate::dom_rec_end::sig_sr(sig),
        valid(sig, d),
        concl(d) is Eq,
        fits_env(sig, concl(d)->Eq_0, rho),
        d->Node_0 is Eta,
    ensures
        sound_ok(sig, concl(d)->Eq_1, concl(d)->Eq_2, concl(d)->Eq_3, rho),
    decreases crate::ti_strip::irank(sig, d), d, 0int,
{
    valid_prems(sig, d);
    crate::ti_strip::irank_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::Eta(l, _) = rule {
        let (ta, tb) = (*a->Bind_1, *a->Bind_2);
        sound(sig, ps[1], rho);
        sound(sig, ps[2], rho);
        assert forall|x: Cpt, aa: Cpt| #[trigger] dfit(sig, ta, rho, aa, x) implies sound_ok(sig, crate::ti_syntax::app(lift(1, 0, m), ExprSpec::Var(0)), crate::ti_syntax::app(lift(1, 0, n), ExprSpec::Var(0)), tb, ext(rho, x)) by {
            fits_ext(sig, g, rho, ta, aa, x);
            sound(sig, ps[3], ext(rho, x));
        }
        assert forall|x: Cpt, aa: Cpt| #[trigger] dfit(sig, ta, rho, aa, x) implies sem_eq(sig, eta_app(m), eta_app(n), ext(rho, x)) by {
            assert(sound_ok(sig, crate::ti_syntax::app(lift(1, 0, m), ExprSpec::Var(0)), crate::ti_syntax::app(lift(1, 0, n), ExprSpec::Var(0)), tb, ext(rho, x)));
        }
        assert(a == ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb)));
        sound_eta(sig, ta, tb, m, n, rho);
    }
}

/// Terms denoting only bottom are sound.
pub proof fn sound_bot_only(sig: Sig, m: ExprSpec, n: ExprSpec, t: ExprSpec, rho: Env)
    requires
        forall|u: Cpt| #[trigger] mem(sig, m, rho, u) ==> u is Bot,
        forall|u: Cpt| #[trigger] mem(sig, n, rho, u) ==> u is Bot,
    ensures
        sound_ok(sig, m, n, t, rho),
{
    mem_bot(sig, m, rho);
    mem_bot(sig, n, rho);
    assert(mem(sig, m, rho, Cpt::Bot) && mem(sig, n, rho, Cpt::Bot)) by {
        reveal(mem);
    }
    assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) == mem(sig, n, rho, u) by {}
    assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) implies tyd_w(sig, m, rho, t, u) by {
        tyd_bot(sig, m, rho, t);
    }
    assert forall|u1: Cpt, u2: Cpt| mem(sig, m, rho, u1) && mem(sig, m, rho, u2) implies #[trigger] jc_pair(sig, m, rho, u1, u2) by {
        assert(join(Cpt::Bot, Cpt::Bot) == Cpt::Bot);
    }
    jc_intro(sig, m, rho);
}

/// AXIOMS AND LOCALS: they denote only bottom.
#[verifier::spinoff_prover]
proof fn sound_leaf_d(sig: Sig, d: Deriv, rho: Env)
    requires
        crate::dom_rec_end::sig_sr(sig),
        valid(sig, d),
        concl(d) is Eq,
        fits_env(sig, concl(d)->Eq_0, rho),
        d->Node_0 is ConstAx || d->Node_0 is Local,
    ensures
        sound_ok(sig, concl(d)->Eq_1, concl(d)->Eq_2, concl(d)->Eq_3, rho),
    decreases crate::ti_strip::irank(sig, d), d, 0int,
{
    valid_prems(sig, d);
    crate::ti_strip::irank_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    match m {
        ExprSpec::Const(c, ls) => {
            let ls2 = n->Const_1;
            if sem_const(sig, c, ls) {
                sound(sig, ps[1], rho);
                crate::dom_sem::sound_sem(sig, c, ls, ls2, rule->ConstAx_0, rho);
                return;
            }
            let (lps, ty) = (sig.consts[c].lps, sig.consts[c].ty);
            crate::ti_level::ls_crank(sig, ty, lps, ls);
            crate::ti_level::ls_crank(sig, ty, lps, ls2);
            assert(!sem_const(sig, c, ls2));
            assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) implies u is Bot by {
                mem_const(sig, c, ls, rho, u);
            }
            assert forall|u: Cpt| #[trigger] mem(sig, n, rho, u) implies u is Bot by {
                mem_const(sig, c, ls2, rho, u);
            }
        },
        _ => {
            assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) implies u is Bot by {
                reveal(mem);
                let w = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
            }
        },
    }
    sound_bot_only(sig, m, n, a, rho);
}

/// DEFINITIONS: a definition denotes its value, which its premise makes
/// sound (in the bottom environment; the value is closed).
#[verifier::spinoff_prover]
proof fn sound_def_d(sig: Sig, d: Deriv, rho: Env)
    requires
        crate::dom_rec_end::sig_sr(sig),
        valid(sig, d),
        concl(d) is Eq,
        fits_env(sig, concl(d)->Eq_0, rho),
        d->Node_0 is ConstDef || d->Node_0 is Delta,
    ensures
        sound_ok(sig, concl(d)->Eq_1, concl(d)->Eq_2, concl(d)->Eq_3, rho),
    decreases crate::ti_strip::irank(sig, d), d, 0int,
{
    valid_prems(sig, d);
    crate::ti_strip::irank_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let t = j->Eq_3;
    let bot = bot_env();
    let c = m->Const_0;
    let ls = m->Const_1;
    let v1 = crate::ti_syntax::dval(sig, c, ls);
    crate::dom_fund::fits_bot(sig, g);
    sound(sig, ps[2], bot);
    let v2 = concl(ps[2])->Eq_2;
    // the members
    if rule is ConstDef {
        let ls2 = n->Const_1;
        assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) == mem(sig, n, rho, u) by {
            mem_const(sig, c, ls, rho, u);
            mem_const(sig, c, ls2, rho, u);
            assert(mem(sig, v1, bot, u) == mem(sig, v2, bot, u));
        }
    } else {
        mem_bot(sig, v1, bot);
        assert(mem(sig, v1, bot, Cpt::Bot)) by {
            reveal(mem);
        }
        assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) == mem(sig, n, rho, u) by {
            mem_const(sig, c, ls, rho, u);
            mem_closed_env(sig, v1, rho, u);
        }
    }
    // typed below the type's elements (the type is closed)
    assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) implies tyd_w(sig, m, rho, t, u) by {
        mem_const(sig, c, ls, rho, u);
        if u is Bot {
            tyd_bot(sig, m, rho, t);
        } else {
            assert(tyd_w(sig, v1, bot, t, u));
            let (vv, aa) = tyd_w_elim(sig, v1, bot, t, u);
            mem_const(sig, c, ls, rho, vv);
            mem_closed_env(sig, t, rho, aa);
            tyd_w_intro(sig, m, rho, t, u, vv, aa);
        }
    }
    // join-closed
    assert forall|u1: Cpt, u2: Cpt| mem(sig, m, rho, u1) && mem(sig, m, rho, u2) implies #[trigger] jc_pair(sig, m, rho, u1, u2) by {
        mem_const(sig, c, ls, rho, u1);
        mem_const(sig, c, ls, rho, u2);
        if !(u1 is Bot) && !(u2 is Bot) {
            jc_elim(sig, v1, bot, u1, u2);
            mem_const(sig, c, ls, rho, join(u1, u2));
        }
    }
    jc_intro(sig, m, rho);
}

#[verifier::spinoff_prover]
proof fn sound_zeta_d(sig: Sig, d: Deriv, rho: Env)
    requires
        crate::dom_rec_end::sig_sr(sig),
        valid(sig, d),
        concl(d) is Eq,
        fits_env(sig, concl(d)->Eq_0, rho),
        d->Node_0 is Zeta,
    ensures
        sound_ok(sig, concl(d)->Eq_1, concl(d)->Eq_2, concl(d)->Eq_3, rho),
    decreases crate::ti_strip::irank(sig, d), d, 0int,
{
    valid_prems(sig, d);
    crate::ti_strip::irank_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::Zeta(l1) = rule {
        let (ta, x0, bd) = (*m->Let_0, *m->Let_1, *m->Let_2);
        sound(sig, ps[2], rho);
        mem_let(sig, ta, x0, bd, rho);
        assert(sem_eq(sig, n, m, rho));
        assert(sem_eq(sig, a, a, rho));
        sound_transfer(sig, n, m, a, a, rho);
    }
}

/// THE RECURSOR'S ETA STEP IS SOUND: its redex denotes as the redex at the
/// major's eta expansion (the major and the expansion denote alike), and
/// that redex as its rule's instance, the step's result (Iota's soundness).
#[verifier::spinoff_prover]
proof fn sound_reta(sig: Sig, g: Ctx, m: ExprSpec, a: ExprSpec, rho: Env)
    requires
        crate::dom_rec_end::sig_sr(sig),
        crate::ti_syntax::iota_ok(sig),
        sound_oracle(crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, crate::beta_model::spine_head(m)->Const_0)), sig),
        crate::ti_hred::rec_smashed(sig, m),
        !crate::ti_syntax::iota_prop(sig, m),
        fits_env(sig, g, rho),
        sound_ok(sig, m, m, a, rho),
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, crate::ti_hred::rec_eta_result(sig, m), crate::ti_hred::rec_eta_result(sig, m), a)),
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, crate::ti_hred::reta_exp(sig, m), crate::ti_hred::reta_exp(sig, m), a)),
        sem_eq(sig, crate::beta_model::spine_args(m)[sig.ienv.recs[crate::beta_model::spine_head(m)->Const_0].major_idx as int],
            crate::ti_eta::eta_cx(sig, crate::beta_model::spine_head(m)->Const_0, crate::beta_model::spine_head(m)->Const_1, crate::beta_model::spine_args(m)), rho),
    ensures
        sound_ok(sig, m, crate::ti_hred::rec_eta_result(sig, m), a, rho),
{
    let h = crate::beta_model::spine_head(m);
    let a0 = crate::beta_model::spine_args(m);
    let rd = sig.ienv.recs[h->Const_0];
    let mi = rd.major_idx as int;
    let f = crate::beta_model::spine_app(h, a0.subrange(0, mi));
    let cx = crate::ti_eta::eta_cx(sig, h->Const_0, h->Const_1, a0);
    let m2 = crate::ti_hred::reta_exp(sig, m);
    let n = crate::ti_hred::rec_eta_result(sig, m);
    crate::ti_eta::reta_fits(sig, m);
    // the redex and the redex at the expansion
    sem_eq_refl(sig, f, rho);
    app_sem_eq(sig, f, a0[mi], f, cx, rho);
    // the rule's instance there
    crate::ti_hred::fire_inst_head(sig, m2, m);
    assert(crate::ti_syntax::iota_lv(sig, m2)) by { reveal(crate::ti_syntax::iota_lv); }
    let cargs = crate::beta_model::spine_args(cx);
    assert forall|q: int| 0 <= q < rd.num_params implies #[trigger] sem_eq(sig, crate::beta_model::spine_args(m2)[q],
        crate::beta_model::spine_args(crate::beta_model::spine_args(m2)[mi])[q], rho) by {
        assert(crate::beta_model::spine_args(m2)[mi] == cx);
        assert(crate::beta_model::spine_args(m2)[q] == a0[q]);
        sem_eq_refl(sig, a0[q], rho);
    }
    crate::dom_iota_sound::sound_iota(sig, g, m2, a, rho);
}

} // verus!
