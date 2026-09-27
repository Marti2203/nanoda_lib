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
use crate::ti_syntax::{Ctx, var_ty, is_zero};
#[cfg(verus_only)]
use crate::subst_algebra::{inst, lift, lift_zero};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The `i`-th variable's value is typed by `a`, a type in the denotation
/// of its declared type.
pub open spec fn fits_at(g: Ctx, rho: Env, i: nat, a: Cpt) -> bool {
    mem(var_ty(g, i), rho, a) && typed(a, Cpt::U) && typed(rho(i), a)
}

/// The `i`-th variable's value is typed within its declared type.
pub open spec fn fits_var(g: Ctx, rho: Env, i: nat) -> bool {
    exists|a: Cpt| #[trigger] fits_at(g, rho, i, a)
}

/// THE ENVIRONMENT FITS THE CONTEXT (the paper's Def 2.30).
pub open spec fn fits(g: Ctx, rho: Env) -> bool {
    &&& forall|i: nat| #[trigger] wf(rho(i))
    &&& forall|i: nat| i < g.len() ==> #[trigger] fits_var(g, rho, i)
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
pub proof fn fits_ext(g: Ctx, rho: Env, ta: ExprSpec, a: Cpt, x: Cpt)
    requires
        fits(g, rho),
        mem(ta, rho, a),
        typed(a, Cpt::U),
        typed(x, a),
    ensures
        fits(g.push(ta), ext(rho, x)),
{
    use crate::ti_meta::var_ty_push;
    typed_wf(x, a);
    assert forall|i: nat| #[trigger] wf(ext(rho, x)(i)) by {
        if i > 0 {
            assert(wf(rho((i - 1) as nat)));
        }
    }
    assert forall|i: nat| i < g.push(ta).len() implies #[trigger] fits_var(g.push(ta), ext(rho, x), i) by {
        var_ty_push(g, ta, i);
        if i == 0 {
            mem_lift1(ta, rho, x, a);
            assert(fits_at(g.push(ta), ext(rho, x), 0, a));
        } else {
            let k = (i - 1) as nat;
            assert(fits_var(g, rho, k));
            let ak = choose|a2: Cpt| #[trigger] fits_at(g, rho, k, a2);
            mem_lift1(var_ty(g, k), rho, x, ak);
            assert(fits_at(g.push(ta), ext(rho, x), i, ak));
        }
    }
}

/// (L5) Instantiating the first variable with `x` is covered by the
/// environment extended with an element of `x`'s denotation.
pub proof fn covers_inst(x: ExprSpec, rho: Env, v: Cpt)
    requires
        mem(x, rho, v),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        covers(crate::ti_subst::isub(0, x), rho, ext(rho, v)),
{
    reveal(mem);
    reveal(typed);
    assert forall|i: nat| #[trigger] mem(crate::ti_subst::isub(0, x)(i), rho, ext(rho, v)(i)) by {
        if i == 0 {
            lift_zero(0, x);
        } else {
            let k = (i - 1) as nat;
            le_refl(rho(k));
            assert(mem_w(ExprSpec::Var(k), rho, rho(k), Wit::Nil));
        }
    }
}

pub proof fn jc_inst(x: ExprSpec, rho: Env)
    requires
        jc(x, rho),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        forall|i: nat| #[trigger] jc(crate::ti_subst::isub(0, x)(i), rho),
{
    assert forall|i: nat| #[trigger] jc(crate::ti_subst::isub(0, x)(i), rho) by {
        if i == 0 {
            lift_zero(0, x);
        } else {
            jc_var((i - 1) as nat, rho);
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
pub open spec fn tyd_at(m: ExprSpec, rho: Env, t: ExprSpec, u: Cpt, v: Cpt, a: Cpt) -> bool {
    mem(m, rho, v) && le(u, v) && mem(t, rho, a) && typed(a, Cpt::U) && typed(v, a)
}

#[verifier::opaque]
pub open spec fn tyd_w(m: ExprSpec, rho: Env, t: ExprSpec, u: Cpt) -> bool {
    exists|v: Cpt, a: Cpt| #[trigger] tyd_at(m, rho, t, u, v, a)
}

/// Every element of `m` lies below one typed within `t` (the paper's
/// `[[m]] : [[t]]`).
pub open spec fn tyd(m: ExprSpec, rho: Env, t: ExprSpec) -> bool {
    forall|u: Cpt| #[trigger] mem(m, rho, u) ==> tyd_w(m, rho, t, u)
}

pub open spec fn sem_eq(m: ExprSpec, n: ExprSpec, rho: Env) -> bool {
    forall|u: Cpt| #[trigger] mem(m, rho, u) == mem(n, rho, u)
}

/// What soundness says of `m == n : t` under `rho`.
pub open spec fn sound_ok(m: ExprSpec, n: ExprSpec, t: ExprSpec, rho: Env) -> bool {
    sem_eq(m, n, rho) && tyd(m, rho, t) && jc(m, rho)
}

/// Bottom is typed below itself anywhere.
pub proof fn tyd_bot(m: ExprSpec, rho: Env, t: ExprSpec)
    ensures
        tyd_w(m, rho, t, Cpt::Bot),
{
    reveal(mem);
    reveal(typed);
    mem_bot(m, rho);
    mem_bot(t, rho);
    typed_basic();
    le_refl(Cpt::Bot);
    assert(tyd_at(m, rho, t, Cpt::Bot, Cpt::Bot, Cpt::Bot));
    tyd_w_intro(m, rho, t, Cpt::Bot, Cpt::Bot, Cpt::Bot);
}

pub proof fn tyd_w_intro(m: ExprSpec, rho: Env, t: ExprSpec, u: Cpt, v: Cpt, a: Cpt)
    requires
        tyd_at(m, rho, t, u, v, a),
    ensures
        tyd_w(m, rho, t, u),
{
    reveal(tyd_w);
}

pub proof fn tyd_w_elim(m: ExprSpec, rho: Env, t: ExprSpec, u: Cpt) -> (r: (Cpt, Cpt))
    requires
        tyd_w(m, rho, t, u),
    ensures
        tyd_at(m, rho, t, u, r.0, r.1),
{
    reveal(tyd_w);
    choose|v: Cpt, a: Cpt| #[trigger] tyd_at(m, rho, t, u, v, a)
}

/// Equal denotations share typing and join-closure.
pub proof fn sound_transfer(m: ExprSpec, n: ExprSpec, t: ExprSpec, t2: ExprSpec, rho: Env)
    requires
        sem_eq(m, n, rho),
        sem_eq(t, t2, rho),
        tyd(m, rho, t),
        jc(m, rho),
    ensures
        tyd(n, rho, t2),
        jc(n, rho),
{
    assert forall|u: Cpt| #[trigger] mem(n, rho, u) implies tyd_w(n, rho, t2, u) by {
        assert(mem(m, rho, u));
        let (v, a) = tyd_w_elim(m, rho, t, u);
        assert(mem(m, rho, v) && mem(t, rho, a));
        tyd_w_intro(n, rho, t2, u, v, a);
    }
    assert forall|u1: Cpt, u2: Cpt| mem(n, rho, u1) && mem(n, rho, u2) implies #[trigger] jc_pair(n, rho, u1, u2) by {
        assert(mem(m, rho, u1) && mem(m, rho, u2));
        jc_elim(m, rho, u1, u2);
        assert(mem(m, rho, join(u1, u2)));
    }
    jc_intro(n, rho);
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
pub proof fn type_elem(t: ExprSpec, rho: Env, l: LevelSpec, a: Cpt) -> (a2: Cpt)
    requires
        tyd(t, rho, ExprSpec::Sort(l)),
        mem(t, rho, a),
    ensures
        mem(t, rho, a2),
        le(a, a2),
        typed(a2, Cpt::U),
        is_zero(l) ==> (a2 is Bot || typed(a2, Cpt::Prop)),
{
    reveal(mem);
    reveal(typed);
    assert(tyd_w(t, rho, ExprSpec::Sort(l), a));
    let (v, s) = tyd_w_elim(t, rho, ExprSpec::Sort(l), a);
    let ws = choose|w: Wit| #[trigger] mem_w(ExprSpec::Sort(l), rho, s, w);
    typed_basic();
    if s is Bot {
        ty_of_bot(cstage(v, s), v);
    } else if s is Prop {
        prop_is_type_sf(v);
    }
    v
}

pub proof fn sem_eq_refl(m: ExprSpec, rho: Env)
    ensures
        sem_eq(m, m, rho),
{
}

pub proof fn sound_sym(m: ExprSpec, n: ExprSpec, t: ExprSpec, rho: Env)
    requires
        sound_ok(n, m, t, rho),
    ensures
        sound_ok(m, n, t, rho),
{
    assert(sem_eq(m, n, rho));
    sound_transfer(n, m, t, t, rho);
}

pub proof fn sound_trans(m: ExprSpec, mid: ExprSpec, n: ExprSpec, t: ExprSpec, rho: Env)
    requires
        sound_ok(m, mid, t, rho),
        sound_ok(mid, n, t, rho),
    ensures
        sound_ok(m, n, t, rho),
{
    assert(sem_eq(m, n, rho));
}

pub proof fn sound_conv(m: ExprSpec, n: ExprSpec, a: ExprSpec, b: ExprSpec, rho: Env)
    requires
        sound_ok(m, n, a, rho),
        sem_eq(a, b, rho),
    ensures
        sound_ok(m, n, b, rho),
{
    sound_transfer(m, m, a, b, rho);
}

/// VARIABLES: the value is the typed top of the variable's denotation.
pub proof fn sound_var(g: Ctx, i: nat, rho: Env)
    requires
        fits(g, rho),
        i < g.len(),
    ensures
        sound_ok(ExprSpec::Var(i), ExprSpec::Var(i), var_ty(g, i), rho),
{
    let m = ExprSpec::Var(i);
    assert(wf(rho(i)));
    jc_var(i, rho);
    assert(fits_var(g, rho, i));
    let a = choose|a: Cpt| #[trigger] fits_at(g, rho, i, a);
    assert forall|u: Cpt| #[trigger] mem(m, rho, u) implies tyd_w(m, rho, var_ty(g, i), u) by {
        reveal(mem);
        let w = choose|w: Wit| #[trigger] mem_w(m, rho, u, w);
        le_refl(rho(i));
        assert(mem_w(m, rho, rho(i), Wit::Nil));
        assert(tyd_at(m, rho, var_ty(g, i), u, rho(i), a));
        tyd_w_intro(m, rho, var_ty(g, i), u, rho(i), a);
    }
}

/// UNIVERSES: a sort's denotation is {bottom, its code}.
pub proof fn sound_univ(l: LevelSpec, l2: LevelSpec, rho: Env)
    requires
        crate::conv_cr::lev_eq(l, l2),
    ensures
        sound_ok(ExprSpec::Sort(l), ExprSpec::Sort(l2), ExprSpec::Sort(crate::ti_syntax::succ(l)), rho),
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
    assert(sem_eq(m, ExprSpec::Sort(l2), rho)) by {
        assert forall|u: Cpt| #[trigger] mem(m, rho, u) == mem(ExprSpec::Sort(l2), rho, u) by {
            if mem(m, rho, u) {
                let w = choose|w: Wit| #[trigger] mem_w(m, rho, u, w);
                assert(mem_w(ExprSpec::Sort(l2), rho, u, w));
            }
            if mem(ExprSpec::Sort(l2), rho, u) {
                let w = choose|w: Wit| #[trigger] mem_w(ExprSpec::Sort(l2), rho, u, w);
                assert(mem_w(m, rho, u, w));
            }
        }
    }
    assert forall|u: Cpt| #[trigger] mem(m, rho, u) implies tyd_w(m, rho, t, u) by {
        let w = choose|w: Wit| #[trigger] mem_w(m, rho, u, w);
        assert(mem_w(m, rho, c, Wit::Nil));
        assert(mem_w(t, rho, Cpt::U, Wit::Nil));
        le_refl(c);
        if u is Bot {
            assert(le(u, c));
        }
        assert(tyd_at(m, rho, t, u, c, Cpt::U));
        tyd_w_intro(m, rho, t, u, c, Cpt::U);
    }
    assert forall|u1: Cpt, u2: Cpt| mem(m, rho, u1) && mem(m, rho, u2) implies #[trigger] jc_pair(m, rho, u1, u2) by {
        let w1 = choose|w: Wit| #[trigger] mem_w(m, rho, u1, w);
        let w2 = choose|w: Wit| #[trigger] mem_w(m, rho, u2, w);
        assert(mem_w(m, rho, join(u1, u2), Wit::Nil));
    }
    jc_intro(m, rho);
}

/// PROOF IRRELEVANCE: a proposition's inhabitants denote {bottom}.
pub proof fn prop_denot_bot(m: ExprSpec, a: ExprSpec, l: LevelSpec, rho: Env, u: Cpt)
    requires
        is_zero(l),
        tyd(a, rho, ExprSpec::Sort(l)),
        tyd(m, rho, a),
        mem(m, rho, u),
    ensures
        u is Bot,
{
    let (v, aa) = tyd_w_elim(m, rho, a, u);
    let a2 = type_elem(a, rho, l, aa);
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
    let w = choose|w: Wit| #[trigger] mem_w(m, rho, u, w);
    mem_wf(m, rho, u, w);
    if !(u is Bot) {
        head_le(u, v);
    }
}

pub proof fn sound_irr(m: ExprSpec, n: ExprSpec, a: ExprSpec, l: LevelSpec, rho: Env)
    requires
        is_zero(l),
        sound_ok(a, a, ExprSpec::Sort(l), rho),
        sound_ok(m, m, a, rho),
        sound_ok(n, n, a, rho),
    ensures
        sound_ok(m, n, a, rho),
{
    assert forall|u: Cpt| #[trigger] mem(m, rho, u) == mem(n, rho, u) by {
        mem_bot(m, rho);
        mem_bot(n, rho);
        reveal(mem);
        if mem(m, rho, u) {
            prop_denot_bot(m, a, l, rho, u);
            assert(mem_w(n, rho, u, bot_w(n)));
        }
        if mem(n, rho, u) {
            prop_denot_bot(n, a, l, rho, u);
            assert(mem_w(m, rho, u, bot_w(m)));
        }
    }
}

} // verus!
