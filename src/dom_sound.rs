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

/// `x` is typed by a type `a` in the denotation of the domain `ta`.
pub open spec fn dfit(ta: ExprSpec, rho: Env, a: Cpt, x: Cpt) -> bool {
    mem(ta, rho, a) && typed(a, Cpt::U) && typed(x, a)
}

/// The body is join-closed under every fitting extension.
pub open spec fn body_jc(ta: ExprSpec, body: ExprSpec, rho: Env) -> bool {
    forall|x: Cpt, a: Cpt| #[trigger] dfit(ta, rho, a, x) ==> jc(body, ext(rho, x))
}

/// The generator's shape for a binder kind.
pub open spec fn gen_shape(bk: BinderKind, a: Cpt, gen: Cpt) -> bool {
    if bk == BinderKind::Pi { gen is Pi && *gen->Pi_0 == a } else { gen is Lam }
}

/// MERGING TWO GENERATORS of a binder's denotation into one above both.
#[verifier::spinoff_prover]
pub proof fn merge_gen(
    bk: BinderKind, ta: ExprSpec, body: ExprSpec, l: LevelSpec, rho: Env,
    a1: Cpt, gen1: Cpt, ws1: Seq<Wit>, a2: Cpt, gen2: Cpt, ws2: Seq<Wit>,
) -> (r: (Cpt, Cpt, Wit))
    requires
        jc(ta, rho),
        tyd(ta, rho, ExprSpec::Sort(l)),
        body_jc(ta, body, rho),
        mem(ta, rho, a1),
        mem(ta, rho, a2),
        typed(a1, Cpt::U),
        typed(a2, Cpt::U),
        gen_shape(bk, a1, gen1),
        gen_shape(bk, a2, gen2),
        entries_ok(body, rho, a1, gen1, ws1),
        entries_ok(body, rho, a2, gen2, ws2),
        bk == BinderKind::Lam ==> exists|k: int| 0 <= k < gen1->Lam_0.len() && !(#[trigger] gen1->Lam_0[k].1 is Bot),
    ensures
        le(gen1, r.1),
        le(gen2, r.1),
        wf(r.1),
        mem_w(ExprSpec::Bind(bk, Box::new(ta), Box::new(body)), rho, r.1, r.2),
{
    let lam = bk == BinderKind::Lam;
    jc_elim(ta, rho, a1, a2);
    typed_wf(a1, Cpt::U);
    typed_wf(a2, Cpt::U);
    join_ub(a1, a2);
    let a = type_elem(ta, rho, l, join(a1, a2));
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
    assert forall|i: int| 0 <= i < gg.len() implies typed(#[trigger] gg[i].0, a) && mem_w(body, ext(rho, gg[i].0), gg[i].1, ws[i]) by {
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
        mem_wf(body, ext(rho, gg[k].0), gg[k].1, ws[k]);
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
        assert(dfit(ta, rho, a, x12));
        assert(jc(body, ext(rho, x12)));
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
        mem_env_mono(body, ext(rho, e1.0), ext(rho, x12), e1.1, ws[i]);
        mem_env_mono(body, ext(rho, e2.0), ext(rho, x12), e2.1, ws[j]);
        reveal(mem);
        jc_elim(body, ext(rho, x12), e1.1, e2.1);
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
    let wa = choose|w: Wit| #[trigger] mem_w(ta, rho, a, w);
    assert(entries_ok(body, rho, a, big, ws));
    le_refl(big);
    let wit = Wit::Gen(a, big, Box::new(wa), ws);
    assert(mem_w(ExprSpec::Bind(bk, Box::new(ta), Box::new(body)), rho, big, wit));
    (a, big, wit)
}

/// One pair of a binder's denotation joins inside it.
#[verifier::spinoff_prover]
proof fn jc_bind_pair(bk: BinderKind, ta: ExprSpec, body: ExprSpec, l: LevelSpec, rho: Env, u1: Cpt, u2: Cpt)
    requires
        jc(ta, rho),
        tyd(ta, rho, ExprSpec::Sort(l)),
        body_jc(ta, body, rho),
        mem(ExprSpec::Bind(bk, Box::new(ta), Box::new(body)), rho, u1),
        mem(ExprSpec::Bind(bk, Box::new(ta), Box::new(body)), rho, u2),
    ensures
        jc_pair(ExprSpec::Bind(bk, Box::new(ta), Box::new(body)), rho, u1, u2),
{
    let m = ExprSpec::Bind(bk, Box::new(ta), Box::new(body));
    reveal(mem);
    let w1 = choose|w: Wit| #[trigger] mem_w(m, rho, u1, w);
    let w2 = choose|w: Wit| #[trigger] mem_w(m, rho, u2, w);
    if u1 is Bot {
        assert(join(u1, u2) == u2);
        return;
    }
    if u2 is Bot {
        assert(join(u1, u2) == u1);
        return;
    }
    if let (Wit::Gen(a1, gen1, wa1, ws1), Wit::Gen(a2, gen2, wa2, ws2)) = (w1, w2) {
        assert(mem_w(ta, rho, a1, *wa1) && mem_w(ta, rho, a2, *wa2));
        if bk == BinderKind::Lam {
            head_le(u1, gen1);
            below_lam_nonbot(u1, gen1);
        }
        let (a, big, wit) = merge_gen(bk, ta, body, l, rho, a1, gen1, ws1, a2, gen2, ws2);
        le_trans(u1, gen1, big);
        le_trans(u2, gen2, big);
        ub_compat(u1, u2, big);
        join_ub(u1, u2);
        join_lub(u1, u2, big);
        mem_down(m, rho, big, join(u1, u2), wit);
    }
}

/// A BINDER'S DENOTATION IS JOIN-CLOSED when its domain is a join-closed
/// type and its body is join-closed under every fitting extension.
pub proof fn jc_binder(bk: BinderKind, ta: ExprSpec, body: ExprSpec, l: LevelSpec, rho: Env)
    requires
        jc(ta, rho),
        tyd(ta, rho, ExprSpec::Sort(l)),
        body_jc(ta, body, rho),
    ensures
        jc(ExprSpec::Bind(bk, Box::new(ta), Box::new(body)), rho),
{
    let m = ExprSpec::Bind(bk, Box::new(ta), Box::new(body));
    assert forall|u1: Cpt, u2: Cpt| mem(m, rho, u1) && mem(m, rho, u2) implies #[trigger] jc_pair(m, rho, u1, u2) by {
        jc_bind_pair(bk, ta, body, l, rho, u1, u2);
    }
    jc_intro(m, rho);
}

/// Bodies agree under every fitting extension.
pub open spec fn body_eq(ta: ExprSpec, b: ExprSpec, b2: ExprSpec, rho: Env) -> bool {
    forall|x: Cpt, a: Cpt| #[trigger] dfit(ta, rho, a, x) ==> sem_eq(b, b2, ext(rho, x))
}

/// One direction of `bind_sem_eq`.
#[verifier::spinoff_prover]
proof fn bind_sub(bk: BinderKind, ta: ExprSpec, b: ExprSpec, ta2: ExprSpec, b2: ExprSpec, rho: Env, u: Cpt)
    requires
        sem_eq(ta, ta2, rho),
        body_eq(ta, b, b2, rho),
        mem(ExprSpec::Bind(bk, Box::new(ta), Box::new(b)), rho, u),
    ensures
        mem(ExprSpec::Bind(bk, Box::new(ta2), Box::new(b2)), rho, u),
{
    let m = ExprSpec::Bind(bk, Box::new(ta), Box::new(b));
    let m2 = ExprSpec::Bind(bk, Box::new(ta2), Box::new(b2));
    reveal(mem);
    let w = choose|w: Wit| #[trigger] mem_w(m, rho, u, w);
    if u is Bot {
        assert(mem_w(m2, rho, u, Wit::Nil));
    } else if let Wit::Gen(a, gen, wa, ws) = w {
        assert(mem_w(ta, rho, a, *wa));
        assert(mem(ta, rho, a));
        assert(mem(ta, rho, a) == mem(ta2, rho, a));
        assert(mem(ta2, rho, a));
        let wa2 = choose|v: Wit| #[trigger] mem_w(ta2, rho, a, v);
        let st = gsteps(gen);
        assert(entries_ok(b, rho, a, gen, ws));
        assert forall|i: int| 0 <= i < ws.len() implies #[trigger] mem(b2, ext(rho, st[i].0), st[i].1) by {
            assert(dfit(ta, rho, a, st[i].0));
            assert(sem_eq(b, b2, ext(rho, st[i].0)));
            assert(mem_w(b, ext(rho, st[i].0), st[i].1, ws[i]));
            assert(mem(b, ext(rho, st[i].0), st[i].1));
        }
        let ws2 = Seq::new(ws.len(), |i: int| choose|v: Wit| #[trigger] mem_w(b2, ext(rho, st[i].0), st[i].1, v));
        assert forall|i: int| 0 <= i < ws2.len() implies
            typed(#[trigger] gsteps(gen)[i].0, a) && mem_w(b2, ext(rho, gsteps(gen)[i].0), gsteps(gen)[i].1, ws2[i]) by {
            assert(mem(b2, ext(rho, st[i].0), st[i].1));
        }
        assert(entries_ok(b2, rho, a, gen, ws2));
        assert(mem_w(m2, rho, u, Wit::Gen(a, gen, Box::new(wa2), ws2)));
    }
}

/// BINDERS WITH EQUAL DOMAINS AND BODIES DENOTE THE SAME.
pub proof fn bind_sem_eq(bk: BinderKind, ta: ExprSpec, b: ExprSpec, ta2: ExprSpec, b2: ExprSpec, rho: Env)
    requires
        sem_eq(ta, ta2, rho),
        body_eq(ta, b, b2, rho),
    ensures
        sem_eq(ExprSpec::Bind(bk, Box::new(ta), Box::new(b)), ExprSpec::Bind(bk, Box::new(ta2), Box::new(b2)), rho),
{
    let m = ExprSpec::Bind(bk, Box::new(ta), Box::new(b));
    let m2 = ExprSpec::Bind(bk, Box::new(ta2), Box::new(b2));
    assert(sem_eq(ta2, ta, rho));
    assert forall|x: Cpt, a: Cpt| #[trigger] dfit(ta2, rho, a, x) implies sem_eq(b2, b, ext(rho, x)) by {
        assert(dfit(ta, rho, a, x));
    }
    assert forall|u: Cpt| #[trigger] mem(m, rho, u) == mem(m2, rho, u) by {
        if mem(m, rho, u) {
            bind_sub(bk, ta, b, ta2, b2, rho, u);
        }
        if mem(m2, rho, u) {
            bind_sub(bk, ta2, b2, ta, b, rho, u);
        }
    }
}

/// The body is typed within `t` under every fitting extension.
pub open spec fn body_tyd(ta: ExprSpec, body: ExprSpec, t: ExprSpec, rho: Env) -> bool {
    forall|x: Cpt, a: Cpt| #[trigger] dfit(ta, rho, a, x) ==> tyd(body, ext(rho, x), t)
}

/// A chosen typed element above `u` (when one exists).
pub open spec fn tw(m: ExprSpec, rho: Env, t: ExprSpec, u: Cpt) -> (Cpt, Cpt) {
    choose|v: Cpt, a: Cpt| #[trigger] tyd_at(m, rho, t, u, v, a)
}

/// RAISING A GENERATOR: each output replaced by the typed element above
/// it that the body's soundness provides.
#[verifier::spinoff_prover]
pub proof fn raise_gen(bk: BinderKind, ta: ExprSpec, body: ExprSpec, t: ExprSpec, rho: Env, u: Cpt, a: Cpt, gen: Cpt, ws: Seq<Wit>)
    -> (r: (Cpt, Wit))
    requires
        mem(ta, rho, a),
        typed(a, Cpt::U),
        gen_shape(bk, a, gen),
        entries_ok(body, rho, a, gen, ws),
        wf(u),
        !(u is Bot),
        le(u, gen),
        body_jc(ta, body, rho),
        body_tyd(ta, body, t, rho),
    ensures
        le(gen, r.0),
        wf(r.0),
        gen_shape(bk, a, r.0),
        mem_w(ExprSpec::Bind(bk, Box::new(ta), Box::new(body)), rho, r.0, r.1),
        gsteps(r.0).len() == gsteps(gen).len(),
        forall|i: int| 0 <= i < gsteps(gen).len() ==> #[trigger] gsteps(r.0)[i] == (gsteps(gen)[i].0,
            tw(body, ext(rho, gsteps(gen)[i].0), t, gsteps(gen)[i].1).0),
        forall|i: int| 0 <= i < gsteps(gen).len() ==> #[trigger] tyd_at(body, ext(rho, gsteps(gen)[i].0), t, gsteps(gen)[i].1,
            tw(body, ext(rho, gsteps(gen)[i].0), t, gsteps(gen)[i].1).0, tw(body, ext(rho, gsteps(gen)[i].0), t, gsteps(gen)[i].1).1),
{
    let lam = bk == BinderKind::Lam;
    let g = gsteps(gen);
    let n = g.len();
    // the typed elements above each output
    assert forall|i: int| 0 <= i < n implies #[trigger] tyd_at(body, ext(rho, g[i].0), t, g[i].1,
        tw(body, ext(rho, g[i].0), t, g[i].1).0, tw(body, ext(rho, g[i].0), t, g[i].1).1) by {
        assert(dfit(ta, rho, a, g[i].0));
        assert(tyd(body, ext(rho, g[i].0), t));
        reveal(mem);
        assert(mem_w(body, ext(rho, g[i].0), g[i].1, ws[i]));
        assert(mem(body, ext(rho, g[i].0), g[i].1));
        let (v, aa) = tyd_w_elim(body, ext(rho, g[i].0), t, g[i].1);
    }
    let g2 = Seq::new(n, |i: int| (g[i].0, tw(body, ext(rho, g[i].0), t, g[i].1).0));
    let big = if lam { Cpt::Lam(g2) } else { Cpt::Pi(Box::new(a), g2) };
    assert(gsteps(big) == g2);
    assert(steps(big, lam) == g2 && steps(gen, lam) == g);
    reveal(mem);
    // witnesses for the raised outputs
    assert forall|i: int| 0 <= i < n implies #[trigger] mem(body, ext(rho, g2[i].0), g2[i].1) by {
        assert(tyd_at(body, ext(rho, g[i].0), t, g[i].1, tw(body, ext(rho, g[i].0), t, g[i].1).0, tw(body, ext(rho, g[i].0), t, g[i].1).1));
    }
    let ws2 = Seq::new(n, |i: int| choose|w: Wit| #[trigger] mem_w(body, ext(rho, g2[i].0), g2[i].1, w));
    assert forall|i: int| 0 <= i < n implies typed(#[trigger] g2[i].0, a) && mem_w(body, ext(rho, g2[i].0), g2[i].1, ws2[i]) by {
        assert(entries_ok(body, rho, a, gen, ws));
        assert(typed(g[i].0, a));
        assert(mem(body, ext(rho, g2[i].0), g2[i].1));
    }
    // well formed
    assert forall|k: int| 0 <= k < n implies wf(#[trigger] g2[k].0) && wf(g2[k].1) by {
        typed_wf(g2[k].0, a);
        mem_wf(body, ext(rho, g2[k].0), g2[k].1, ws2[k]);
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
        assert(dfit(ta, rho, a, x12));
        assert(jc(body, ext(rho, x12)));
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
        mem_env_mono(body, ext(rho, e1.0), ext(rho, x12), e1.1, ws2[i]);
        mem_env_mono(body, ext(rho, e2.0), ext(rho, x12), e2.1, ws2[j]);
        jc_elim(body, ext(rho, x12), e1.1, e2.1);
    }
    if lam {
        head_le(u, gen);
        below_lam_nonbot(u, gen);
        let k = choose|k: int| 0 <= k < gen->Lam_0.len() && !(#[trigger] gen->Lam_0[k].1 is Bot);
        assert(tyd_at(body, ext(rho, g[k].0), t, g[k].1, g2[k].1, tw(body, ext(rho, g[k].0), t, g[k].1).1));
        mem_wf(body, ext(rho, g[k].0), g[k].1, ws[k]);
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
        assert(tyd_at(body, ext(rho, g[k].0), t, g[k].1, tw(body, ext(rho, g[k].0), t, g[k].1).0, tw(body, ext(rho, g[k].0), t, g[k].1).1));
    }
    if !lam {
        le_refl(a);
    }
    gen_raise(gen, big, lam);
    // in the denotation
    let wa = choose|w: Wit| #[trigger] mem_w(ta, rho, a, w);
    assert(entries_ok(body, rho, a, big, ws2));
    le_refl(big);
    let wit = Wit::Gen(a, big, Box::new(wa), ws2);
    assert(mem_w(ExprSpec::Bind(bk, Box::new(ta), Box::new(body)), rho, big, wit));
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
pub proof fn typed_in_sort(v: Cpt, s: Cpt, l: LevelSpec, rho: Env)
    requires
        typed(v, s),
        mem(ExprSpec::Sort(l), rho, s),
    ensures
        typed(v, sortc(l)),
        typed(v, Cpt::U),
        is_zero(l) ==> typed(v, Cpt::Prop),
{
    reveal(mem);
    let w = choose|w: Wit| #[trigger] mem_w(ExprSpec::Sort(l), rho, s, w);
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
pub proof fn sound_pi_ty(ta: ExprSpec, b: ExprSpec, l1: LevelSpec, l2: LevelSpec, rho: Env)
    requires
        body_jc(ta, b, rho),
        body_tyd(ta, b, ExprSpec::Sort(l2), rho),
    ensures
        tyd(ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(b)), rho, ExprSpec::Sort(crate::ti_syntax::imax(l1, l2))),
{
    let m = ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(b));
    let st = ExprSpec::Sort(crate::ti_syntax::imax(l1, l2));
    let c = sortc(crate::ti_syntax::imax(l1, l2));
    assert forall|u: Cpt| #[trigger] mem(m, rho, u) implies tyd_w(m, rho, st, u) by {
        if u is Bot {
            tyd_bot(m, rho, st);
        } else {
            reveal(mem);
            let w = choose|w: Wit| #[trigger] mem_w(m, rho, u, w);
            if let Wit::Gen(a, gen, wa, ws) = w {
                assert(mem_w(ta, rho, a, *wa));
                let (big, wit) = raise_gen(BinderKind::Pi, ta, b, ExprSpec::Sort(l2), rho, u, a, gen, ws);
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
                    assert(g2[k] == (g[k].0, tw(b, ext(rho, g[k].0), ExprSpec::Sort(l2), g[k].1).0));
                    let (v, s) = tw(b, ext(rho, g[k].0), ExprSpec::Sort(l2), g[k].1);
                    assert(tyd_at(b, ext(rho, g[k].0), ExprSpec::Sort(l2), g[k].1, v, s));
                    assert(entries_ok(b, rho, a, gen, ws));
                    assert(typed(g[k].0, a));
                    typed_up(g[k].0, a, (n - 1) as nat);
                    typed_in_sort(v, s, l2, ext(rho, g[k].0));
                    typed_up(v, outc, (n - 1) as nat);
                }
                assert(stg(n, c));
                assert(has_type(n, big, c));
                typed_down(big, c, n);
                le_trans(u, gen, big);
                assert(mem(m, rho, big));
                assert(mem_w(st, rho, c, Wit::Nil));
                assert(tyd_at(m, rho, st, u, big, c));
                tyd_w_intro(m, rho, st, u, big, c);
            }
        }
    }
}

/// THE LAMBDA RULE, TYPING: a lambda's denotation lies below lambdas typed
/// by Pi codes in the Pi type's denotation.
#[verifier::spinoff_prover]
pub proof fn sound_lam_ty(ta: ExprSpec, bd: ExprSpec, tb: ExprSpec, rho: Env)
    requires
        body_jc(ta, bd, rho),
        body_tyd(ta, bd, tb, rho),
        body_jc(ta, tb, rho),
    ensures
        tyd(ExprSpec::Bind(BinderKind::Lam, Box::new(ta), Box::new(bd)), rho, ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb))),
{
    let m = ExprSpec::Bind(BinderKind::Lam, Box::new(ta), Box::new(bd));
    let pt = ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb));
    assert forall|u: Cpt| #[trigger] mem(m, rho, u) implies tyd_w(m, rho, pt, u) by {
        if u is Bot {
            tyd_bot(m, rho, pt);
        } else {
            reveal(mem);
            let w = choose|w: Wit| #[trigger] mem_w(m, rho, u, w);
            if let Wit::Gen(a, gen, wa, ws) = w {
                assert(mem_w(ta, rho, a, *wa));
                let (big, wit) = raise_gen(BinderKind::Lam, ta, bd, tb, rho, u, a, gen, ws);
                let g = gsteps(gen);
                let g2 = gsteps(big);
                let nn = g.len();
                assert(entries_ok(bd, rho, a, gen, ws));
                // the Pi code: same inputs, the outputs' types
                let gt = Seq::new(nn, |i: int| (g[i].0, tw(bd, ext(rho, g[i].0), tb, g[i].1).1));
                let p = Cpt::Pi(Box::new(a), gt);
                assert forall|i: int| 0 <= i < nn implies #[trigger] tyd_at(bd, ext(rho, g[i].0), tb, g[i].1, g2[i].1, gt[i].1) by {
                    assert(g2[i] == (g[i].0, tw(bd, ext(rho, g[i].0), tb, g[i].1).0));
                }
                assert forall|i: int| 0 <= i < nn implies #[trigger] mem(tb, ext(rho, gt[i].0), gt[i].1) by {
                    assert(tyd_at(bd, ext(rho, g[i].0), tb, g[i].1, g2[i].1, gt[i].1));
                }
                let wsb = Seq::new(nn, |i: int| choose|v: Wit| #[trigger] mem_w(tb, ext(rho, gt[i].0), gt[i].1, v));
                assert forall|k: int| 0 <= k < nn implies wf(#[trigger] gt[k].0) && wf(gt[k].1) && typed(gt[k].0, a)
                    && typed(gt[k].1, Cpt::U) && mem_w(tb, ext(rho, gt[k].0), gt[k].1, wsb[k]) by {
                    assert(typed(g[k].0, a));
                    typed_wf(g[k].0, a);
                    assert(tyd_at(bd, ext(rho, g[k].0), tb, g[k].1, g2[k].1, gt[k].1));
                    typed_wf(gt[k].1, Cpt::U);
                    assert(mem(tb, ext(rho, gt[k].0), gt[k].1));
                }
                fok_iff(gt);
                assert forall|e1: (Cpt, Cpt), e2: (Cpt, Cpt)| #[trigger] gt.contains(e1) && #[trigger] gt.contains(e2) && compat(e1.0, e2.0)
                    implies compat(e1.1, e2.1) by {
                    let i = choose|i: int| 0 <= i < nn && gt[i] == e1;
                    let j = choose|j: int| 0 <= j < nn && gt[j] == e2;
                    let x12 = join(e1.0, e2.0);
                    typed_join(e1.0, e2.0, a);
                    join_ub(e1.0, e2.0);
                    assert(dfit(ta, rho, a, x12));
                    assert(jc(tb, ext(rho, x12)));
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
                    mem_env_mono(tb, ext(rho, e1.0), ext(rho, x12), e1.1, wsb[i]);
                    mem_env_mono(tb, ext(rho, e2.0), ext(rho, x12), e2.1, wsb[j]);
                    jc_elim(tb, ext(rho, x12), e1.1, e2.1);
                }
                typed_wf(a, Cpt::U);
                assert(wf(p));
                // the Pi code is in the Pi type's denotation
                assert(entries_ok(tb, rho, a, p, wsb));
                le_refl(p);
                assert(mem_w(pt, rho, p, Wit::Gen(a, p, wa, wsb)));
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
                    assert(tyd_at(bd, ext(rho, g[k].0), tb, g[k].1, g2[k].1, gt[k].1));
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
                assert(mem(m, rho, big));
                assert(mem(pt, rho, p));
                assert(tyd_at(m, rho, pt, u, big, p));
                tyd_w_intro(m, rho, pt, u, big, p);
            }
        }
    }
}

pub proof fn app_sem_eq(f: ExprSpec, x: ExprSpec, f2: ExprSpec, x2: ExprSpec, rho: Env)
    requires
        sem_eq(f, f2, rho),
        sem_eq(x, x2, rho),
    ensures
        sem_eq(ExprSpec::App(Box::new(f), Box::new(x)), ExprSpec::App(Box::new(f2), Box::new(x2)), rho),
{
    let m = ExprSpec::App(Box::new(f), Box::new(x));
    let m2 = ExprSpec::App(Box::new(f2), Box::new(x2));
    assert forall|u: Cpt| #[trigger] mem(m, rho, u) == mem(m2, rho, u) by {
        reveal(mem);
        if mem(m, rho, u) {
            let w = choose|w: Wit| #[trigger] mem_w(m, rho, u, w);
            if let Wit::Ap(wf_, wx, w1, w2) = w {
                assert(mem_w(f, rho, wf_, *w1) && mem_w(x, rho, wx, *w2));
                assert(mem(f, rho, wf_) && mem(x, rho, wx));
                assert(mem(f, rho, wf_) == mem(f2, rho, wf_));
                assert(mem(x, rho, wx) == mem(x2, rho, wx));
                let v1 = choose|v: Wit| #[trigger] mem_w(f2, rho, wf_, v);
                let v2 = choose|v: Wit| #[trigger] mem_w(x2, rho, wx, v);
                assert(mem_w(m2, rho, u, Wit::Ap(wf_, wx, Box::new(v1), Box::new(v2))));
            }
        }
        if mem(m2, rho, u) {
            let w = choose|w: Wit| #[trigger] mem_w(m2, rho, u, w);
            if let Wit::Ap(wf_, wx, w1, w2) = w {
                assert(mem_w(f2, rho, wf_, *w1) && mem_w(x2, rho, wx, *w2));
                assert(mem(f2, rho, wf_) && mem(x2, rho, wx));
                assert(mem(f, rho, wf_) == mem(f2, rho, wf_));
                assert(mem(x, rho, wx) == mem(x2, rho, wx));
                let v1 = choose|v: Wit| #[trigger] mem_w(f, rho, wf_, v);
                let v2 = choose|v: Wit| #[trigger] mem_w(x, rho, wx, v);
                assert(mem_w(m, rho, u, Wit::Ap(wf_, wx, Box::new(v1), Box::new(v2))));
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
proof fn app_jc_pair(f: ExprSpec, x: ExprSpec, rho: Env, u1: Cpt, u2: Cpt)
    requires
        jc(f, rho),
        jc(x, rho),
        mem(ExprSpec::App(Box::new(f), Box::new(x)), rho, u1),
        mem(ExprSpec::App(Box::new(f), Box::new(x)), rho, u2),
    ensures
        jc_pair(ExprSpec::App(Box::new(f), Box::new(x)), rho, u1, u2),
{
    let m = ExprSpec::App(Box::new(f), Box::new(x));
    reveal(mem);
    let w1 = choose|w: Wit| #[trigger] mem_w(m, rho, u1, w);
    let w2 = choose|w: Wit| #[trigger] mem_w(m, rho, u2, w);
    if let (Wit::Ap(f1, x1, a1, b1), Wit::Ap(f2, x2, a2, b2)) = (w1, w2) {
        assert(mem_w(f, rho, f1, *a1) && mem_w(f, rho, f2, *a2) && mem_w(x, rho, x1, *b1) && mem_w(x, rho, x2, *b2));
        assert(mem(f, rho, f1) && mem(f, rho, f2) && mem(x, rho, x1) && mem(x, rho, x2));
        jc_elim(f, rho, f1, f2);
        jc_elim(x, rho, x1, x2);
        mem_wf(f, rho, f1, *a1);
        mem_wf(f, rho, f2, *a2);
        mem_wf(x, rho, x1, *b1);
        mem_wf(x, rho, x2, *b2);
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
        let wfw = choose|v: Wit| #[trigger] mem_w(f, rho, fw, v);
        let wxv = choose|v: Wit| #[trigger] mem_w(x, rho, xv, v);
        assert(mem_w(m, rho, join(u1, u2), Wit::Ap(fw, xv, Box::new(wfw), Box::new(wxv))));
    }
}

pub proof fn app_jc(f: ExprSpec, x: ExprSpec, rho: Env)
    requires
        jc(f, rho),
        jc(x, rho),
    ensures
        jc(ExprSpec::App(Box::new(f), Box::new(x)), rho),
{
    let m = ExprSpec::App(Box::new(f), Box::new(x));
    assert forall|u1: Cpt, u2: Cpt| mem(m, rho, u1) && mem(m, rho, u2) implies #[trigger] jc_pair(m, rho, u1, u2) by {
        app_jc_pair(f, x, rho, u1, u2);
    }
    jc_intro(m, rho);
}

/// A Pi code of `Pi ta tb`'s denotation, at an argument fitting the
/// domain, has its codomain in the denotation of `tb[x]`.
#[verifier::spinoff_prover]
pub proof fn cod_in_inst(ta: ExprSpec, tb: ExprSpec, x: ExprSpec, rho: Env, p: Cpt, v: Cpt, ax: Cpt)
    requires
        mem(ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb)), rho, p),
        wf(p),
        p is Pi,
        dfit(ta, rho, ax, v),
        mem(x, rho, v),
        body_jc(ta, tb, rho),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        mem(inst(0, x, tb), rho, cod(p, v)),
{
    use crate::ti_subst::{psub, isub, inst_is_psub};
    reveal(mem);
    let mpi = ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb));
    let w = choose|w: Wit| #[trigger] mem_w(mpi, rho, p, w);
    typed_wf(v, ax);
    if let Wit::Gen(a, gen, wa, ws) = w {
        let g = gen->Pi_1;
        assert(entries_ok(tb, rho, a, gen, ws));
        let ev = ext(rho, v);
        assert(jc(tb, ev));
        let tg = seq![gen];
        assert(tg[0] == gen);
        let sm = selk(tg, v, ht(gen), false);
        assert forall|y: Cpt| #[trigger] sm.contains(y) implies mem(tb, ev, y) by {
            sel_pi_mem(tg, v, ht(gen), 1, y);
            let k = choose|k: int| 0 <= k < g.len() && #[trigger] g[k].1 == y && le(g[k].0, v);
            assert(gsteps(gen)[k] == g[k]);
            assert(mem_w(tb, ext(rho, g[k].0), y, ws[k]));
            assert forall|q: nat| #[trigger] le(ext(rho, g[k].0)(q), ev(q)) by {
                if q > 0 {
                    le_refl(rho((q - 1) as nat));
                }
            }
            mem_env_mono(tb, ext(rho, g[k].0), ev, y, ws[k]);
        }
        assert forall|y: Cpt| #[trigger] sm.contains(y) implies wf(y) by {
            let wy = choose|w2: Wit| #[trigger] mem_w(tb, ev, y, w2);
            mem_wf(tb, ev, y, wy);
        }
        assert forall|y: Cpt, z: Cpt| #[trigger] sm.contains(y) && #[trigger] sm.contains(z) implies compat(y, z) by {
            jc_elim(tb, ev, y, z);
        }
        assert(pw(sm));
        selk_fits(gen, v, false);
        pw_coh(sm, dec(ht(gen)));
        assert forall|i: int| 0 <= i < sm.len() implies #[trigger] mem(tb, ev, sm[i]) by {
            assert(sm.contains(sm[i]));
        }
        jall_mem(tb, ev, sm, sm.len() as int);
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
        // into the instance, then down
        covers_inst(x, rho, v);
        let wj = choose|w2: Wit| #[trigger] mem_w(tb, ev, j, w2);
        mem_psub_back(tb, isub(0, x), rho, ev, j, wj);
        inst_is_psub(0, x, tb);
        mem_down_e(inst(0, x, tb), rho, j, cod(p, v));
    }
}

/// THE APPLICATION RULE, TYPING.
#[verifier::spinoff_prover]
pub proof fn sound_app_ty(f: ExprSpec, x: ExprSpec, ta: ExprSpec, tb: ExprSpec, rho: Env)
    requires
        tyd(f, rho, ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb))),
        tyd(x, rho, ta),
        body_jc(ta, tb, rho),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        tyd(ExprSpec::App(Box::new(f), Box::new(x)), rho, inst(0, x, tb)),
{
    let m = ExprSpec::App(Box::new(f), Box::new(x));
    let pt = ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(tb));
    let t = inst(0, x, tb);
    assert forall|u: Cpt| #[trigger] mem(m, rho, u) implies tyd_w(m, rho, t, u) by {
        if u is Bot {
            tyd_bot(m, rho, t);
        } else {
            reveal(mem);
            let w = choose|w: Wit| #[trigger] mem_w(m, rho, u, w);
            if let Wit::Ap(fw, xv, w1, w2) = w {
                assert(mem_w(f, rho, fw, *w1) && mem_w(x, rho, xv, *w2));
                assert(mem(f, rho, fw) && mem(x, rho, xv));
                mem_wf(f, rho, fw, *w1);
                mem_wf(x, rho, xv, *w2);
                let (fw2, p) = tyd_w_elim(f, rho, pt, fw);
                let (xv2, ax) = tyd_w_elim(x, rho, ta, xv);
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
                assert(dfit(ta, rho, ax, xv2));
                cod_in_inst(ta, tb, x, rho, p, xv2, ax);
                app_wf(fw2, xv2);
                le_refl(top);
                let wf2 = choose|v: Wit| #[trigger] mem_w(f, rho, fw2, v);
                let wx2 = choose|v: Wit| #[trigger] mem_w(x, rho, xv2, v);
                assert(mem_w(m, rho, top, Wit::Ap(fw2, xv2, Box::new(wf2), Box::new(wx2))));
                assert(tyd_at(m, rho, t, u, top, cod(p, xv2)));
                tyd_w_intro(m, rho, t, u, top, cod(p, xv2));
            }
        }
    }
}

} // verus!
