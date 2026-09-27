//! THE DOMAIN MODEL of the typed judgment (typed inversion, stage 4; the
//! paper's Figure 4 in compact form). `mem_w(m, rho, u, w)`: the compact
//! `u` belongs to the denotation of `m` under the environment `rho`, as
//! witnessed by `w` (the generator and domain chosen at each binder, the
//! function and argument at each application) -- explicit witnesses, so
//! no existential sits inside the recursion. A sort denotes {bottom, Prop}
//! when its level is zero under every assignment, else {bottom, U}.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::ti_syntax::is_zero;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub type Env = spec_fn(nat) -> Cpt;

pub open spec fn ext(rho: Env, u: Cpt) -> Env {
    |i: nat| if i == 0 { u } else { rho((i - 1) as nat) }
}

/// Stage-free semantic typing, at the least stage containing both.
pub open spec fn typed(u: Cpt, a: Cpt) -> bool {
    has_type(vstd::math::max(ht(u) as int, ht(a) as int) as nat + 1, u, a)
}

/// The universe code a sort denotes.
pub open spec fn sortc(l: LevelSpec) -> Cpt {
    if is_zero(l) { Cpt::Prop } else { Cpt::U }
}

/// A membership witness.
pub enum Wit {
    Nil,
    /// At a binder: the domain element, the generator, the domain's
    /// witness, one witness per generator entry.
    Gen(Cpt, Cpt, Box<Wit>, Seq<Wit>),
    /// At an application: the function and argument elements and their
    /// witnesses.
    Ap(Cpt, Cpt, Box<Wit>, Box<Wit>),
}

/// The generator's step list (Lam or Pi).
pub open spec fn gsteps(gen: Cpt) -> Seq<(Cpt, Cpt)> {
    match gen {
        Cpt::Lam(f) => f,
        Cpt::Pi(_, g) => g,
        _ => Seq::empty(),
    }
}

/// The entries of a generator: typed at the domain, outputs in the body's
/// denotation at the input.
pub open spec fn entries_ok(body: ExprSpec, rho: Env, a: Cpt, gen: Cpt, ws: Seq<Wit>) -> bool
    decreases body, 2int,
{
    ws.len() == gsteps(gen).len() && forall|i: int| 0 <= i < ws.len() ==>
        typed(#[trigger] gsteps(gen)[i].0, a) && mem_w(body, ext(rho, gsteps(gen)[i].0), gsteps(gen)[i].1, ws[i])
}

/// MEMBERSHIP, as witnessed.
pub open spec fn mem_w(m: ExprSpec, rho: Env, u: Cpt, w: Wit) -> bool
    decreases m, 1int,
{
    match m {
        ExprSpec::Var(i) => wf(u) && le(u, rho(i)),
        ExprSpec::Sort(l) => u is Bot || u == sortc(l),
        ExprSpec::Bind(bk, ta, b) => u is Bot || match w {
            Wit::Gen(a, gen, wa, ws) => wf(u) && le(u, gen) && typed(a, Cpt::U) && mem_w(*ta, rho, a, *wa) && (
                if bk == BinderKind::Pi { gen is Pi && *gen->Pi_0 == a } else { bk == BinderKind::Lam && gen is Lam })
                && entries_ok(*b, rho, a, gen, ws),
            _ => false,
        },
        ExprSpec::App(f, x) => match w {
            Wit::Ap(wf_, wx, w1, w2) => wf(u) && mem_w(*f, rho, wf_, *w1) && mem_w(*x, rho, wx, *w2)
                && le(u, crate::dom_compact::app(wf_, wx)),
            _ => false,
        },
        _ => u is Bot,
    }
}

/// `u` is in the denotation of `m`.
pub open spec fn mem(m: ExprSpec, rho: Env, u: Cpt) -> bool {
    exists|w: Wit| #[trigger] mem_w(m, rho, u, w)
}

/// A witness for bottom.
pub open spec fn bot_w(m: ExprSpec) -> Wit
    decreases m,
{
    match m {
        ExprSpec::App(f, x) => Wit::Ap(Cpt::Bot, Cpt::Bot, Box::new(bot_w(*f)), Box::new(bot_w(*x))),
        _ => Wit::Nil,
    }
}

/// (I1) Every denotation contains bottom.
pub proof fn mem_bot(m: ExprSpec, rho: Env)
    ensures
        mem_w(m, rho, Cpt::Bot, bot_w(m)),
    decreases m,
{
    if let ExprSpec::App(f, x) = m {
        mem_bot(*f, rho);
        mem_bot(*x, rho);
    }
}

/// (I2) Denotations are closed downward (on well-formed elements), with
/// the same witness.
pub proof fn mem_down(m: ExprSpec, rho: Env, u: Cpt, u2: Cpt, w: Wit)
    requires
        mem_w(m, rho, u, w),
        le(u2, u),
        wf(u2),
    ensures
        mem_w(m, rho, u2, w),
{
    match m {
        ExprSpec::Var(i) => {
            le_trans(u2, u, rho(i));
        },
        ExprSpec::Sort(l) => {
            if !(u2 is Bot) {
                head_le(u2, u);
                assert(!(u is Bot));
            }
        },
        ExprSpec::Bind(bk, ta, b) => {
            if !(u2 is Bot) {
                head_le(u2, u);
                if let Wit::Gen(a, gen, wa, ws) = w {
                    le_trans(u2, u, gen);
                }
            }
        },
        ExprSpec::App(f, x) => {
            if let Wit::Ap(wf_, wx, w1, w2) = w {
                le_trans(u2, u, crate::dom_compact::app(wf_, wx));
            }
        },
        _ => {
            if !(u2 is Bot) {
                head_le(u2, u);
            }
        },
    }
}

/// Environments ordered pointwise.
pub open spec fn env_le(rho: Env, rho2: Env) -> bool {
    forall|i: nat| #[trigger] le(rho(i), rho2(i))
}

/// (I4) Denotations grow with the environment, with the same witness.
pub proof fn mem_env_mono(m: ExprSpec, rho: Env, rho2: Env, u: Cpt, w: Wit)
    requires
        mem_w(m, rho, u, w),
        env_le(rho, rho2),
    ensures
        mem_w(m, rho2, u, w),
    decreases m,
{
    match m {
        ExprSpec::Var(i) => {
            le_trans(u, rho(i), rho2(i));
        },
        ExprSpec::Bind(bk, ta, b) => {
            if !(u is Bot) {
                if let Wit::Gen(a, gen, wa, ws) = w {
                    assert(entries_ok(*b, rho, a, gen, ws));
                    mem_env_mono(*ta, rho, rho2, a, *wa);
                    assert forall|i: int| 0 <= i < ws.len() implies
                        typed(#[trigger] gsteps(gen)[i].0, a) && mem_w(*b, ext(rho2, gsteps(gen)[i].0), gsteps(gen)[i].1, ws[i]) by {
                        let x = gsteps(gen)[i].0;
                        assert forall|j: nat| #[trigger] le(ext(rho, x)(j), ext(rho2, x)(j)) by {
                            if j == 0 {
                                le_refl(x);
                            }
                        }
                        mem_env_mono(*b, ext(rho, x), ext(rho2, x), gsteps(gen)[i].1, ws[i]);
                    }
                    assert(entries_ok(*b, rho2, a, gen, ws));
                }
            }
        },
        ExprSpec::App(f, x) => {
            if let Wit::Ap(wf_, wx, w1, w2) = w {
                mem_env_mono(*f, rho, rho2, wf_, *w1);
                mem_env_mono(*x, rho, rho2, wx, *w2);
            }
        },
        _ => {},
    }
}

/// Membership reads the environment only pointwise.
pub proof fn mem_env_ext(m: ExprSpec, rho: Env, rho2: Env, u: Cpt, w: Wit)
    requires
        mem_w(m, rho, u, w),
        forall|i: nat| #[trigger] rho(i) == rho2(i),
    ensures
        mem_w(m, rho2, u, w),
{
    assert forall|i: nat| #[trigger] le(rho(i), rho2(i)) by {
        le_refl(rho(i));
    }
    mem_env_mono(m, rho, rho2, u, w);
}

/// The environment read through a renaming.
pub open spec fn env_rn(rho: Env, r: spec_fn(nat) -> nat) -> Env {
    |i: nat| rho(r(i))
}

/// RENAMING, SEMANTICALLY: a renamed term under `rho` is the term under
/// `rho` read through the renaming, with the same witness.
pub proof fn mem_rn(m: ExprSpec, r: spec_fn(nat) -> nat, rho: Env, u: Cpt, w: Wit)
    ensures
        mem_w(crate::ti_subst::psub(m, crate::ti_subst::rn(r)), rho, u, w) == mem_w(m, env_rn(rho, r), u, w),
    decreases m,
{
    use crate::ti_subst::{psub, rn, up, upr, up_rn, psub_ext};
    match m {
        ExprSpec::Bind(bk, ta, b) => {
            mem_rn(*ta, r, rho, u, w);
            if let Wit::Gen(a, gen, wa, ws) = w {
                mem_rn(*ta, r, rho, a, *wa);
                up_rn(r);
                psub_ext(*b, up(rn(r)), rn(upr(r)));
                assert forall|i: int| 0 <= i < ws.len() implies
                    mem_w(psub(*b, rn(upr(r))), ext(rho, #[trigger] gsteps(gen)[i].0), gsteps(gen)[i].1, ws[i])
                    == mem_w(*b, ext(env_rn(rho, r), gsteps(gen)[i].0), gsteps(gen)[i].1, ws[i]) by {
                    let x = gsteps(gen)[i].0;
                    mem_rn(*b, upr(r), ext(rho, x), gsteps(gen)[i].1, ws[i]);
                    assert forall|j: nat| #[trigger] env_rn(ext(rho, x), upr(r))(j) == ext(env_rn(rho, r), x)(j) by {}
                    if mem_w(*b, env_rn(ext(rho, x), upr(r)), gsteps(gen)[i].1, ws[i]) {
                        mem_env_ext(*b, env_rn(ext(rho, x), upr(r)), ext(env_rn(rho, r), x), gsteps(gen)[i].1, ws[i]);
                    }
                    if mem_w(*b, ext(env_rn(rho, r), x), gsteps(gen)[i].1, ws[i]) {
                        mem_env_ext(*b, ext(env_rn(rho, r), x), env_rn(ext(rho, x), upr(r)), gsteps(gen)[i].1, ws[i]);
                    }
                }
                assert(entries_ok(psub(*b, up(rn(r))), rho, a, gen, ws) == entries_ok(*b, env_rn(rho, r), a, gen, ws));
            }
        },
        ExprSpec::App(f, x) => {
            if let Wit::Ap(wf_, wx, w1, w2) = w {
                mem_rn(*f, r, rho, wf_, *w1);
                mem_rn(*x, r, rho, wx, *w2);
            }
        },
        _ => {},
    }
}

/// Down-closure, for the existential form.
pub proof fn mem_down_e(m: ExprSpec, rho: Env, u: Cpt, u2: Cpt)
    requires
        mem(m, rho, u),
        le(u2, u),
        wf(u2),
    ensures
        mem(m, rho, u2),
{
    let w = choose|w: Wit| #[trigger] mem_w(m, rho, u, w);
    mem_down(m, rho, u, u2, w);
}

/// Every element of a denotation is well formed.
pub proof fn mem_wf(m: ExprSpec, rho: Env, u: Cpt, w: Wit)
    requires
        mem_w(m, rho, u, w),
    ensures
        wf(u),
{
}

/// The environment `rho2` is covered by `s` under `rho`: each entry is in
/// the denotation of the corresponding substituted term.
pub open spec fn covers(s: crate::ti_subst::Sub, rho: Env, rho2: Env) -> bool {
    forall|i: nat| #[trigger] mem(s(i), rho, rho2(i))
}

/// Covering moves under a binder.
pub proof fn covers_up(s: crate::ti_subst::Sub, rho: Env, rho2: Env, x: Cpt)
    requires
        covers(s, rho, rho2),
        wf(x),
    ensures
        covers(crate::ti_subst::up(s), ext(rho, x), ext(rho2, x)),
{
    use crate::ti_subst::{psub, rn, up, lift_is_rn, lr};
    assert forall|i: nat| #[trigger] mem(up(s)(i), ext(rho, x), ext(rho2, x)(i)) by {
        if i == 0 {
            le_refl(x);
            assert(mem_w(ExprSpec::Var(0), ext(rho, x), x, Wit::Nil));
        } else {
            let k = (i - 1) as nat;
            assert(mem(s(k), rho, rho2(k)));
            let w = choose|w: Wit| #[trigger] mem_w(s(k), rho, rho2(k), w);
            crate::subst_algebra::lift_zero(0, s(k));
            lift_is_rn(1, 0, s(k));
            mem_rn(s(k), lr(1, 0), ext(rho, x), rho2(k), w);
            assert forall|j: nat| #[trigger] rho(j) == env_rn(ext(rho, x), lr(1, 0))(j) by {}
            mem_env_ext(s(k), rho, env_rn(ext(rho, x), lr(1, 0)), rho2(k), w);
            assert(mem_w(up(s)(i), ext(rho, x), rho2(k), w));
        }
    }
}

/// SUBSTITUTION, SEMANTICALLY (the easy direction): what a term denotes
/// under a covered environment, its substitution instance denotes.
pub proof fn mem_psub_back(m: ExprSpec, s: crate::ti_subst::Sub, rho: Env, rho2: Env, u: Cpt, w: Wit)
    requires
        mem_w(m, rho2, u, w),
        covers(s, rho, rho2),
    ensures
        mem(crate::ti_subst::psub(m, s), rho, u),
    decreases m,
{
    use crate::ti_subst::{psub, up};
    match m {
        ExprSpec::Var(i) => {
            assert(mem(s(i), rho, rho2(i)));
            mem_down_e(s(i), rho, rho2(i), u);
        },
        ExprSpec::Sort(l) => {
            assert(mem_w(psub(m, s), rho, u, Wit::Nil));
        },
        ExprSpec::Bind(bk, ta, b) => {
            if u is Bot {
                assert(mem_w(psub(m, s), rho, u, Wit::Nil));
            } else if let Wit::Gen(a, gen, wa, ws) = w {
                mem_psub_back(*ta, s, rho, rho2, a, *wa);
                let wa2 = choose|w2: Wit| #[trigger] mem_w(psub(*ta, s), rho, a, w2);
                let st = gsteps(gen);
                assert(entries_ok(*b, rho2, a, gen, ws));
                assert forall|i: int| 0 <= i < ws.len() implies
                    #[trigger] mem(psub(*b, up(s)), ext(rho, st[i].0), st[i].1) by {
                    assert(typed(st[i].0, a));
                    covers_up(s, rho, rho2, st[i].0);
                    mem_psub_back(*b, up(s), ext(rho, st[i].0), ext(rho2, st[i].0), st[i].1, ws[i]);
                }
                let ws2 = Seq::new(ws.len(), |i: int| choose|w2: Wit| #[trigger] mem_w(psub(*b, up(s)), ext(rho, st[i].0), st[i].1, w2));
                assert forall|i: int| 0 <= i < ws2.len() implies
                    typed(#[trigger] gsteps(gen)[i].0, a) && mem_w(psub(*b, up(s)), ext(rho, gsteps(gen)[i].0), gsteps(gen)[i].1, ws2[i]) by {
                    assert(mem(psub(*b, up(s)), ext(rho, st[i].0), st[i].1));
                }
                assert(entries_ok(psub(*b, up(s)), rho, a, gen, ws2));
                assert(mem_w(psub(m, s), rho, u, Wit::Gen(a, gen, Box::new(wa2), ws2)));
            }
        },
        ExprSpec::App(f, x) => {
            if let Wit::Ap(wf_, wx, w1, w2) = w {
                mem_psub_back(*f, s, rho, rho2, wf_, *w1);
                mem_psub_back(*x, s, rho, rho2, wx, *w2);
                let v1 = choose|v: Wit| #[trigger] mem_w(psub(*f, s), rho, wf_, v);
                let v2 = choose|v: Wit| #[trigger] mem_w(psub(*x, s), rho, wx, v);
                assert(mem_w(psub(m, s), rho, u, Wit::Ap(wf_, wx, Box::new(v1), Box::new(v2))));
            }
        },
        _ => {
            assert(mem_w(psub(m, s), rho, u, Wit::Nil));
        },
    }
}

/// The canonical stage of a typing.
pub open spec fn cstage(u: Cpt, a: Cpt) -> nat {
    vstd::math::max(ht(u) as int, ht(a) as int) as nat + 1
}

/// A typing at its canonical stage holds at every later stage.
pub proof fn typed_up(u: Cpt, a: Cpt, n: nat)
    requires
        typed(u, a),
        n >= cstage(u, a),
    ensures
        has_type(n, u, a),
    decreases n,
{
    if n > cstage(u, a) {
        typed_up(u, a, (n - 1) as nat);
        ty_stable((n - 1) as nat, u, a);
    }
}

/// A typing at a stage containing both is the canonical typing.
pub proof fn typed_down(u: Cpt, a: Cpt, n: nat)
    requires
        has_type(n, u, a),
    ensures
        typed(u, a),
        n >= cstage(u, a),
    decreases n,
{
    ty_pos(n, u, a);
    if n > cstage(u, a) {
        assert(stg((n - 1) as nat, u) && stg((n - 1) as nat, a));
        ty_stable((n - 1) as nat, u, a);
        typed_down(u, a, (n - 1) as nat);
    }
}

/// RAISING THE TYPE, stage-free.
pub proof fn typed_weak(u: Cpt, a: Cpt, a2: Cpt)
    requires
        typed(u, a),
        le(a, a2),
        typed(a2, Cpt::U),
    ensures
        typed(u, a2),
{
    let n = vstd::math::max(cstage(u, a) as int, cstage(a2, Cpt::U) as int) as nat + ht(u) + 1;
    typed_up(u, a, n);
    typed_up(a2, Cpt::U, n);
    ty_weak(n, u, a, a2);
    typed_down(u, a2, n);
}

/// JOINS, stage-free.
pub proof fn typed_join(u: Cpt, v: Cpt, a: Cpt)
    requires
        compat(u, v),
        typed(u, a),
        typed(v, a),
    ensures
        typed(join(u, v), a),
{
    let n = vstd::math::max(cstage(u, a) as int, cstage(v, a) as int) as nat;
    typed_up(u, a, n);
    typed_up(v, a, n);
    ty_join(n, u, v, a);
    typed_down(join(u, v), a, n);
}

/// A typed element is well formed, and so is its type.
pub proof fn typed_wf(u: Cpt, a: Cpt)
    requires
        typed(u, a),
    ensures
        wf(u),
        wf(a),
{
}

/// A binary join is least.
pub proof fn join_lub(u: Cpt, v: Cpt, w: Cpt)
    requires
        wf(u),
        wf(v),
        compat(u, v),
        le(u, w),
        le(v, w),
    ensures
        le(join(u, v), w),
{
    let t = seq![u, v];
    compat_refl(u);
    compat_refl(v);
    compat_symm(u, v);
    assert forall|y: Cpt, z: Cpt| #[trigger] t.contains(y) && #[trigger] t.contains(z) implies compat(y, z) by {
        let i = choose|i: int| 0 <= i < 2 && t[i] == y;
        let j = choose|j: int| 0 <= j < 2 && t[j] == z;
    }
    assert forall|y: Cpt| #[trigger] t.contains(y) implies wf(y) by {
        let i = choose|i: int| 0 <= i < 2 && t[i] == y;
    }
    let b = vstd::math::max(ht(u) as int, ht(v) as int) as nat;
    assert(fits(t, b));
    pw_coh(t, b);
    assert forall|y: Cpt| #[trigger] t.contains(y) implies le(y, w) by {
        let i = choose|i: int| 0 <= i < 2 && t[i] == y;
    }
    jall_lub(t, b, w);
    assert(joinall(t, 0) == Cpt::Bot);
    assert(joinall(t, 1) == u);
    assert(jall(t) == join(u, v));
}

/// A denotation is closed under compatible joins.
pub open spec fn jc(m: ExprSpec, rho: Env) -> bool {
    forall|u1: Cpt, u2: Cpt| #[trigger] mem(m, rho, u1) && #[trigger] mem(m, rho, u2)
        ==> compat(u1, u2) && mem(m, rho, join(u1, u2))
}

pub proof fn jc_var(i: nat, rho: Env)
    requires
        wf(rho(i)),
    ensures
        jc(ExprSpec::Var(i), rho),
{
    assert forall|u1: Cpt, u2: Cpt| #[trigger] mem(ExprSpec::Var(i), rho, u1) && #[trigger] mem(ExprSpec::Var(i), rho, u2)
        implies compat(u1, u2) && mem(ExprSpec::Var(i), rho, join(u1, u2)) by {
        let w1 = choose|w: Wit| #[trigger] mem_w(ExprSpec::Var(i), rho, u1, w);
        let w2 = choose|w: Wit| #[trigger] mem_w(ExprSpec::Var(i), rho, u2, w);
        ub_compat(u1, u2, rho(i));
        join_ub(u1, u2);
        join_lub(u1, u2, rho(i));
        assert(mem_w(ExprSpec::Var(i), rho, join(u1, u2), Wit::Nil));
    }
}

/// A lifted term under an extended environment denotes what the term
/// denotes.
pub proof fn mem_lift1(t: ExprSpec, rho: Env, x: Cpt, u: Cpt)
    ensures
        mem(crate::subst_algebra::lift(1, 0, t), ext(rho, x), u) == mem(t, rho, u),
{
    use crate::ti_subst::{lift_is_rn, lr};
    lift_is_rn(1, 0, t);
    assert forall|j: nat| #[trigger] rho(j) == env_rn(ext(rho, x), lr(1, 0))(j) by {}
    if mem(t, rho, u) {
        let w = choose|w: Wit| #[trigger] mem_w(t, rho, u, w);
        mem_env_ext(t, rho, env_rn(ext(rho, x), lr(1, 0)), u, w);
        mem_rn(t, lr(1, 0), ext(rho, x), u, w);
        assert(mem_w(crate::subst_algebra::lift(1, 0, t), ext(rho, x), u, w));
    }
    if mem(crate::subst_algebra::lift(1, 0, t), ext(rho, x), u) {
        let w = choose|w: Wit| #[trigger] mem_w(crate::subst_algebra::lift(1, 0, t), ext(rho, x), u, w);
        mem_rn(t, lr(1, 0), ext(rho, x), u, w);
        mem_env_ext(t, env_rn(ext(rho, x), lr(1, 0)), rho, u, w);
    }
}

pub proof fn jc_lift(t: ExprSpec, rho: Env, x: Cpt)
    requires
        jc(t, rho),
    ensures
        jc(crate::subst_algebra::lift(1, 0, t), ext(rho, x)),
{
    let lt = crate::subst_algebra::lift(1, 0, t);
    assert forall|u1: Cpt, u2: Cpt| #[trigger] mem(lt, ext(rho, x), u1) && #[trigger] mem(lt, ext(rho, x), u2)
        implies compat(u1, u2) && mem(lt, ext(rho, x), join(u1, u2)) by {
        mem_lift1(t, rho, x, u1);
        mem_lift1(t, rho, x, u2);
        mem_lift1(t, rho, x, join(u1, u2));
    }
}

/// The join of members of a join-closed denotation is a member.
pub proof fn jall_mem(m: ExprSpec, rho: Env, t: Seq<Cpt>, k: int)
    requires
        jc(m, rho),
        0 <= k <= t.len(),
        forall|i: int| 0 <= i < t.len() ==> #[trigger] mem(m, rho, t[i]),
    ensures
        mem(m, rho, joinall(t, k)),
    decreases k,
{
    if k == 0 {
        mem_bot(m, rho);
    } else {
        jall_mem(m, rho, t, k - 1);
        assert(mem(m, rho, t[k - 1]));
    }
}

pub open spec fn bot_env() -> Env {
    |i: nat| Cpt::Bot
}

pub open spec fn env_join2(r1: Env, r2: Env) -> Env {
    |i: nat| join(r1(i), r2(i))
}

/// The environment shifted past its first entry.
pub open spec fn tail(r: Env) -> Env {
    |i: nat| r(i + 1)
}

pub proof fn covers_bot(s: crate::ti_subst::Sub, rho: Env)
    ensures
        covers(s, rho, bot_env()),
{
    assert forall|i: nat| #[trigger] mem(s(i), rho, bot_env()(i)) by {
        mem_bot(s(i), rho);
    }
}

/// Two covering environments join into one above both.
pub proof fn covers_join2(s: crate::ti_subst::Sub, rho: Env, r1: Env, r2: Env)
    requires
        covers(s, rho, r1),
        covers(s, rho, r2),
        forall|i: nat| #[trigger] jc(s(i), rho),
    ensures
        covers(s, rho, env_join2(r1, r2)),
        env_le(r1, env_join2(r1, r2)),
        env_le(r2, env_join2(r1, r2)),
{
    assert forall|i: nat| #[trigger] mem(s(i), rho, env_join2(r1, r2)(i)) && le(r1(i), env_join2(r1, r2)(i)) && le(r2(i), env_join2(r1, r2)(i)) by {
        assert(mem(s(i), rho, r1(i)) && mem(s(i), rho, r2(i)));
        assert(jc(s(i), rho));
        let w1 = choose|w: Wit| #[trigger] mem_w(s(i), rho, r1(i), w);
        let w2 = choose|w: Wit| #[trigger] mem_w(s(i), rho, r2(i), w);
        mem_wf(s(i), rho, r1(i), w1);
        mem_wf(s(i), rho, r2(i), w2);
        join_ub(r1(i), r2(i));
    }
    assert forall|i: nat| #[trigger] le(r1(i), env_join2(r1, r2)(i)) by {
        assert(mem(s(i), rho, env_join2(r1, r2)(i)) && le(r1(i), env_join2(r1, r2)(i)));
    }
    assert forall|i: nat| #[trigger] le(r2(i), env_join2(r1, r2)(i)) by {
        assert(mem(s(i), rho, env_join2(r1, r2)(i)) && le(r2(i), env_join2(r1, r2)(i)));
    }
}

/// The substitution moved under a binder is still join-closed pointwise.
pub proof fn jc_up(s: crate::ti_subst::Sub, rho: Env, x: Cpt)
    requires
        forall|i: nat| #[trigger] jc(s(i), rho),
        wf(x),
    ensures
        forall|i: nat| #[trigger] jc(crate::ti_subst::up(s)(i), ext(rho, x)),
{
    assert forall|i: nat| #[trigger] jc(crate::ti_subst::up(s)(i), ext(rho, x)) by {
        if i == 0 {
            jc_var(0, ext(rho, x));
        } else {
            assert(jc(s((i - 1) as nat), rho));
            jc_lift(s((i - 1) as nat), rho, x);
        }
    }
}

/// A covering of `up(s)` under `ext(rho, x)`: its head is below `x`, its
/// tail covers `s`.
pub proof fn covers_up_back(s: crate::ti_subst::Sub, rho: Env, x: Cpt, r: Env)
    requires
        covers(crate::ti_subst::up(s), ext(rho, x), r),
    ensures
        le(r(0), x),
        covers(s, rho, tail(r)),
{
    assert(mem(crate::ti_subst::up(s)(0), ext(rho, x), r(0)));
    let w0 = choose|w: Wit| #[trigger] mem_w(ExprSpec::Var(0), ext(rho, x), r(0), w);
    assert forall|i: nat| #[trigger] mem(s(i), rho, tail(r)(i)) by {
        assert(mem(crate::ti_subst::up(s)(i + 1), ext(rho, x), r(i + 1)));
        mem_lift1(s(i), rho, x, r(i + 1));
    }
}

/// The entries of a binder's generator, pulled back through the
/// substitution into one covering environment.
proof fn entries_fwd(b: ExprSpec, s: crate::ti_subst::Sub, rho: Env, gen: Cpt, ws: Seq<Wit>, k: int) -> (acc: Env)
    requires
        0 <= k <= ws.len(),
        ws.len() == gsteps(gen).len(),
        forall|i: int| 0 <= i < ws.len() ==> wf(#[trigger] gsteps(gen)[i].0)
            && mem_w(crate::ti_subst::psub(b, crate::ti_subst::up(s)), ext(rho, gsteps(gen)[i].0), gsteps(gen)[i].1, ws[i]),
        forall|i: nat| #[trigger] jc(s(i), rho),
    ensures
        covers(s, rho, acc),
        forall|i: int| 0 <= i < k ==> #[trigger] mem(b, ext(acc, gsteps(gen)[i].0), gsteps(gen)[i].1),
    decreases b, k + 1,
{
    if k == 0 {
        covers_bot(s, rho);
        bot_env()
    } else {
        let acc0 = entries_fwd(b, s, rho, gen, ws, k - 1);
        let (x, y) = gsteps(gen)[k - 1];
        jc_up(s, rho, x);
        let r = mem_psub_fwd(b, crate::ti_subst::up(s), ext(rho, x), y, ws[k - 1]);
        covers_up_back(s, rho, x, r);
        covers_join2(s, rho, acc0, tail(r));
        let acc = env_join2(acc0, tail(r));
        assert forall|i: int| 0 <= i < k implies #[trigger] mem(b, ext(acc, gsteps(gen)[i].0), gsteps(gen)[i].1) by {
            let xi = gsteps(gen)[i].0;
            assert forall|j: nat| #[trigger] le(ext(acc0, xi)(j), ext(acc, xi)(j)) by {
                if j == 0 {
                    le_refl(xi);
                }
            }
            if i < k - 1 {
                assert(mem(b, ext(acc0, gsteps(gen)[i].0), gsteps(gen)[i].1));
                let wi = choose|w: Wit| #[trigger] mem_w(b, ext(acc0, xi), gsteps(gen)[i].1, w);
                mem_env_mono(b, ext(acc0, xi), ext(acc, xi), gsteps(gen)[i].1, wi);
            } else {
                assert forall|j: nat| #[trigger] le(r(j), ext(acc, x)(j)) by {
                    if j > 0 {
                        assert(le(tail(r)((j - 1) as nat), acc((j - 1) as nat)));
                    }
                }
                let wi = choose|w: Wit| #[trigger] mem_w(b, r, y, w);
                mem_env_mono(b, r, ext(acc, x), y, wi);
            }
        }
        acc
    }
}

/// SUBSTITUTION, SEMANTICALLY (the other direction, for join-closed
/// substitutions): what a substitution instance denotes, the term denotes
/// under some covered environment.
pub proof fn mem_psub_fwd(m: ExprSpec, s: crate::ti_subst::Sub, rho: Env, u: Cpt, w: Wit) -> (rho2: Env)
    requires
        mem_w(crate::ti_subst::psub(m, s), rho, u, w),
        forall|i: nat| #[trigger] jc(s(i), rho),
    ensures
        covers(s, rho, rho2),
        mem(m, rho2, u),
    decreases m, 0int,
{
    use crate::ti_subst::{psub, up};
    match m {
        ExprSpec::Var(i) => {
            let r: Env = |j: nat| if j == i { u } else { Cpt::Bot };
            mem_wf(s(i), rho, u, w);
            assert forall|j: nat| #[trigger] mem(s(j), rho, r(j)) by {
                if j == i {
                    assert(mem_w(s(i), rho, u, w));
                } else {
                    mem_bot(s(j), rho);
                }
            }
            le_refl(u);
            assert(mem_w(m, r, u, Wit::Nil));
            r
        },
        ExprSpec::Bind(bk, ta, b) => {
            covers_bot(s, rho);
            if u is Bot {
                assert(mem_w(m, bot_env(), u, Wit::Nil));
                bot_env()
            } else if let Wit::Gen(a, gen, wa, ws) = w {
                let ra = mem_psub_fwd(*ta, s, rho, a, *wa);
                assert(entries_ok(psub(*b, up(s)), rho, a, gen, ws));
                let acc = entries_fwd(*b, s, rho, gen, ws, ws.len() as int);
                covers_join2(s, rho, ra, acc);
                let r2 = env_join2(ra, acc);
                let wa2 = choose|v: Wit| #[trigger] mem_w(*ta, ra, a, v);
                mem_env_mono(*ta, ra, r2, a, wa2);
                let st = gsteps(gen);
                assert forall|i: int| 0 <= i < ws.len() implies #[trigger] mem(*b, ext(r2, st[i].0), st[i].1) by {
                    let xi = st[i].0;
                    assert(mem(*b, ext(acc, xi), st[i].1));
                    assert forall|j: nat| #[trigger] le(ext(acc, xi)(j), ext(r2, xi)(j)) by {
                        if j == 0 {
                            le_refl(xi);
                        }
                    }
                    let wi = choose|v: Wit| #[trigger] mem_w(*b, ext(acc, xi), st[i].1, v);
                    mem_env_mono(*b, ext(acc, xi), ext(r2, xi), st[i].1, wi);
                }
                let ws2 = Seq::new(ws.len(), |i: int| choose|v: Wit| #[trigger] mem_w(*b, ext(r2, st[i].0), st[i].1, v));
                assert forall|i: int| 0 <= i < ws2.len() implies
                    typed(#[trigger] gsteps(gen)[i].0, a) && mem_w(*b, ext(r2, gsteps(gen)[i].0), gsteps(gen)[i].1, ws2[i]) by {
                    assert(mem(*b, ext(r2, st[i].0), st[i].1));
                }
                assert(entries_ok(*b, r2, a, gen, ws2));
                assert(mem_w(m, r2, u, Wit::Gen(a, gen, Box::new(wa2), ws2)));
                r2
            } else {
                assert(false);
                bot_env()
            }
        },
        ExprSpec::App(f, x) => {
            if let Wit::Ap(wf_, wx, w1, w2) = w {
                let r1 = mem_psub_fwd(*f, s, rho, wf_, *w1);
                let r2 = mem_psub_fwd(*x, s, rho, wx, *w2);
                covers_join2(s, rho, r1, r2);
                let r = env_join2(r1, r2);
                let v1 = choose|v: Wit| #[trigger] mem_w(*f, r1, wf_, v);
                let v2 = choose|v: Wit| #[trigger] mem_w(*x, r2, wx, v);
                mem_env_mono(*f, r1, r, wf_, v1);
                mem_env_mono(*x, r2, r, wx, v2);
                assert(mem_w(m, r, u, Wit::Ap(wf_, wx, Box::new(v1), Box::new(v2))));
                r
            } else {
                assert(false);
                bot_env()
            }
        },
        _ => {
            covers_bot(s, rho);
            assert(mem_w(m, bot_env(), u, Wit::Nil));
            bot_env()
        },
    }
}

} // verus!
