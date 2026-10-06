//! THE DOMAIN MODEL of the typed judgment (typed inversion, stage 4; the
//! paper's Figure 4 in compact form). `mem_w(sig, m, rho, u, w)`: the compact
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
use crate::ti_syntax::{is_zero, dval, crank};
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub type Env = spec_fn(nat) -> Cpt;

pub open spec fn ext(rho: Env, u: Cpt) -> Env {
    |i: nat| if i == 0 { u } else { rho((i - 1) as nat) }
}

/// Stage-free semantic typing, at the least stage containing both.
#[verifier::opaque]
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
    /// At a semantic constant: the element of its type, the typed element
    /// above the member, and the type element's witness.
    Sem(Cpt, Cpt, Box<Wit>),
    /// At a projection: the subject's constructor value and its witness.
    Pj(Cpt, Box<Wit>),
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
pub open spec fn entries_ok(sig: Sig, body: ExprSpec, rho: Env, a: Cpt, gen: Cpt, ws: Seq<Wit>) -> bool
    decreases crank(sig, body), crate::ti_zsize::zsize(body), 2int,
{
    ws.len() == gsteps(gen).len() && forall|i: int| 0 <= i < ws.len() ==>
        typed(#[trigger] gsteps(gen)[i].0, a) && mem_w(sig, body, ext(rho, gsteps(gen)[i].0), gsteps(gen)[i].1, ws[i])
}

/// `c.{ls}` unfolds: a definition at a matching level instance, whose value
/// mentions only lower-ranked constants.
pub open spec fn unfolds(sig: Sig, c: u64, ls: Seq<LevelSpec>) -> bool {
    &&& crate::ti_syntax::is_def(sig, c, ls)
    &&& sig.rank.contains_key(c)
    &&& crank(sig, dval(sig, c, ls)) <= sig.rank[c]
}

/// `c.{ls}` is interpreted semantically: an axiom whose type mentions only
/// lower-ranked constants.
pub open spec fn sem_const(sig: Sig, c: u64, ls: Seq<LevelSpec>) -> bool {
    &&& sig.consts.contains_key(c)
    &&& sig.consts[c].val is None
    &&& sig.consts[c].lps.len() == ls.len()
    &&& sig.rank.contains_key(c)
    &&& crank(sig, crate::ti_syntax::dty_at(sig, c, ls)) <= sig.rank[c]
    &&& !(sig.ienv.ctor_ind.contains_key(c) && sig.ienv.recs.contains_key(c))
}

/// `v` approximates the code function of the type former `c` at levels
/// `ls` down its type telescope `t`, the inputs so far being `pre`: a
/// lambda whose entries' outputs approximate it at one more input, and at
/// a sort the canonical code of `c` at the inputs. An axiom of any other
/// type has only bottom.
pub open spec fn tf_fun(sig: Sig, c: u64, ls: Seq<LevelSpec>, t: ExprSpec, pre: Seq<Cpt>, v: Cpt) -> bool
    decreases t,
{
    v is Bot || match t {
        ExprSpec::Bind(BinderKind::Pi, _, b) => match v {
            Cpt::Lam(f) => forall|i: int| 0 <= i < f.len() ==> tf_fun(sig, c, ls, *b, pre.push(f[i].0), #[trigger] f[i].1),
            _ => false,
        },
        ExprSpec::Sort(_) => le(v, crate::dom_code::canon_code(sig, c, ls, pre)),
        _ => false,
    }
}

/// `v` approximates the code function of the constructor at position `pc`
/// of inductive `ind` (with `np` parameters) down its type telescope `t`,
/// `k` being the binder's position and `fs` the fields so far: a lambda
/// whose entries' outputs approximate it at one more input, and at the end
/// (an application of the inductive, past the parameters) the value, the
/// constructor's position over the fields.
pub open spec fn cf_fun(ind: u64, pc: nat, sm: bool, np: nat, t: ExprSpec, fs: Seq<Cpt>, k: nat, v: Cpt) -> bool
    decreases t,
{
    v is Bot || match t {
        ExprSpec::Bind(BinderKind::Pi, _, b) => match v {
            Cpt::Lam(f) => forall|i: int| 0 <= i < f.len() ==>
                cf_fun(ind, pc, sm, np, *b, if k < np { fs } else { fs.push(f[i].0) }, k + 1, #[trigger] f[i].1),
            _ => false,
        },
        _ => k >= np && crate::beta_model::spine_head(t) is Const && crate::beta_model::spine_head(t)->Const_0 == ind
            && le(v, Cpt::Nd(NdKey::Con(ind, pc, sm), fs)),
    }
}

/// `v` approximates recursor `rid`'s code function down its type
/// telescope `t`, the inputs so far being `pre`: a lambda whose entries'
/// outputs approximate it at one more input, and past the telescope's
/// last Pi the code function's value at the inputs.
pub open spec fn rf_fun(sig: Sig, rid: u64, t: ExprSpec, pre: Seq<Cpt>, v: Cpt) -> bool
    decreases t,
{
    v is Bot || match t {
        ExprSpec::Bind(BinderKind::Pi, _, b) => match v {
            Cpt::Lam(f) => forall|i: int| 0 <= i < f.len() ==> rf_fun(sig, rid, *b, pre.push(f[i].0), #[trigger] f[i].1),
            _ => false,
        },
        _ => le(v, crate::dom_rec::recval(sig, rid, pre)),
    }
}

/// `c` is a constructor of `ind`'s canonical recursor.
pub open spec fn ctor_of(sig: Sig, ind: u64, c: u64) -> bool {
    crate::dom_code::has_canon(sig, ind)
        && exists|p: int| 0 <= p < crate::dom_code::canon_shape(sig, ind).nmin() && crate::dom_code::canon_shape(sig, ind).ctors[p] == c
}

/// Its position there.
pub open spec fn ctor_pos(sig: Sig, ind: u64, c: u64) -> int {
    choose|p: int| 0 <= p < crate::dom_code::canon_shape(sig, ind).nmin() && crate::dom_code::canon_shape(sig, ind).ctors[p] == c
}

/// The code function a semantic constant approximates: a constructor's
/// where its inductive has canonical tables, a recursor's where the model
/// interprets it (`rec_hyps`; otherwise both only bottom), or a type
/// former's.
pub open spec fn code_ok(sig: Sig, c: u64, ls: Seq<LevelSpec>, a: Cpt, v: Cpt) -> bool {
    let t = crate::ti_syntax::dty_at(sig, c, ls);
    if sig.ienv.ctor_ind.contains_key(c) {
        let ind = sig.ienv.ctor_ind[c];
        v is Bot || (ctor_of(sig, ind, c) && crate::dom_code::canon_ok(sig, ind)
            && cf_fun(ind, ctor_pos(sig, ind, c) as nat, crate::dom_code::smash(sig, ind), crate::dom_code::canon_shape(sig, ind).np, t, Seq::empty(), 0, v))
    } else if sig.ienv.recs.contains_key(c) {
        v is Bot || (crate::dom_rec_end::rec_hyps(sig, c) && rf_fun(sig, c, t, Seq::empty(), v))
    } else {
        tf_fun(sig, c, ls, t, Seq::empty(), v)
    }
}

/// MEMBERSHIP, as witnessed. A definition denotes its value (closed, so in
/// the empty environment); an axiom what lies below an approximation of
/// its code function typed within its type; locals only bottom.
pub open spec fn mem_w(sig: Sig, m: ExprSpec, rho: Env, u: Cpt, w: Wit) -> bool
    decreases crank(sig, m), crate::ti_zsize::zsize(m), 1int,
    via mem_w_decreases
{
    match m {
        ExprSpec::Var(i) => wf(u) && le(u, rho(i)),
        ExprSpec::Sort(l) => u is Bot || u == sortc(l),
        ExprSpec::Bind(bk, ta, b) => u is Bot || match w {
            Wit::Gen(a, gen, wa, ws) => wf(u) && le(u, gen) && typed(a, Cpt::U) && mem_w(sig, *ta, rho, a, *wa) && (
                if bk == BinderKind::Pi { gen is Pi && *gen->Pi_0 == a } else { bk == BinderKind::Lam && gen is Lam })
                && entries_ok(sig, *b, rho, a, gen, ws),
            _ => false,
        },
        ExprSpec::App(f, x) => match w {
            Wit::Ap(wf_, wx, w1, w2) => wf(u) && mem_w(sig, *f, rho, wf_, *w1) && mem_w(sig, *x, rho, wx, *w2)
                && le(u, crate::dom_compact::app(wf_, wx)),
            _ => false,
        },
        ExprSpec::Const(c, ls) => u is Bot || (unfolds(sig, c, ls) && wf(u) && mem_w(sig, dval(sig, c, ls), bot_env(), u, w))
            || (sem_const(sig, c, ls) && match w {
                Wit::Sem(a, v, wa) => wf(u) && le(u, v) && typed(a, Cpt::U) && typed(v, a)
                    && code_ok(sig, c, ls, a, v)
                    && mem_w(sig, crate::ti_syntax::dty_at(sig, c, ls), bot_env(), a, *wa),
                _ => false,
            }),
        ExprSpec::Let(t, v, b) => mem_w(sig, crate::subst_algebra::inst(0, *v, *b), rho, u, w),
        ExprSpec::Proj(i, x) => u is Bot || match w {
            Wit::Pj(v, wx) => wf(u) && mem_w(sig, *x, rho, v, *wx) && v is Nd && v->Nd_0 is Con
                && (i as int) < v->Nd_1.len() && le(u, v->Nd_1[i as int]),
            _ => false,
        },
        _ => u is Bot,
    }
}

#[via_fn]
proof fn mem_w_decreases(sig: Sig, m: ExprSpec, rho: Env, u: Cpt, w: Wit) {
    if let ExprSpec::Let(t, v, b) = m {
        let_measure(sig, *t, *v, *b);
    } else if let ExprSpec::Bind(bk, t, b) = m {
        crate::ti_zsize::zsize_bind(bk, *t, *b);
    }
}

/// A `let` weighs more than its instance, with no more constants or loose
/// variables, and substitutes like it.
pub proof fn let_measure(sig: Sig, t: ExprSpec, v: ExprSpec, b: ExprSpec)
    ensures
        crank(sig, crate::subst_algebra::inst(0, v, b)) <= crank(sig, ExprSpec::Let(Box::new(t), Box::new(v), Box::new(b))),
        crate::ti_zsize::zsize(crate::subst_algebra::inst(0, v, b)) < crate::ti_zsize::zsize(ExprSpec::Let(Box::new(t), Box::new(v), Box::new(b))),
        crate::expr_model::nlbv(crate::subst_algebra::inst(0, v, b)) <= crate::expr_model::nlbv(ExprSpec::Let(Box::new(t), Box::new(v), Box::new(b))),
        forall|s: crate::ti_subst::Sub| #[trigger] crate::ti_subst::psub(crate::subst_algebra::inst(0, v, b), s)
            == crate::subst_algebra::inst(0, crate::ti_subst::psub(v, s), crate::ti_subst::psub(b, crate::ti_subst::up(s))),
        forall|s: crate::ti_subst::Sub| #[trigger] crate::ti_subst::psub(ExprSpec::Let(Box::new(t), Box::new(v), Box::new(b)), s)
            == ExprSpec::Let(Box::new(crate::ti_subst::psub(t, s)), Box::new(crate::ti_subst::psub(v, s)), Box::new(crate::ti_subst::psub(b, crate::ti_subst::up(s)))),
{
    let m = ExprSpec::Let(Box::new(t), Box::new(v), Box::new(b));
    crate::ti_zsize::crank_inst(sig, 0, v, b);
    crate::ti_zsize::zsize_let(t, v, b);
    crate::ti_scope::inst_scope(0, v, b, crate::expr_model::nlbv(m));
    assert forall|s: crate::ti_subst::Sub| #[trigger] crate::ti_subst::psub(crate::subst_algebra::inst(0, v, b), s)
        == crate::subst_algebra::inst(0, crate::ti_subst::psub(v, s), crate::ti_subst::psub(b, crate::ti_subst::up(s))) by {
        crate::ti_subst::psub_inst0(b, v, s);
    }
}

/// `u` is in the denotation of `m`.
#[verifier::opaque]
pub open spec fn mem(sig: Sig, m: ExprSpec, rho: Env, u: Cpt) -> bool {
    exists|w: Wit| #[trigger] mem_w(sig, m, rho, u, w)
}

/// A witness for bottom.
pub open spec fn bot_w(m: ExprSpec) -> Wit
    decreases crate::ti_zsize::zsize(m),
{
    match m {
        ExprSpec::App(f, x) => Wit::Ap(Cpt::Bot, Cpt::Bot, Box::new(bot_w(*f)), Box::new(bot_w(*x))),
        ExprSpec::Let(t, v, b) => {
            let r = crate::subst_algebra::inst(0, *v, *b);
            if crate::ti_zsize::zsize(r) < crate::ti_zsize::zsize(m) { bot_w(r) } else { Wit::Nil }
        },
        _ => Wit::Nil,
    }
}

/// (I1) Every denotation contains bottom.
pub proof fn mem_bot(sig: Sig, m: ExprSpec, rho: Env)
    ensures
        mem_w(sig, m, rho, Cpt::Bot, bot_w(m)),
    decreases crate::ti_zsize::zsize(m),
{
    reveal(mem);
    reveal(typed);
    reveal(jc);
    if let ExprSpec::App(f, x) = m {
        mem_bot(sig, *f, rho);
        mem_bot(sig, *x, rho);
    } else if let ExprSpec::Let(t, v, b) = m {
        let_measure(sig, *t, *v, *b);
        mem_bot(sig, crate::subst_algebra::inst(0, *v, *b), rho);
    }
}

/// (I2) Denotations are closed downward (on well-formed elements), with
/// the same witness.
pub proof fn mem_down(sig: Sig, m: ExprSpec, rho: Env, u: Cpt, u2: Cpt, w: Wit)
    requires
        mem_w(sig, m, rho, u, w),
        le(u2, u),
        wf(u2),
    ensures
        mem_w(sig, m, rho, u2, w),
    decreases crank(sig, m), crate::ti_zsize::zsize(m),
{
    reveal(mem);
    reveal(typed);
    reveal(jc);
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
        ExprSpec::Let(t, v, b) => {
            let_measure(sig, *t, *v, *b);
            mem_down(sig, crate::subst_algebra::inst(0, *v, *b), rho, u, u2, w);
        },
        ExprSpec::Const(c, ls) => {
            if !(u2 is Bot) {
                head_le(u2, u);
                if unfolds(sig, c, ls) {
                    mem_down(sig, dval(sig, c, ls), bot_env(), u, u2, w);
                } else if let Wit::Sem(a, v, wa) = w {
                    le_trans(u2, u, v);
                }
            }
        },
        ExprSpec::Proj(i, x) => {
            if !(u2 is Bot) {
                head_le(u2, u);
                if let Wit::Pj(v, wx) = w {
                    le_trans(u2, u, v->Nd_1[i as int]);
                }
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
pub proof fn mem_env_mono(sig: Sig, m: ExprSpec, rho: Env, rho2: Env, u: Cpt, w: Wit)
    requires
        mem_w(sig, m, rho, u, w),
        env_le(rho, rho2),
    ensures
        mem_w(sig, m, rho2, u, w),
    decreases crank(sig, m), crate::ti_zsize::zsize(m),
{
    if let ExprSpec::Bind(bk0, ta0, b0) = m {
        crate::ti_zsize::zsize_bind(bk0, *ta0, *b0);
    }
    reveal(mem);
    reveal(typed);
    reveal(jc);
    match m {
        ExprSpec::Var(i) => {
            le_trans(u, rho(i), rho2(i));
        },
        ExprSpec::Bind(bk, ta, b) => {
            if !(u is Bot) {
                if let Wit::Gen(a, gen, wa, ws) = w {
                    assert(entries_ok(sig, *b, rho, a, gen, ws));
                    mem_env_mono(sig, *ta, rho, rho2, a, *wa);
                    assert forall|i: int| 0 <= i < ws.len() implies
                        typed(#[trigger] gsteps(gen)[i].0, a) && mem_w(sig, *b, ext(rho2, gsteps(gen)[i].0), gsteps(gen)[i].1, ws[i]) by {
                        let x = gsteps(gen)[i].0;
                        assert forall|j: nat| #[trigger] le(ext(rho, x)(j), ext(rho2, x)(j)) by {
                            if j == 0 {
                                le_refl(x);
                            }
                        }
                        mem_env_mono(sig, *b, ext(rho, x), ext(rho2, x), gsteps(gen)[i].1, ws[i]);
                    }
                    assert(entries_ok(sig, *b, rho2, a, gen, ws));
                }
            }
        },
        ExprSpec::App(f, x) => {
            if let Wit::Ap(wf_, wx, w1, w2) = w {
                mem_env_mono(sig, *f, rho, rho2, wf_, *w1);
                mem_env_mono(sig, *x, rho, rho2, wx, *w2);
            }
        },
        ExprSpec::Let(t, v, b) => {
            let_measure(sig, *t, *v, *b);
            mem_env_mono(sig, crate::subst_algebra::inst(0, *v, *b), rho, rho2, u, w);
        },
        ExprSpec::Proj(i, x) => {
            if !(u is Bot) {
                if let Wit::Pj(v, wx) = w {
                    mem_env_mono(sig, *x, rho, rho2, v, *wx);
                }
            }
        },
        _ => {},
    }
}

/// Membership reads the environment only pointwise.
pub proof fn mem_env_ext(sig: Sig, m: ExprSpec, rho: Env, rho2: Env, u: Cpt, w: Wit)
    requires
        mem_w(sig, m, rho, u, w),
        forall|i: nat| #[trigger] rho(i) == rho2(i),
    ensures
        mem_w(sig, m, rho2, u, w),
{
    reveal(mem);
    reveal(typed);
    reveal(jc);
    assert forall|i: nat| #[trigger] le(rho(i), rho2(i)) by {
        le_refl(rho(i));
    }
    mem_env_mono(sig, m, rho, rho2, u, w);
}

/// The environment read through a renaming.
pub open spec fn env_rn(rho: Env, r: spec_fn(nat) -> nat) -> Env {
    |i: nat| rho(r(i))
}

/// RENAMING, SEMANTICALLY: a renamed term under `rho` is the term under
/// `rho` read through the renaming, with the same witness.
pub proof fn mem_rn(sig: Sig, m: ExprSpec, r: spec_fn(nat) -> nat, rho: Env, u: Cpt, w: Wit)
    ensures
        mem_w(sig, crate::ti_subst::psub(m, crate::ti_subst::rn(r)), rho, u, w) == mem_w(sig, m, env_rn(rho, r), u, w),
    decreases crank(sig, m), crate::ti_zsize::zsize(m),
{
    if let ExprSpec::Bind(bk0, ta0, b0) = m {
        crate::ti_zsize::zsize_bind(bk0, *ta0, *b0);
    }
    reveal(mem);
    reveal(typed);
    reveal(jc);
    use crate::ti_subst::{psub, rn, up, upr, up_rn, psub_ext};
    match m {
        ExprSpec::Bind(bk, ta, b) => {
            mem_rn(sig, *ta, r, rho, u, w);
            if let Wit::Gen(a, gen, wa, ws) = w {
                mem_rn(sig, *ta, r, rho, a, *wa);
                up_rn(r);
                psub_ext(*b, up(rn(r)), rn(upr(r)));
                assert forall|i: int| 0 <= i < ws.len() implies
                    mem_w(sig, psub(*b, rn(upr(r))), ext(rho, #[trigger] gsteps(gen)[i].0), gsteps(gen)[i].1, ws[i])
                    == mem_w(sig, *b, ext(env_rn(rho, r), gsteps(gen)[i].0), gsteps(gen)[i].1, ws[i]) by {
                    let x = gsteps(gen)[i].0;
                    mem_rn(sig, *b, upr(r), ext(rho, x), gsteps(gen)[i].1, ws[i]);
                    assert forall|j: nat| #[trigger] env_rn(ext(rho, x), upr(r))(j) == ext(env_rn(rho, r), x)(j) by {}
                    if mem_w(sig, *b, env_rn(ext(rho, x), upr(r)), gsteps(gen)[i].1, ws[i]) {
                        mem_env_ext(sig, *b, env_rn(ext(rho, x), upr(r)), ext(env_rn(rho, r), x), gsteps(gen)[i].1, ws[i]);
                    }
                    if mem_w(sig, *b, ext(env_rn(rho, r), x), gsteps(gen)[i].1, ws[i]) {
                        mem_env_ext(sig, *b, ext(env_rn(rho, r), x), env_rn(ext(rho, x), upr(r)), gsteps(gen)[i].1, ws[i]);
                    }
                }
                assert(entries_ok(sig, psub(*b, up(rn(r))), rho, a, gen, ws) == entries_ok(sig, *b, env_rn(rho, r), a, gen, ws));
            }
        },
        ExprSpec::App(f, x) => {
            if let Wit::Ap(wf_, wx, w1, w2) = w {
                mem_rn(sig, *f, r, rho, wf_, *w1);
                mem_rn(sig, *x, r, rho, wx, *w2);
            }
        },
        ExprSpec::Let(t, v, b) => {
            let_measure(sig, *t, *v, *b);
            mem_rn(sig, crate::subst_algebra::inst(0, *v, *b), r, rho, u, w);
        },
        ExprSpec::Proj(i, x) => {
            if let Wit::Pj(v, wx) = w {
                mem_rn(sig, *x, r, rho, v, *wx);
            }
        },
        _ => {},
    }
}

/// Down-closure, for the existential form.
pub proof fn mem_down_e(sig: Sig, m: ExprSpec, rho: Env, u: Cpt, u2: Cpt)
    requires
        mem(sig, m, rho, u),
        le(u2, u),
        wf(u2),
    ensures
        mem(sig, m, rho, u2),
{
    reveal(mem);
    reveal(typed);
    reveal(jc);
    let w = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
    mem_down(sig, m, rho, u, u2, w);
}

/// Every element of a denotation is well formed.
pub proof fn mem_wf(sig: Sig, m: ExprSpec, rho: Env, u: Cpt, w: Wit)
    requires
        mem_w(sig, m, rho, u, w),
    ensures
        wf(u),
    decreases crank(sig, m), crate::ti_zsize::zsize(m),
{
    reveal(mem);
    reveal(typed);
    reveal(jc);
    if let ExprSpec::Let(t, v, b) = m {
        let_measure(sig, *t, *v, *b);
        mem_wf(sig, crate::subst_algebra::inst(0, *v, *b), rho, u, w);
    }
}

/// The environment `rho2` is covered by `s` under `rho`: each entry is in
/// the denotation of the corresponding substituted term.
pub open spec fn covers(sig: Sig, s: crate::ti_subst::Sub, rho: Env, rho2: Env) -> bool {
    forall|i: nat| #[trigger] mem(sig, s(i), rho, rho2(i))
}

/// Covering moves under a binder.
pub proof fn covers_up(sig: Sig, s: crate::ti_subst::Sub, rho: Env, rho2: Env, x: Cpt)
    requires
        covers(sig, s, rho, rho2),
        wf(x),
    ensures
        covers(sig, crate::ti_subst::up(s), ext(rho, x), ext(rho2, x)),
{
    reveal(mem);
    reveal(typed);
    reveal(jc);
    use crate::ti_subst::{psub, rn, up, lift_is_rn, lr};
    assert forall|i: nat| #[trigger] mem(sig, up(s)(i), ext(rho, x), ext(rho2, x)(i)) by {
        if i == 0 {
            le_refl(x);
            assert(mem_w(sig, ExprSpec::Var(0), ext(rho, x), x, Wit::Nil));
        } else {
            let k = (i - 1) as nat;
            assert(mem(sig, s(k), rho, rho2(k)));
            let w = choose|w: Wit| #[trigger] mem_w(sig, s(k), rho, rho2(k), w);
            crate::subst_algebra::lift_zero(0, s(k));
            lift_is_rn(1, 0, s(k));
            mem_rn(sig, s(k), lr(1, 0), ext(rho, x), rho2(k), w);
            assert forall|j: nat| #[trigger] rho(j) == env_rn(ext(rho, x), lr(1, 0))(j) by {}
            mem_env_ext(sig, s(k), rho, env_rn(ext(rho, x), lr(1, 0)), rho2(k), w);
            assert(mem_w(sig, up(s)(i), ext(rho, x), rho2(k), w));
        }
    }
}

/// SUBSTITUTION, SEMANTICALLY (the easy direction): what a term denotes
/// under a covered environment, its substitution instance denotes.
pub proof fn mem_psub_back(sig: Sig, m: ExprSpec, s: crate::ti_subst::Sub, rho: Env, rho2: Env, u: Cpt, w: Wit)
    requires
        mem_w(sig, m, rho2, u, w),
        covers(sig, s, rho, rho2),
    ensures
        mem(sig, crate::ti_subst::psub(m, s), rho, u),
    decreases crank(sig, m), crate::ti_zsize::zsize(m),
{
    if let ExprSpec::Bind(bk0, ta0, b0) = m {
        crate::ti_zsize::zsize_bind(bk0, *ta0, *b0);
    }
    reveal(mem);
    reveal(typed);
    reveal(jc);
    use crate::ti_subst::{psub, up};
    match m {
        ExprSpec::Var(i) => {
            assert(mem(sig, s(i), rho, rho2(i)));
            mem_down_e(sig, s(i), rho, rho2(i), u);
        },
        ExprSpec::Sort(l) => {
            assert(mem_w(sig, psub(m, s), rho, u, Wit::Nil));
        },
        ExprSpec::Bind(bk, ta, b) => {
            if u is Bot {
                assert(mem_w(sig, psub(m, s), rho, u, Wit::Nil));
            } else if let Wit::Gen(a, gen, wa, ws) = w {
                mem_psub_back(sig, *ta, s, rho, rho2, a, *wa);
                let wa2 = choose|w2: Wit| #[trigger] mem_w(sig, psub(*ta, s), rho, a, w2);
                let st = gsteps(gen);
                assert(entries_ok(sig, *b, rho2, a, gen, ws));
                assert forall|i: int| 0 <= i < ws.len() implies
                    #[trigger] mem(sig, psub(*b, up(s)), ext(rho, st[i].0), st[i].1) by {
                    assert(typed(st[i].0, a));
                    covers_up(sig, s, rho, rho2, st[i].0);
                    mem_psub_back(sig, *b, up(s), ext(rho, st[i].0), ext(rho2, st[i].0), st[i].1, ws[i]);
                }
                let ws2 = Seq::new(ws.len(), |i: int| choose|w2: Wit| #[trigger] mem_w(sig, psub(*b, up(s)), ext(rho, st[i].0), st[i].1, w2));
                assert forall|i: int| 0 <= i < ws2.len() implies
                    typed(#[trigger] gsteps(gen)[i].0, a) && mem_w(sig, psub(*b, up(s)), ext(rho, gsteps(gen)[i].0), gsteps(gen)[i].1, ws2[i]) by {
                    assert(mem(sig, psub(*b, up(s)), ext(rho, st[i].0), st[i].1));
                }
                assert(entries_ok(sig, psub(*b, up(s)), rho, a, gen, ws2));
                assert(mem_w(sig, psub(m, s), rho, u, Wit::Gen(a, gen, Box::new(wa2), ws2)));
            }
        },
        ExprSpec::App(f, x) => {
            if let Wit::Ap(wf_, wx, w1, w2) = w {
                mem_psub_back(sig, *f, s, rho, rho2, wf_, *w1);
                mem_psub_back(sig, *x, s, rho, rho2, wx, *w2);
                let v1 = choose|v: Wit| #[trigger] mem_w(sig, psub(*f, s), rho, wf_, v);
                let v2 = choose|v: Wit| #[trigger] mem_w(sig, psub(*x, s), rho, wx, v);
                assert(mem_w(sig, psub(m, s), rho, u, Wit::Ap(wf_, wx, Box::new(v1), Box::new(v2))));
            }
        },
        ExprSpec::Const(..) => {
            assert(mem_w(sig, psub(m, s), rho, u, w));
        },
        ExprSpec::Let(t, v, b) => {
            let_measure(sig, *t, *v, *b);
            let r = crate::subst_algebra::inst(0, *v, *b);
            mem_psub_back(sig, r, s, rho, rho2, u, w);
            let w2 = choose|v2: Wit| #[trigger] mem_w(sig, psub(r, s), rho, u, v2);
            assert(mem_w(sig, psub(m, s), rho, u, w2));
        },
        ExprSpec::Proj(i, x) => {
            if u is Bot {
                assert(mem_w(sig, psub(m, s), rho, u, Wit::Nil));
            } else if let Wit::Pj(v, wx) = w {
                mem_psub_back(sig, *x, s, rho, rho2, v, *wx);
                let v1 = choose|v1: Wit| #[trigger] mem_w(sig, psub(*x, s), rho, v, v1);
                assert(mem_w(sig, psub(m, s), rho, u, Wit::Pj(v, Box::new(v1))));
            }
        },
        _ => {
            assert(mem_w(sig, psub(m, s), rho, u, Wit::Nil));
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
    reveal(mem);
    reveal(typed);
    reveal(jc);
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
    reveal(mem);
    reveal(typed);
    reveal(jc);
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
    reveal(mem);
    reveal(typed);
    reveal(jc);
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
    reveal(mem);
    reveal(typed);
    reveal(jc);
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
    reveal(mem);
    reveal(typed);
    reveal(jc);
}

/// Two elements below a well-formed bound are compatible, and their join
/// is below it.
pub proof fn below_pair(u1: Cpt, u2: Cpt, w: Cpt)
    requires
        wf(u1),
        wf(u2),
        wf(w),
        le(u1, w),
        le(u2, w),
    ensures
        compat(u1, u2),
        wf(join(u1, u2)),
        le(join(u1, u2), w),
{
    ub_compat(u1, u2, w);
    join_ub(u1, u2);
    join_lub(u1, u2, w);
}

/// A denotation is closed under compatible joins.
#[verifier::opaque]
pub open spec fn jc(sig: Sig, m: ExprSpec, rho: Env) -> bool {
    forall|u1: Cpt, u2: Cpt| #[trigger] mem(sig, m, rho, u1) && #[trigger] mem(sig, m, rho, u2)
        ==> compat(u1, u2) && mem(sig, m, rho, join(u1, u2))
}

pub proof fn jc_var(sig: Sig, i: nat, rho: Env)
    requires
        wf(rho(i)),
    ensures
        jc(sig, ExprSpec::Var(i), rho),
{
    let m = ExprSpec::Var(i);
    assert forall|u1: Cpt, u2: Cpt| mem(sig, m, rho, u1) && mem(sig, m, rho, u2)
        implies #[trigger] jc_pair(sig, m, rho, u1, u2) by {
        reveal(mem);
        let w1 = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u1, w);
        let w2 = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u2, w);
        below_pair(u1, u2, rho(i));
        assert(mem_w(sig, m, rho, join(u1, u2), Wit::Nil));
    }
    jc_intro(sig, m, rho);
}

/// A lifted term under an extended environment denotes what the term
/// denotes.
pub proof fn mem_lift1(sig: Sig, t: ExprSpec, rho: Env, x: Cpt, u: Cpt)
    ensures
        mem(sig, crate::subst_algebra::lift(1, 0, t), ext(rho, x), u) == mem(sig, t, rho, u),
{
    reveal(mem);
    reveal(typed);
    reveal(jc);
    use crate::ti_subst::{lift_is_rn, lr};
    lift_is_rn(1, 0, t);
    assert forall|j: nat| #[trigger] rho(j) == env_rn(ext(rho, x), lr(1, 0))(j) by {}
    if mem(sig, t, rho, u) {
        let w = choose|w: Wit| #[trigger] mem_w(sig, t, rho, u, w);
        mem_env_ext(sig, t, rho, env_rn(ext(rho, x), lr(1, 0)), u, w);
        mem_rn(sig, t, lr(1, 0), ext(rho, x), u, w);
        assert(mem_w(sig, crate::subst_algebra::lift(1, 0, t), ext(rho, x), u, w));
    }
    if mem(sig, crate::subst_algebra::lift(1, 0, t), ext(rho, x), u) {
        let w = choose|w: Wit| #[trigger] mem_w(sig, crate::subst_algebra::lift(1, 0, t), ext(rho, x), u, w);
        mem_rn(sig, t, lr(1, 0), ext(rho, x), u, w);
        mem_env_ext(sig, t, env_rn(ext(rho, x), lr(1, 0)), rho, u, w);
    }
}

pub proof fn jc_lift(sig: Sig, t: ExprSpec, rho: Env, x: Cpt)
    requires
        jc(sig, t, rho),
    ensures
        jc(sig, crate::subst_algebra::lift(1, 0, t), ext(rho, x)),
{
    reveal(mem);
    reveal(typed);
    reveal(jc);
    let lt = crate::subst_algebra::lift(1, 0, t);
    assert forall|u1: Cpt, u2: Cpt| #[trigger] mem(sig, lt, ext(rho, x), u1) && #[trigger] mem(sig, lt, ext(rho, x), u2)
        implies compat(u1, u2) && mem(sig, lt, ext(rho, x), join(u1, u2)) by {
        mem_lift1(sig, t, rho, x, u1);
        mem_lift1(sig, t, rho, x, u2);
        mem_lift1(sig, t, rho, x, join(u1, u2));
    }
}

/// The join of members of a join-closed denotation is a member.
pub proof fn jall_mem(sig: Sig, m: ExprSpec, rho: Env, t: Seq<Cpt>, k: int)
    requires
        jc(sig, m, rho),
        0 <= k <= t.len(),
        forall|i: int| 0 <= i < t.len() ==> #[trigger] mem(sig, m, rho, t[i]),
    ensures
        mem(sig, m, rho, joinall(t, k)),
    decreases k,
{
    reveal(mem);
    if k == 0 {
        mem_bot(sig, m, rho);
    } else {
        jall_mem(sig, m, rho, t, k - 1);
        assert(mem(sig, m, rho, t[k - 1]));
        jc_elim(sig, m, rho, joinall(t, k - 1), t[k - 1]);
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

pub proof fn covers_bot(sig: Sig, s: crate::ti_subst::Sub, rho: Env)
    ensures
        covers(sig, s, rho, bot_env()),
{
    reveal(mem);
    reveal(typed);
    reveal(jc);
    assert forall|i: nat| #[trigger] mem(sig, s(i), rho, bot_env()(i)) by {
        mem_bot(sig, s(i), rho);
    }
}

/// Two covering environments join into one above both.
pub proof fn covers_join2(sig: Sig, s: crate::ti_subst::Sub, rho: Env, r1: Env, r2: Env)
    requires
        covers(sig, s, rho, r1),
        covers(sig, s, rho, r2),
        forall|i: nat| #[trigger] jc(sig, s(i), rho),
    ensures
        covers(sig, s, rho, env_join2(r1, r2)),
        env_le(r1, env_join2(r1, r2)),
        env_le(r2, env_join2(r1, r2)),
{
    reveal(mem);
    reveal(typed);
    assert forall|i: nat| #[trigger] mem(sig, s(i), rho, env_join2(r1, r2)(i)) && le(r1(i), env_join2(r1, r2)(i)) && le(r2(i), env_join2(r1, r2)(i)) by {
        assert(mem(sig, s(i), rho, r1(i)) && mem(sig, s(i), rho, r2(i)));
        jc_elim(sig, s(i), rho, r1(i), r2(i));
        let w1 = choose|w: Wit| #[trigger] mem_w(sig, s(i), rho, r1(i), w);
        let w2 = choose|w: Wit| #[trigger] mem_w(sig, s(i), rho, r2(i), w);
        mem_wf(sig, s(i), rho, r1(i), w1);
        mem_wf(sig, s(i), rho, r2(i), w2);
        join_ub(r1(i), r2(i));
    }
    assert forall|i: nat| #[trigger] le(r1(i), env_join2(r1, r2)(i)) by {
        assert(mem(sig, s(i), rho, env_join2(r1, r2)(i)) && le(r1(i), env_join2(r1, r2)(i)));
    }
    assert forall|i: nat| #[trigger] le(r2(i), env_join2(r1, r2)(i)) by {
        assert(mem(sig, s(i), rho, env_join2(r1, r2)(i)) && le(r2(i), env_join2(r1, r2)(i)));
    }
}

/// The substitution moved under a binder is still join-closed pointwise.
pub proof fn jc_up(sig: Sig, s: crate::ti_subst::Sub, rho: Env, x: Cpt)
    requires
        forall|i: nat| #[trigger] jc(sig, s(i), rho),
        wf(x),
    ensures
        forall|i: nat| #[trigger] jc(sig, crate::ti_subst::up(s)(i), ext(rho, x)),
{
    reveal(mem);
    reveal(typed);
    reveal(jc);
    assert forall|i: nat| #[trigger] jc(sig, crate::ti_subst::up(s)(i), ext(rho, x)) by {
        if i == 0 {
            jc_var(sig, 0, ext(rho, x));
        } else {
            assert(jc(sig, s((i - 1) as nat), rho));
            jc_lift(sig, s((i - 1) as nat), rho, x);
        }
    }
}

/// A covering of `up(s)` under `ext(rho, x)`: its head is below `x`, its
/// tail covers `s`.
pub proof fn covers_up_back(sig: Sig, s: crate::ti_subst::Sub, rho: Env, x: Cpt, r: Env)
    requires
        covers(sig, crate::ti_subst::up(s), ext(rho, x), r),
    ensures
        le(r(0), x),
        covers(sig, s, rho, tail(r)),
{
    reveal(mem);
    reveal(typed);
    reveal(jc);
    assert(mem(sig, crate::ti_subst::up(s)(0), ext(rho, x), r(0)));
    let w0 = choose|w: Wit| #[trigger] mem_w(sig, ExprSpec::Var(0), ext(rho, x), r(0), w);
    assert forall|i: nat| #[trigger] mem(sig, s(i), rho, tail(r)(i)) by {
        assert(mem(sig, crate::ti_subst::up(s)(i + 1), ext(rho, x), r(i + 1)));
        mem_lift1(sig, s(i), rho, x, r(i + 1));
    }
}

/// The entries of a binder's generator, pulled back through the
/// substitution into one covering environment.
proof fn entries_fwd(sig: Sig, b: ExprSpec, s: crate::ti_subst::Sub, rho: Env, gen: Cpt, ws: Seq<Wit>, k: int) -> (acc: Env)
    requires
        0 <= k <= ws.len(),
        ws.len() == gsteps(gen).len(),
        forall|i: int| 0 <= i < ws.len() ==> wf(#[trigger] gsteps(gen)[i].0)
            && mem_w(sig, crate::ti_subst::psub(b, crate::ti_subst::up(s)), ext(rho, gsteps(gen)[i].0), gsteps(gen)[i].1, ws[i]),
        forall|i: nat| #[trigger] jc(sig, s(i), rho),
    ensures
        covers(sig, s, rho, acc),
        forall|i: int| 0 <= i < k ==> #[trigger] mem(sig, b, ext(acc, gsteps(gen)[i].0), gsteps(gen)[i].1),
    decreases crank(sig, b), crate::ti_zsize::zsize(b), k + 1,
{
    reveal(mem);
    reveal(typed);
    reveal(jc);
    if k == 0 {
        covers_bot(sig, s, rho);
        bot_env()
    } else {
        let acc0 = entries_fwd(sig, b, s, rho, gen, ws, k - 1);
        let (x, y) = gsteps(gen)[k - 1];
        jc_up(sig, s, rho, x);
        let r = mem_psub_fwd(sig, b, crate::ti_subst::up(s), ext(rho, x), y, ws[k - 1]);
        covers_up_back(sig, s, rho, x, r);
        covers_join2(sig, s, rho, acc0, tail(r));
        let acc = env_join2(acc0, tail(r));
        assert forall|i: int| 0 <= i < k implies #[trigger] mem(sig, b, ext(acc, gsteps(gen)[i].0), gsteps(gen)[i].1) by {
            let xi = gsteps(gen)[i].0;
            assert forall|j: nat| #[trigger] le(ext(acc0, xi)(j), ext(acc, xi)(j)) by {
                if j == 0 {
                    le_refl(xi);
                }
            }
            if i < k - 1 {
                assert(mem(sig, b, ext(acc0, gsteps(gen)[i].0), gsteps(gen)[i].1));
                let wi = choose|w: Wit| #[trigger] mem_w(sig, b, ext(acc0, xi), gsteps(gen)[i].1, w);
                mem_env_mono(sig, b, ext(acc0, xi), ext(acc, xi), gsteps(gen)[i].1, wi);
            } else {
                assert forall|j: nat| #[trigger] le(r(j), ext(acc, x)(j)) by {
                    if j > 0 {
                        assert(le(tail(r)((j - 1) as nat), acc((j - 1) as nat)));
                    }
                }
                let wi = choose|w: Wit| #[trigger] mem_w(sig, b, r, y, w);
                mem_env_mono(sig, b, r, ext(acc, x), y, wi);
            }
        }
        acc
    }
}

/// SUBSTITUTION, SEMANTICALLY (the other direction, for join-closed
/// substitutions): what a substitution instance denotes, the term denotes
/// under some covered environment.
pub proof fn mem_psub_fwd(sig: Sig, m: ExprSpec, s: crate::ti_subst::Sub, rho: Env, u: Cpt, w: Wit) -> (rho2: Env)
    requires
        mem_w(sig, crate::ti_subst::psub(m, s), rho, u, w),
        forall|i: nat| #[trigger] jc(sig, s(i), rho),
    ensures
        covers(sig, s, rho, rho2),
        mem(sig, m, rho2, u),
    decreases crank(sig, m), crate::ti_zsize::zsize(m), 0int,
{
    if let ExprSpec::Bind(bk0, ta0, b0) = m {
        crate::ti_zsize::zsize_bind(bk0, *ta0, *b0);
    }
    reveal(mem);
    reveal(typed);
    reveal(jc);
    use crate::ti_subst::{psub, up};
    match m {
        ExprSpec::Var(i) => {
            let r: Env = |j: nat| if j == i { u } else { Cpt::Bot };
            mem_wf(sig, s(i), rho, u, w);
            assert forall|j: nat| #[trigger] mem(sig, s(j), rho, r(j)) by {
                if j == i {
                    assert(mem_w(sig, s(i), rho, u, w));
                } else {
                    mem_bot(sig, s(j), rho);
                }
            }
            le_refl(u);
            assert(mem_w(sig, m, r, u, Wit::Nil));
            r
        },
        ExprSpec::Bind(bk, ta, b) => {
            covers_bot(sig, s, rho);
            if u is Bot {
                assert(mem_w(sig, m, bot_env(), u, Wit::Nil));
                bot_env()
            } else if let Wit::Gen(a, gen, wa, ws) = w {
                let ra = mem_psub_fwd(sig, *ta, s, rho, a, *wa);
                assert(entries_ok(sig, psub(*b, up(s)), rho, a, gen, ws));
                let acc = entries_fwd(sig, *b, s, rho, gen, ws, ws.len() as int);
                covers_join2(sig, s, rho, ra, acc);
                let r2 = env_join2(ra, acc);
                let wa2 = choose|v: Wit| #[trigger] mem_w(sig, *ta, ra, a, v);
                mem_env_mono(sig, *ta, ra, r2, a, wa2);
                let st = gsteps(gen);
                assert forall|i: int| 0 <= i < ws.len() implies #[trigger] mem(sig, *b, ext(r2, st[i].0), st[i].1) by {
                    let xi = st[i].0;
                    assert(mem(sig, *b, ext(acc, xi), st[i].1));
                    assert forall|j: nat| #[trigger] le(ext(acc, xi)(j), ext(r2, xi)(j)) by {
                        if j == 0 {
                            le_refl(xi);
                        }
                    }
                    let wi = choose|v: Wit| #[trigger] mem_w(sig, *b, ext(acc, xi), st[i].1, v);
                    mem_env_mono(sig, *b, ext(acc, xi), ext(r2, xi), st[i].1, wi);
                }
                let ws2 = Seq::new(ws.len(), |i: int| choose|v: Wit| #[trigger] mem_w(sig, *b, ext(r2, st[i].0), st[i].1, v));
                assert forall|i: int| 0 <= i < ws2.len() implies
                    typed(#[trigger] gsteps(gen)[i].0, a) && mem_w(sig, *b, ext(r2, gsteps(gen)[i].0), gsteps(gen)[i].1, ws2[i]) by {
                    assert(mem(sig, *b, ext(r2, st[i].0), st[i].1));
                }
                assert(entries_ok(sig, *b, r2, a, gen, ws2));
                assert(mem_w(sig, m, r2, u, Wit::Gen(a, gen, Box::new(wa2), ws2)));
                r2
            } else {
                assert(false);
                bot_env()
            }
        },
        ExprSpec::App(f, x) => {
            if let Wit::Ap(wf_, wx, w1, w2) = w {
                let r1 = mem_psub_fwd(sig, *f, s, rho, wf_, *w1);
                let r2 = mem_psub_fwd(sig, *x, s, rho, wx, *w2);
                covers_join2(sig, s, rho, r1, r2);
                let r = env_join2(r1, r2);
                let v1 = choose|v: Wit| #[trigger] mem_w(sig, *f, r1, wf_, v);
                let v2 = choose|v: Wit| #[trigger] mem_w(sig, *x, r2, wx, v);
                mem_env_mono(sig, *f, r1, r, wf_, v1);
                mem_env_mono(sig, *x, r2, r, wx, v2);
                assert(mem_w(sig, m, r, u, Wit::Ap(wf_, wx, Box::new(v1), Box::new(v2))));
                r
            } else {
                assert(false);
                bot_env()
            }
        },
        ExprSpec::Let(t, v, b) => {
            let_measure(sig, *t, *v, *b);
            let r = crate::subst_algebra::inst(0, *v, *b);
            assert(mem_w(sig, psub(r, s), rho, u, w));
            let r2 = mem_psub_fwd(sig, r, s, rho, u, w);
            let w2 = choose|v2: Wit| #[trigger] mem_w(sig, r, r2, u, v2);
            assert(mem_w(sig, m, r2, u, w2));
            r2
        },
        ExprSpec::Const(..) => {
            covers_bot(sig, s, rho);
            assert(mem_w(sig, m, bot_env(), u, w));
            bot_env()
        },
        ExprSpec::Proj(i, x) => {
            if u is Bot {
                covers_bot(sig, s, rho);
                assert(mem_w(sig, m, bot_env(), u, Wit::Nil));
                bot_env()
            } else if let Wit::Pj(v, wx) = w {
                let r = mem_psub_fwd(sig, *x, s, rho, v, *wx);
                let v1 = choose|v1: Wit| #[trigger] mem_w(sig, *x, r, v, v1);
                assert(mem_w(sig, m, r, u, Wit::Pj(v, Box::new(v1))));
                r
            } else {
                assert(false);
                bot_env()
            }
        },
        _ => {
            covers_bot(sig, s, rho);
            assert(mem_w(sig, m, bot_env(), u, Wit::Nil));
            bot_env()
        },
    }
}

/// Using join-closure at one pair.
pub proof fn jc_elim(sig: Sig, m: ExprSpec, rho: Env, u1: Cpt, u2: Cpt)
    requires
        jc(sig, m, rho),
        mem(sig, m, rho, u1),
        mem(sig, m, rho, u2),
    ensures
        compat(u1, u2),
        mem(sig, m, rho, join(u1, u2)),
{
    reveal(jc);
}

/// Establishing join-closure from every pair.
pub proof fn jc_intro(sig: Sig, m: ExprSpec, rho: Env)
    requires
        forall|u1: Cpt, u2: Cpt| mem(sig, m, rho, u1) && mem(sig, m, rho, u2) ==> #[trigger] jc_pair(sig, m, rho, u1, u2),
    ensures
        jc(sig, m, rho),
{
    reveal(jc);
    assert forall|u1: Cpt, u2: Cpt| #[trigger] mem(sig, m, rho, u1) && #[trigger] mem(sig, m, rho, u2)
        implies compat(u1, u2) && mem(sig, m, rho, join(u1, u2)) by {
        assert(jc_pair(sig, m, rho, u1, u2));
    }
}

/// Join-closure at one pair, as an atom.
pub open spec fn jc_pair(sig: Sig, m: ExprSpec, rho: Env, u1: Cpt, u2: Cpt) -> bool {
    compat(u1, u2) && mem(sig, m, rho, join(u1, u2))
}

/// Environments that agree below `k` give a term with no loose variable
/// from `k` on the same members, with the same witnesses.
pub proof fn mem_closed(sig: Sig, e: ExprSpec, rho: Env, rho2: Env, k: nat, u: Cpt, w: Wit)
    requires
        crate::expr_model::nlbv(e) <= k,
        forall|i: nat| i < k ==> #[trigger] rho(i) == rho2(i),
    ensures
        mem_w(sig, e, rho, u, w) == mem_w(sig, e, rho2, u, w),
    decreases crank(sig, e), crate::ti_zsize::zsize(e),
{
    if let ExprSpec::Bind(bk0, ta0, b0) = e {
        crate::ti_zsize::zsize_bind(bk0, *ta0, *b0);
    }
    match e {
        ExprSpec::Bind(bk, ta, b) => {
            if let Wit::Gen(a, gen, wa, ws) = w {
                mem_closed(sig, *ta, rho, rho2, k, a, *wa);
                assert forall|i: int| 0 <= i < gsteps(gen).len() implies
                    #[trigger] mem_w(sig, *b, ext(rho, gsteps(gen)[i].0), gsteps(gen)[i].1, ws[i])
                        == mem_w(sig, *b, ext(rho2, gsteps(gen)[i].0), gsteps(gen)[i].1, ws[i]) by {
                    let x = gsteps(gen)[i].0;
                    assert forall|j: nat| j < k + 1 implies #[trigger] ext(rho, x)(j) == ext(rho2, x)(j) by {
                        if j > 0 {
                            assert(rho((j - 1) as nat) == rho2((j - 1) as nat));
                        }
                    }
                    mem_closed(sig, *b, ext(rho, x), ext(rho2, x), k + 1, gsteps(gen)[i].1, ws[i]);
                }
                if entries_ok(sig, *b, rho, a, gen, ws) {
                    assert forall|i: int| 0 <= i < ws.len() implies typed(#[trigger] gsteps(gen)[i].0, a)
                        && mem_w(sig, *b, ext(rho2, gsteps(gen)[i].0), gsteps(gen)[i].1, ws[i]) by {
                        assert(typed(gsteps(gen)[i].0, a) && mem_w(sig, *b, ext(rho, gsteps(gen)[i].0), gsteps(gen)[i].1, ws[i]));
                    }
                }
                if entries_ok(sig, *b, rho2, a, gen, ws) {
                    assert forall|i: int| 0 <= i < ws.len() implies typed(#[trigger] gsteps(gen)[i].0, a)
                        && mem_w(sig, *b, ext(rho, gsteps(gen)[i].0), gsteps(gen)[i].1, ws[i]) by {
                        assert(typed(gsteps(gen)[i].0, a) && mem_w(sig, *b, ext(rho2, gsteps(gen)[i].0), gsteps(gen)[i].1, ws[i]));
                    }
                }
            }
        },
        ExprSpec::App(f, x) => {
            if let Wit::Ap(wf_, wx, w1, w2) = w {
                mem_closed(sig, *f, rho, rho2, k, wf_, *w1);
                mem_closed(sig, *x, rho, rho2, k, wx, *w2);
            }
        },
        ExprSpec::Proj(i, x) => {
            if let Wit::Pj(v, wx) = w {
                mem_closed(sig, *x, rho, rho2, k, v, *wx);
            }
        },
        ExprSpec::Let(t, v, b) => {
            let_measure(sig, *t, *v, *b);
            mem_closed(sig, crate::subst_algebra::inst(0, *v, *b), rho, rho2, k, u, w);
        },
        _ => {},
    }
}

/// A closed term denotes the same in every environment.
pub proof fn mem_closed_env(sig: Sig, e: ExprSpec, rho: Env, u: Cpt)
    requires
        crate::expr_model::nlbv(e) == 0,
    ensures
        mem(sig, e, rho, u) == mem(sig, e, bot_env(), u),
{
    reveal(mem);
    if mem(sig, e, rho, u) {
        let w = choose|w: Wit| #[trigger] mem_w(sig, e, rho, u, w);
        mem_closed(sig, e, rho, bot_env(), 0, u, w);
    }
    if mem(sig, e, bot_env(), u) {
        let w = choose|w: Wit| #[trigger] mem_w(sig, e, bot_env(), u, w);
        mem_closed(sig, e, rho, bot_env(), 0, u, w);
    }
}

/// What a constant denotes: bottom, and a definition's value.
pub proof fn mem_const(sig: Sig, c: u64, ls: Seq<LevelSpec>, rho: Env, u: Cpt)
    ensures
        crate::ti_syntax::def_ok(sig, c, ls) ==> mem(sig, ExprSpec::Const(c, ls), rho, u) == (u is Bot || mem(sig, dval(sig, c, ls), bot_env(), u)),
        !crate::ti_syntax::is_def(sig, c, ls) && !sem_const(sig, c, ls) ==> mem(sig, ExprSpec::Const(c, ls), rho, u) == (u is Bot),
{
    reveal(mem);
    let m = ExprSpec::Const(c, ls);
    assert(mem_w(sig, m, rho, Cpt::Bot, Wit::Nil));
    if crate::ti_syntax::def_ok(sig, c, ls) {
        assert(unfolds(sig, c, ls));
        if mem(sig, dval(sig, c, ls), bot_env(), u) {
            let w = choose|w: Wit| #[trigger] mem_w(sig, dval(sig, c, ls), bot_env(), u, w);
            mem_wf(sig, dval(sig, c, ls), bot_env(), u, w);
            assert(mem_w(sig, m, rho, u, w));
        }
        if mem(sig, m, rho, u) && !(u is Bot) {
            let w = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
            assert(mem_w(sig, dval(sig, c, ls), bot_env(), u, w));
        }
    }
}

/// A `let` denotes its body's instance.
pub proof fn mem_let(sig: Sig, t: ExprSpec, v: ExprSpec, b: ExprSpec, rho: Env)
    ensures
        forall|u: Cpt| #[trigger] mem(sig, ExprSpec::Let(Box::new(t), Box::new(v), Box::new(b)), rho, u)
            == mem(sig, crate::subst_algebra::inst(0, v, b), rho, u),
{
    reveal(mem);
    let m = ExprSpec::Let(Box::new(t), Box::new(v), Box::new(b));
    let r = crate::subst_algebra::inst(0, v, b);
    assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) == mem(sig, r, rho, u) by {
        if mem(sig, m, rho, u) {
            let w = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
            assert(mem_w(sig, r, rho, u, w));
        }
        if mem(sig, r, rho, u) {
            let w = choose|w: Wit| #[trigger] mem_w(sig, r, rho, u, w);
            assert(mem_w(sig, m, rho, u, w));
        }
    }
}

} // verus!
