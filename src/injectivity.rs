//! INJECTIVITY (layer 2 of the metatheory). Reduction keeps a Pi a Pi and a
//! Sort that Sort, so by Church-Rosser (`ceq_jn_into`) two convertible Pis have
//! convertible domains and codomains, two convertible Sorts have equivalent
//! levels, and a Sort never converts with a binder.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::beta_model::*;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::confluence::pstep_bind_shape;
#[cfg(verus_only)]
use crate::conv_cr::*;
#[cfg(verus_only)]
use crate::conv_frag::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A Sort has no reduct but itself.
pub proof fn star_sort_inv(env: EnvSpec, l: LevelSpec, e: ExprSpec)
    requires
        pstep_star(env, ExprSpec::Sort(l), e),
    ensures
        e == ExprSpec::Sort(l),
{
    let ch = choose|c: Seq<ExprSpec>| c.len() >= 1 && c[0] == ExprSpec::Sort(l) && c[c.len() - 1] == e && pstep_chain_valid(env, c);
    sort_chain(env, l, ch, (ch.len() - 1) as nat);
}

proof fn sort_chain(env: EnvSpec, l: LevelSpec, ch: Seq<ExprSpec>, n: nat)
    requires
        ch.len() >= 1,
        ch[0] == ExprSpec::Sort(l),
        n < ch.len(),
        pstep_chain_valid(env, ch),
    ensures
        ch[n as int] == ExprSpec::Sort(l),
    decreases n,
{
    if n > 0 {
        let m = (n - 1) as nat;
        sort_chain(env, l, ch, m);
        assert(pstep(env, ch[m as int], ch[m as int + 1]));
    }
}

/// Every reduct of a binder is that binder with reduced parts.
pub proof fn star_bind_inv(env: EnvSpec, bk: BinderKind, t: ExprSpec, b: ExprSpec, e: ExprSpec) -> (r: (ExprSpec, ExprSpec))
    requires
        pstep_star(env, ExprSpec::Bind(bk, Box::new(t), Box::new(b)), e),
    ensures
        e == ExprSpec::Bind(bk, Box::new(r.0), Box::new(r.1)),
        pstep_star(env, t, r.0),
        pstep_star(env, b, r.1),
{
    let ch = choose|c: Seq<ExprSpec>| c.len() >= 1 && c[0] == ExprSpec::Bind(bk, Box::new(t), Box::new(b)) && c[c.len() - 1] == e
        && pstep_chain_valid(env, c);
    bind_chain(env, bk, t, b, ch, (ch.len() - 1) as nat)
}

proof fn bind_chain(env: EnvSpec, bk: BinderKind, t: ExprSpec, b: ExprSpec, ch: Seq<ExprSpec>, n: nat) -> (r: (ExprSpec, ExprSpec))
    requires
        ch.len() >= 1,
        ch[0] == ExprSpec::Bind(bk, Box::new(t), Box::new(b)),
        n < ch.len(),
        pstep_chain_valid(env, ch),
    ensures
        ch[n as int] == ExprSpec::Bind(bk, Box::new(r.0), Box::new(r.1)),
        pstep_star(env, t, r.0),
        pstep_star(env, b, r.1),
    decreases n,
{
    if n == 0 {
        pstep_star_refl(env, t);
        pstep_star_refl(env, b);
        (t, b)
    } else {
        let m = (n - 1) as nat;
        let (t1, b1) = bind_chain(env, bk, t, b, ch, m);
        assert(pstep(env, ch[m as int], ch[m as int + 1]));
        let (t2, b2) = pstep_bind_shape(env, bk, t1, b1, ch[n as int]);
        pstep_star_one(env, t1, t2);
        pstep_star_one(env, b1, b2);
        pstep_star_trans(env, t, t1, t2);
        pstep_star_trans(env, b, b1, b2);
        (t2, b2)
    }
}

/// PI INJECTIVITY: convertible binders have the same kind, joinable
/// domains and joinable bodies.
pub proof fn ceq_bind_inj(
    env: EnvSpec,
    ne: EnvSpec,
    bk1: BinderKind,
    t1: ExprSpec,
    b1: ExprSpec,
    bk2: BinderKind,
    t2: ExprSpec,
    b2: ExprSpec,
    h: nat,
)
    requires
        cr_into(env, ne),
        ceq(env, ExprSpec::Bind(bk1, Box::new(t1), Box::new(b1)), ExprSpec::Bind(bk2, Box::new(t2), Box::new(b2)), h),
    ensures
        bk1 == bk2,
        jn(env, t1, t2),
        jn(env, b1, b2),
{
    let x = ExprSpec::Bind(bk1, Box::new(t1), Box::new(b1));
    let y = ExprSpec::Bind(bk2, Box::new(t2), Box::new(b2));
    ceq_jn_into(env, ne, x, y, h);
    let (x2, y2) = jn_elim(ne, x, y);
    let (t3, b3) = star_bind_inv(ne, bk1, t1, b1, x2);
    let (t4, b4) = star_bind_inv(ne, bk2, t2, b2, y2);
    assert(lveq(t3, t4) && lveq(b3, b4));
    jn_intro(ne, t1, t2, t3, t4);
    jn_intro(ne, b1, b2, b3, b4);
    jn_up(env, ne, t1, t2);
    jn_up(env, ne, b1, b2);
}

/// SORT INJECTIVITY: convertible Sorts have equivalent levels.
pub proof fn ceq_sort_inj(env: EnvSpec, ne: EnvSpec, l1: LevelSpec, l2: LevelSpec, h: nat)
    requires
        cr_into(env, ne),
        ceq(env, ExprSpec::Sort(l1), ExprSpec::Sort(l2), h),
    ensures
        lev_eq(l1, l2),
{
    ceq_jn_into(env, ne, ExprSpec::Sort(l1), ExprSpec::Sort(l2), h);
    let (x2, y2) = jn_elim(ne, ExprSpec::Sort(l1), ExprSpec::Sort(l2));
    star_sort_inv(ne, l1, x2);
    star_sort_inv(ne, l2, y2);
}

/// A Sort never converts with a binder.
pub proof fn ceq_sort_bind(env: EnvSpec, ne: EnvSpec, l: LevelSpec, bk: BinderKind, t: ExprSpec, b: ExprSpec, h: nat)
    requires
        cr_into(env, ne),
    ensures
        !ceq(env, ExprSpec::Sort(l), ExprSpec::Bind(bk, Box::new(t), Box::new(b)), h),
{
    if ceq(env, ExprSpec::Sort(l), ExprSpec::Bind(bk, Box::new(t), Box::new(b)), h) {
        ceq_jn_into(env, ne, ExprSpec::Sort(l), ExprSpec::Bind(bk, Box::new(t), Box::new(b)), h);
        let (x2, y2) = jn_elim(ne, ExprSpec::Sort(l), ExprSpec::Bind(bk, Box::new(t), Box::new(b)));
        star_sort_inv(ne, l, x2);
        let (t2, b2) = star_bind_inv(ne, bk, t, b, y2);
    }
}

} // verus!
