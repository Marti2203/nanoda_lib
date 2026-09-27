//! CONVERSION WITHOUT ETA IS JOINABILITY (layer 1 of the metatheory, the
//! fragment). `ceq` is `deq` without its eta leaf -- a sub-relation
//! (`ceq_deq`) -- and in an environment where the redex kinds do not
//! overlap (`cr_env`), `ceq`-convertible terms have reducts that agree up to
//! universe-level equivalence (`ceq_jn`). Eta is the one generator
//! reduction cannot see; full Lean conversion replaces this layer only.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::beta_model::*;
#[cfg(verus_only)]
use crate::expr_model::fv_absent;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::confluence::env_conf;
#[cfg(verus_only)]
use crate::conv_cr::*;
#[cfg(verus_only)]
use crate::swap_model::env_fv_free;
#[cfg(verus_only)]
use crate::tc_model::{deq, deq_c, deq_chain_valid, deq_leaf, deq_quot, deq_rec, fresh_marker, inst_free, quot_ready, quot_result};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One step of eta-free conversion: `deq_c` without `deq_eta`.
pub open spec fn ceq_c(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat) -> bool
    decreases h, 0int,
{
    ||| defeq(env, x, y)
    ||| deq_leaf(x, y)
    ||| deq_quot(env.export, x, y)
    ||| deq_rec(env, x, y)
    ||| (h > 0 && match (x, y) {
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => ceq_c(env, *f1, *f2, (h - 1) as nat)
            && ceq_c(env, *a1, *a2, (h - 1) as nat),
        (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => bk1 == bk2 && ceq_c(env, *t1, *t2, (h - 1) as nat)
            && (ceq_c(env, *b1, *b2, (h - 1) as nat) || (exists|k: nat| #[trigger]
            fresh_marker(k) && fv_absent(*b1, k) && fv_absent(*b2, k) && ceq(
                env,
                inst_free(*b1, k),
                inst_free(*b2, k),
                (h - 1) as nat,
            ))),
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => ceq_c(env, *t1, *t2, (h - 1) as nat)
            && ceq_c(env, *v1, *v2, (h - 1) as nat) && ceq_c(env, *b1, *b2, (h - 1) as nat),
        (ExprSpec::Proj(p1, s1), ExprSpec::Proj(p2, s2)) => p1 == p2 && ceq_c(env, *s1, *s2, (h - 1) as nat),
        _ => false,
    })
}

pub open spec fn ceq_chain_valid(env: EnvSpec, ch: Seq<ExprSpec>, h: nat) -> bool
    decreases h, 1int,
{
    forall|i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 ==> ceq_c(env, ch[i], ch[i + 1], h)
}

/// Eta-free conversion: chains of `ceq_c` steps.
pub open spec fn ceq(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat) -> bool
    decreases h, 2int,
{
    exists|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && ceq_chain_valid(env, ch, h)
}

/// `ceq_c` is a sub-relation of `deq_c`.
pub proof fn ceq_c_deq_c(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat)
    requires
        ceq_c(env, x, y, h),
    ensures
        deq_c(env, x, y, h),
    decreases h, 0int,
{
    if defeq(env, x, y) || deq_leaf(x, y) || deq_quot(env.export, x, y) || deq_rec(env, x, y) {
    } else {
        match (x, y) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                ceq_c_deq_c(env, *f1, *f2, (h - 1) as nat);
                ceq_c_deq_c(env, *a1, *a2, (h - 1) as nat);
            },
            (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => {
                ceq_c_deq_c(env, *t1, *t2, (h - 1) as nat);
                if ceq_c(env, *b1, *b2, (h - 1) as nat) {
                    ceq_c_deq_c(env, *b1, *b2, (h - 1) as nat);
                } else {
                    let k = choose|k: nat| #[trigger]
                        fresh_marker(k) && fv_absent(*b1, k) && fv_absent(*b2, k) && ceq(
                            env,
                            inst_free(*b1, k),
                            inst_free(*b2, k),
                            (h - 1) as nat,
                        );
                    ceq_deq(env, inst_free(*b1, k), inst_free(*b2, k), (h - 1) as nat);
                    assert(fresh_marker(k));
                }
            },
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                ceq_c_deq_c(env, *t1, *t2, (h - 1) as nat);
                ceq_c_deq_c(env, *v1, *v2, (h - 1) as nat);
                ceq_c_deq_c(env, *b1, *b2, (h - 1) as nat);
            },
            (ExprSpec::Proj(p1, s1), ExprSpec::Proj(p2, s2)) => {
                ceq_c_deq_c(env, *s1, *s2, (h - 1) as nat);
            },
            _ => {},
        }
    }
}

/// `ceq` is a sub-relation of `deq`.
pub proof fn ceq_deq(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat)
    requires
        ceq(env, x, y, h),
    ensures
        deq(env, x, y, h),
    decreases h, 1int,
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && ceq_chain_valid(env, ch, h);
    assert forall|i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies deq_c(env, ch[i], ch[i + 1], h) by {
        ceq_c_deq_c(env, ch[i], ch[i + 1], h);
    }
    assert(deq_chain_valid(env, ch, h));
}

/// Every recursor rule is well formed, so the conversion leaf's readiness
/// (`rec_ready_u`) is reduction's (`rec_ready`).
pub open spec fn env_rules_ok(env: EnvSpec) -> bool {
    forall|id: u64, i: int| #![trigger env.recs[id].rules[i]]
        env.recs.contains_key(id) && 0 <= i < env.recs[id].rules.len() ==> rule_rhs_ok(env, env.recs[id].rules[i])
}

/// The environment facts Church-Rosser runs on.
pub open spec fn cr_env(env: EnvSpec) -> bool {
    &&& env_conf(env)
    &&& env_fv_free(env)
    &&& env_rules_ok(env)
}

pub proof fn rec_ready_of_u(env: EnvSpec, s: ExprSpec)
    requires
        env_rules_ok(env),
        rec_ready_u(env, s),
    ensures
        rec_ready(env, s),
{
    if let ExprSpec::Const(rid, lv) = spine_head(s) {
        if let Some(rd) = env.rec_data(rid) {
            let major = spine_args(s)[rd.major_idx as int];
            if let ExprSpec::Const(cid, clv) = spine_head(major) {
                find_rule_spec(rd.rules, cid);
                if let Some(ri) = find_rule(rd.rules, cid) {
                    assert(env.recs.contains_key(rid));
                    assert(rule_rhs_ok(env, env.recs[rid].rules[ri]));
                }
            }
        }
    }
}

/// A quotient redex joins its contractum.
pub proof fn jn_quot_leaf(env: EnvSpec, x: ExprSpec)
    requires
        quot_ready(env.export, x),
    ensures
        jn(env, x, quot_result(env.export, x)),
{
    if let ExprSpec::App(f, a) = x {
        assert(pstep(env, *f, *f));
        assert(pstep(env, *a, *a));
        pstep_quot_intro(env, f, a, *f, *a, quot_result(env.export, x));
        pstep_star_one(env, x, quot_result(env.export, x));
        jn_of_star(env, x, quot_result(env.export, x));
    } else {
        assert(spine_args(x).len() == 0);
    }
}

/// A recursor redex joins its contractum.
pub proof fn jn_rec_leaf(env: EnvSpec, x: ExprSpec)
    requires
        rec_ready(env, x),
    ensures
        jn(env, x, rec_result(env, x)),
{
    if let ExprSpec::App(f, a) = x {
        assert(pstep(env, *f, *f));
        assert(pstep(env, *a, *a));
        pstep_rec_intro(env, f, a, *f, *a, rec_result(env, x));
        pstep_star_one(env, x, rec_result(env, x));
        jn_of_star(env, x, rec_result(env, x));
    } else {
        assert(spine_args(x).len() == 0);
    }
}

pub proof fn jn_of_leaf(env: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        cr_env(env),
        defeq(env, x, y) || deq_leaf(x, y) || deq_quot(env.export, x, y) || deq_rec(env, x, y),
    ensures
        jn(env, x, y),
{
    if defeq(env, x, y) {
        jn_of_defeq(env, x, y);
    } else if deq_leaf(x, y) {
        assert(lveq(x, y));
        jn_of_lveq(env, x, y);
    } else if deq_quot(env.export, x, y) {
        if quot_ready(env.export, x) && y == quot_result(env.export, x) {
            jn_quot_leaf(env, x);
        } else {
            jn_quot_leaf(env, y);
            jn_symm(env, y, x);
        }
    } else {
        if rec_ready_u(env, x) && y == rec_result(env, x) {
            rec_ready_of_u(env, x);
            jn_rec_leaf(env, x);
        } else {
            rec_ready_of_u(env, y);
            jn_rec_leaf(env, y);
            jn_symm(env, y, x);
        }
    }
}

/// ONE ETA-FREE CONVERSION STEP IS JOINABLE.
pub proof fn ceq_c_jn(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat)
    requires
        cr_env(env),
        ceq_c(env, x, y, h),
    ensures
        jn(env, x, y),
    decreases h, 0int, 0int,
{
    if defeq(env, x, y) || deq_leaf(x, y) || deq_quot(env.export, x, y) || deq_rec(env, x, y) {
        jn_of_leaf(env, x, y);
    } else {
        match (x, y) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                ceq_c_jn(env, *f1, *f2, (h - 1) as nat);
                ceq_c_jn(env, *a1, *a2, (h - 1) as nat);
                jn_app(env, *f1, *f2, *a1, *a2);
            },
            (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => {
                ceq_c_jn(env, *t1, *t2, (h - 1) as nat);
                if ceq_c(env, *b1, *b2, (h - 1) as nat) {
                    ceq_c_jn(env, *b1, *b2, (h - 1) as nat);
                } else {
                    let k = choose|k: nat| #[trigger]
                        fresh_marker(k) && fv_absent(*b1, k) && fv_absent(*b2, k) && ceq(
                            env,
                            inst_free(*b1, k),
                            inst_free(*b2, k),
                            (h - 1) as nat,
                        );
                    ceq_jn(env, inst_free(*b1, k), inst_free(*b2, k), (h - 1) as nat);
                    jn_open(env, k, *b1, *b2);
                }
                jn_bind(env, bk1, *t1, *t2, *b1, *b2);
            },
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                ceq_c_jn(env, *t1, *t2, (h - 1) as nat);
                ceq_c_jn(env, *v1, *v2, (h - 1) as nat);
                ceq_c_jn(env, *b1, *b2, (h - 1) as nat);
                jn_let(env, *t1, *t2, *v1, *v2, *b1, *b2);
            },
            (ExprSpec::Proj(p1, s1), ExprSpec::Proj(p2, s2)) => {
                ceq_c_jn(env, *s1, *s2, (h - 1) as nat);
                jn_proj(env, p1, *s1, *s2);
            },
            _ => {},
        }
    }
}

proof fn ceq_chain_jn(env: EnvSpec, ch: Seq<ExprSpec>, h: nat, n: nat)
    requires
        cr_env(env),
        ch.len() >= 1,
        n < ch.len(),
        ceq_chain_valid(env, ch, h),
    ensures
        jn(env, ch[0], ch[n as int]),
    decreases h, 1int, n,
{
    if n == 0 {
        jn_refl(env, ch[0]);
    } else {
        let m = (n - 1) as nat;
        ceq_chain_jn(env, ch, h, m);
        assert(ceq_c(env, ch[m as int], ch[m as int + 1], h));
        ceq_c_jn(env, ch[m as int], ch[n as int], h);
        jn_trans(env, ch[0], ch[m as int], ch[n as int]);
    }
}

/// CHURCH-ROSSER FOR ETA-FREE CONVERSION: convertible terms reduce to terms
/// equal up to universe-level equivalence.
pub proof fn ceq_jn(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat)
    requires
        cr_env(env),
        ceq(env, x, y, h),
    ensures
        jn(env, x, y),
    decreases h, 2int, 0int,
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && ceq_chain_valid(env, ch, h);
    ceq_chain_jn(env, ch, h, (ch.len() - 1) as nat);
}

} // verus!
