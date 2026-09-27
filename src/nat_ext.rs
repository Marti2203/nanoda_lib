//! THE NAT-LITERAL EXTENSION AGREES WITH THE DEFINITIONS. The kernel folds
//! `Nat.add 2 3` to `5` with built-in arithmetic while `Nat.add` is also a
//! definition, so reduction has two overlapping rules there and confluence
//! is not provable for an arbitrary environment (an export may define
//! `Nat.add a b := 0`). `h_nat_ext` is the named hypothesis Lean's own
//! kernel rests on: each fold result is joinable, with folding off, with
//! the application it replaces. Under it every reduction step of the real
//! environment is a conversion of its fold-free form, which is confluent,
//! so eta-free conversion lands in joinability there (`ceq_jn_ext`).
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::beta_model::*;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::confluence::env_conf;
#[cfg(verus_only)]
use crate::conv_cr::*;
#[cfg(verus_only)]
use crate::conv_frag::*;
#[cfg(verus_only)]
use crate::fclose::{pstep_star_inst, pstep_star_inst_arg};
#[cfg(verus_only)]
use crate::subst_algebra::{env_bv_free, inst, subst1_is_inst};
#[cfg(verus_only)]
use crate::swap_model::env_fv_free;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// THE NAMED HYPOTHESIS: every foldable Nat-op application is joinable,
/// by reduction with the extension off, with the value the built-in
/// arithmetic returns.
pub open spec fn h_nat_ext(env: EnvSpec) -> bool {
    forall|s: ExprSpec| #[trigger] nat_fold_ready(env.export, s) ==> defeq(nofold(env), s, nat_fold_result(env.export, s))
}

/// The environment facts for Church-Rosser in a real environment: its
/// fold-free form is confluent, and the extension agrees with it.
pub open spec fn cr_ext(env: EnvSpec) -> bool {
    &&& env_conf(nofold(env))
    &&& env_fv_free(env)
    &&& env_rules_ok(env)
    &&& h_nat_ext(env)
}

/// Joinability is stable under substituting joinable terms.
pub proof fn jn_subst1(ne: EnvSpec, b1: ExprSpec, b2: ExprSpec, a1: ExprSpec, a2: ExprSpec)
    requires
        env_bv_free(ne),
        jn(ne, b1, b2),
        jn(ne, a1, a2),
    ensures
        jn(ne, subst1(b1, a1), subst1(b2, a2)),
{
    let (b3, b4) = jn_elim(ne, b1, b2);
    let (a3, a4) = jn_elim(ne, a1, a2);
    subst1_is_inst(b1, a1);
    subst1_is_inst(b2, a2);
    pstep_star_inst(ne, 0, a1, b1, b3);
    pstep_star_inst_arg(ne, 0, a1, a3, b3);
    pstep_star_trans(ne, inst(0, a1, b1), inst(0, a1, b3), inst(0, a3, b3));
    pstep_star_inst(ne, 0, a2, b2, b4);
    pstep_star_inst_arg(ne, 0, a2, a4, b4);
    pstep_star_trans(ne, inst(0, a2, b2), inst(0, a2, b4), inst(0, a4, b4));
    lveq_inst(0, a3, a4, b3, b4);
    jn_intro(ne, subst1(b1, a1), subst1(b2, a2), inst(0, a3, b3), inst(0, a4, b4));
}

/// A step `x -> y` of `ne` makes `x` and `y` joinable in `ne`.
proof fn jn_step(ne: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        pstep(ne, x, y),
    ensures
        jn(ne, x, y),
{
    pstep_star_one(ne, x, y);
    jn_of_star(ne, x, y);
}

/// `iota_extract` reads only the constructor table, which `nofold` keeps.
proof fn iota_same(env: EnvSpec, pidx: usize, inner2: ExprSpec, e2: ExprSpec)
    requires
        iota_extract(env, pidx, inner2, e2),
    ensures
        iota_extract(nofold(env), pidx, inner2, e2),
{
    assert(forall|id: u64| #[trigger] nofold(env).ctor_num_params(id) == env.ctor_num_params(id));
}

/// EVERY STEP OF THE REAL ENVIRONMENT IS A CONVERSION OF THE FOLD-FREE ONE.
pub proof fn pstep_ext_jn(env: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        cr_ext(env),
        pstep(env, x, y),
    ensures
        jn(nofold(env), x, y),
    decreases x,
{
    let ne = nofold(env);
    cr_into_tables(env, ne);
    if x == y {
        jn_refl(ne, x);
        return;
    }
    match x {
        ExprSpec::App(f, a) => {
            let beta = match *f {
                ExprSpec::Bind(BinderKind::Lam, _, body) => exists|body2: ExprSpec, a2: ExprSpec|
                    #![trigger subst1(body2, a2)]
                    pstep(env, *body, body2) && pstep(env, *a, a2) && y == subst1(body2, a2),
                _ => false,
            };
            if beta {
                if let ExprSpec::Bind(BinderKind::Lam, t, body) = *f {
                    let (body2, a2) = choose|body2: ExprSpec, a2: ExprSpec|
                        #![trigger subst1(body2, a2)]
                        pstep(env, *body, body2) && pstep(env, *a, a2) && y == subst1(body2, a2);
                    pstep_ext_jn(env, *body, body2);
                    pstep_ext_jn(env, *a, a2);
                    let m = subst1(*body, *a);
                    assert(pstep(ne, *body, *body));
                    assert(pstep(ne, *a, *a));
                    assert(pstep(ne, x, m));
                    jn_step(ne, x, m);
                    jn_subst1(ne, *body, body2, *a, a2);
                    jn_trans(ne, x, m, y);
                }
            } else if exists|f2: ExprSpec, a2: ExprSpec|
                pstep(env, *f, f2) && pstep(env, *a, a2) && y == ExprSpec::App(Box::new(f2), Box::new(a2)) {
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    pstep(env, *f, f2) && pstep(env, *a, a2) && y == ExprSpec::App(Box::new(f2), Box::new(a2));
                pstep_ext_jn(env, *f, f2);
                pstep_ext_jn(env, *a, a2);
                jn_app(ne, *f, f2, *a, a2);
            } else if pstep_rec(env, *f, *a, y) {
                let (f2, a2) = pstep_rec_destruct(env, *f, *a, y);
                pstep_ext_jn(env, *f, f2);
                pstep_ext_jn(env, *a, a2);
                jn_app(ne, *f, f2, *a, a2);
                let s = ExprSpec::App(Box::new(f2), Box::new(a2));
                rec_same(env, ne, s);
                assert(pstep(ne, f2, f2));
                assert(pstep(ne, a2, a2));
                pstep_rec_intro(ne, Box::new(f2), Box::new(a2), f2, a2, y);
                jn_step(ne, s, y);
                jn_trans(ne, x, s, y);
            } else if pstep_fold(env, *f, *a, y) {
                let (f2, a2) = pstep_fold_destruct(env, *f, *a, y);
                pstep_ext_jn(env, *f, f2);
                pstep_ext_jn(env, *a, a2);
                jn_app(ne, *f, f2, *a, a2);
                let s = ExprSpec::App(Box::new(f2), Box::new(a2));
                assert(nat_fold_ready(env.export, s));
                jn_of_defeq(ne, s, y);
                jn_trans(ne, x, s, y);
            } else {
                let (f2, a2) = pstep_quot_destruct(env, *f, *a, y);
                pstep_ext_jn(env, *f, f2);
                pstep_ext_jn(env, *a, a2);
                jn_app(ne, *f, f2, *a, a2);
                let s = ExprSpec::App(Box::new(f2), Box::new(a2));
                assert(pstep(ne, f2, f2));
                assert(pstep(ne, a2, a2));
                pstep_quot_intro(ne, Box::new(f2), Box::new(a2), f2, a2, y);
                jn_step(ne, s, y);
                jn_trans(ne, x, s, y);
            }
        },
        ExprSpec::Bind(bk, t, b) => {
            let (t2, b2) = choose|t2: ExprSpec, b2: ExprSpec|
                pstep(env, *t, t2) && pstep(env, *b, b2) && y == ExprSpec::Bind(bk, Box::new(t2), Box::new(b2));
            pstep_ext_jn(env, *t, t2);
            pstep_ext_jn(env, *b, b2);
            jn_bind(ne, bk, *t, t2, *b, b2);
        },
        ExprSpec::Let(t, v, b) => {
            if exists|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)] pstep(env, *b, b2) && pstep(env, *v, v2) && y == subst1(b2, v2) {
                let (b2, v2) = choose|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env, *b, b2) && pstep(env, *v, v2) && y == subst1(b2, v2);
                pstep_ext_jn(env, *b, b2);
                pstep_ext_jn(env, *v, v2);
                let m = subst1(*b, *v);
                assert(pstep(ne, *b, *b));
                assert(pstep(ne, *v, *v));
                assert(pstep(ne, x, m));
                jn_step(ne, x, m);
                jn_subst1(ne, *b, b2, *v, v2);
                jn_trans(ne, x, m, y);
            } else {
                let (t2, v2, b2) = choose|t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                    pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && y == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                pstep_ext_jn(env, *t, t2);
                pstep_ext_jn(env, *v, v2);
                pstep_ext_jn(env, *b, b2);
                jn_let(ne, *t, t2, *v, v2, *b, b2);
            }
        },
        ExprSpec::Proj(pidx, inner) => {
            if let ExprSpec::Proj(pidx2, inner2) = y {
                if pidx == pidx2 && pstep(env, *inner, *inner2) {
                    pstep_ext_jn(env, *inner, *inner2);
                    jn_proj(ne, pidx, *inner, *inner2);
                    return;
                }
            }
            let inner2 = choose|inner2: ExprSpec| (#[trigger] iota_reduct(inner2)) && pstep(env, *inner, inner2) && iota_extract(env, pidx, inner2, y);
            pstep_ext_jn(env, *inner, inner2);
            jn_proj(ne, pidx, *inner, inner2);
            let s = ExprSpec::Proj(pidx, Box::new(inner2));
            iota_same(env, pidx, inner2, y);
            assert(iota_reduct(inner2));
            assert(pstep(ne, inner2, inner2));
            assert(pstep(ne, s, y));
            jn_step(ne, s, y);
            jn_trans(ne, x, s, y);
        },
        _ => {
            assert(pstep(ne, x, y));
            jn_step(ne, x, y);
        },
    }
}

proof fn star_ext_chain(env: EnvSpec, ch: Seq<ExprSpec>, n: nat)
    requires
        cr_ext(env),
        ch.len() >= 1,
        n < ch.len(),
        pstep_chain_valid(env, ch),
    ensures
        jn(nofold(env), ch[0], ch[n as int]),
    decreases n,
{
    if n == 0 {
        jn_refl(nofold(env), ch[0]);
    } else {
        let m = (n - 1) as nat;
        star_ext_chain(env, ch, m);
        assert(pstep(env, ch[m as int], ch[m as int + 1]));
        pstep_ext_jn(env, ch[m as int], ch[n as int]);
        jn_trans(nofold(env), ch[0], ch[m as int], ch[n as int]);
    }
}

pub proof fn star_ext_jn(env: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        cr_ext(env),
        pstep_star(env, x, y),
    ensures
        jn(nofold(env), x, y),
{
    let ch = choose|c: Seq<ExprSpec>| c.len() >= 1 && c[0] == x && c[c.len() - 1] == y && pstep_chain_valid(env, c);
    star_ext_chain(env, ch, (ch.len() - 1) as nat);
}

/// Joinability in the real environment is joinability in the fold-free one.
pub proof fn defeq_ext_jn(env: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        cr_ext(env),
        defeq(env, x, y),
    ensures
        jn(nofold(env), x, y),
{
    let z = choose|z: ExprSpec| #[trigger] pstep_star(env, x, z) && #[trigger] pstep_star(env, y, z);
    star_ext_jn(env, x, z);
    star_ext_jn(env, y, z);
    jn_symm(nofold(env), y, z);
    jn_trans(nofold(env), x, z, y);
}

pub proof fn cr_into_ext(env: EnvSpec)
    requires
        cr_ext(env),
    ensures
        cr_into(env, nofold(env)),
{
    assert forall|x: ExprSpec, y: ExprSpec| #[trigger] defeq(env, x, y) implies jn(nofold(env), x, y) by {
        defeq_ext_jn(env, x, y);
    }
}

/// CHURCH-ROSSER FOR ETA-FREE CONVERSION IN A REAL ENVIRONMENT: under the
/// extension hypothesis, convertible terms have reducts (with folding off,
/// and so also with it on) equal up to universe-level equivalence.
pub proof fn ceq_jn_ext(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat)
    requires
        cr_ext(env),
        ceq(env, x, y, h),
    ensures
        jn(nofold(env), x, y),
        jn(env, x, y),
{
    cr_into_ext(env);
    ceq_jn_into(env, nofold(env), x, y, h);
    jn_up(env, nofold(env), x, y);
}

} // verus!
