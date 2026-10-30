//! NAT.ADD COMPUTES. The kernel folds `Nat.add x y` on numerals to a
//! literal by built-in arithmetic. Where the export declares `Nat.add` by
//! Lean's own definition (structural recursion through `Nat.brecOn`), that
//! fold is a conversion of the definition: both sides reduce, without
//! folding, to the same numeral `succ^(a+b) zero`. This is `h_nat_ext`
//! (docs/TYPED_TARGET.md, "The conditional theorem") for `Nat.add`, proven
//! from the definitions instead of assumed.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::beta_model::*;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::conv_frag::nofold;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A step without folding is a step.
pub proof fn pstep_nofold_up(env: EnvSpec, a: ExprSpec, b: ExprSpec)
    requires
        pstep(nofold(env), a, b),
    ensures
        pstep(env, a, b),
    decreases a,
{
    let ne = nofold(env);
    if a == b {
        return;
    }
    assert(forall|id: u64| #[trigger] ne.rec_data(id) == env.rec_data(id));
    assert(forall|id: u64| #[trigger] ne.ctor_num_params(id) == env.ctor_num_params(id));
    match a {
        ExprSpec::App(f, x) => {
            let beta = match *f {
                ExprSpec::Bind(BinderKind::Lam, _, body) => exists|body2: ExprSpec, a2: ExprSpec|
                    #![trigger subst1(body2, a2)]
                    pstep(ne, *body, body2) && pstep(ne, *x, a2) && b == subst1(body2, a2),
                _ => false,
            };
            let cong = exists|f2: ExprSpec, a2: ExprSpec|
                pstep(ne, *f, f2) && pstep(ne, *x, a2) && b == ExprSpec::App(Box::new(f2), Box::new(a2));
            let rec = exists|f2: ExprSpec, a2: ExprSpec|
                (#[trigger] rec_reduct(f2, a2)) && pstep(ne, *f, f2) && pstep(ne, *x, a2)
                    && rec_ready(ne, ExprSpec::App(Box::new(f2), Box::new(a2))) && b == rec_result(ne, ExprSpec::App(Box::new(f2), Box::new(a2)));
            if beta {
                if let ExprSpec::Bind(BinderKind::Lam, _, body) = *f {
                    let (body2, a2) = choose|body2: ExprSpec, a2: ExprSpec|
                        #![trigger subst1(body2, a2)]
                        pstep(ne, *body, body2) && pstep(ne, *x, a2) && b == subst1(body2, a2);
                    pstep_nofold_up(env, *body, body2);
                    pstep_nofold_up(env, *x, a2);
                }
            } else if cong {
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    pstep(ne, *f, f2) && pstep(ne, *x, a2) && b == ExprSpec::App(Box::new(f2), Box::new(a2));
                pstep_nofold_up(env, *f, f2);
                pstep_nofold_up(env, *x, a2);
            } else if rec {
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    (#[trigger] rec_reduct(f2, a2)) && pstep(ne, *f, f2) && pstep(ne, *x, a2)
                        && rec_ready(ne, ExprSpec::App(Box::new(f2), Box::new(a2))) && b == rec_result(ne, ExprSpec::App(Box::new(f2), Box::new(a2)));
                pstep_nofold_up(env, *f, f2);
                pstep_nofold_up(env, *x, a2);
                assert(rec_ready(env, ExprSpec::App(Box::new(f2), Box::new(a2))));
                assert(b == rec_result(env, ExprSpec::App(Box::new(f2), Box::new(a2))));
                assert(rec_reduct(f2, a2));
            } else if exists|f2: ExprSpec, a2: ExprSpec|
                (#[trigger] fold_reduct(f2, a2)) && pstep(ne, *f, f2) && pstep(ne, *x, a2)
                    && fold_on(ne, ExprSpec::App(Box::new(f2), Box::new(a2))) && nat_fold_ready(ne.export, ExprSpec::App(Box::new(f2), Box::new(a2)))
                    && b == nat_fold_result(ne.export, ExprSpec::App(Box::new(f2), Box::new(a2))) {
                // a fold of an operation that is no definition: it folds anywhere
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    (#[trigger] fold_reduct(f2, a2)) && pstep(ne, *f, f2) && pstep(ne, *x, a2)
                        && fold_on(ne, ExprSpec::App(Box::new(f2), Box::new(a2))) && nat_fold_ready(ne.export, ExprSpec::App(Box::new(f2), Box::new(a2)))
                        && b == nat_fold_result(ne.export, ExprSpec::App(Box::new(f2), Box::new(a2)));
                pstep_nofold_up(env, *f, f2);
                pstep_nofold_up(env, *x, a2);
                assert(fold_on(env, ExprSpec::App(Box::new(f2), Box::new(a2))));
                assert(fold_reduct(f2, a2));
            } else {
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    (#[trigger] quot_reduct(f2, a2)) && pstep(ne, *f, f2) && pstep(ne, *x, a2)
                        && crate::tc_model::quot_ready(ne.export, ExprSpec::App(Box::new(f2), Box::new(a2)))
                        && b == crate::tc_model::quot_result(ne.export, ExprSpec::App(Box::new(f2), Box::new(a2)));
                pstep_nofold_up(env, *f, f2);
                pstep_nofold_up(env, *x, a2);
            }
        },
        ExprSpec::Bind(bk, t, body) => {
            let (t2, b2) = choose|t2: ExprSpec, b2: ExprSpec|
                pstep(ne, *t, t2) && pstep(ne, *body, b2) && b == ExprSpec::Bind(bk, Box::new(t2), Box::new(b2));
            pstep_nofold_up(env, *t, t2);
            pstep_nofold_up(env, *body, b2);
        },
        ExprSpec::Let(t, v, body) => {
            if exists|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                pstep(ne, *body, b2) && pstep(ne, *v, v2) && b == subst1(b2, v2) {
                let (b2, v2) = choose|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(ne, *body, b2) && pstep(ne, *v, v2) && b == subst1(b2, v2);
                pstep_nofold_up(env, *body, b2);
                pstep_nofold_up(env, *v, v2);
            } else {
                let (t2, v2, b2) = choose|t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                    pstep(ne, *t, t2) && pstep(ne, *v, v2) && pstep(ne, *body, b2)
                        && b == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                pstep_nofold_up(env, *t, t2);
                pstep_nofold_up(env, *v, v2);
                pstep_nofold_up(env, *body, b2);
            }
        },
        ExprSpec::Proj(i, inner) => {
            if let ExprSpec::Proj(i2, inner2) = b {
                if i == i2 && pstep(ne, *inner, *inner2) {
                    pstep_nofold_up(env, *inner, *inner2);
                    return;
                }
            }
            let inner2 = choose|inner2: ExprSpec| (#[trigger] iota_reduct(inner2)) && pstep(ne, *inner, inner2)
                && iota_extract(ne, i, inner2, b);
            pstep_nofold_up(env, *inner, inner2);
            assert(iota_extract(env, i, inner2, b));
        },
        _ => {},
    }
}

/// A DEFINITION APPLIED TO ITS ARGUMENTS unfolds and beta-reduces at once:
/// to its value's body (at the instance's levels) with the closed
/// arguments substituted.
pub proof fn delta_beta(ne: EnvSpec, id: u64, ls: Seq<crate::level_model::LevelSpec>, args: Seq<ExprSpec>, body: ExprSpec)
    requires
        ne.contains_key(id),
        ne[id].0.len() == ls.len(),
        spine_bind(crate::expr_model::subst_expr_levels(ne[id].1, ne[id].0, ls), args.len()) == Some(body),
        crate::expr_model::nlbv(body) <= args.len(),
        forall|i: int| 0 <= i < args.len() ==> crate::expr_model::nlbv(#[trigger] args[i]) <= 0,
    ensures
        pstep_star(ne, spine_app(ExprSpec::Const(id, ls), args), crate::expr_model::subst_full(body, args, 0)),
{
    let v = crate::expr_model::subst_expr_levels(ne[id].1, ne[id].0, ls);
    assert(pstep(ne, ExprSpec::Const(id, ls), v));
    pstep_star_one(ne, ExprSpec::Const(id, ls), v);
    pstep_spine_app_star(ne, ExprSpec::Const(id, ls), v, args);
    pstep_star_spine_reduce(ne, v, args);
    spine_reduce_eq_subst_full(v, args, body, 0);
    pstep_star_trans(ne, spine_app(ExprSpec::Const(id, ls), args), spine_app(v, args), crate::expr_model::subst_full(body, args, 0));
}

pub open spec fn mk_app(f: ExprSpec, a: ExprSpec) -> ExprSpec {
    ExprSpec::App(Box::new(f), Box::new(a))
}

pub open spec fn fun_of(e: ExprSpec) -> ExprSpec {
    match e { ExprSpec::App(f, _) => *f, _ => ExprSpec::Closed }
}

pub open spec fn arg_of(e: ExprSpec) -> ExprSpec {
    match e { ExprSpec::App(_, a) => *a, _ => ExprSpec::Closed }
}

/// `Nat.add`'s body under its two binders: `Nat.brecOn M y Nat.add._f x`
/// (`x` is `#1`, `y` is `#0`).
pub open spec fn add_body(brec: ExprSpec, m: ExprSpec, f: ExprSpec) -> ExprSpec {
    mk_app(mk_app(mk_app(mk_app(brec, m), ExprSpec::Var(0)), f), ExprSpec::Var(1))
}

/// `Nat.add`'s value is Lean's: its body is `add_body` of its own parts,
/// the head and the step function constants, the motive closed.
pub open spec fn std_nat_add(v: ExprSpec) -> bool {
    spine_bind(v, 2) is Some && {
        let b = spine_bind(v, 2)->Some_0;
        let (brec, m, f) = (fun_of(fun_of(fun_of(fun_of(b)))), arg_of(fun_of(fun_of(fun_of(b)))), arg_of(fun_of(b)));
        &&& b == add_body(brec, m, f)
        &&& brec is Const && f is Const
        &&& crate::expr_model::nlbv(m) == 0
    }
}

/// `Nat.add x y` unfolds to `Nat.brecOn M y Nat.add._f x`.
#[verifier::spinoff_prover]
pub proof fn add_unfold(ne: EnvSpec, add: u64, x: ExprSpec, y: ExprSpec)
    requires
        ne.contains_key(add),
        ne[add].0.len() == 0,
        std_nat_add(ne[add].1),
        crate::expr_model::nlbv(x) == 0,
        crate::expr_model::nlbv(y) == 0,
    ensures ({
        let b = spine_bind(ne[add].1, 2)->Some_0;
        let (brec, m, f) = (fun_of(fun_of(fun_of(fun_of(b)))), arg_of(fun_of(fun_of(fun_of(b)))), arg_of(fun_of(b)));
        pstep_star(ne, mk_app(mk_app(ExprSpec::Const(add, Seq::empty()), x), y), mk_app(mk_app(mk_app(mk_app(brec, m), y), f), x))
    }),
{
    let v = ne[add].1;
    let b = spine_bind(v, 2)->Some_0;
    let (brec, m, f) = (fun_of(fun_of(fun_of(fun_of(b)))), arg_of(fun_of(fun_of(fun_of(b)))), arg_of(fun_of(b)));
    assert(ne[add].0 =~= Seq::<u64>::empty());
    crate::expr_model::subst_expr_levels_empty(v);
    assert(crate::expr_model::subst_expr_levels(v, ne[add].0, Seq::empty()) == v);
    let args = seq![x, y];
    assert(spine_app(ExprSpec::Const(add, Seq::empty()), args) == mk_app(mk_app(ExprSpec::Const(add, Seq::empty()), x), y)) by {
        reveal_with_fuel(spine_app, 3);
    }
    assert(crate::expr_model::nlbv(b) <= 2) by {
        reveal_with_fuel(crate::expr_model::nlbv, 6);
    }
    delta_beta(ne, add, Seq::empty(), args, b);
    crate::expr_model::subst_full_noop(m, args, 0);
    crate::expr_model::subst_full_noop(brec, args, 0);
    crate::expr_model::subst_full_noop(f, args, 0);
    assert(crate::expr_model::subst_full(b, args, 0) == mk_app(mk_app(mk_app(mk_app(brec, m), y), f), x)) by {
        reveal_with_fuel(crate::expr_model::subst_full, 6);
    }
}

/// Stripping lambdas commutes with substituting levels.
pub proof fn levels_spine_bind(v: ExprSpec, n: nat, ks: Seq<u64>, vs: Seq<crate::level_model::LevelSpec>)
    requires
        spine_bind(v, n) is Some,
    ensures
        spine_bind(crate::expr_model::subst_expr_levels(v, ks, vs), n)
            == Some(crate::expr_model::subst_expr_levels(spine_bind(v, n)->Some_0, ks, vs)),
    decreases n,
{
    if n > 0 {
        if let ExprSpec::Bind(BinderKind::Lam, _, b) = v {
            levels_spine_bind(*b, (n - 1) as nat, ks, vs);
        }
    }
}

/// `Nat.brecOn`'s body under its three binders (motive `#2`, major `#1`,
/// step `#0`): the first component of `Nat.brecOn.go motive major step`.
pub open spec fn brec_on_body(go: ExprSpec) -> ExprSpec {
    ExprSpec::Proj(0, Box::new(mk_app(mk_app(mk_app(go, ExprSpec::Var(2)), ExprSpec::Var(1)), ExprSpec::Var(0))))
}

pub open spec fn brec_on_go_const(b: ExprSpec) -> ExprSpec {
    match b { ExprSpec::Proj(_, x) => fun_of(fun_of(fun_of(*x))), _ => ExprSpec::Closed }
}

pub open spec fn std_brec_on(v: ExprSpec) -> bool {
    spine_bind(v, 3) is Some && {
        let b = spine_bind(v, 3)->Some_0;
        b == brec_on_body(brec_on_go_const(b)) && brec_on_go_const(b) is Const
    }
}

/// `Nat.brecOn.{u} m t f` unfolds to `(Nat.brecOn.go.{u} m t f).0`.
#[verifier::spinoff_prover]
pub proof fn brec_on_unfold(ne: EnvSpec, id: u64, ls: Seq<crate::level_model::LevelSpec>, m: ExprSpec, t: ExprSpec, f: ExprSpec)
    requires
        ne.contains_key(id),
        ne[id].0.len() == ls.len(),
        std_brec_on(ne[id].1),
        crate::expr_model::nlbv(m) == 0,
        crate::expr_model::nlbv(t) == 0,
        crate::expr_model::nlbv(f) == 0,
    ensures ({
        let g = brec_on_go_const(spine_bind(ne[id].1, 3)->Some_0);
        let g2 = ExprSpec::Const(g->Const_0, crate::level_model::subst_levels_spec(g->Const_1, ne[id].0, ls));
        pstep_star(ne, mk_app(mk_app(mk_app(ExprSpec::Const(id, ls), m), t), f), ExprSpec::Proj(0, Box::new(mk_app(mk_app(mk_app(g2, m), t), f))))
    }),
{
    let v = ne[id].1;
    let b = spine_bind(v, 3)->Some_0;
    let g = brec_on_go_const(b);
    let (ks, vs) = (ne[id].0, ls);
    let g2 = ExprSpec::Const(g->Const_0, crate::level_model::subst_levels_spec(g->Const_1, ks, vs));
    levels_spine_bind(v, 3, ks, vs);
    let b2 = crate::expr_model::subst_expr_levels(b, ks, vs);
    assert(b2 == brec_on_body(g2)) by {
        reveal_with_fuel(crate::expr_model::subst_expr_levels, 6);
    }
    let args = seq![m, t, f];
    assert(spine_app(ExprSpec::Const(id, ls), args) == mk_app(mk_app(mk_app(ExprSpec::Const(id, ls), m), t), f)) by {
        reveal_with_fuel(spine_app, 4);
    }
    assert(crate::expr_model::nlbv(b2) <= 3) by {
        reveal_with_fuel(crate::expr_model::nlbv, 6);
    }
    delta_beta(ne, id, ls, args, b2);
    assert(crate::expr_model::subst_full(b2, args, 0) == ExprSpec::Proj(0, Box::new(mk_app(mk_app(mk_app(g2, m), t), f)))) by {
        reveal_with_fuel(crate::expr_model::subst_full, 6);
    }
}

pub open spec fn mk_lam(t: ExprSpec, b: ExprSpec) -> ExprSpec {
    ExprSpec::Bind(BinderKind::Lam, Box::new(t), Box::new(b))
}

pub open spec fn mk_app4(h: ExprSpec, a: ExprSpec, b: ExprSpec, c: ExprSpec, d: ExprSpec) -> ExprSpec {
    mk_app(mk_app(mk_app(mk_app(h, a), b), c), d)
}

/// A four-argument application `h a b c d`, read off: its head and its
/// arguments in order.
pub open spec fn head_of4(e: ExprSpec) -> ExprSpec { fun_of(fun_of(fun_of(fun_of(e)))) }
pub open spec fn arg1_of4(e: ExprSpec) -> ExprSpec { arg_of(fun_of(fun_of(fun_of(e)))) }
pub open spec fn arg2_of4(e: ExprSpec) -> ExprSpec { arg_of(fun_of(fun_of(e))) }
pub open spec fn arg3_of4(e: ExprSpec) -> ExprSpec { arg_of(fun_of(e)) }
pub open spec fn arg4_of4(e: ExprSpec) -> ExprSpec { arg_of(e) }

pub open spec fn is_app4(e: ExprSpec) -> bool {
    e == mk_app4(head_of4(e), arg1_of4(e), arg2_of4(e), arg3_of4(e), arg4_of4(e))
}

pub open spec fn lam_type(e: ExprSpec) -> ExprSpec {
    match e { ExprSpec::Bind(_, t, _) => *t, _ => ExprSpec::Closed }
}

pub open spec fn lam_body(e: ExprSpec) -> ExprSpec {
    match e { ExprSpec::Bind(_, _, b) => *b, _ => ExprSpec::Closed }
}

/// The base case of `Nat.brecOn.go` at the step function `f`:
/// `PProd.mk _ _ (f Nat.zero _) _`.
pub open spec fn base_shape(x: ExprSpec, f: ExprSpec, zid: u64) -> bool {
    &&& is_app4(x) && head_of4(x) is Const
    &&& arg3_of4(x) == mk_app(mk_app(f, const_expr_no_levels(zid)), arg_of(arg3_of4(x)))
}

/// The step case at `f`: `λ n ih. PProd.mk _ _ (f (Nat.succ n) ih) ih`.
pub open spec fn step_shape(x: ExprSpec, f: ExprSpec, sid: u64) -> bool {
    let b = lam_body(lam_body(x));
    &&& x == mk_lam(lam_type(x), mk_lam(lam_type(lam_body(x)), b))
    &&& is_app4(b) && head_of4(b) is Const
    &&& arg3_of4(b) == mk_app(mk_app(f, mk_app(const_expr_no_levels(sid), ExprSpec::Var(1))), ExprSpec::Var(0))
    &&& arg4_of4(b) == ExprSpec::Var(0)
}

/// `Nat.brecOn.go`'s value is Lean's: under its three binders (motive `#2`,
/// major `#1`, step function `#0`), `Nat.rec P BASE STEP #1` with the base
/// and step cases above at `#0` (the inner step function is `#2` under the
/// step case's two binders).
pub open spec fn std_brec_on_go(v: ExprSpec, zid: u64, sid: u64) -> bool {
    spine_bind(v, 3) is Some && {
        let b = spine_bind(v, 3)->Some_0;
        &&& is_app4(b) && head_of4(b) is Const && arg4_of4(b) == ExprSpec::Var(1)
        &&& base_shape(arg2_of4(b), ExprSpec::Var(0), zid)
        &&& step_shape(arg3_of4(b), ExprSpec::Var(2), sid)
    }
}

/// A constant without levels keeps none under level substitution.
pub proof fn levels_const_nil(id: u64, ks: Seq<u64>, vs: Seq<crate::level_model::LevelSpec>)
    ensures
        crate::expr_model::subst_expr_levels(const_expr_no_levels(id), ks, vs) == const_expr_no_levels(id),
{
    assert(crate::level_model::subst_levels_spec(Seq::<crate::level_model::LevelSpec>::empty(), ks, vs)
        =~= Seq::<crate::level_model::LevelSpec>::empty());
}

pub open spec fn inst_levels(e: ExprSpec, ks: Seq<u64>, vs: Seq<crate::level_model::LevelSpec>) -> ExprSpec {
    crate::expr_model::subst_expr_levels(e, ks, vs)
}

pub open spec fn inst_args(e: ExprSpec, args: Seq<ExprSpec>, k: nat) -> ExprSpec {
    crate::expr_model::subst_full(e, args, k)
}

pub proof fn inst_levels_app(f: ExprSpec, a: ExprSpec, ks: Seq<u64>, vs: Seq<crate::level_model::LevelSpec>)
    ensures inst_levels(mk_app(f, a), ks, vs) == mk_app(inst_levels(f, ks, vs), inst_levels(a, ks, vs)),
{}

pub proof fn inst_levels_lam(t: ExprSpec, b: ExprSpec, ks: Seq<u64>, vs: Seq<crate::level_model::LevelSpec>)
    ensures inst_levels(mk_lam(t, b), ks, vs) == mk_lam(inst_levels(t, ks, vs), inst_levels(b, ks, vs)),
{}

pub proof fn inst_args_app(f: ExprSpec, a: ExprSpec, args: Seq<ExprSpec>, k: nat)
    ensures inst_args(mk_app(f, a), args, k) == mk_app(inst_args(f, args, k), inst_args(a, args, k)),
{}

pub proof fn inst_args_lam(t: ExprSpec, b: ExprSpec, args: Seq<ExprSpec>, k: nat)
    ensures inst_args(mk_lam(t, b), args, k) == mk_lam(inst_args(t, args, k), inst_args(b, args, k + 1)),
{}

pub proof fn inst_levels_app4(h: ExprSpec, a: ExprSpec, b: ExprSpec, c: ExprSpec, d: ExprSpec, ks: Seq<u64>, vs: Seq<crate::level_model::LevelSpec>)
    ensures inst_levels(mk_app4(h, a, b, c, d), ks, vs) == mk_app4(inst_levels(h, ks, vs), inst_levels(a, ks, vs), inst_levels(b, ks, vs), inst_levels(c, ks, vs), inst_levels(d, ks, vs)),
{
    inst_levels_app(mk_app(mk_app(mk_app(h, a), b), c), d, ks, vs);
    inst_levels_app(mk_app(mk_app(h, a), b), c, ks, vs);
    inst_levels_app(mk_app(h, a), b, ks, vs);
    inst_levels_app(h, a, ks, vs);
}

pub proof fn inst_args_app4(h: ExprSpec, a: ExprSpec, b: ExprSpec, c: ExprSpec, d: ExprSpec, args: Seq<ExprSpec>, k: nat)
    ensures inst_args(mk_app4(h, a, b, c, d), args, k) == mk_app4(inst_args(h, args, k), inst_args(a, args, k), inst_args(b, args, k), inst_args(c, args, k), inst_args(d, args, k)),
{
    inst_args_app(mk_app(mk_app(mk_app(h, a), b), c), d, args, k);
    inst_args_app(mk_app(mk_app(h, a), b), c, args, k);
    inst_args_app(mk_app(h, a), b, args, k);
    inst_args_app(h, a, args, k);
}

/// A four-argument spine is its parts.
pub proof fn app4_parts(h: ExprSpec, a: ExprSpec, b: ExprSpec, c: ExprSpec, d: ExprSpec)
    ensures ({
        let e = mk_app4(h, a, b, c, d);
        &&& is_app4(e) && head_of4(e) == h && arg1_of4(e) == a && arg2_of4(e) == b && arg3_of4(e) == c && arg4_of4(e) == d
    }),
{}

/// The base case's shape survives level substitution, then substituting the
/// step function `f` for `#0` (closed arguments, `f` among them).
pub proof fn base_case_inst(x: ExprSpec, ks: Seq<u64>, vs: Seq<crate::level_model::LevelSpec>, args: Seq<ExprSpec>, f: ExprSpec, zid: u64)
    requires
        base_shape(x, ExprSpec::Var(0), zid),
        args.len() == 3, args[2] == f, crate::expr_model::nlbv(f) == 0,
    ensures
        base_shape(inst_args(inst_levels(x, ks, vs), args, 0), f, zid),
        head_of4(inst_args(inst_levels(x, ks, vs), args, 0))->Const_0 == head_of4(x)->Const_0,
{
    let zc = const_expr_no_levels(zid);
    let fz = arg3_of4(x);
    let u1 = arg_of(fz);
    inst_levels_app4(head_of4(x), arg1_of4(x), arg2_of4(x), fz, arg4_of4(x), ks, vs);
    inst_levels_app(mk_app(ExprSpec::Var(0), zc), u1, ks, vs);
    inst_levels_app(ExprSpec::Var(0), zc, ks, vs);
    levels_const_nil(zid, ks, vs);
    let x2 = inst_levels(x, ks, vs);
    inst_args_app4(inst_levels(head_of4(x), ks, vs), inst_levels(arg1_of4(x), ks, vs), inst_levels(arg2_of4(x), ks, vs), inst_levels(fz, ks, vs), inst_levels(arg4_of4(x), ks, vs), args, 0);
    inst_args_app(mk_app(ExprSpec::Var(0), zc), inst_levels(u1, ks, vs), args, 0);
    inst_args_app(ExprSpec::Var(0), zc, args, 0);
    crate::expr_model::subst_full_noop(zc, args, 0);
    app4_parts(inst_args(inst_levels(head_of4(x), ks, vs), args, 0), inst_args(inst_levels(arg1_of4(x), ks, vs), args, 0), inst_args(inst_levels(arg2_of4(x), ks, vs), args, 0),
        mk_app(mk_app(f, zc), inst_args(inst_levels(u1, ks, vs), args, 0)), inst_args(inst_levels(arg4_of4(x), ks, vs), args, 0));
}

/// The step case's shape likewise, the step function being `#2` under its
/// two binders.
pub proof fn step_case_inst(x: ExprSpec, ks: Seq<u64>, vs: Seq<crate::level_model::LevelSpec>, args: Seq<ExprSpec>, f: ExprSpec, sid: u64)
    requires
        step_shape(x, ExprSpec::Var(2), sid),
        args.len() == 3, args[2] == f, crate::expr_model::nlbv(f) == 0,
    ensures
        step_shape(inst_args(inst_levels(x, ks, vs), args, 0), f, sid),
        head_of4(lam_body(lam_body(inst_args(inst_levels(x, ks, vs), args, 0))))->Const_0 == head_of4(lam_body(lam_body(x)))->Const_0,
{
    let sc = const_expr_no_levels(sid);
    let (t1, t2, b) = (lam_type(x), lam_type(lam_body(x)), lam_body(lam_body(x)));
    let fs = mk_app(mk_app(ExprSpec::Var(2), mk_app(sc, ExprSpec::Var(1))), ExprSpec::Var(0));
    inst_levels_lam(t1, mk_lam(t2, b), ks, vs);
    inst_levels_lam(t2, b, ks, vs);
    inst_levels_app4(head_of4(b), arg1_of4(b), arg2_of4(b), fs, ExprSpec::Var(0), ks, vs);
    inst_levels_app(mk_app(ExprSpec::Var(2), mk_app(sc, ExprSpec::Var(1))), ExprSpec::Var(0), ks, vs);
    inst_levels_app(ExprSpec::Var(2), mk_app(sc, ExprSpec::Var(1)), ks, vs);
    inst_levels_app(sc, ExprSpec::Var(1), ks, vs);
    levels_const_nil(sid, ks, vs);
    let b2 = inst_levels(b, ks, vs);
    inst_args_lam(inst_levels(t1, ks, vs), mk_lam(inst_levels(t2, ks, vs), b2), args, 0);
    inst_args_lam(inst_levels(t2, ks, vs), b2, args, 1);
    inst_args_app4(inst_levels(head_of4(b), ks, vs), inst_levels(arg1_of4(b), ks, vs), inst_levels(arg2_of4(b), ks, vs), fs, ExprSpec::Var(0), args, 2);
    inst_args_app(mk_app(ExprSpec::Var(2), mk_app(sc, ExprSpec::Var(1))), ExprSpec::Var(0), args, 2);
    inst_args_app(ExprSpec::Var(2), mk_app(sc, ExprSpec::Var(1)), args, 2);
    inst_args_app(sc, ExprSpec::Var(1), args, 2);
    crate::expr_model::subst_full_noop(sc, args, 2);
    let b3 = mk_app4(inst_args(inst_levels(head_of4(b), ks, vs), args, 2), inst_args(inst_levels(arg1_of4(b), ks, vs), args, 2), inst_args(inst_levels(arg2_of4(b), ks, vs), args, 2),
        mk_app(mk_app(f, mk_app(sc, ExprSpec::Var(1))), ExprSpec::Var(0)), ExprSpec::Var(0));
    app4_parts(inst_args(inst_levels(head_of4(b), ks, vs), args, 2), inst_args(inst_levels(arg1_of4(b), ks, vs), args, 2), inst_args(inst_levels(arg2_of4(b), ks, vs), args, 2),
        mk_app(mk_app(f, mk_app(sc, ExprSpec::Var(1))), ExprSpec::Var(0)), ExprSpec::Var(0));
}

/// `Nat.brecOn.go.{u} m t f` unfolds to `Nat.rec P BASE STEP t`, with the
/// base and step cases at `f`, all closed.
#[verifier::spinoff_prover]
pub proof fn brec_on_go_unfold(ne: EnvSpec, id: u64, ls: Seq<crate::level_model::LevelSpec>, m: ExprSpec, t: ExprSpec, f: ExprSpec)
    requires
        ne.contains_key(id),
        ne[id].0.len() == ls.len(),
        std_brec_on_go(ne[id].1, crate::expr_arena_bridge::nat_zero_id(ne.export), crate::expr_arena_bridge::nat_succ_id(ne.export)),
        crate::expr_model::nlbv(ne[id].1) == 0,
        crate::expr_model::nlbv(m) == 0,
        crate::expr_model::nlbv(t) == 0,
        crate::expr_model::nlbv(f) == 0,
    ensures ({
        let r = inst_args(inst_levels(spine_bind(ne[id].1, 3)->Some_0, ne[id].0, ls), seq![m, t, f], 0);
        let h = head_of4(spine_bind(ne[id].1, 3)->Some_0);
        &&& pstep_star(ne, mk_app(mk_app(mk_app(ExprSpec::Const(id, ls), m), t), f), r)
        &&& is_app4(r) && arg4_of4(r) == t
        &&& head_of4(r) == ExprSpec::Const(h->Const_0, crate::level_model::subst_levels_spec(h->Const_1, ne[id].0, ls))
        &&& base_shape(arg2_of4(r), f, crate::expr_arena_bridge::nat_zero_id(ne.export))
        &&& step_shape(arg3_of4(r), f, crate::expr_arena_bridge::nat_succ_id(ne.export))
        &&& head_of4(arg2_of4(r))->Const_0 == head_of4(arg2_of4(spine_bind(ne[id].1, 3)->Some_0))->Const_0
        &&& head_of4(lam_body(lam_body(arg3_of4(r))))->Const_0 == head_of4(lam_body(lam_body(arg3_of4(spine_bind(ne[id].1, 3)->Some_0))))->Const_0
        &&& crate::expr_model::nlbv(arg1_of4(r)) == 0 && crate::expr_model::nlbv(arg2_of4(r)) == 0 && crate::expr_model::nlbv(arg3_of4(r)) == 0
    }),
{
    let (zid, sid) = (crate::expr_arena_bridge::nat_zero_id(ne.export), crate::expr_arena_bridge::nat_succ_id(ne.export));
    let v = ne[id].1;
    let b = spine_bind(v, 3)->Some_0;
    let (ks, vs) = (ne[id].0, ls);
    let args = seq![m, t, f];
    assert(b == mk_app4(head_of4(b), arg1_of4(b), arg2_of4(b), arg3_of4(b), ExprSpec::Var(1)));
    levels_spine_bind(v, 3, ks, vs);
    crate::beta_model::spine_bind_nlbv(v, 3, b, 0);
    let b2 = inst_levels(b, ks, vs);
    crate::ti_level::ls_nlbv(b, ks, vs);
    inst_levels_app4(head_of4(b), arg1_of4(b), arg2_of4(b), arg3_of4(b), ExprSpec::Var(1), ks, vs);
    let r = inst_args(b2, args, 0);
    inst_args_app4(inst_levels(head_of4(b), ks, vs), inst_levels(arg1_of4(b), ks, vs), inst_levels(arg2_of4(b), ks, vs), inst_levels(arg3_of4(b), ks, vs), ExprSpec::Var(1), args, 0);
    crate::expr_model::subst_full_noop(inst_levels(head_of4(b), ks, vs), args, 0);
    let (p2, ba2, st2) = (inst_args(inst_levels(arg1_of4(b), ks, vs), args, 0), inst_args(inst_levels(arg2_of4(b), ks, vs), args, 0), inst_args(inst_levels(arg3_of4(b), ks, vs), args, 0));
    app4_parts(inst_levels(head_of4(b), ks, vs), p2, ba2, st2, t);
    base_case_inst(arg2_of4(b), ks, vs, args, f, zid);
    step_case_inst(arg3_of4(b), ks, vs, args, f, sid);
    assert(spine_app(ExprSpec::Const(id, ls), args) == mk_app(mk_app(mk_app(ExprSpec::Const(id, ls), m), t), f)) by {
        reveal_with_fuel(spine_app, 4);
    }
    delta_beta(ne, id, ls, args, b2);
    assert(crate::expr_model::nlbv(arg1_of4(b)) <= 3 && crate::expr_model::nlbv(arg2_of4(b)) <= 3 && crate::expr_model::nlbv(arg3_of4(b)) <= 3) by {
        reveal_with_fuel(crate::expr_model::nlbv, 5);
    }
    crate::ti_level::ls_nlbv(arg1_of4(b), ks, vs);
    crate::ti_level::ls_nlbv(arg2_of4(b), ks, vs);
    crate::ti_level::ls_nlbv(arg3_of4(b), ks, vs);
    crate::beta_model::subst_full_nlbv_bound_n(inst_levels(arg1_of4(b), ks, vs), args, 0);
    crate::beta_model::subst_full_nlbv_bound_n(inst_levels(arg2_of4(b), ks, vs), args, 0);
    crate::beta_model::subst_full_nlbv_bound_n(inst_levels(arg3_of4(b), ks, vs), args, 0);
}

/// `Nat.rec`'s data is Lean's: no parameters, one motive, two minor
/// premises, the major premise fourth, one universe parameter; the rules
/// `zero: λ m z s. z` and `succ: λ m z s n. s n (Nat.rec m z s n)` (binder
/// types as exported), each fit to fire.
pub open spec fn std_nat_rec(ne: EnvSpec, rid: u64) -> bool {
    let (zid, sid) = (crate::expr_arena_bridge::nat_zero_id(ne.export), crate::expr_arena_bridge::nat_succ_id(ne.export));
    ne.rec_data(rid) is Some && {
        let rd = ne.rec_data(rid)->Some_0;
        let r0 = rd.rules[0];
        let r1 = rd.rules[1];
        &&& rd.num_params == 0 && rd.num_motives == 1 && rd.num_minors == 2 && rd.major_idx == 3
        &&& rd.uparams.len() == 1
        &&& rd.rules.len() == 2 && zid != sid
        &&& r0.ctor_id == zid && r0.nfields == 0 && spine_bind(r0.rhs, 3) == Some(ExprSpec::Var(1))
        &&& r1.ctor_id == sid && r1.nfields == 1
        &&& spine_bind(r1.rhs, 4) == Some(mk_app(mk_app(ExprSpec::Var(1), ExprSpec::Var(0)),
            mk_app4(ExprSpec::Const(rid, seq![crate::level_model::LevelSpec::Param(rd.uparams[0])]),
                ExprSpec::Var(3), ExprSpec::Var(2), ExprSpec::Var(1), ExprSpec::Var(0))))
        &&& rule_rhs_ok(ne, r0) && rule_rhs_ok(ne, r1)
    }
}

pub proof fn spine_app4_parts(h: ExprSpec, a: ExprSpec, b: ExprSpec, c: ExprSpec, d: ExprSpec)
    requires
        h is Const,
    ensures
        spine_head(mk_app4(h, a, b, c, d)) == h,
        spine_args(mk_app4(h, a, b, c, d)) == seq![a, b, c, d],
        spine_app(h, seq![a, b, c, d]) == mk_app4(h, a, b, c, d),
{
    reveal_with_fuel(spine_head, 5);
    reveal_with_fuel(spine_args, 5);
    reveal_with_fuel(spine_app, 5);
    assert(spine_args(mk_app4(h, a, b, c, d)) =~= seq![a, b, c, d]);
}

/// Iota at zero: `Nat.rec p b s Nat.zero` reduces to `b`.
#[verifier::spinoff_prover]
pub proof fn nat_rec_zero(ne: EnvSpec, rid: u64, lv: Seq<crate::level_model::LevelSpec>, p: ExprSpec, b: ExprSpec, s: ExprSpec)
    requires
        std_nat_rec(ne, rid),
        lv.len() == 1,
        crate::expr_model::nlbv(p) == 0 && crate::expr_model::nlbv(b) == 0 && crate::expr_model::nlbv(s) == 0,
    ensures
        pstep_star(ne, mk_app4(ExprSpec::Const(rid, lv), p, b, s, const_expr_no_levels(crate::expr_arena_bridge::nat_zero_id(ne.export))), b),
{
    let zc = const_expr_no_levels(crate::expr_arena_bridge::nat_zero_id(ne.export));
    let rd = ne.rec_data(rid)->Some_0;
    let rule = rd.rules[0];
    let c = ExprSpec::Const(rid, lv);
    let e = mk_app4(c, p, b, s, zc);
    spine_app4_parts(c, p, b, s, zc);
    assert(find_rule(rd.rules, crate::expr_arena_bridge::nat_zero_id(ne.export)) == Some(0int));
    assert(spine_head(zc) == zc && spine_args(zc) =~= Seq::<ExprSpec>::empty());
    let f = mk_app(mk_app(mk_app(c, p), b), s);
    assert(rec_ready(ne, mk_app(f, zc)));
    let body = inst_levels(rule.rhs, rd.uparams, lv);
    let args = seq![p, b, s, zc];
    assert(args.subrange(0, 3) =~= seq![p, b, s]);
    assert(spine_args(zc).subrange(0, 0) =~= Seq::<ExprSpec>::empty());
    assert(args.subrange(4, 4) =~= Seq::<ExprSpec>::empty());
    let r = rec_result(ne, mk_app(f, zc));
    assert(r == spine_app(body, seq![p, b, s]));
    assert(pstep(ne, f, f));
    assert(pstep(ne, zc, zc));
    pstep_rec_intro(ne, Box::new(f), Box::new(zc), f, zc, r);
    pstep_star_one(ne, e, r);
    levels_spine_bind(rule.rhs, 3, rd.uparams, lv);
    pstep_star_spine_reduce(ne, body, seq![p, b, s]);
    spine_reduce_eq_subst_full(body, seq![p, b, s], ExprSpec::Var(1), 0);
    pstep_star_trans(ne, e, r, b);
}

/// Iota at a successor: `Nat.rec p b s (Nat.succ n)` reduces to
/// `s n (Nat.rec p b s n)`, the recursive call at the same instance.
#[verifier::spinoff_prover]
pub proof fn nat_rec_succ(ne: EnvSpec, rid: u64, lv: Seq<crate::level_model::LevelSpec>, p: ExprSpec, b: ExprSpec, s: ExprSpec, n: ExprSpec)
    requires
        std_nat_rec(ne, rid),
        lv.len() == 1,
        crate::expr_model::nlbv(p) == 0 && crate::expr_model::nlbv(b) == 0 && crate::expr_model::nlbv(s) == 0
            && crate::expr_model::nlbv(n) == 0,
    ensures
        pstep_star(ne, mk_app4(ExprSpec::Const(rid, lv), p, b, s, mk_app(const_expr_no_levels(crate::expr_arena_bridge::nat_succ_id(ne.export)), n)),
            mk_app(mk_app(s, n), mk_app4(ExprSpec::Const(rid, lv), p, b, s, n))),
{
    let sc = const_expr_no_levels(crate::expr_arena_bridge::nat_succ_id(ne.export));
    let major = mk_app(sc, n);
    let rd = ne.rec_data(rid)->Some_0;
    let rule = rd.rules[1];
    let c = ExprSpec::Const(rid, lv);
    let e = mk_app4(c, p, b, s, major);
    spine_app4_parts(c, p, b, s, major);
    assert(find_rule(rd.rules.drop_first(), crate::expr_arena_bridge::nat_succ_id(ne.export)) == Some(0int));
    assert(find_rule(rd.rules, crate::expr_arena_bridge::nat_succ_id(ne.export)) == Some(1int));
    assert(spine_head(major) == sc && spine_args(major) =~= seq![n]) by {
        reveal_with_fuel(spine_head, 2);
        reveal_with_fuel(spine_args, 2);
    }
    let f = mk_app(mk_app(mk_app(c, p), b), s);
    assert(rec_ready(ne, mk_app(f, major)));
    let body = inst_levels(rule.rhs, rd.uparams, lv);
    let args = seq![p, b, s, major];
    assert(args.subrange(0, 3) =~= seq![p, b, s]);
    assert(seq![n].subrange(0, 1) =~= seq![n]);
    assert(args.subrange(4, 4) =~= Seq::<ExprSpec>::empty());
    let r = rec_result(ne, mk_app(f, major));
    assert(spine_app(spine_app(body, seq![p, b, s]), seq![n]) == spine_app(body, seq![p, b, s, n])) by {
        crate::beta_model::spine_app_concat(body, seq![p, b, s], seq![n]);
        assert(seq![p, b, s] + seq![n] =~= seq![p, b, s, n]);
    }
    assert(r == spine_app(body, seq![p, b, s, n]));
    assert(pstep(ne, f, f));
    assert(pstep(ne, major, major));
    pstep_rec_intro(ne, Box::new(f), Box::new(major), f, major, r);
    pstep_star_one(ne, e, r);
    // the rule's body at the instance
    let k = rd.uparams[0];
    let lp = seq![crate::level_model::LevelSpec::Param(k)];
    assert(crate::level_model::subst_levels_spec(lp, rd.uparams, lv) =~= lv) by {
        assert(rd.uparams =~= seq![k]);
        reveal_with_fuel(crate::level_model::find_level_idx, 2);
    }
    let rb = mk_app(mk_app(ExprSpec::Var(1), ExprSpec::Var(0)), mk_app4(ExprSpec::Const(rid, lp), ExprSpec::Var(3), ExprSpec::Var(2), ExprSpec::Var(1), ExprSpec::Var(0)));
    levels_spine_bind(rule.rhs, 4, rd.uparams, lv);
    inst_levels_app(mk_app(ExprSpec::Var(1), ExprSpec::Var(0)), mk_app4(ExprSpec::Const(rid, lp), ExprSpec::Var(3), ExprSpec::Var(2), ExprSpec::Var(1), ExprSpec::Var(0)), rd.uparams, lv);
    inst_levels_app(ExprSpec::Var(1), ExprSpec::Var(0), rd.uparams, lv);
    inst_levels_app4(ExprSpec::Const(rid, lp), ExprSpec::Var(3), ExprSpec::Var(2), ExprSpec::Var(1), ExprSpec::Var(0), rd.uparams, lv);
    let rb2 = mk_app(mk_app(ExprSpec::Var(1), ExprSpec::Var(0)), mk_app4(c, ExprSpec::Var(3), ExprSpec::Var(2), ExprSpec::Var(1), ExprSpec::Var(0)));
    assert(inst_levels(rb, rd.uparams, lv) == rb2);
    let sargs = seq![p, b, s, n];
    pstep_star_spine_reduce(ne, body, sargs);
    assert(crate::expr_model::nlbv(rb2) <= 4) by {
        reveal_with_fuel(crate::expr_model::nlbv, 6);
    }
    spine_reduce_eq_subst_full(body, sargs, rb2, 0);
    inst_args_app(mk_app(ExprSpec::Var(1), ExprSpec::Var(0)), mk_app4(c, ExprSpec::Var(3), ExprSpec::Var(2), ExprSpec::Var(1), ExprSpec::Var(0)), sargs, 0);
    inst_args_app(ExprSpec::Var(1), ExprSpec::Var(0), sargs, 0);
    inst_args_app4(c, ExprSpec::Var(3), ExprSpec::Var(2), ExprSpec::Var(1), ExprSpec::Var(0), sargs, 0);
    assert(inst_args(rb2, sargs, 0) == mk_app(mk_app(s, n), mk_app4(c, p, b, s, n)));
    pstep_star_trans(ne, e, r, mk_app(mk_app(s, n), mk_app4(c, p, b, s, n)));
}

pub open spec fn mk_app6(h: ExprSpec, a: ExprSpec, b: ExprSpec, c: ExprSpec, d: ExprSpec, e: ExprSpec, f: ExprSpec) -> ExprSpec {
    mk_app(mk_app(mk_app4(h, a, b, c, d), e), f)
}

/// `Nat.add._f`'s first case: `λ a _. a`.
pub open spec fn add_zero_case(x: ExprSpec) -> bool {
    x == mk_lam(lam_type(x), mk_lam(lam_type(lam_body(x)), ExprSpec::Var(1)))
}

/// Its second case: `λ a n b. Nat.succ (b.0 a)`.
pub open spec fn add_succ_case(x: ExprSpec, sid: u64) -> bool {
    x == mk_lam(lam_type(x), mk_lam(lam_type(lam_body(x)), mk_lam(lam_type(lam_body(lam_body(x))),
        mk_app(const_expr_no_levels(sid), mk_app(ExprSpec::Proj(0, Box::new(ExprSpec::Var(0))), ExprSpec::Var(2))))))
}

/// `Nat.add._f`'s value is Lean's: under its three binders (major `#2`,
/// below `#1`, the other operand `#0`),
/// `Nat.add.match_1 mot #0 #2 H1 H2 #1`.
pub open spec fn std_add_f(v: ExprSpec, sid: u64) -> bool {
    spine_bind(v, 3) is Some && {
        let b = spine_bind(v, 3)->Some_0;
        let c = fun_of(fun_of(b));
        &&& b == mk_app6(head_of4(c), arg1_of4(c), ExprSpec::Var(0), ExprSpec::Var(2), arg4_of4(c), arg_of(fun_of(b)), ExprSpec::Var(1))
        &&& head_of4(c) is Const
        &&& crate::expr_model::nlbv(arg1_of4(c)) == 0
        &&& add_zero_case(arg4_of4(c)) && add_succ_case(arg_of(fun_of(b)), sid)
    }
}

/// `Nat.add.match_1`'s value is Lean's: under its five binders (motive
/// `#4`, `x` `#3`, `y` `#2`, `h1` `#1`, `h2` `#0`),
/// `Nat.casesOn mot #2 (#1 #3) (λ n. #1 #4 n)`.
pub open spec fn std_add_match(v: ExprSpec) -> bool {
    spine_bind(v, 5) is Some && {
        let b = spine_bind(v, 5)->Some_0;
        &&& b == mk_app4(head_of4(b), arg1_of4(b), ExprSpec::Var(2), mk_app(ExprSpec::Var(1), ExprSpec::Var(3)),
            mk_lam(lam_type(arg4_of4(b)), mk_app(mk_app(ExprSpec::Var(1), ExprSpec::Var(4)), ExprSpec::Var(0))))
        &&& head_of4(b) is Const
    }
}

/// `Nat.casesOn`'s value is Lean's: under its four binders (motive `#3`,
/// major `#2`, `zero` case `#1`, `succ` case `#0`),
/// `Nat.rec #3 #1 (λ n _. #2 n) #2`.
pub open spec fn std_cases_on(v: ExprSpec) -> bool {
    spine_bind(v, 4) is Some && {
        let b = spine_bind(v, 4)->Some_0;
        let st = arg3_of4(b);
        &&& b == mk_app4(head_of4(b), ExprSpec::Var(3), ExprSpec::Var(1),
            mk_lam(lam_type(st), mk_lam(lam_type(lam_body(st)), mk_app(ExprSpec::Var(2), ExprSpec::Var(1)))), ExprSpec::Var(2))
        &&& head_of4(b) is Const
    }
}

pub proof fn add_zero_case_inst(x: ExprSpec, ks: Seq<u64>, vs: Seq<crate::level_model::LevelSpec>, args: Seq<ExprSpec>, k: nat)
    requires
        add_zero_case(x),
    ensures
        add_zero_case(inst_args(inst_levels(x, ks, vs), args, k)),
{
    let (t1, t2) = (lam_type(x), lam_type(lam_body(x)));
    inst_levels_lam(t1, mk_lam(t2, ExprSpec::Var(1)), ks, vs);
    inst_levels_lam(t2, ExprSpec::Var(1), ks, vs);
    inst_args_lam(inst_levels(t1, ks, vs), mk_lam(inst_levels(t2, ks, vs), ExprSpec::Var(1)), args, k);
    inst_args_lam(inst_levels(t2, ks, vs), ExprSpec::Var(1), args, k + 1);
}

pub proof fn add_succ_case_inst(x: ExprSpec, ks: Seq<u64>, vs: Seq<crate::level_model::LevelSpec>, args: Seq<ExprSpec>, k: nat, sid: u64)
    requires
        add_succ_case(x, sid),
    ensures
        add_succ_case(inst_args(inst_levels(x, ks, vs), args, k), sid),
{
    let (t1, t2, t3) = (lam_type(x), lam_type(lam_body(x)), lam_type(lam_body(lam_body(x))));
    let sc = const_expr_no_levels(sid);
    let pr = ExprSpec::Proj(0, Box::new(ExprSpec::Var(0)));
    let body = mk_app(sc, mk_app(pr, ExprSpec::Var(2)));
    inst_levels_lam(t1, mk_lam(t2, mk_lam(t3, body)), ks, vs);
    inst_levels_lam(t2, mk_lam(t3, body), ks, vs);
    inst_levels_lam(t3, body, ks, vs);
    inst_levels_app(sc, mk_app(pr, ExprSpec::Var(2)), ks, vs);
    inst_levels_app(pr, ExprSpec::Var(2), ks, vs);
    levels_const_nil(sid, ks, vs);
    assert(inst_levels(ExprSpec::Var(0), ks, vs) == ExprSpec::Var(0));
    assert(inst_levels(pr, ks, vs) == pr);
    inst_args_lam(inst_levels(t1, ks, vs), mk_lam(inst_levels(t2, ks, vs), mk_lam(inst_levels(t3, ks, vs), body)), args, k);
    inst_args_lam(inst_levels(t2, ks, vs), mk_lam(inst_levels(t3, ks, vs), body), args, k + 1);
    inst_args_lam(inst_levels(t3, ks, vs), body, args, k + 2);
    inst_args_app(sc, mk_app(pr, ExprSpec::Var(2)), args, k + 3);
    inst_args_app(pr, ExprSpec::Var(2), args, k + 3);
    crate::expr_model::subst_full_noop(sc, args, k + 3);
    assert(inst_args(ExprSpec::Var(0), args, k + 3) == ExprSpec::Var(0));
    assert(inst_args(pr, args, k + 3) == pr);
}

pub proof fn inst_levels_app6(h: ExprSpec, a: ExprSpec, b: ExprSpec, c: ExprSpec, d: ExprSpec, e: ExprSpec, f: ExprSpec, ks: Seq<u64>, vs: Seq<crate::level_model::LevelSpec>)
    ensures inst_levels(mk_app6(h, a, b, c, d, e, f), ks, vs) == mk_app6(inst_levels(h, ks, vs), inst_levels(a, ks, vs), inst_levels(b, ks, vs), inst_levels(c, ks, vs), inst_levels(d, ks, vs), inst_levels(e, ks, vs), inst_levels(f, ks, vs)),
{
    inst_levels_app(mk_app(mk_app4(h, a, b, c, d), e), f, ks, vs);
    inst_levels_app(mk_app4(h, a, b, c, d), e, ks, vs);
    inst_levels_app4(h, a, b, c, d, ks, vs);
}

pub proof fn inst_args_app6(h: ExprSpec, a: ExprSpec, b: ExprSpec, c: ExprSpec, d: ExprSpec, e: ExprSpec, f: ExprSpec, args: Seq<ExprSpec>, k: nat)
    ensures inst_args(mk_app6(h, a, b, c, d, e, f), args, k) == mk_app6(inst_args(h, args, k), inst_args(a, args, k), inst_args(b, args, k), inst_args(c, args, k), inst_args(d, args, k), inst_args(e, args, k), inst_args(f, args, k)),
{
    inst_args_app(mk_app(mk_app4(h, a, b, c, d), e), f, args, k);
    inst_args_app(mk_app4(h, a, b, c, d), e, args, k);
    inst_args_app4(h, a, b, c, d, args, k);
}

pub proof fn spine_app3_parts(h: ExprSpec, a: ExprSpec, b: ExprSpec, c: ExprSpec)
    ensures
        spine_app(h, seq![a, b, c]) == mk_app(mk_app(mk_app(h, a), b), c),
{
    reveal_with_fuel(spine_app, 4);
}

/// `Nat.add._f t below z` unfolds to `Nat.add.match_1 mot z t H1 H2 below`.
#[verifier::spinoff_prover]
pub proof fn add_f_unfold(ne: EnvSpec, id: u64, ls: Seq<crate::level_model::LevelSpec>, t: ExprSpec, below: ExprSpec, z: ExprSpec)
    requires
        ne.contains_key(id),
        ne[id].0.len() == ls.len(),
        std_add_f(ne[id].1, crate::expr_arena_bridge::nat_succ_id(ne.export)),
        crate::expr_model::nlbv(ne[id].1) == 0,
        crate::expr_model::nlbv(t) == 0 && crate::expr_model::nlbv(below) == 0 && crate::expr_model::nlbv(z) == 0,
    ensures ({
        let sid = crate::expr_arena_bridge::nat_succ_id(ne.export);
        let c = fun_of(fun_of(spine_bind(ne[id].1, 3)->Some_0));
        let r = mk_app6(ExprSpec::Const(head_of4(c)->Const_0, crate::level_model::subst_levels_spec(head_of4(c)->Const_1, ne[id].0, ls)),
            inst_args(inst_levels(arg1_of4(c), ne[id].0, ls), seq![t, below, z], 0), z, t,
            inst_args(inst_levels(arg4_of4(c), ne[id].0, ls), seq![t, below, z], 0), inst_args(inst_levels(arg_of(fun_of(spine_bind(ne[id].1, 3)->Some_0)), ne[id].0, ls), seq![t, below, z], 0), below);
        &&& pstep_star(ne, mk_app(mk_app(mk_app(ExprSpec::Const(id, ls), t), below), z), r)
        &&& add_zero_case(inst_args(inst_levels(arg4_of4(c), ne[id].0, ls), seq![t, below, z], 0))
        &&& add_succ_case(inst_args(inst_levels(arg_of(fun_of(spine_bind(ne[id].1, 3)->Some_0)), ne[id].0, ls), seq![t, below, z], 0), sid)
        &&& crate::expr_model::nlbv(inst_args(inst_levels(arg1_of4(c), ne[id].0, ls), seq![t, below, z], 0)) == 0
        &&& crate::expr_model::nlbv(inst_args(inst_levels(arg4_of4(c), ne[id].0, ls), seq![t, below, z], 0)) == 0
        &&& crate::expr_model::nlbv(inst_args(inst_levels(arg_of(fun_of(spine_bind(ne[id].1, 3)->Some_0)), ne[id].0, ls), seq![t, below, z], 0)) == 0
    }),
{
    let sid = crate::expr_arena_bridge::nat_succ_id(ne.export);
    let v = ne[id].1;
    let b = spine_bind(v, 3)->Some_0;
    let c = fun_of(fun_of(b));
    let (h, mot, h1, h2) = (head_of4(c), arg1_of4(c), arg4_of4(c), arg_of(fun_of(b)));
    let (ks, vs) = (ne[id].0, ls);
    let args = seq![t, below, z];
    levels_spine_bind(v, 3, ks, vs);
    crate::beta_model::spine_bind_nlbv(v, 3, b, 0);
    crate::ti_level::ls_nlbv(b, ks, vs);
    inst_levels_app6(h, mot, ExprSpec::Var(0), ExprSpec::Var(2), h1, h2, ExprSpec::Var(1), ks, vs);
    let b2 = inst_levels(b, ks, vs);
    inst_args_app6(inst_levels(h, ks, vs), inst_levels(mot, ks, vs), ExprSpec::Var(0), ExprSpec::Var(2), inst_levels(h1, ks, vs), inst_levels(h2, ks, vs), ExprSpec::Var(1), args, 0);
    crate::expr_model::subst_full_noop(inst_levels(h, ks, vs), args, 0);
    crate::ti_level::ls_nlbv(mot, ks, vs);
    crate::expr_model::subst_full_noop(inst_levels(mot, ks, vs), args, 0);
    add_zero_case_inst(h1, ks, vs, args, 0);
    add_succ_case_inst(h2, ks, vs, args, 0, sid);
    spine_app3_parts(ExprSpec::Const(id, ls), t, below, z);
    delta_beta(ne, id, ls, args, b2);
    assert(crate::expr_model::nlbv(h1) <= 3 && crate::expr_model::nlbv(h2) <= 3) by {
        reveal_with_fuel(crate::expr_model::nlbv, 6);
    }
    crate::ti_level::ls_nlbv(h1, ks, vs);
    crate::ti_level::ls_nlbv(h2, ks, vs);
    crate::beta_model::subst_full_nlbv_bound_n(inst_levels(h1, ks, vs), args, 0);
    crate::beta_model::subst_full_nlbv_bound_n(inst_levels(h2, ks, vs), args, 0);
}

/// `Nat.add.match_1 mot x y h1 h2` unfolds to
/// `Nat.casesOn mot' y (h1 x) (λ n. h2 x n)`.
#[verifier::spinoff_prover]
pub proof fn add_match_unfold(ne: EnvSpec, id: u64, ls: Seq<crate::level_model::LevelSpec>, mot: ExprSpec, x: ExprSpec, y: ExprSpec, h1: ExprSpec, h2: ExprSpec)
    requires
        ne.contains_key(id),
        ne[id].0.len() == ls.len(),
        std_add_match(ne[id].1),
        crate::expr_model::nlbv(ne[id].1) == 0,
        crate::expr_model::nlbv(mot) == 0 && crate::expr_model::nlbv(x) == 0 && crate::expr_model::nlbv(y) == 0
            && crate::expr_model::nlbv(h1) == 0 && crate::expr_model::nlbv(h2) == 0,
    ensures ({
        let b = spine_bind(ne[id].1, 5)->Some_0;
        let args = seq![mot, x, y, h1, h2];
        let r = mk_app4(ExprSpec::Const(head_of4(b)->Const_0, crate::level_model::subst_levels_spec(head_of4(b)->Const_1, ne[id].0, ls)),
            inst_args(inst_levels(arg1_of4(b), ne[id].0, ls), args, 0), y, mk_app(h1, x),
            mk_lam(inst_args(inst_levels(lam_type(arg4_of4(b)), ne[id].0, ls), args, 0), mk_app(mk_app(h2, x), ExprSpec::Var(0))));
        &&& pstep_star(ne, mk_app(mk_app4(ExprSpec::Const(id, ls), mot, x, y, h1), h2), r)
        &&& crate::expr_model::nlbv(inst_args(inst_levels(arg1_of4(b), ne[id].0, ls), args, 0)) == 0
        &&& crate::expr_model::nlbv(arg4_of4(r)) == 0
    }),
{
    let v = ne[id].1;
    let b = spine_bind(v, 5)->Some_0;
    let (h, mot2, t6) = (head_of4(b), arg1_of4(b), lam_type(arg4_of4(b)));
    let (ks, vs) = (ne[id].0, ls);
    let args = seq![mot, x, y, h1, h2];
    let inner = mk_app(mk_app(ExprSpec::Var(1), ExprSpec::Var(4)), ExprSpec::Var(0));
    levels_spine_bind(v, 5, ks, vs);
    crate::beta_model::spine_bind_nlbv(v, 5, b, 0);
    crate::ti_level::ls_nlbv(b, ks, vs);
    inst_levels_app4(h, mot2, ExprSpec::Var(2), mk_app(ExprSpec::Var(1), ExprSpec::Var(3)), mk_lam(t6, inner), ks, vs);
    inst_levels_app(ExprSpec::Var(1), ExprSpec::Var(3), ks, vs);
    inst_levels_lam(t6, inner, ks, vs);
    inst_levels_app(mk_app(ExprSpec::Var(1), ExprSpec::Var(4)), ExprSpec::Var(0), ks, vs);
    inst_levels_app(ExprSpec::Var(1), ExprSpec::Var(4), ks, vs);
    let b2 = inst_levels(b, ks, vs);
    inst_args_app4(inst_levels(h, ks, vs), inst_levels(mot2, ks, vs), ExprSpec::Var(2), mk_app(ExprSpec::Var(1), ExprSpec::Var(3)),
        mk_lam(inst_levels(t6, ks, vs), inner), args, 0);
    inst_args_app(ExprSpec::Var(1), ExprSpec::Var(3), args, 0);
    inst_args_lam(inst_levels(t6, ks, vs), inner, args, 0);
    inst_args_app(mk_app(ExprSpec::Var(1), ExprSpec::Var(4)), ExprSpec::Var(0), args, 1);
    inst_args_app(ExprSpec::Var(1), ExprSpec::Var(4), args, 1);
    crate::expr_model::subst_full_noop(inst_levels(h, ks, vs), args, 0);
    assert(spine_app(ExprSpec::Const(id, ls), args) == mk_app(mk_app4(ExprSpec::Const(id, ls), mot, x, y, h1), h2)) by {
        reveal_with_fuel(spine_app, 6);
    }
    delta_beta(ne, id, ls, args, b2);
    assert(crate::expr_model::nlbv(mot2) <= 5) by {
        reveal_with_fuel(crate::expr_model::nlbv, 6);
    }
    crate::ti_level::ls_nlbv(mot2, ks, vs);
    crate::beta_model::subst_full_nlbv_bound_n(inst_levels(mot2, ks, vs), args, 0);
    assert(crate::expr_model::nlbv(t6) <= 5) by {
        reveal_with_fuel(crate::expr_model::nlbv, 6);
    }
    crate::ti_level::ls_nlbv(t6, ks, vs);
    crate::beta_model::subst_full_nlbv_bound_n(inst_levels(t6, ks, vs), args, 0);
    let rr = mk_lam(inst_args(inst_levels(t6, ks, vs), args, 0), mk_app(mk_app(h2, x), ExprSpec::Var(0)));
    assert(crate::expr_model::nlbv(rr) == 0) by {
        reveal_with_fuel(crate::expr_model::nlbv, 4);
    }
}

/// `Nat.casesOn mot t z s` unfolds to `Nat.rec mot z (λ n _. s n) t`.
#[verifier::spinoff_prover]
pub proof fn cases_on_unfold(ne: EnvSpec, id: u64, ls: Seq<crate::level_model::LevelSpec>, mot: ExprSpec, t: ExprSpec, z: ExprSpec, s: ExprSpec)
    requires
        ne.contains_key(id),
        ne[id].0.len() == ls.len(),
        std_cases_on(ne[id].1),
        crate::expr_model::nlbv(ne[id].1) == 0,
        crate::expr_model::nlbv(mot) == 0 && crate::expr_model::nlbv(t) == 0 && crate::expr_model::nlbv(z) == 0
            && crate::expr_model::nlbv(s) == 0,
    ensures ({
        let b = spine_bind(ne[id].1, 4)->Some_0;
        let st = arg3_of4(b);
        let args = seq![mot, t, z, s];
        let r = mk_app4(ExprSpec::Const(head_of4(b)->Const_0, crate::level_model::subst_levels_spec(head_of4(b)->Const_1, ne[id].0, ls)),
            mot, z, mk_lam(inst_args(inst_levels(lam_type(st), ne[id].0, ls), args, 0),
                mk_lam(inst_args(inst_levels(lam_type(lam_body(st)), ne[id].0, ls), args, 1), mk_app(s, ExprSpec::Var(1)))), t);
        &&& pstep_star(ne, mk_app4(ExprSpec::Const(id, ls), mot, t, z, s), r)
        &&& crate::expr_model::nlbv(arg3_of4(r)) == 0
    }),
{
    let v = ne[id].1;
    let b = spine_bind(v, 4)->Some_0;
    let st = arg3_of4(b);
    let (h, t1, t2) = (head_of4(b), lam_type(st), lam_type(lam_body(st)));
    let (ks, vs) = (ne[id].0, ls);
    let args = seq![mot, t, z, s];
    let inner = mk_app(ExprSpec::Var(2), ExprSpec::Var(1));
    levels_spine_bind(v, 4, ks, vs);
    crate::beta_model::spine_bind_nlbv(v, 4, b, 0);
    crate::ti_level::ls_nlbv(b, ks, vs);
    inst_levels_app4(h, ExprSpec::Var(3), ExprSpec::Var(1), mk_lam(t1, mk_lam(t2, inner)), ExprSpec::Var(2), ks, vs);
    inst_levels_lam(t1, mk_lam(t2, inner), ks, vs);
    inst_levels_lam(t2, inner, ks, vs);
    inst_levels_app(ExprSpec::Var(2), ExprSpec::Var(1), ks, vs);
    let b2 = inst_levels(b, ks, vs);
    inst_args_app4(inst_levels(h, ks, vs), ExprSpec::Var(3), ExprSpec::Var(1), mk_lam(inst_levels(t1, ks, vs), mk_lam(inst_levels(t2, ks, vs), inner)),
        ExprSpec::Var(2), args, 0);
    inst_args_lam(inst_levels(t1, ks, vs), mk_lam(inst_levels(t2, ks, vs), inner), args, 0);
    inst_args_lam(inst_levels(t2, ks, vs), inner, args, 1);
    inst_args_app(ExprSpec::Var(2), ExprSpec::Var(1), args, 2);
    crate::expr_model::subst_full_noop(inst_levels(h, ks, vs), args, 0);
    spine_app4_parts(ExprSpec::Const(id, ls), mot, t, z, s);
    delta_beta(ne, id, ls, args, b2);
    assert(crate::expr_model::nlbv(t1) <= 4 && crate::expr_model::nlbv(t2) <= 5) by {
        reveal_with_fuel(crate::expr_model::nlbv, 7);
    }
    crate::ti_level::ls_nlbv(t1, ks, vs);
    crate::ti_level::ls_nlbv(t2, ks, vs);
    crate::beta_model::subst_full_nlbv_bound_n(inst_levels(t1, ks, vs), args, 0);
    crate::beta_model::subst_full_nlbv_bound_n(inst_levels(t2, ks, vs), args, 1);
    let ll = mk_lam(inst_args(inst_levels(t1, ks, vs), args, 0), mk_lam(inst_args(inst_levels(t2, ks, vs), args, 1), mk_app(s, ExprSpec::Var(1))));
    assert(crate::expr_model::nlbv(ll) == 0) by {
        reveal_with_fuel(crate::expr_model::nlbv, 5);
    }
}

/// A constant naming a closed definition, used at its universe arity.
pub open spec fn linked(ne: EnvSpec, c: ExprSpec) -> bool {
    &&& c is Const
    &&& ne.contains_key(c->Const_0)
    &&& ne[c->Const_0].0.len() == c->Const_1.len()
    &&& crate::expr_model::nlbv(ne[c->Const_0].1) == 0
}

/// The constant `Nat.add._f`'s body calls (`Nat.add.match_1`), the one that
/// calls (`Nat.casesOn`), and the recursor that calls.
pub open spec fn f_match(ne: EnvSpec, fid: u64) -> ExprSpec {
    head_of4(fun_of(fun_of(spine_bind(ne[fid].1, 3)->Some_0)))
}

pub open spec fn match_cases(ne: EnvSpec, mid: u64) -> ExprSpec {
    head_of4(spine_bind(ne[mid].1, 5)->Some_0)
}

pub open spec fn cases_rec(ne: EnvSpec, cid: u64) -> ExprSpec {
    head_of4(spine_bind(ne[cid].1, 4)->Some_0)
}

/// `f` is Lean's `Nat.add._f`, and the definitions it reaches are Lean's.
pub open spec fn add_f_links(ne: EnvSpec, f: ExprSpec) -> bool {
    let sid = crate::expr_arena_bridge::nat_succ_id(ne.export);
    let m = f_match(ne, f->Const_0);
    let c = match_cases(ne, m->Const_0);
    let r = cases_rec(ne, c->Const_0);
    &&& linked(ne, f) && std_add_f(ne[f->Const_0].1, sid)
    &&& linked(ne, m) && std_add_match(ne[m->Const_0].1)
    &&& linked(ne, c) && std_cases_on(ne[c->Const_0].1)
    &&& std_nat_rec(ne, r->Const_0) && r->Const_1.len() == 1
}

/// `Nat.add._f` at zero: `_f Nat.zero below z` reduces to `z`.
#[verifier::spinoff_prover]
pub proof fn add_f_zero(ne: EnvSpec, f: ExprSpec, below: ExprSpec, z: ExprSpec)
    requires
        add_f_links(ne, f),
        crate::expr_model::nlbv(below) == 0 && crate::expr_model::nlbv(z) == 0,
    ensures
        pstep_star(ne, mk_app(mk_app(mk_app(f, const_expr_no_levels(crate::expr_arena_bridge::nat_zero_id(ne.export))), below), z), z),
{
    let zc = const_expr_no_levels(crate::expr_arena_bridge::nat_zero_id(ne.export));
    let (fid, uf) = (f->Const_0, f->Const_1);
    let e0 = mk_app(mk_app(mk_app(f, zc), below), z);
    // `_f` to `match_1`
    add_f_unfold(ne, fid, uf, zc, below, z);
    let fb = spine_bind(ne[fid].1, 3)->Some_0;
    let fc = fun_of(fun_of(fb));
    let fargs = seq![zc, below, z];
    let m = f_match(ne, fid);
    let mls = crate::level_model::subst_levels_spec(m->Const_1, ne[fid].0, uf);
    let mot = inst_args(inst_levels(arg1_of4(fc), ne[fid].0, uf), fargs, 0);
    let h1 = inst_args(inst_levels(arg4_of4(fc), ne[fid].0, uf), fargs, 0);
    let h2 = inst_args(inst_levels(arg_of(fun_of(fb)), ne[fid].0, uf), fargs, 0);
    let mc = ExprSpec::Const(m->Const_0, mls);
    let e1 = mk_app6(mc, mot, z, zc, h1, h2, below);
    // `match_1` to `casesOn`
    add_match_unfold(ne, m->Const_0, mls, mot, z, zc, h1, h2);
    let mb = spine_bind(ne[m->Const_0].1, 5)->Some_0;
    let margs = seq![mot, z, zc, h1, h2];
    let c = match_cases(ne, m->Const_0);
    let cls = crate::level_model::subst_levels_spec(c->Const_1, ne[m->Const_0].0, mls);
    let mot2 = inst_args(inst_levels(arg1_of4(mb), ne[m->Const_0].0, mls), margs, 0);
    let sfun = mk_lam(inst_args(inst_levels(lam_type(arg4_of4(mb)), ne[m->Const_0].0, mls), margs, 0), mk_app(mk_app(h2, z), ExprSpec::Var(0)));
    let cc = ExprSpec::Const(c->Const_0, cls);
    let x2 = mk_app4(cc, mot2, zc, mk_app(h1, z), sfun);
    pstep_star_app_congr(ne, mk_app(mk_app4(mc, mot, z, zc, h1), h2), x2, below);
    // `casesOn` to `Nat.rec`
    cases_on_unfold(ne, c->Const_0, cls, mot2, zc, mk_app(h1, z), sfun);
    let cb = spine_bind(ne[c->Const_0].1, 4)->Some_0;
    let cargs = seq![mot2, zc, mk_app(h1, z), sfun];
    let r = cases_rec(ne, c->Const_0);
    let rls = crate::level_model::subst_levels_spec(r->Const_1, ne[c->Const_0].0, cls);
    let st = arg3_of4(cb);
    let stepl = mk_lam(inst_args(inst_levels(lam_type(st), ne[c->Const_0].0, cls), cargs, 0),
        mk_lam(inst_args(inst_levels(lam_type(lam_body(st)), ne[c->Const_0].0, cls), cargs, 1), mk_app(sfun, ExprSpec::Var(1))));
    let rc = ExprSpec::Const(r->Const_0, rls);
    let x3 = mk_app4(rc, mot2, mk_app(h1, z), stepl, zc);
    pstep_star_app_congr(ne, x2, x3, below);
    // iota at zero
    assert(crate::expr_model::nlbv(mk_app(h1, z)) == 0);
    nat_rec_zero(ne, r->Const_0, rls, mot2, mk_app(h1, z), stepl);
    pstep_star_app_congr(ne, x3, mk_app(h1, z), below);
    // `(λ a _. a) z below` to `z`
    assert(spine_bind(h1, 2) == Some(ExprSpec::Var(1))) by {
        reveal_with_fuel(spine_bind, 3);
    }
    pstep_star_spine_reduce(ne, h1, seq![z, below]);
    spine_reduce_eq_subst_full(h1, seq![z, below], ExprSpec::Var(1), 0);
    assert(spine_app(h1, seq![z, below]) == mk_app(mk_app(h1, z), below)) by {
        reveal_with_fuel(spine_app, 3);
    }
    pstep_star_trans(ne, e0, e1, mk_app(x2, below));
    pstep_star_trans(ne, e0, mk_app(x2, below), mk_app(x3, below));
    pstep_star_trans(ne, e0, mk_app(x3, below), mk_app(mk_app(h1, z), below));
    pstep_star_trans(ne, e0, mk_app(mk_app(h1, z), below), z);
}

/// `Nat.add._f` at a successor: `_f (Nat.succ n) below z` reduces to
/// `Nat.succ (below.0 z)` -- the recursive call is the first component of
/// `below`.
#[verifier::spinoff_prover]
pub proof fn add_f_succ(ne: EnvSpec, f: ExprSpec, n: ExprSpec, below: ExprSpec, z: ExprSpec)
    requires
        add_f_links(ne, f),
        crate::expr_model::nlbv(n) == 0 && crate::expr_model::nlbv(below) == 0 && crate::expr_model::nlbv(z) == 0,
    ensures ({
        let sc = const_expr_no_levels(crate::expr_arena_bridge::nat_succ_id(ne.export));
        pstep_star(ne, mk_app(mk_app(mk_app(f, mk_app(sc, n)), below), z),
            mk_app(sc, mk_app(ExprSpec::Proj(0, Box::new(below)), z)))
    }),
{
    let sid = crate::expr_arena_bridge::nat_succ_id(ne.export);
    let sc = const_expr_no_levels(sid);
    let t = mk_app(sc, n);
    let (fid, uf) = (f->Const_0, f->Const_1);
    let e0 = mk_app(mk_app(mk_app(f, t), below), z);
    assert(crate::expr_model::nlbv(t) == 0) by {
        reveal_with_fuel(crate::expr_model::nlbv, 3);
    }
    // `_f` to `match_1`
    add_f_unfold(ne, fid, uf, t, below, z);
    let fb = spine_bind(ne[fid].1, 3)->Some_0;
    let fc = fun_of(fun_of(fb));
    let fargs = seq![t, below, z];
    let m = f_match(ne, fid);
    let mls = crate::level_model::subst_levels_spec(m->Const_1, ne[fid].0, uf);
    let mot = inst_args(inst_levels(arg1_of4(fc), ne[fid].0, uf), fargs, 0);
    let h1 = inst_args(inst_levels(arg4_of4(fc), ne[fid].0, uf), fargs, 0);
    let h2 = inst_args(inst_levels(arg_of(fun_of(fb)), ne[fid].0, uf), fargs, 0);
    let mc = ExprSpec::Const(m->Const_0, mls);
    let e1 = mk_app6(mc, mot, z, t, h1, h2, below);
    // `match_1` to `casesOn`
    add_match_unfold(ne, m->Const_0, mls, mot, z, t, h1, h2);
    let mb = spine_bind(ne[m->Const_0].1, 5)->Some_0;
    let margs = seq![mot, z, t, h1, h2];
    let c = match_cases(ne, m->Const_0);
    let cls = crate::level_model::subst_levels_spec(c->Const_1, ne[m->Const_0].0, mls);
    let mot2 = inst_args(inst_levels(arg1_of4(mb), ne[m->Const_0].0, mls), margs, 0);
    let sbody = mk_app(mk_app(h2, z), ExprSpec::Var(0));
    let sfun = mk_lam(inst_args(inst_levels(lam_type(arg4_of4(mb)), ne[m->Const_0].0, mls), margs, 0), sbody);
    let cc = ExprSpec::Const(c->Const_0, cls);
    let x2 = mk_app4(cc, mot2, t, mk_app(h1, z), sfun);
    pstep_star_app_congr(ne, mk_app(mk_app4(mc, mot, z, t, h1), h2), x2, below);
    // `casesOn` to `Nat.rec`
    cases_on_unfold(ne, c->Const_0, cls, mot2, t, mk_app(h1, z), sfun);
    let cb = spine_bind(ne[c->Const_0].1, 4)->Some_0;
    let cargs = seq![mot2, t, mk_app(h1, z), sfun];
    let r = cases_rec(ne, c->Const_0);
    let rls = crate::level_model::subst_levels_spec(r->Const_1, ne[c->Const_0].0, cls);
    let st = arg3_of4(cb);
    let stepl = mk_lam(inst_args(inst_levels(lam_type(st), ne[c->Const_0].0, cls), cargs, 0),
        mk_lam(inst_args(inst_levels(lam_type(lam_body(st)), ne[c->Const_0].0, cls), cargs, 1), mk_app(sfun, ExprSpec::Var(1))));
    let rc = ExprSpec::Const(r->Const_0, rls);
    let x3 = mk_app4(rc, mot2, mk_app(h1, z), stepl, t);
    pstep_star_app_congr(ne, x2, x3, below);
    // iota at the successor
    assert(crate::expr_model::nlbv(mk_app(h1, z)) == 0);
    nat_rec_succ(ne, r->Const_0, rls, mot2, mk_app(h1, z), stepl, n);
    let q = mk_app4(rc, mot2, mk_app(h1, z), stepl, n);
    let x4 = mk_app(mk_app(stepl, n), q);
    pstep_star_app_congr(ne, x3, x4, below);
    // `(λ n _. sfun n) n q` to `sfun n`
    assert(spine_bind(stepl, 2) == Some(mk_app(sfun, ExprSpec::Var(1)))) by {
        reveal_with_fuel(spine_bind, 3);
    }
    assert(crate::expr_model::nlbv(q) == 0) by {
        reveal_with_fuel(crate::expr_model::nlbv, 6);
    }
    pstep_star_spine_reduce(ne, stepl, seq![n, q]);
    assert(crate::expr_model::nlbv(mk_app(sfun, ExprSpec::Var(1))) <= 2) by {
        reveal_with_fuel(crate::expr_model::nlbv, 3);
    }
    spine_reduce_eq_subst_full(stepl, seq![n, q], mk_app(sfun, ExprSpec::Var(1)), 0);
    inst_args_app(sfun, ExprSpec::Var(1), seq![n, q], 0);
    crate::expr_model::subst_full_noop(sfun, seq![n, q], 0);
    assert(spine_app(stepl, seq![n, q]) == x4) by {
        reveal_with_fuel(spine_app, 3);
    }
    let x5 = mk_app(sfun, n);
    pstep_star_app_congr(ne, x4, x5, below);
    // `sfun n` to `h2 z n`
    assert(spine_bind(sfun, 1) == Some(sbody)) by {
        reveal_with_fuel(spine_bind, 2);
    }
    pstep_star_spine_reduce(ne, sfun, seq![n]);
    assert(crate::expr_model::nlbv(sbody) <= 1) by {
        reveal_with_fuel(crate::expr_model::nlbv, 3);
    }
    spine_reduce_eq_subst_full(sfun, seq![n], sbody, 0);
    inst_args_app(mk_app(h2, z), ExprSpec::Var(0), seq![n], 0);
    inst_args_app(h2, z, seq![n], 0);
    crate::expr_model::subst_full_noop(h2, seq![n], 0);
    crate::expr_model::subst_full_noop(z, seq![n], 0);
    assert(spine_app(sfun, seq![n]) == x5) by {
        reveal_with_fuel(spine_app, 2);
    }
    let x6 = mk_app(mk_app(h2, z), n);
    pstep_star_app_congr(ne, x5, x6, below);
    // `(λ a n b. succ (b.0 a)) z n below` to `succ (below.0 z)`
    let pr = ExprSpec::Proj(0, Box::new(ExprSpec::Var(0)));
    let hb = mk_app(sc, mk_app(pr, ExprSpec::Var(2)));
    assert(spine_bind(h2, 3) == Some(hb)) by {
        reveal_with_fuel(spine_bind, 4);
    }
    let hargs = seq![z, n, below];
    pstep_star_spine_reduce(ne, h2, hargs);
    assert(crate::expr_model::nlbv(hb) <= 3) by {
        reveal_with_fuel(crate::expr_model::nlbv, 5);
    }
    spine_reduce_eq_subst_full(h2, hargs, hb, 0);
    inst_args_app(sc, mk_app(pr, ExprSpec::Var(2)), hargs, 0);
    inst_args_app(pr, ExprSpec::Var(2), hargs, 0);
    crate::expr_model::subst_full_noop(sc, hargs, 0);
    assert(inst_args(pr, hargs, 0) == ExprSpec::Proj(0, Box::new(below))) by {
        assert(inst_args(ExprSpec::Var(0), hargs, 0) == below);
    }
    spine_app3_parts(h2, z, n, below);
    let fin = mk_app(sc, mk_app(ExprSpec::Proj(0, Box::new(below)), z));
    pstep_star_trans(ne, e0, e1, mk_app(x2, below));
    pstep_star_trans(ne, e0, mk_app(x2, below), mk_app(x3, below));
    pstep_star_trans(ne, e0, mk_app(x3, below), mk_app(x4, below));
    pstep_star_trans(ne, e0, mk_app(x4, below), mk_app(x5, below));
    pstep_star_trans(ne, e0, mk_app(x5, below), mk_app(x6, below));
    pstep_star_trans(ne, e0, mk_app(x6, below), fin);
}

/// `x` under `n` applications of `Nat.succ`.
pub open spec fn succs(sid: u64, n: nat, x: ExprSpec) -> ExprSpec
    decreases n,
{
    if n == 0 { x } else { mk_app(const_expr_no_levels(sid), succs(sid, (n - 1) as nat, x)) }
}

/// Canonical numerals are closed.
pub proof fn canon_numeral_closed(export: nat, k: nat)
    ensures
        crate::expr_model::nlbv(canon_numeral(export, k)) == 0,
    decreases k,
{
    if k > 0 {
        canon_numeral_closed(export, (k - 1) as nat);
    }
    reveal_with_fuel(crate::expr_model::nlbv, 3);
}

/// `Nat.succ` applications lift a reduction of their innermost term.
pub proof fn succs_star(ne: EnvSpec, n: nat, x: ExprSpec, y: ExprSpec)
    requires
        pstep_star(ne, x, y),
    ensures
        pstep_star(ne, succs(crate::expr_arena_bridge::nat_succ_id(ne.export), n, x), succs(crate::expr_arena_bridge::nat_succ_id(ne.export), n, y)),
    decreases n,
{
    if n > 0 {
        let sid = crate::expr_arena_bridge::nat_succ_id(ne.export);
        succs_star(ne, (n - 1) as nat, x, y);
        pstep_star_app_arg_congr(ne, const_expr_no_levels(sid), succs(sid, (n - 1) as nat, x), succs(sid, (n - 1) as nat, y));
    }
}

/// `n` successors of the canonical numeral `a` are the canonical `a + n`.
pub proof fn succs_canon(export: nat, n: nat, a: nat)
    ensures
        succs(crate::expr_arena_bridge::nat_succ_id(export), n, canon_numeral(export, a)) == canon_numeral(export, a + n),
    decreases n,
{
    if n > 0 {
        succs_canon(export, (n - 1) as nat, a);
    }
}

/// THE RECURSION `Nat.brecOn.go` BUILDS: at `n`, its first component,
/// applied to `x`, reduces to `n` successors of `x`.
#[verifier::spinoff_prover]
pub proof fn go_rec_add(ne: EnvSpec, rid: u64, rls: Seq<crate::level_model::LevelSpec>, p: ExprSpec, base: ExprSpec, step: ExprSpec,
    f: ExprSpec, x: ExprSpec, n: nat)
    requires
        std_nat_rec(ne, rid),
        rls.len() == 1,
        add_f_links(ne, f),
        crate::expr_model::nlbv(f) == 0,
        crate::expr_model::nlbv(p) == 0 && crate::expr_model::nlbv(base) == 0 && crate::expr_model::nlbv(step) == 0
            && crate::expr_model::nlbv(x) == 0,
        base_shape(base, f, crate::expr_arena_bridge::nat_zero_id(ne.export)),
        step_shape(step, f, crate::expr_arena_bridge::nat_succ_id(ne.export)),
        ne.ctor_num_params(head_of4(base)->Const_0) == Some(2u16),
        ne.ctor_num_params(head_of4(lam_body(lam_body(step)))->Const_0) == Some(2u16),
    ensures
        pstep_star(ne, mk_app(ExprSpec::Proj(0, Box::new(mk_app4(ExprSpec::Const(rid, rls), p, base, step, canon_numeral(ne.export, n)))), x),
            succs(crate::expr_arena_bridge::nat_succ_id(ne.export), n, x)),
    decreases n,
{
    let (zid, sid) = (crate::expr_arena_bridge::nat_zero_id(ne.export), crate::expr_arena_bridge::nat_succ_id(ne.export));
    let sc = const_expr_no_levels(sid);
    let rc = ExprSpec::Const(rid, rls);
    let rn = mk_app4(rc, p, base, step, canon_numeral(ne.export, n));
    let e0 = mk_app(ExprSpec::Proj(0, Box::new(rn)), x);
    if n == 0 {
        nat_rec_zero(ne, rid, rls, p, base, step);
        let mk = head_of4(base);
        let fz = arg3_of4(base);
        spine_app4_parts(mk, arg1_of4(base), arg2_of4(base), fz, arg4_of4(base));
        crate::beta_model::pstep_star_iota(ne, 0, rn, mk->Const_0, mk->Const_1, seq![arg1_of4(base), arg2_of4(base), fz, arg4_of4(base)], 2);
        pstep_star_app_congr(ne, ExprSpec::Proj(0, Box::new(rn)), fz, x);
        let u1 = arg_of(fz);
        assert(crate::expr_model::nlbv(u1) == 0) by {
            reveal_with_fuel(crate::expr_model::nlbv, 7);
        }
        add_f_zero(ne, f, u1, x);
        pstep_star_trans(ne, e0, mk_app(fz, x), x);
    } else {
        let k = (n - 1) as nat;
        let nk = canon_numeral(ne.export, k);
        let rk = mk_app4(rc, p, base, step, nk);
        canon_numeral_closed(ne.export, k);
        nat_rec_succ(ne, rid, rls, p, base, step, nk);
        // the step case at `k` and the recursive value
        let sb = lam_body(lam_body(step));
        assert(spine_bind(step, 2) == Some(sb)) by {
            reveal_with_fuel(spine_bind, 3);
        }
        assert(crate::expr_model::nlbv(rk) == 0) by {
            reveal_with_fuel(crate::expr_model::nlbv, 6);
        }
        let sargs = seq![nk, rk];
        pstep_star_spine_reduce(ne, step, sargs);
        assert(crate::expr_model::nlbv(sb) <= 2) by {
            reveal_with_fuel(crate::expr_model::nlbv, 3);
        }
        spine_reduce_eq_subst_full(step, sargs, sb, 0);
        let fs = mk_app(mk_app(f, mk_app(sc, ExprSpec::Var(1))), ExprSpec::Var(0));
        inst_args_app4(head_of4(sb), arg1_of4(sb), arg2_of4(sb), fs, ExprSpec::Var(0), sargs, 0);
        inst_args_app(mk_app(f, mk_app(sc, ExprSpec::Var(1))), ExprSpec::Var(0), sargs, 0);
        inst_args_app(f, mk_app(sc, ExprSpec::Var(1)), sargs, 0);
        inst_args_app(sc, ExprSpec::Var(1), sargs, 0);
        crate::expr_model::subst_full_noop(f, sargs, 0);
        crate::expr_model::subst_full_noop(sc, sargs, 0);
        crate::expr_model::subst_full_noop(head_of4(sb), sargs, 0);
        let mk2 = head_of4(sb);
        let fsk = mk_app(mk_app(f, mk_app(sc, nk)), rk);
        let a1 = inst_args(arg1_of4(sb), sargs, 0);
        let a2 = inst_args(arg2_of4(sb), sargs, 0);
        let built = mk_app4(mk2, a1, a2, fsk, rk);
        assert(inst_args(sb, sargs, 0) == built);
        assert(spine_app(step, sargs) == mk_app(mk_app(step, nk), rk)) by {
            reveal_with_fuel(spine_app, 3);
        }
        let rn1 = mk_app(mk_app(step, nk), rk);
        assert(rn == mk_app4(rc, p, base, step, mk_app(sc, nk)));
        pstep_star_trans(ne, rn, rn1, built);
        spine_app4_parts(mk2, a1, a2, fsk, rk);
        crate::beta_model::pstep_star_iota(ne, 0, rn, mk2->Const_0, mk2->Const_1, seq![a1, a2, fsk, rk], 2);
        pstep_star_app_congr(ne, ExprSpec::Proj(0, Box::new(rn)), fsk, x);
        // `_f (succ k) r_k x` to `succ (r_k.0 x)`, then the induction
        add_f_succ(ne, f, nk, rk, x);
        let inner = mk_app(ExprSpec::Proj(0, Box::new(rk)), x);
        go_rec_add(ne, rid, rls, p, base, step, f, x, k);
        pstep_star_app_arg_congr(ne, sc, inner, succs(sid, k, x));
        pstep_star_trans(ne, e0, mk_app(fsk, x), mk_app(sc, inner));
        pstep_star_trans(ne, e0, mk_app(sc, inner), succs(sid, n, x));
    }
}

/// THE EXPORT DECLARES `Nat.add` AS LEAN DOES: its value, and the values of
/// `Nat.brecOn`, `Nat.brecOn.go`, `Nat.add._f`, `Nat.add.match_1` and
/// `Nat.casesOn` it reaches, are Lean's (binder types and type arguments
/// as exported), `Nat.rec`'s rules are Lean's, and `PProd.mk` takes two
/// parameters. Checkable on the declarations.
#[verifier::opaque]
pub open spec fn std_nat_add_env(ne: EnvSpec, add: u64) -> bool {
    let (zid, sid) = (crate::expr_arena_bridge::nat_zero_id(ne.export), crate::expr_arena_bridge::nat_succ_id(ne.export));
    let ab = spine_bind(ne[add].1, 2)->Some_0;
    let (brec, f) = (head_of4(ab), arg3_of4(ab));
    let go = brec_on_go_const(spine_bind(ne[brec->Const_0].1, 3)->Some_0);
    let gb = spine_bind(ne[go->Const_0].1, 3)->Some_0;
    let rc = head_of4(gb);
    &&& ne.contains_key(add) && ne[add].0.len() == 0 && std_nat_add(ne[add].1)
    &&& linked(ne, brec) && std_brec_on(ne[brec->Const_0].1)
    &&& linked(ne, go) && std_brec_on_go(ne[go->Const_0].1, zid, sid)
    &&& std_nat_rec(ne, rc->Const_0) && rc->Const_1.len() == 1
    &&& ne.ctor_num_params(head_of4(arg2_of4(gb))->Const_0) == Some(2u16)
    &&& ne.ctor_num_params(head_of4(lam_body(lam_body(arg3_of4(gb))))->Const_0) == Some(2u16)
    &&& add_f_links(ne, f)
}

/// `Nat.add` is defined where it is declared as Lean does.
pub proof fn std_nat_add_env_defined(ne: EnvSpec, add: u64)
    requires
        std_nat_add_env(ne, add),
    ensures
        ne.contains_key(add),
        ne.defs.contains_key(add),
{
    reveal(std_nat_add_env);
}

/// Numerals are closed.
pub proof fn numeral_closed(export: nat, e: ExprSpec)
    requires
        crate::beta_model::nat_value(export, e) is Some,
    ensures
        crate::expr_model::nlbv(e) == 0,
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        numeral_closed(export, *x);
    }
    reveal_with_fuel(crate::expr_model::nlbv, 3);
}

/// `Nat.add x y` ON NUMERALS REDUCES, WITHOUT FOLDING, TO THE CANONICAL
/// NUMERAL OF THE SUM.
#[verifier::spinoff_prover]
pub proof fn add_computes(ne: EnvSpec, add: u64, x: ExprSpec, y: ExprSpec)
    requires
        std_nat_add_env(ne, add),
        crate::beta_model::nat_value(ne.export, x) is Some,
        crate::beta_model::nat_value(ne.export, y) is Some,
    ensures
        pstep_star(ne, mk_app(mk_app(ExprSpec::Const(add, Seq::empty()), x), y),
            canon_numeral(ne.export, crate::beta_model::nat_value(ne.export, x)->Some_0 + crate::beta_model::nat_value(ne.export, y)->Some_0)),
{
    reveal(std_nat_add_env);
    let (zid, sid) = (crate::expr_arena_bridge::nat_zero_id(ne.export), crate::expr_arena_bridge::nat_succ_id(ne.export));
    let a = crate::beta_model::nat_value(ne.export, x)->Some_0;
    let b = crate::beta_model::nat_value(ne.export, y)->Some_0;
    let (na, nb) = (canon_numeral(ne.export, a), canon_numeral(ne.export, b));
    numeral_closed(ne.export, x);
    numeral_closed(ne.export, y);
    canon_numeral_closed(ne.export, a);
    canon_numeral_closed(ne.export, b);
    let ab = spine_bind(ne[add].1, 2)->Some_0;
    let (brec, m, f) = (head_of4(ab), arg1_of4(ab), arg3_of4(ab));
    let e0 = mk_app(mk_app(ExprSpec::Const(add, Seq::empty()), x), y);
    // `Nat.add x y` to `Nat.brecOn M y F x`
    add_unfold(ne, add, x, y);
    let e1 = mk_app(mk_app(mk_app(mk_app(brec, m), y), f), x);
    // `y` to its canonical numeral
    numeral_star(ne, y);
    pstep_star_app_arg_congr(ne, mk_app(brec, m), y, nb);
    pstep_star_app_congr(ne, mk_app(mk_app(brec, m), y), mk_app(mk_app(brec, m), nb), f);
    pstep_star_app_congr(ne, mk_app(mk_app(mk_app(brec, m), y), f), mk_app(mk_app(mk_app(brec, m), nb), f), x);
    let e2 = mk_app(mk_app(mk_app(mk_app(brec, m), nb), f), x);
    // `Nat.brecOn` to `(Nat.brecOn.go M nb F).0`
    assert(crate::expr_model::nlbv(f) == 0);
    brec_on_unfold(ne, brec->Const_0, brec->Const_1, m, nb, f);
    let go = brec_on_go_const(spine_bind(ne[brec->Const_0].1, 3)->Some_0);
    let gls = crate::level_model::subst_levels_spec(go->Const_1, ne[brec->Const_0].0, brec->Const_1);
    let gc = ExprSpec::Const(go->Const_0, gls);
    let gapp = mk_app(mk_app(mk_app(gc, m), nb), f);
    pstep_star_app_congr(ne, mk_app(mk_app(mk_app(brec, m), nb), f), ExprSpec::Proj(0, Box::new(gapp)), x);
    let e3 = mk_app(ExprSpec::Proj(0, Box::new(gapp)), x);
    // `Nat.brecOn.go` to `Nat.rec P BASE STEP nb`
    brec_on_go_unfold(ne, go->Const_0, gls, m, nb, f);
    let gb = spine_bind(ne[go->Const_0].1, 3)->Some_0;
    let r = inst_args(inst_levels(gb, ne[go->Const_0].0, gls), seq![m, nb, f], 0);
    pstep_star_proj_congr(ne, 0, gapp, r);
    pstep_star_app_congr(ne, ExprSpec::Proj(0, Box::new(gapp)), ExprSpec::Proj(0, Box::new(r)), x);
    let e4 = mk_app(ExprSpec::Proj(0, Box::new(r)), x);
    // the recursion: `b` successors of `x`
    let rc = head_of4(gb);
    let rls = crate::level_model::subst_levels_spec(rc->Const_1, ne[go->Const_0].0, gls);
    assert(r == mk_app4(ExprSpec::Const(rc->Const_0, rls), arg1_of4(r), arg2_of4(r), arg3_of4(r), nb));
    go_rec_add(ne, rc->Const_0, rls, arg1_of4(r), arg2_of4(r), arg3_of4(r), f, x, b);
    // `x` to its canonical numeral, under the successors
    numeral_star(ne, x);
    succs_star(ne, b, x, na);
    succs_canon(ne.export, b, a);
    pstep_star_trans(ne, e0, e1, e2);
    pstep_star_trans(ne, e0, e2, e3);
    pstep_star_trans(ne, e0, e3, e4);
    pstep_star_trans(ne, e0, e4, succs(sid, b, x));
    pstep_star_trans(ne, e0, succs(sid, b, x), canon_numeral(ne.export, a + b));
}

/// The fold-free environment declares `Nat.add` as the environment does.
pub proof fn std_nat_add_env_nofold(env: EnvSpec, add: u64)
    requires
        std_nat_add_env(env, add),
    ensures
        std_nat_add_env(nofold(env), add),
{
    reveal(std_nat_add_env);
    let ne = nofold(env);
    assert(forall|id: u64| #[trigger] ne.rec_data(id) == env.rec_data(id));
    assert(forall|id: u64| #[trigger] ne.ctor_num_params(id) == env.ctor_num_params(id));
    assert(ne.defs == env.defs && ne.export == env.export);
}

/// THE KERNEL'S `Nat.add` FOLD IS A CONVERSION OF THE DEFINITION: a ready
/// fold redex headed by `Nat.add` and its folded literal reduce, without
/// folding, to the same numeral.
#[verifier::spinoff_prover]
pub proof fn add_fold_joins(env: EnvSpec, add: u64, s: ExprSpec)
    requires
        std_nat_add_env(env, add),
        nat_fold_ready(env.export, s),
        spine_head(s) is Const && spine_head(s)->Const_0 == add,
        crate::expr_arena_bridge::nat_bin_op_of(env.export, add) == Some(0u8),
    ensures ({
        let args = spine_args(s);
        let c = canon_numeral(env.export, crate::beta_model::nat_value(env.export, args[0])->Some_0
            + crate::beta_model::nat_value(env.export, args[1])->Some_0);
        &&& pstep_star(nofold(env), s, c)
        &&& pstep_star(nofold(env), nat_fold_result(env.export, s), c)
    }),
{
    let ne = nofold(env);
    std_nat_add_env_nofold(env, add);
    let args = spine_args(s);
    let lv = spine_head(s)->Const_1;
    assert(lv =~= Seq::<crate::level_model::LevelSpec>::empty());
    let (x, y) = (args[0], args[1]);
    assert(s == mk_app(mk_app(ExprSpec::Const(add, Seq::empty()), x), y)) by {
        crate::beta_model::spine_recompose(s);
        reveal_with_fuel(spine_app, 3);
    }
    add_computes(ne, add, x, y);
    let a = crate::beta_model::nat_value(env.export, x)->Some_0;
    let b = crate::beta_model::nat_value(env.export, y)->Some_0;
    assert(nat_fold_result(env.export, s) == ExprSpec::NatLit(crate::expr_model::NatLitPayload(Ghost(a + b))));
    lit_star(ne, a + b);
}

/// THE NAT EXTENSION AGREES WITH THE DEFINITIONS (`nat_ext::h_nat_ext`)
/// where the only defined Nat operation is `Nat.add`, declared as Lean
/// does: its fold joins the definition (`add_fold_joins`), and an operation
/// that is no definition folds in the fold-free environment too.
pub proof fn h_nat_ext_of(env: EnvSpec)
    requires
        forall|id: u64| #[trigger] crate::expr_arena_bridge::nat_bin_op_of(env.export, id) is Some && env.defs.contains_key(id)
            ==> crate::expr_arena_bridge::nat_bin_op_of(env.export, id) == Some(0u8) && std_nat_add_env(env, id),
    ensures
        crate::nat_ext::h_nat_ext(env),
{
    let ne = nofold(env);
    assert forall|s: ExprSpec| #[trigger] nat_fold_ready(env.export, s) implies defeq(ne, s, nat_fold_result(env.export, s)) by {
        let id = spine_head(s)->Const_0;
        let r = nat_fold_result(env.export, s);
        if env.defs.contains_key(id) {
            add_fold_joins(env, id, s);
            let args = spine_args(s);
            let c = canon_numeral(env.export, crate::beta_model::nat_value(env.export, args[0])->Some_0
                + crate::beta_model::nat_value(env.export, args[1])->Some_0);
            assert(pstep_star(ne, s, c) && pstep_star(ne, r, c));
        } else {
            // `s` is `op x y`: the fold fires in the fold-free environment
            let (f, a) = (*s->App_0, *s->App_1);
            assert(fold_on(ne, ExprSpec::App(Box::new(f), Box::new(a))));
            assert(pstep(ne, f, f) && pstep(ne, a, a));
            assert(fold_reduct(f, a));
            assert(s == ExprSpec::App(Box::new(f), Box::new(a)));
            assert(pstep(ne, s, r));
            pstep_star_one(ne, s, r);
            pstep_star_refl(ne, r);
        }
    }
}

/// The canonical numeral `succ^k zero`.
pub open spec fn canon_numeral(export: nat, k: nat) -> ExprSpec
    decreases k,
{
    if k == 0 {
        const_expr_no_levels(crate::expr_arena_bridge::nat_zero_id(export))
    } else {
        ExprSpec::App(Box::new(const_expr_no_levels(crate::expr_arena_bridge::nat_succ_id(export))), Box::new(canon_numeral(export, (k - 1) as nat)))
    }
}

/// A numeral (a literal, `Nat.zero`, or `Nat.succ` of a numeral) reduces,
/// without folding, to the canonical numeral of its value.
pub proof fn numeral_star(ne: EnvSpec, e: ExprSpec)
    requires
        crate::beta_model::nat_value(ne.export, e) is Some,
    ensures
        pstep_star(ne, e, canon_numeral(ne.export, crate::beta_model::nat_value(ne.export, e)->Some_0)),
    decreases e, crate::beta_model::nat_value(ne.export, e)->Some_0,
{
    let k = crate::beta_model::nat_value(ne.export, e)->Some_0;
    match e {
        ExprSpec::NatLit(n) => {
            if n.0@ == 0 {
                assert(pstep(ne, e, canon_numeral(ne.export, 0)));
                pstep_star_one(ne, e, canon_numeral(ne.export, 0));
            } else {
                let p = ExprSpec::NatLit(crate::expr_model::NatLitPayload(Ghost((n.0@ - 1) as nat)));
                let succ = const_expr_no_levels(crate::expr_arena_bridge::nat_succ_id(ne.export));
                let e1 = ExprSpec::App(Box::new(succ), Box::new(p));
                assert(pstep(ne, e, e1));
                pstep_star_one(ne, e, e1);
                assert(crate::beta_model::nat_value(ne.export, p) == Some((n.0@ - 1) as nat));
                lit_star(ne, (n.0@ - 1) as nat);
                pstep_star_app_arg_congr(ne, succ, p, canon_numeral(ne.export, (n.0@ - 1) as nat));
                pstep_star_trans(ne, e, e1, canon_numeral(ne.export, k));
            }
        },
        ExprSpec::App(f, x) => {
            if let ExprSpec::Const(_, ls) = *f {
                assert(ls =~= Seq::<crate::level_model::LevelSpec>::empty());
            }
            numeral_star(ne, *x);
            pstep_star_app_arg_congr(ne, *f, *x, canon_numeral(ne.export, (k - 1) as nat));
        },
        _ => {
            if let ExprSpec::Const(_, ls) = e {
                assert(ls =~= Seq::<crate::level_model::LevelSpec>::empty());
            }
            pstep_star_refl(ne, e);
        },
    }
}

/// A literal reduces to its canonical numeral.
pub proof fn lit_star(ne: EnvSpec, v: nat)
    ensures
        pstep_star(ne, ExprSpec::NatLit(crate::expr_model::NatLitPayload(Ghost(v))), canon_numeral(ne.export, v)),
    decreases v,
{
    let e = ExprSpec::NatLit(crate::expr_model::NatLitPayload(Ghost(v)));
    if v == 0 {
        assert(pstep(ne, e, canon_numeral(ne.export, 0)));
        pstep_star_one(ne, e, canon_numeral(ne.export, 0));
    } else {
        let p = ExprSpec::NatLit(crate::expr_model::NatLitPayload(Ghost((v - 1) as nat)));
        let succ = const_expr_no_levels(crate::expr_arena_bridge::nat_succ_id(ne.export));
        let e1 = ExprSpec::App(Box::new(succ), Box::new(p));
        assert(pstep(ne, e, e1));
        pstep_star_one(ne, e, e1);
        lit_star(ne, (v - 1) as nat);
        pstep_star_app_arg_congr(ne, succ, p, canon_numeral(ne.export, (v - 1) as nat));
        pstep_star_trans(ne, e, e1, canon_numeral(ne.export, v));
    }
}

} // verus!
