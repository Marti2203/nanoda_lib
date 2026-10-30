//! NAT.BLE COMPUTES. As `nat_add` for `Nat.add`: where the export declares
//! `Nat.ble` as Lean does (structural recursion on its first argument
//! through `Nat.brecOn`, a double case split in `Nat.ble.match_1`), the
//! kernel's fold of `Nat.ble x y` on numerals is a conversion of the
//! definition: the redex reduces, without folding, to `Bool.true` or
//! `Bool.false` as `x <= y`.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::beta_model::*;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::nat_add::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `Nat.ble`'s body under its two binders: `Nat.brecOn M x Nat.ble._f y`
/// (`x` is `#1`, `y` is `#0`): the recursion is on the first argument.
pub open spec fn ble_body(brec: ExprSpec, m: ExprSpec, f: ExprSpec) -> ExprSpec {
    mk_app(mk_app(mk_app(mk_app(brec, m), ExprSpec::Var(1)), f), ExprSpec::Var(0))
}

/// `Nat.ble`'s value is Lean's.
pub open spec fn std_nat_ble(v: ExprSpec) -> bool {
    spine_bind(v, 2) is Some && {
        let b = spine_bind(v, 2)->Some_0;
        let (brec, m, f) = (head_of4(b), arg1_of4(b), arg3_of4(b));
        &&& b == ble_body(brec, m, f)
        &&& brec is Const && f is Const
        &&& crate::expr_model::nlbv(m) == 0
    }
}

/// `Nat.ble x y` unfolds to `Nat.brecOn M x Nat.ble._f y`.
#[verifier::spinoff_prover]
pub proof fn ble_unfold(ne: EnvSpec, ble: u64, x: ExprSpec, y: ExprSpec)
    requires
        ne.contains_key(ble),
        ne[ble].0.len() == 0,
        std_nat_ble(ne[ble].1),
        crate::expr_model::nlbv(x) == 0,
        crate::expr_model::nlbv(y) == 0,
    ensures ({
        let b = spine_bind(ne[ble].1, 2)->Some_0;
        pstep_star(ne, mk_app(mk_app(ExprSpec::Const(ble, Seq::empty()), x), y),
            mk_app(mk_app(mk_app(mk_app(head_of4(b), arg1_of4(b)), x), arg3_of4(b)), y))
    }),
{
    let v = ne[ble].1;
    let b = spine_bind(v, 2)->Some_0;
    let (brec, m, f) = (head_of4(b), arg1_of4(b), arg3_of4(b));
    assert(ne[ble].0 =~= Seq::<u64>::empty());
    crate::expr_model::subst_expr_levels_empty(v);
    let args = seq![x, y];
    assert(spine_app(ExprSpec::Const(ble, Seq::empty()), args) == mk_app(mk_app(ExprSpec::Const(ble, Seq::empty()), x), y)) by {
        reveal_with_fuel(spine_app, 3);
    }
    assert(crate::expr_model::nlbv(b) <= 2) by {
        reveal_with_fuel(crate::expr_model::nlbv, 6);
    }
    delta_beta(ne, ble, Seq::empty(), args, b);
    crate::expr_model::subst_full_noop(m, args, 0);
    crate::expr_model::subst_full_noop(brec, args, 0);
    crate::expr_model::subst_full_noop(f, args, 0);
    assert(crate::expr_model::subst_full(b, args, 0) == mk_app(mk_app(mk_app(mk_app(brec, m), x), f), y)) by {
        reveal_with_fuel(crate::expr_model::subst_full, 6);
    }
}

pub open spec fn mk_app7(h: ExprSpec, a: ExprSpec, b: ExprSpec, c: ExprSpec, d: ExprSpec, e: ExprSpec, f: ExprSpec, g: ExprSpec) -> ExprSpec {
    mk_app(mk_app6(h, a, b, c, d, e, f), g)
}

/// A constant case: `λ _ _. c`.
pub open spec fn const_case(x: ExprSpec, c: ExprSpec) -> bool {
    x == mk_lam(lam_type(x), mk_lam(lam_type(lam_body(x)), c))
}

/// `Nat.ble._f`'s third case: `λ n m b. b.0 m`.
pub open spec fn ble_rec_case(x: ExprSpec) -> bool {
    x == mk_lam(lam_type(x), mk_lam(lam_type(lam_body(x)), mk_lam(lam_type(lam_body(lam_body(x))),
        mk_app(ExprSpec::Proj(0, Box::new(ExprSpec::Var(0))), ExprSpec::Var(1)))))
}

/// The parts of `Nat.ble._f`'s body read off it: the seven-argument call
/// `Nat.ble.match_1 mot t z H1 H2 H3 below`.
pub open spec fn blef_call(b: ExprSpec) -> ExprSpec { fun_of(fun_of(fun_of(b))) }

/// `Nat.ble._f`'s value is Lean's: under its three binders (major `#2`,
/// below `#1`, the other operand `#0`),
/// `Nat.ble.match_1 mot #2 #0 (λ _ _. true) (λ _ _. false) (λ n m b. b.0 m) #1`.
pub open spec fn std_ble_f(v: ExprSpec, tid: u64, fid: u64) -> bool {
    spine_bind(v, 3) is Some && {
        let b = spine_bind(v, 3)->Some_0;
        let c = blef_call(b);
        &&& b == mk_app7(head_of4(c), arg1_of4(c), ExprSpec::Var(2), ExprSpec::Var(0), arg4_of4(c),
            arg_of(fun_of(fun_of(b))), arg_of(fun_of(b)), ExprSpec::Var(1))
        &&& head_of4(c) is Const
        &&& crate::expr_model::nlbv(arg1_of4(c)) == 0
        &&& const_case(arg4_of4(c), const_expr_no_levels(tid))
        &&& const_case(arg_of(fun_of(fun_of(b))), const_expr_no_levels(fid))
        &&& ble_rec_case(arg_of(fun_of(b)))
    }
}

/// `Nat.ble.match_1`'s value is Lean's: under its six binders (motive
/// `#5`, `x` `#4`, `y` `#3`, the cases `#2`, `#1`, `#0`),
/// `Nat.casesOn mot x (h1 y) (λ n. Nat.casesOn mot' y (h2 n) (λ m. h3 n m))`.
pub open spec fn std_ble_match(v: ExprSpec) -> bool {
    spine_bind(v, 6) is Some && {
        let b = spine_bind(v, 6)->Some_0;
        let outer = arg4_of4(b);
        let inner = lam_body(outer);
        let last = arg4_of4(inner);
        &&& b == mk_app4(head_of4(b), arg1_of4(b), ExprSpec::Var(4), mk_app(ExprSpec::Var(2), ExprSpec::Var(3)),
            mk_lam(lam_type(outer), mk_app4(head_of4(inner), arg1_of4(inner), ExprSpec::Var(4),
                mk_app(ExprSpec::Var(2), ExprSpec::Var(0)),
                mk_lam(lam_type(last), mk_app(mk_app(ExprSpec::Var(2), ExprSpec::Var(1)), ExprSpec::Var(0))))))
        &&& head_of4(b) is Const && head_of4(inner) is Const
        &&& head_of4(b)->Const_0 == head_of4(inner)->Const_0 && head_of4(b)->Const_1 == head_of4(inner)->Const_1
    }
}

pub proof fn inst_levels_app7(h: ExprSpec, a: ExprSpec, b: ExprSpec, c: ExprSpec, d: ExprSpec, e: ExprSpec, f: ExprSpec, g: ExprSpec, ks: Seq<u64>, vs: Seq<crate::level_model::LevelSpec>)
    ensures inst_levels(mk_app7(h, a, b, c, d, e, f, g), ks, vs) == mk_app7(inst_levels(h, ks, vs), inst_levels(a, ks, vs), inst_levels(b, ks, vs),
        inst_levels(c, ks, vs), inst_levels(d, ks, vs), inst_levels(e, ks, vs), inst_levels(f, ks, vs), inst_levels(g, ks, vs)),
{
    inst_levels_app(mk_app6(h, a, b, c, d, e, f), g, ks, vs);
    inst_levels_app6(h, a, b, c, d, e, f, ks, vs);
}

pub proof fn inst_args_app7(h: ExprSpec, a: ExprSpec, b: ExprSpec, c: ExprSpec, d: ExprSpec, e: ExprSpec, f: ExprSpec, g: ExprSpec, args: Seq<ExprSpec>, k: nat)
    ensures inst_args(mk_app7(h, a, b, c, d, e, f, g), args, k) == mk_app7(inst_args(h, args, k), inst_args(a, args, k), inst_args(b, args, k),
        inst_args(c, args, k), inst_args(d, args, k), inst_args(e, args, k), inst_args(f, args, k), inst_args(g, args, k)),
{
    inst_args_app(mk_app6(h, a, b, c, d, e, f), g, args, k);
    inst_args_app6(h, a, b, c, d, e, f, args, k);
}

/// A constant case keeps its shape under level and argument substitution
/// (its body a closed constant without levels).
pub proof fn const_case_inst(x: ExprSpec, cid: u64, ks: Seq<u64>, vs: Seq<crate::level_model::LevelSpec>, args: Seq<ExprSpec>, k: nat)
    requires
        const_case(x, const_expr_no_levels(cid)),
    ensures
        const_case(inst_args(inst_levels(x, ks, vs), args, k), const_expr_no_levels(cid)),
{
    let c = const_expr_no_levels(cid);
    let (t1, t2) = (lam_type(x), lam_type(lam_body(x)));
    inst_levels_lam(t1, mk_lam(t2, c), ks, vs);
    inst_levels_lam(t2, c, ks, vs);
    levels_const_nil(cid, ks, vs);
    inst_args_lam(inst_levels(t1, ks, vs), mk_lam(inst_levels(t2, ks, vs), c), args, k);
    inst_args_lam(inst_levels(t2, ks, vs), c, args, k + 1);
    crate::expr_model::subst_full_noop(c, args, k + 2);
}

/// So does the recursive case (its body bound variables only).
pub proof fn ble_rec_case_inst(x: ExprSpec, ks: Seq<u64>, vs: Seq<crate::level_model::LevelSpec>, args: Seq<ExprSpec>, k: nat)
    requires
        ble_rec_case(x),
    ensures
        ble_rec_case(inst_args(inst_levels(x, ks, vs), args, k)),
{
    let (t1, t2, t3) = (lam_type(x), lam_type(lam_body(x)), lam_type(lam_body(lam_body(x))));
    let pr = ExprSpec::Proj(0, Box::new(ExprSpec::Var(0)));
    let body = mk_app(pr, ExprSpec::Var(1));
    inst_levels_lam(t1, mk_lam(t2, mk_lam(t3, body)), ks, vs);
    inst_levels_lam(t2, mk_lam(t3, body), ks, vs);
    inst_levels_lam(t3, body, ks, vs);
    inst_levels_app(pr, ExprSpec::Var(1), ks, vs);
    assert(inst_levels(ExprSpec::Var(0), ks, vs) == ExprSpec::Var(0));
    assert(inst_levels(pr, ks, vs) == pr);
    inst_args_lam(inst_levels(t1, ks, vs), mk_lam(inst_levels(t2, ks, vs), mk_lam(inst_levels(t3, ks, vs), body)), args, k);
    inst_args_lam(inst_levels(t2, ks, vs), mk_lam(inst_levels(t3, ks, vs), body), args, k + 1);
    inst_args_lam(inst_levels(t3, ks, vs), body, args, k + 2);
    inst_args_app(pr, ExprSpec::Var(1), args, k + 3);
    assert(inst_args(ExprSpec::Var(0), args, k + 3) == ExprSpec::Var(0));
    assert(inst_args(pr, args, k + 3) == pr);
}

/// `Nat.ble._f t below z` unfolds to
/// `Nat.ble.match_1 mot t z H1 H2 H3 below`.
#[verifier::spinoff_prover]
pub proof fn ble_f_unfold(ne: EnvSpec, id: u64, ls: Seq<crate::level_model::LevelSpec>, t: ExprSpec, below: ExprSpec, z: ExprSpec)
    requires
        ne.contains_key(id),
        ne[id].0.len() == ls.len(),
        std_ble_f(ne[id].1, crate::expr_arena_bridge::bool_true_id(ne.export), crate::expr_arena_bridge::bool_false_id(ne.export)),
        crate::expr_model::nlbv(ne[id].1) == 0,
        crate::expr_model::nlbv(t) == 0 && crate::expr_model::nlbv(below) == 0 && crate::expr_model::nlbv(z) == 0,
    ensures ({
        let (tid, fid) = (crate::expr_arena_bridge::bool_true_id(ne.export), crate::expr_arena_bridge::bool_false_id(ne.export));
        let b = spine_bind(ne[id].1, 3)->Some_0;
        let c = blef_call(b);
        let args = seq![t, below, z];
        let (ks, vs) = (ne[id].0, ls);
        let (h1, h2, h3) = (inst_args(inst_levels(arg4_of4(c), ks, vs), args, 0), inst_args(inst_levels(arg_of(fun_of(fun_of(b))), ks, vs), args, 0),
            inst_args(inst_levels(arg_of(fun_of(b)), ks, vs), args, 0));
        let r = mk_app7(ExprSpec::Const(head_of4(c)->Const_0, crate::level_model::subst_levels_spec(head_of4(c)->Const_1, ks, vs)),
            inst_args(inst_levels(arg1_of4(c), ks, vs), args, 0), t, z, h1, h2, h3, below);
        &&& pstep_star(ne, mk_app(mk_app(mk_app(ExprSpec::Const(id, ls), t), below), z), r)
        &&& const_case(h1, const_expr_no_levels(tid)) && const_case(h2, const_expr_no_levels(fid)) && ble_rec_case(h3)
        &&& crate::expr_model::nlbv(h1) == 0 && crate::expr_model::nlbv(h2) == 0 && crate::expr_model::nlbv(h3) == 0
        &&& crate::expr_model::nlbv(inst_args(inst_levels(arg1_of4(c), ks, vs), args, 0)) == 0
    }),
{
    let (tid, fid) = (crate::expr_arena_bridge::bool_true_id(ne.export), crate::expr_arena_bridge::bool_false_id(ne.export));
    let v = ne[id].1;
    let b = spine_bind(v, 3)->Some_0;
    let c = blef_call(b);
    let (h, mot, x1, x2, x3) = (head_of4(c), arg1_of4(c), arg4_of4(c), arg_of(fun_of(fun_of(b))), arg_of(fun_of(b)));
    let (ks, vs) = (ne[id].0, ls);
    let args = seq![t, below, z];
    levels_spine_bind(v, 3, ks, vs);
    crate::beta_model::spine_bind_nlbv(v, 3, b, 0);
    crate::ti_level::ls_nlbv(b, ks, vs);
    inst_levels_app7(h, mot, ExprSpec::Var(2), ExprSpec::Var(0), x1, x2, x3, ExprSpec::Var(1), ks, vs);
    let b2 = inst_levels(b, ks, vs);
    inst_args_app7(inst_levels(h, ks, vs), inst_levels(mot, ks, vs), ExprSpec::Var(2), ExprSpec::Var(0), inst_levels(x1, ks, vs),
        inst_levels(x2, ks, vs), inst_levels(x3, ks, vs), ExprSpec::Var(1), args, 0);
    crate::expr_model::subst_full_noop(inst_levels(h, ks, vs), args, 0);
    crate::ti_level::ls_nlbv(mot, ks, vs);
    crate::expr_model::subst_full_noop(inst_levels(mot, ks, vs), args, 0);
    const_case_inst(x1, tid, ks, vs, args, 0);
    const_case_inst(x2, fid, ks, vs, args, 0);
    ble_rec_case_inst(x3, ks, vs, args, 0);
    spine_app3_parts(ExprSpec::Const(id, ls), t, below, z);
    delta_beta(ne, id, ls, args, b2);
    assert(crate::expr_model::nlbv(x1) <= 3 && crate::expr_model::nlbv(x2) <= 3 && crate::expr_model::nlbv(x3) <= 3) by {
        reveal_with_fuel(crate::expr_model::nlbv, 8);
    }
    crate::ti_level::ls_nlbv(x1, ks, vs);
    crate::ti_level::ls_nlbv(x2, ks, vs);
    crate::ti_level::ls_nlbv(x3, ks, vs);
    crate::beta_model::subst_full_nlbv_bound_n(inst_levels(x1, ks, vs), args, 0);
    crate::beta_model::subst_full_nlbv_bound_n(inst_levels(x2, ks, vs), args, 0);
    crate::beta_model::subst_full_nlbv_bound_n(inst_levels(x3, ks, vs), args, 0);
}

/// The inner case split of `Nat.ble.match_1` (under the outer case's
/// binder): at the arguments, `Nat.casesOn mot2 y (h2 n) (λ m. h3 n m)`.
#[verifier::spinoff_prover]
pub proof fn ble_match_inner(hc: ExprSpec, mot2: ExprSpec, t1: ExprSpec, ks: Seq<u64>, vs: Seq<crate::level_model::LevelSpec>,
    args: Seq<ExprSpec>)
    requires
        hc is Const,
        args.len() == 6,
    ensures ({
        let lastb = mk_app(mk_app(ExprSpec::Var(2), ExprSpec::Var(1)), ExprSpec::Var(0));
        let innerb = mk_app4(hc, mot2, ExprSpec::Var(4), mk_app(ExprSpec::Var(2), ExprSpec::Var(0)), mk_lam(t1, lastb));
        let hl = inst_levels(hc, ks, vs);
        inst_args(inst_levels(innerb, ks, vs), args, 1) == mk_app4(hl, inst_args(inst_levels(mot2, ks, vs), args, 1), args[2],
            mk_app(args[4], ExprSpec::Var(0)), mk_lam(inst_args(inst_levels(t1, ks, vs), args, 1), mk_app(mk_app(args[5], ExprSpec::Var(1)), ExprSpec::Var(0))))
    }),
{
    let lastb = mk_app(mk_app(ExprSpec::Var(2), ExprSpec::Var(1)), ExprSpec::Var(0));
    inst_levels_app4(hc, mot2, ExprSpec::Var(4), mk_app(ExprSpec::Var(2), ExprSpec::Var(0)), mk_lam(t1, lastb), ks, vs);
    inst_levels_app(ExprSpec::Var(2), ExprSpec::Var(0), ks, vs);
    inst_levels_lam(t1, lastb, ks, vs);
    inst_levels_app(mk_app(ExprSpec::Var(2), ExprSpec::Var(1)), ExprSpec::Var(0), ks, vs);
    inst_levels_app(ExprSpec::Var(2), ExprSpec::Var(1), ks, vs);
    let hl = inst_levels(hc, ks, vs);
    inst_args_app4(hl, inst_levels(mot2, ks, vs), ExprSpec::Var(4), mk_app(ExprSpec::Var(2), ExprSpec::Var(0)), mk_lam(inst_levels(t1, ks, vs), lastb), args, 1);
    inst_args_app(ExprSpec::Var(2), ExprSpec::Var(0), args, 1);
    inst_args_lam(inst_levels(t1, ks, vs), lastb, args, 1);
    inst_args_app(mk_app(ExprSpec::Var(2), ExprSpec::Var(1)), ExprSpec::Var(0), args, 2);
    inst_args_app(ExprSpec::Var(2), ExprSpec::Var(1), args, 2);
    crate::expr_model::subst_full_noop(hl, args, 1);
}

/// `Nat.ble.match_1 mot x y h1 h2 h3` unfolds to
/// `Nat.casesOn mot1 x (h1 y) (λ n. Nat.casesOn mot2 y (h2 n) (λ m. h3 n m))`.
#[verifier::spinoff_prover]
pub proof fn ble_match_unfold(ne: EnvSpec, id: u64, ls: Seq<crate::level_model::LevelSpec>, mot: ExprSpec, x: ExprSpec, y: ExprSpec,
    h1: ExprSpec, h2: ExprSpec, h3: ExprSpec)
    requires
        ne.contains_key(id),
        ne[id].0.len() == ls.len(),
        std_ble_match(ne[id].1),
        crate::expr_model::nlbv(ne[id].1) == 0,
        crate::expr_model::nlbv(mot) == 0 && crate::expr_model::nlbv(x) == 0 && crate::expr_model::nlbv(y) == 0
            && crate::expr_model::nlbv(h1) == 0 && crate::expr_model::nlbv(h2) == 0 && crate::expr_model::nlbv(h3) == 0,
    ensures ({
        let b = spine_bind(ne[id].1, 6)->Some_0;
        let outer = arg4_of4(b);
        let inner = lam_body(outer);
        let args = seq![mot, x, y, h1, h2, h3];
        let (ks, vs) = (ne[id].0, ls);
        let cc = inst_levels(head_of4(b), ks, vs);
        let succ_case = mk_lam(inst_args(inst_levels(lam_type(outer), ks, vs), args, 0),
            mk_app4(cc, inst_args(inst_levels(arg1_of4(inner), ks, vs), args, 1), y, mk_app(h2, ExprSpec::Var(0)),
                mk_lam(inst_args(inst_levels(lam_type(arg4_of4(inner)), ks, vs), args, 1), mk_app(mk_app(h3, ExprSpec::Var(1)), ExprSpec::Var(0)))));
        let r = mk_app4(cc, inst_args(inst_levels(arg1_of4(b), ks, vs), args, 0), x, mk_app(h1, y), succ_case);
        &&& pstep_star(ne, mk_app(mk_app(mk_app4(ExprSpec::Const(id, ls), mot, x, y, h1), h2), h3), r)
        &&& cc == ExprSpec::Const(head_of4(b)->Const_0, crate::level_model::subst_levels_spec(head_of4(b)->Const_1, ks, vs))
    }),
{
    let v = ne[id].1;
    let b = spine_bind(v, 6)->Some_0;
    let outer = arg4_of4(b);
    let inner = lam_body(outer);
    let last = arg4_of4(inner);
    let (ks, vs) = (ne[id].0, ls);
    let args = seq![mot, x, y, h1, h2, h3];
    let (h, mot1, t0, mot2, t1) = (head_of4(b), arg1_of4(b), lam_type(outer), arg1_of4(inner), lam_type(last));
    let lastb = mk_app(mk_app(ExprSpec::Var(2), ExprSpec::Var(1)), ExprSpec::Var(0));
    let innerb = mk_app4(h, mot2, ExprSpec::Var(4), mk_app(ExprSpec::Var(2), ExprSpec::Var(0)), mk_lam(t1, lastb));
    levels_spine_bind(v, 6, ks, vs);
    crate::beta_model::spine_bind_nlbv(v, 6, b, 0);
    crate::ti_level::ls_nlbv(b, ks, vs);
    inst_levels_app4(h, mot1, ExprSpec::Var(4), mk_app(ExprSpec::Var(2), ExprSpec::Var(3)), mk_lam(t0, innerb), ks, vs);
    inst_levels_app(ExprSpec::Var(2), ExprSpec::Var(3), ks, vs);
    inst_levels_lam(t0, innerb, ks, vs);
    let hl = inst_levels(h, ks, vs);
    let b2 = inst_levels(b, ks, vs);
    inst_args_app4(hl, inst_levels(mot1, ks, vs), ExprSpec::Var(4), mk_app(ExprSpec::Var(2), ExprSpec::Var(3)), mk_lam(inst_levels(t0, ks, vs), inst_levels(innerb, ks, vs)), args, 0);
    inst_args_app(ExprSpec::Var(2), ExprSpec::Var(3), args, 0);
    inst_args_lam(inst_levels(t0, ks, vs), inst_levels(innerb, ks, vs), args, 0);
    ble_match_inner(h, mot2, t1, ks, vs, args);
    crate::expr_model::subst_full_noop(hl, args, 0);
    assert(spine_app(ExprSpec::Const(id, ls), args) == mk_app(mk_app(mk_app4(ExprSpec::Const(id, ls), mot, x, y, h1), h2), h3)) by {
        reveal_with_fuel(spine_app, 7);
    }
    delta_beta(ne, id, ls, args, b2);
}

/// The unfolded `Nat.ble.match_1`'s motive and successor case are closed.
#[verifier::spinoff_prover]
pub proof fn ble_match_closed(ne: EnvSpec, id: u64, ls: Seq<crate::level_model::LevelSpec>, args: Seq<ExprSpec>)
    requires
        std_ble_match(ne[id].1),
        crate::expr_model::nlbv(ne[id].1) == 0,
        args.len() == 6,
        forall|i: int| 0 <= i < 6 ==> crate::expr_model::nlbv(#[trigger] args[i]) == 0,
    ensures ({
        let b = spine_bind(ne[id].1, 6)->Some_0;
        let outer = arg4_of4(b);
        let inner = lam_body(outer);
        let (ks, vs) = (ne[id].0, ls);
        let cc = inst_levels(head_of4(b), ks, vs);
        let succ_case = mk_lam(inst_args(inst_levels(lam_type(outer), ks, vs), args, 0),
            mk_app4(cc, inst_args(inst_levels(arg1_of4(inner), ks, vs), args, 1), args[2], mk_app(args[4], ExprSpec::Var(0)),
                mk_lam(inst_args(inst_levels(lam_type(arg4_of4(inner)), ks, vs), args, 1), mk_app(mk_app(args[5], ExprSpec::Var(1)), ExprSpec::Var(0)))));
        &&& crate::expr_model::nlbv(inst_args(inst_levels(arg1_of4(b), ks, vs), args, 0)) == 0
        &&& crate::expr_model::nlbv(succ_case) == 0
    }),
{
    let v = ne[id].1;
    let b = spine_bind(v, 6)->Some_0;
    let outer = arg4_of4(b);
    let inner = lam_body(outer);
    let (ks, vs) = (ne[id].0, ls);
    let (mot1, t0, mot2, t1) = (arg1_of4(b), lam_type(outer), arg1_of4(inner), lam_type(arg4_of4(inner)));
    crate::beta_model::spine_bind_nlbv(v, 6, b, 0);
    assert(crate::expr_model::nlbv(mot1) <= 6 && crate::expr_model::nlbv(t0) <= 6 && crate::expr_model::nlbv(mot2) <= 7
        && crate::expr_model::nlbv(t1) <= 7) by {
        reveal_with_fuel(crate::expr_model::nlbv, 8);
    }
    crate::ti_level::ls_nlbv(mot1, ks, vs);
    crate::ti_level::ls_nlbv(t0, ks, vs);
    crate::ti_level::ls_nlbv(mot2, ks, vs);
    crate::ti_level::ls_nlbv(t1, ks, vs);
    crate::beta_model::subst_full_nlbv_bound_n(inst_levels(mot1, ks, vs), args, 0);
    crate::beta_model::subst_full_nlbv_bound_n(inst_levels(t0, ks, vs), args, 0);
    crate::beta_model::subst_full_nlbv_bound_n(inst_levels(mot2, ks, vs), args, 1);
    crate::beta_model::subst_full_nlbv_bound_n(inst_levels(t1, ks, vs), args, 1);
    let cc = inst_levels(head_of4(b), ks, vs);
    assert(crate::expr_model::nlbv(cc) == 0);
    reveal_with_fuel(crate::expr_model::nlbv, 8);
}

/// The constant `Nat.ble._f`'s body calls (`Nat.ble.match_1`) and the one
/// that calls (`Nat.casesOn`).
pub open spec fn blef_match(ne: EnvSpec, fid: u64) -> ExprSpec {
    head_of4(blef_call(spine_bind(ne[fid].1, 3)->Some_0))
}

pub open spec fn blem_cases(ne: EnvSpec, mid: u64) -> ExprSpec {
    head_of4(spine_bind(ne[mid].1, 6)->Some_0)
}

/// `f` is Lean's `Nat.ble._f`, and the definitions it reaches are Lean's.
pub open spec fn ble_f_links(ne: EnvSpec, f: ExprSpec) -> bool {
    let (tid, fid) = (crate::expr_arena_bridge::bool_true_id(ne.export), crate::expr_arena_bridge::bool_false_id(ne.export));
    let m = blef_match(ne, f->Const_0);
    let c = blem_cases(ne, m->Const_0);
    let r = cases_rec(ne, c->Const_0);
    &&& linked(ne, f) && std_ble_f(ne[f->Const_0].1, tid, fid)
    &&& linked(ne, m) && std_ble_match(ne[m->Const_0].1)
    &&& linked(ne, c) && std_cases_on(ne[c->Const_0].1)
    &&& std_nat_rec(ne, r->Const_0) && r->Const_1.len() == 1
}

/// The pieces `Nat.ble._f t below z` reduces to.
pub ghost struct BleCases {
    pub cc: ExprSpec,
    pub mot1: ExprSpec,
    pub h1: ExprSpec,
    pub h2: ExprSpec,
    pub h3: ExprSpec,
    pub t0: ExprSpec,
    pub mot2: ExprSpec,
    pub t1: ExprSpec,
}

impl BleCases {
    pub open spec fn succ_case(self, z: ExprSpec) -> ExprSpec {
        mk_lam(self.t0, mk_app4(self.cc, self.mot2, z, mk_app(self.h2, ExprSpec::Var(0)),
            mk_lam(self.t1, mk_app(mk_app(self.h3, ExprSpec::Var(1)), ExprSpec::Var(0)))))
    }
}

/// `Nat.ble._f t below z` reduces to
/// `Nat.casesOn mot1 t (h1 z) (λ n. Nat.casesOn mot2 z (h2 n) (λ m. h3 n m)) below`,
/// the cases Lean's and every piece closed.
#[verifier::spinoff_prover]
pub proof fn ble_f_cases(ne: EnvSpec, f: ExprSpec, t: ExprSpec, below: ExprSpec, z: ExprSpec) -> (r: BleCases)
    requires
        ble_f_links(ne, f),
        crate::expr_model::nlbv(t) == 0 && crate::expr_model::nlbv(below) == 0 && crate::expr_model::nlbv(z) == 0,
    ensures
        pstep_star(ne, mk_app(mk_app(mk_app(f, t), below), z), mk_app(mk_app4(r.cc, r.mot1, t, mk_app(r.h1, z), r.succ_case(z)), below)),
        const_case(r.h1, const_expr_no_levels(crate::expr_arena_bridge::bool_true_id(ne.export))),
        const_case(r.h2, const_expr_no_levels(crate::expr_arena_bridge::bool_false_id(ne.export))),
        ble_rec_case(r.h3),
        crate::expr_model::nlbv(r.h1) == 0 && crate::expr_model::nlbv(r.h2) == 0 && crate::expr_model::nlbv(r.h3) == 0,
        crate::expr_model::nlbv(r.mot1) == 0 && crate::expr_model::nlbv(r.succ_case(z)) == 0,
        r.cc is Const && linked(ne, r.cc) && std_cases_on(ne[r.cc->Const_0].1),
        std_nat_rec(ne, cases_rec(ne, r.cc->Const_0)->Const_0) && cases_rec(ne, r.cc->Const_0)->Const_1.len() == 1,
{
    let (fid, uf) = (f->Const_0, f->Const_1);
    let e0 = mk_app(mk_app(mk_app(f, t), below), z);
    ble_f_unfold(ne, fid, uf, t, below, z);
    let fb = spine_bind(ne[fid].1, 3)->Some_0;
    let fc = blef_call(fb);
    let fargs = seq![t, below, z];
    let (ks, vs) = (ne[fid].0, uf);
    let mot = inst_args(inst_levels(arg1_of4(fc), ks, vs), fargs, 0);
    let h1 = inst_args(inst_levels(arg4_of4(fc), ks, vs), fargs, 0);
    let h2 = inst_args(inst_levels(arg_of(fun_of(fun_of(fb))), ks, vs), fargs, 0);
    let h3 = inst_args(inst_levels(arg_of(fun_of(fb)), ks, vs), fargs, 0);
    let m = blef_match(ne, fid);
    let mls = crate::level_model::subst_levels_spec(m->Const_1, ks, vs);
    let mc = ExprSpec::Const(m->Const_0, mls);
    let e1 = mk_app7(mc, mot, t, z, h1, h2, h3, below);
    // `match_1` to the case split
    ble_match_unfold(ne, m->Const_0, mls, mot, t, z, h1, h2, h3);
    let margs = seq![mot, t, z, h1, h2, h3];
    assert forall|i: int| 0 <= i < 6 implies crate::expr_model::nlbv(#[trigger] margs[i]) == 0 by {}
    ble_match_closed(ne, m->Const_0, mls, margs);
    let mb = spine_bind(ne[m->Const_0].1, 6)->Some_0;
    let outer = arg4_of4(mb);
    let inner = lam_body(outer);
    let (mks, mvs) = (ne[m->Const_0].0, mls);
    let cc = inst_levels(head_of4(mb), mks, mvs);
    let r = BleCases {
        cc,
        mot1: inst_args(inst_levels(arg1_of4(mb), mks, mvs), margs, 0),
        h1, h2, h3,
        t0: inst_args(inst_levels(lam_type(outer), mks, mvs), margs, 0),
        mot2: inst_args(inst_levels(arg1_of4(inner), mks, mvs), margs, 1),
        t1: inst_args(inst_levels(lam_type(arg4_of4(inner)), mks, mvs), margs, 1),
    };
    let x2 = mk_app4(cc, r.mot1, t, mk_app(h1, z), r.succ_case(z));
    pstep_star_app_congr(ne, mk_app(mk_app(mk_app4(mc, mot, t, z, h1), h2), h3), x2, below);
    pstep_star_trans(ne, e0, e1, mk_app(x2, below));
    assert(cc == ExprSpec::Const(head_of4(mb)->Const_0, crate::level_model::subst_levels_spec(head_of4(mb)->Const_1, mks, mvs)));
    r
}

/// A constant case applied to two arguments is its constant.
pub proof fn const_case_beta(ne: EnvSpec, h: ExprSpec, c: ExprSpec, a: ExprSpec, b: ExprSpec)
    requires
        const_case(h, c),
        crate::expr_model::nlbv(c) == 0,
        crate::expr_model::nlbv(a) == 0 && crate::expr_model::nlbv(b) == 0,
    ensures
        pstep_star(ne, mk_app(mk_app(h, a), b), c),
{
    assert(spine_bind(h, 2) == Some(c)) by {
        reveal_with_fuel(spine_bind, 3);
    }
    pstep_star_spine_reduce(ne, h, seq![a, b]);
    spine_reduce_eq_subst_full(h, seq![a, b], c, 0);
    crate::expr_model::subst_full_noop(c, seq![a, b], 0);
    assert(spine_app(h, seq![a, b]) == mk_app(mk_app(h, a), b)) by {
        reveal_with_fuel(spine_app, 3);
    }
}

/// `Nat.ble._f Nat.zero below z` reduces to `Bool.true`.
#[verifier::spinoff_prover]
pub proof fn ble_f_zero(ne: EnvSpec, f: ExprSpec, below: ExprSpec, z: ExprSpec)
    requires
        ble_f_links(ne, f),
        crate::expr_model::nlbv(below) == 0 && crate::expr_model::nlbv(z) == 0,
    ensures
        pstep_star(ne, mk_app(mk_app(mk_app(f, const_expr_no_levels(crate::expr_arena_bridge::nat_zero_id(ne.export))), below), z),
            const_expr_no_levels(crate::expr_arena_bridge::bool_true_id(ne.export))),
{
    let zc = const_expr_no_levels(crate::expr_arena_bridge::nat_zero_id(ne.export));
    let tc = const_expr_no_levels(crate::expr_arena_bridge::bool_true_id(ne.export));
    let e0 = mk_app(mk_app(mk_app(f, zc), below), z);
    let r = ble_f_cases(ne, f, zc, below, z);
    let sc = r.succ_case(z);
    let x1 = mk_app4(r.cc, r.mot1, zc, mk_app(r.h1, z), sc);
    // `casesOn` to `Nat.rec`
    cases_on_unfold(ne, r.cc->Const_0, r.cc->Const_1, r.mot1, zc, mk_app(r.h1, z), sc);
    let cb = spine_bind(ne[r.cc->Const_0].1, 4)->Some_0;
    let cargs = seq![r.mot1, zc, mk_app(r.h1, z), sc];
    let (cks, cvs) = (ne[r.cc->Const_0].0, r.cc->Const_1);
    let rc0 = cases_rec(ne, r.cc->Const_0);
    let rls = crate::level_model::subst_levels_spec(rc0->Const_1, cks, cvs);
    let st = arg3_of4(cb);
    let stepl = mk_lam(inst_args(inst_levels(lam_type(st), cks, cvs), cargs, 0),
        mk_lam(inst_args(inst_levels(lam_type(lam_body(st)), cks, cvs), cargs, 1), mk_app(sc, ExprSpec::Var(1))));
    let x2 = mk_app4(ExprSpec::Const(rc0->Const_0, rls), r.mot1, mk_app(r.h1, z), stepl, zc);
    pstep_star_app_congr(ne, x1, x2, below);
    // iota at zero, then the constant case
    assert(crate::expr_model::nlbv(mk_app(r.h1, z)) == 0);
    nat_rec_zero(ne, rc0->Const_0, rls, r.mot1, mk_app(r.h1, z), stepl);
    pstep_star_app_congr(ne, x2, mk_app(r.h1, z), below);
    const_case_beta(ne, r.h1, tc, z, below);
    pstep_star_trans(ne, e0, mk_app(x1, below), mk_app(x2, below));
    pstep_star_trans(ne, e0, mk_app(x2, below), mk_app(mk_app(r.h1, z), below));
    pstep_star_trans(ne, e0, mk_app(mk_app(r.h1, z), below), tc);
}

/// `Nat.ble._f (Nat.succ n) below z` reduces to the inner case split
/// `Nat.casesOn mot2' z (h2 n) (λ m. h3 n m) below`.
#[verifier::spinoff_prover]
pub proof fn ble_f_succ_split(ne: EnvSpec, f: ExprSpec, n: ExprSpec, below: ExprSpec, z: ExprSpec) -> (res: (BleCases, ExprSpec, ExprSpec))
    requires
        ble_f_links(ne, f),
        crate::expr_model::nlbv(n) == 0 && crate::expr_model::nlbv(below) == 0 && crate::expr_model::nlbv(z) == 0,
    ensures ({
        let (r, mot2, t1) = res;
        let sc = const_expr_no_levels(crate::expr_arena_bridge::nat_succ_id(ne.export));
        let inner_case = mk_lam(t1, mk_app(mk_app(r.h3, n), ExprSpec::Var(0)));
        &&& pstep_star(ne, mk_app(mk_app(mk_app(f, mk_app(sc, n)), below), z),
            mk_app(mk_app4(r.cc, mot2, z, mk_app(r.h2, n), inner_case), below))
        &&& const_case(r.h2, const_expr_no_levels(crate::expr_arena_bridge::bool_false_id(ne.export)))
        &&& ble_rec_case(r.h3)
        &&& crate::expr_model::nlbv(r.h2) == 0 && crate::expr_model::nlbv(r.h3) == 0
        &&& crate::expr_model::nlbv(mot2) == 0 && crate::expr_model::nlbv(inner_case) == 0
        &&& r.cc is Const && linked(ne, r.cc) && std_cases_on(ne[r.cc->Const_0].1)
        &&& std_nat_rec(ne, cases_rec(ne, r.cc->Const_0)->Const_0) && cases_rec(ne, r.cc->Const_0)->Const_1.len() == 1
    }),
{
    let sc = const_expr_no_levels(crate::expr_arena_bridge::nat_succ_id(ne.export));
    let t = mk_app(sc, n);
    assert(crate::expr_model::nlbv(t) == 0) by {
        reveal_with_fuel(crate::expr_model::nlbv, 3);
    }
    let e0 = mk_app(mk_app(mk_app(f, t), below), z);
    let r = ble_f_cases(ne, f, t, below, z);
    let scase = r.succ_case(z);
    let x1 = mk_app4(r.cc, r.mot1, t, mk_app(r.h1, z), scase);
    // `casesOn` to `Nat.rec`, iota at the successor
    cases_on_unfold(ne, r.cc->Const_0, r.cc->Const_1, r.mot1, t, mk_app(r.h1, z), scase);
    let cb = spine_bind(ne[r.cc->Const_0].1, 4)->Some_0;
    let cargs = seq![r.mot1, t, mk_app(r.h1, z), scase];
    let (cks, cvs) = (ne[r.cc->Const_0].0, r.cc->Const_1);
    let rc0 = cases_rec(ne, r.cc->Const_0);
    let rls = crate::level_model::subst_levels_spec(rc0->Const_1, cks, cvs);
    let st = arg3_of4(cb);
    let stepl = mk_lam(inst_args(inst_levels(lam_type(st), cks, cvs), cargs, 0),
        mk_lam(inst_args(inst_levels(lam_type(lam_body(st)), cks, cvs), cargs, 1), mk_app(scase, ExprSpec::Var(1))));
    let rc = ExprSpec::Const(rc0->Const_0, rls);
    let x2 = mk_app4(rc, r.mot1, mk_app(r.h1, z), stepl, t);
    pstep_star_app_congr(ne, x1, x2, below);
    assert(crate::expr_model::nlbv(mk_app(r.h1, z)) == 0);
    nat_rec_succ(ne, rc0->Const_0, rls, r.mot1, mk_app(r.h1, z), stepl, n);
    let q = mk_app4(rc, r.mot1, mk_app(r.h1, z), stepl, n);
    let x3 = mk_app(mk_app(stepl, n), q);
    pstep_star_app_congr(ne, x2, x3, below);
    // `(λ n _. scase n) n q` to `scase n`
    assert(spine_bind(stepl, 2) == Some(mk_app(scase, ExprSpec::Var(1)))) by {
        reveal_with_fuel(spine_bind, 3);
    }
    assert(crate::expr_model::nlbv(q) == 0) by {
        reveal_with_fuel(crate::expr_model::nlbv, 6);
    }
    pstep_star_spine_reduce(ne, stepl, seq![n, q]);
    assert(crate::expr_model::nlbv(mk_app(scase, ExprSpec::Var(1))) <= 2) by {
        reveal_with_fuel(crate::expr_model::nlbv, 3);
    }
    spine_reduce_eq_subst_full(stepl, seq![n, q], mk_app(scase, ExprSpec::Var(1)), 0);
    inst_args_app(scase, ExprSpec::Var(1), seq![n, q], 0);
    crate::expr_model::subst_full_noop(scase, seq![n, q], 0);
    assert(spine_app(stepl, seq![n, q]) == x3) by {
        reveal_with_fuel(spine_app, 3);
    }
    let x4 = mk_app(scase, n);
    pstep_star_app_congr(ne, x3, x4, below);
    // `scase n` to the inner case split
    let lastb = mk_app(mk_app(r.h3, ExprSpec::Var(1)), ExprSpec::Var(0));
    let body = mk_app4(r.cc, r.mot2, z, mk_app(r.h2, ExprSpec::Var(0)), mk_lam(r.t1, lastb));
    assert(spine_bind(scase, 1) == Some(body)) by {
        reveal_with_fuel(spine_bind, 2);
    }
    pstep_star_spine_reduce(ne, scase, seq![n]);
    assert(crate::expr_model::nlbv(body) <= 1) by {
        reveal_with_fuel(crate::expr_model::nlbv, 2);
    }
    spine_reduce_eq_subst_full(scase, seq![n], body, 0);
    let a1 = seq![n];
    inst_args_app4(r.cc, r.mot2, z, mk_app(r.h2, ExprSpec::Var(0)), mk_lam(r.t1, lastb), a1, 0);
    inst_args_app(r.h2, ExprSpec::Var(0), a1, 0);
    inst_args_lam(r.t1, lastb, a1, 0);
    inst_args_app(mk_app(r.h3, ExprSpec::Var(1)), ExprSpec::Var(0), a1, 1);
    inst_args_app(r.h3, ExprSpec::Var(1), a1, 1);
    crate::expr_model::subst_full_noop(r.cc, a1, 0);
    crate::expr_model::subst_full_noop(z, a1, 0);
    crate::expr_model::subst_full_noop(r.h2, a1, 0);
    crate::expr_model::subst_full_noop(r.h3, a1, 1);
    assert(inst_args(ExprSpec::Var(0), a1, 0) == n);
    assert(inst_args(ExprSpec::Var(1), a1, 1) == n);
    assert(inst_args(ExprSpec::Var(0), a1, 1) == ExprSpec::Var(0));
    let mot2 = inst_args(r.mot2, a1, 0);
    let t1 = inst_args(r.t1, a1, 0);
    let inner_case = mk_lam(t1, mk_app(mk_app(r.h3, n), ExprSpec::Var(0)));
    let x5 = mk_app4(r.cc, mot2, z, mk_app(r.h2, n), inner_case);
    assert(inst_args(body, a1, 0) == x5);
    assert(spine_app(scase, a1) == x4) by {
        reveal_with_fuel(spine_app, 2);
    }
    pstep_star_app_congr(ne, x4, x5, below);
    // closedness, from the closed successor case
    assert(crate::expr_model::nlbv(r.mot2) <= 1 && crate::expr_model::nlbv(r.t1) <= 1) by {
        reveal_with_fuel(crate::expr_model::nlbv, 6);
    }
    crate::beta_model::subst_full_nlbv_bound_n(r.mot2, a1, 0);
    crate::beta_model::subst_full_nlbv_bound_n(r.t1, a1, 0);
    assert(crate::expr_model::nlbv(inner_case) == 0) by {
        reveal_with_fuel(crate::expr_model::nlbv, 4);
    }
    pstep_star_trans(ne, e0, mk_app(x1, below), mk_app(x2, below));
    pstep_star_trans(ne, e0, mk_app(x2, below), mk_app(x3, below));
    pstep_star_trans(ne, e0, mk_app(x3, below), mk_app(x4, below));
    pstep_star_trans(ne, e0, mk_app(x4, below), mk_app(x5, below));
    (r, mot2, t1)
}

/// `Nat.ble._f (Nat.succ n) below Nat.zero` reduces to `Bool.false`.
#[verifier::spinoff_prover]
pub proof fn ble_f_succ_zero(ne: EnvSpec, f: ExprSpec, n: ExprSpec, below: ExprSpec)
    requires
        ble_f_links(ne, f),
        crate::expr_model::nlbv(n) == 0 && crate::expr_model::nlbv(below) == 0,
    ensures
        pstep_star(ne, mk_app(mk_app(mk_app(f, mk_app(const_expr_no_levels(crate::expr_arena_bridge::nat_succ_id(ne.export)), n)), below),
            const_expr_no_levels(crate::expr_arena_bridge::nat_zero_id(ne.export))),
            const_expr_no_levels(crate::expr_arena_bridge::bool_false_id(ne.export))),
{
    let zc = const_expr_no_levels(crate::expr_arena_bridge::nat_zero_id(ne.export));
    let fc = const_expr_no_levels(crate::expr_arena_bridge::bool_false_id(ne.export));
    let sc = const_expr_no_levels(crate::expr_arena_bridge::nat_succ_id(ne.export));
    let e0 = mk_app(mk_app(mk_app(f, mk_app(sc, n)), below), zc);
    let (r, mot2, t1) = ble_f_succ_split(ne, f, n, below, zc);
    let ic = mk_lam(t1, mk_app(mk_app(r.h3, n), ExprSpec::Var(0)));
    let x1 = mk_app4(r.cc, mot2, zc, mk_app(r.h2, n), ic);
    cases_on_unfold(ne, r.cc->Const_0, r.cc->Const_1, mot2, zc, mk_app(r.h2, n), ic);
    let cb = spine_bind(ne[r.cc->Const_0].1, 4)->Some_0;
    let cargs = seq![mot2, zc, mk_app(r.h2, n), ic];
    let (cks, cvs) = (ne[r.cc->Const_0].0, r.cc->Const_1);
    let rc0 = cases_rec(ne, r.cc->Const_0);
    let rls = crate::level_model::subst_levels_spec(rc0->Const_1, cks, cvs);
    let st = arg3_of4(cb);
    let stepl = mk_lam(inst_args(inst_levels(lam_type(st), cks, cvs), cargs, 0),
        mk_lam(inst_args(inst_levels(lam_type(lam_body(st)), cks, cvs), cargs, 1), mk_app(ic, ExprSpec::Var(1))));
    let x2 = mk_app4(ExprSpec::Const(rc0->Const_0, rls), mot2, mk_app(r.h2, n), stepl, zc);
    pstep_star_app_congr(ne, x1, x2, below);
    assert(crate::expr_model::nlbv(mk_app(r.h2, n)) == 0);
    nat_rec_zero(ne, rc0->Const_0, rls, mot2, mk_app(r.h2, n), stepl);
    pstep_star_app_congr(ne, x2, mk_app(r.h2, n), below);
    const_case_beta(ne, r.h2, fc, n, below);
    pstep_star_trans(ne, e0, mk_app(x1, below), mk_app(x2, below));
    pstep_star_trans(ne, e0, mk_app(x2, below), mk_app(mk_app(r.h2, n), below));
    pstep_star_trans(ne, e0, mk_app(mk_app(r.h2, n), below), fc);
}

/// `Nat.ble._f (Nat.succ n) below (Nat.succ m)` reduces to `below.0 m`:
/// the recursive call at the predecessors.
#[verifier::spinoff_prover]
pub proof fn ble_f_succ_succ(ne: EnvSpec, f: ExprSpec, n: ExprSpec, below: ExprSpec, m: ExprSpec)
    requires
        ble_f_links(ne, f),
        crate::expr_model::nlbv(n) == 0 && crate::expr_model::nlbv(below) == 0 && crate::expr_model::nlbv(m) == 0,
    ensures ({
        let sc = const_expr_no_levels(crate::expr_arena_bridge::nat_succ_id(ne.export));
        pstep_star(ne, mk_app(mk_app(mk_app(f, mk_app(sc, n)), below), mk_app(sc, m)),
            mk_app(ExprSpec::Proj(0, Box::new(below)), m))
    }),
{
    let sc = const_expr_no_levels(crate::expr_arena_bridge::nat_succ_id(ne.export));
    let z = mk_app(sc, m);
    assert(crate::expr_model::nlbv(z) == 0) by {
        reveal_with_fuel(crate::expr_model::nlbv, 3);
    }
    let e0 = mk_app(mk_app(mk_app(f, mk_app(sc, n)), below), z);
    let (r, mot2, t1) = ble_f_succ_split(ne, f, n, below, z);
    let ib = mk_app(mk_app(r.h3, n), ExprSpec::Var(0));
    let ic = mk_lam(t1, ib);
    let x1 = mk_app4(r.cc, mot2, z, mk_app(r.h2, n), ic);
    cases_on_unfold(ne, r.cc->Const_0, r.cc->Const_1, mot2, z, mk_app(r.h2, n), ic);
    let cb = spine_bind(ne[r.cc->Const_0].1, 4)->Some_0;
    let cargs = seq![mot2, z, mk_app(r.h2, n), ic];
    let (cks, cvs) = (ne[r.cc->Const_0].0, r.cc->Const_1);
    let rc0 = cases_rec(ne, r.cc->Const_0);
    let rls = crate::level_model::subst_levels_spec(rc0->Const_1, cks, cvs);
    let st = arg3_of4(cb);
    let stepl = mk_lam(inst_args(inst_levels(lam_type(st), cks, cvs), cargs, 0),
        mk_lam(inst_args(inst_levels(lam_type(lam_body(st)), cks, cvs), cargs, 1), mk_app(ic, ExprSpec::Var(1))));
    let rc = ExprSpec::Const(rc0->Const_0, rls);
    let x2 = mk_app4(rc, mot2, mk_app(r.h2, n), stepl, z);
    pstep_star_app_congr(ne, x1, x2, below);
    assert(crate::expr_model::nlbv(mk_app(r.h2, n)) == 0);
    nat_rec_succ(ne, rc0->Const_0, rls, mot2, mk_app(r.h2, n), stepl, m);
    let q = mk_app4(rc, mot2, mk_app(r.h2, n), stepl, m);
    let x3 = mk_app(mk_app(stepl, m), q);
    pstep_star_app_congr(ne, x2, x3, below);
    // `(λ m _. ic m) m q` to `ic m`
    assert(spine_bind(stepl, 2) == Some(mk_app(ic, ExprSpec::Var(1)))) by {
        reveal_with_fuel(spine_bind, 3);
    }
    assert(crate::expr_model::nlbv(q) == 0) by {
        reveal_with_fuel(crate::expr_model::nlbv, 6);
    }
    pstep_star_spine_reduce(ne, stepl, seq![m, q]);
    assert(crate::expr_model::nlbv(mk_app(ic, ExprSpec::Var(1))) <= 2) by {
        reveal_with_fuel(crate::expr_model::nlbv, 3);
    }
    spine_reduce_eq_subst_full(stepl, seq![m, q], mk_app(ic, ExprSpec::Var(1)), 0);
    inst_args_app(ic, ExprSpec::Var(1), seq![m, q], 0);
    crate::expr_model::subst_full_noop(ic, seq![m, q], 0);
    assert(spine_app(stepl, seq![m, q]) == x3) by {
        reveal_with_fuel(spine_app, 3);
    }
    let x4 = mk_app(ic, m);
    pstep_star_app_congr(ne, x3, x4, below);
    // `ic m` to `h3 n m`
    assert(spine_bind(ic, 1) == Some(ib)) by {
        reveal_with_fuel(spine_bind, 2);
    }
    pstep_star_spine_reduce(ne, ic, seq![m]);
    assert(crate::expr_model::nlbv(ib) <= 1) by {
        reveal_with_fuel(crate::expr_model::nlbv, 3);
    }
    spine_reduce_eq_subst_full(ic, seq![m], ib, 0);
    inst_args_app(mk_app(r.h3, n), ExprSpec::Var(0), seq![m], 0);
    inst_args_app(r.h3, n, seq![m], 0);
    crate::expr_model::subst_full_noop(r.h3, seq![m], 0);
    crate::expr_model::subst_full_noop(n, seq![m], 0);
    assert(inst_args(ExprSpec::Var(0), seq![m], 0) == m);
    assert(spine_app(ic, seq![m]) == x4) by {
        reveal_with_fuel(spine_app, 2);
    }
    let x5 = mk_app(mk_app(r.h3, n), m);
    pstep_star_app_congr(ne, x4, x5, below);
    // `(λ n m b. b.0 m) n m below` to `below.0 m`
    let pr = ExprSpec::Proj(0, Box::new(ExprSpec::Var(0)));
    let hb = mk_app(pr, ExprSpec::Var(1));
    assert(spine_bind(r.h3, 3) == Some(hb)) by {
        reveal_with_fuel(spine_bind, 4);
    }
    let hargs = seq![n, m, below];
    pstep_star_spine_reduce(ne, r.h3, hargs);
    assert(crate::expr_model::nlbv(hb) <= 3) by {
        reveal_with_fuel(crate::expr_model::nlbv, 4);
    }
    spine_reduce_eq_subst_full(r.h3, hargs, hb, 0);
    inst_args_app(pr, ExprSpec::Var(1), hargs, 0);
    assert(inst_args(ExprSpec::Var(0), hargs, 0) == below);
    assert(inst_args(pr, hargs, 0) == ExprSpec::Proj(0, Box::new(below)));
    assert(inst_args(ExprSpec::Var(1), hargs, 0) == m);
    spine_app3_parts(r.h3, n, m, below);
    let fin = mk_app(ExprSpec::Proj(0, Box::new(below)), m);
    pstep_star_trans(ne, e0, mk_app(x1, below), mk_app(x2, below));
    pstep_star_trans(ne, e0, mk_app(x2, below), mk_app(x3, below));
    pstep_star_trans(ne, e0, mk_app(x3, below), mk_app(x4, below));
    pstep_star_trans(ne, e0, mk_app(x4, below), mk_app(x5, below));
    pstep_star_trans(ne, e0, mk_app(x5, below), fin);
}

/// `Bool.true` or `Bool.false`, as `b`.
pub open spec fn bool_const(export: nat, b: bool) -> ExprSpec {
    const_expr_no_levels(if b { crate::expr_arena_bridge::bool_true_id(export) } else { crate::expr_arena_bridge::bool_false_id(export) })
}

/// THE RECURSION `Nat.brecOn.go` BUILDS FOR `Nat.ble`: at `n`, its first
/// component applied to the canonical numeral `k` reduces to whether
/// `n <= k`.
#[verifier::spinoff_prover]
pub proof fn go_rec_ble(ne: EnvSpec, rid: u64, rls: Seq<crate::level_model::LevelSpec>, p: ExprSpec, base: ExprSpec, step: ExprSpec,
    f: ExprSpec, n: nat, k: nat)
    requires
        std_nat_rec(ne, rid),
        rls.len() == 1,
        ble_f_links(ne, f),
        crate::expr_model::nlbv(f) == 0,
        crate::expr_model::nlbv(p) == 0 && crate::expr_model::nlbv(base) == 0 && crate::expr_model::nlbv(step) == 0,
        base_shape(base, f, crate::expr_arena_bridge::nat_zero_id(ne.export)),
        step_shape(step, f, crate::expr_arena_bridge::nat_succ_id(ne.export)),
        ne.ctor_num_params(head_of4(base)->Const_0) == Some(2u16),
        ne.ctor_num_params(head_of4(lam_body(lam_body(step)))->Const_0) == Some(2u16),
    ensures
        pstep_star(ne, mk_app(ExprSpec::Proj(0, Box::new(mk_app4(ExprSpec::Const(rid, rls), p, base, step, canon_numeral(ne.export, n)))),
            canon_numeral(ne.export, k)), bool_const(ne.export, n <= k)),
    decreases n,
{
    let sc = const_expr_no_levels(crate::expr_arena_bridge::nat_succ_id(ne.export));
    let rc = ExprSpec::Const(rid, rls);
    let rn = mk_app4(rc, p, base, step, canon_numeral(ne.export, n));
    let y = canon_numeral(ne.export, k);
    canon_numeral_closed(ne.export, k);
    let e0 = mk_app(ExprSpec::Proj(0, Box::new(rn)), y);
    if n == 0 {
        nat_rec_zero(ne, rid, rls, p, base, step);
        let mk = head_of4(base);
        let fz = arg3_of4(base);
        spine_app4_parts(mk, arg1_of4(base), arg2_of4(base), fz, arg4_of4(base));
        crate::beta_model::pstep_star_iota(ne, 0, rn, mk->Const_0, mk->Const_1, seq![arg1_of4(base), arg2_of4(base), fz, arg4_of4(base)], 2);
        pstep_star_app_congr(ne, ExprSpec::Proj(0, Box::new(rn)), fz, y);
        let u1 = arg_of(fz);
        assert(crate::expr_model::nlbv(u1) == 0) by {
            reveal_with_fuel(crate::expr_model::nlbv, 7);
        }
        ble_f_zero(ne, f, u1, y);
        pstep_star_trans(ne, e0, mk_app(fz, y), bool_const(ne.export, true));
    } else {
        let j = (n - 1) as nat;
        let nj = canon_numeral(ne.export, j);
        let rj = mk_app4(rc, p, base, step, nj);
        canon_numeral_closed(ne.export, j);
        nat_rec_succ(ne, rid, rls, p, base, step, nj);
        let sb = lam_body(lam_body(step));
        assert(spine_bind(step, 2) == Some(sb)) by {
            reveal_with_fuel(spine_bind, 3);
        }
        assert(crate::expr_model::nlbv(rj) == 0) by {
            reveal_with_fuel(crate::expr_model::nlbv, 6);
        }
        let sargs = seq![nj, rj];
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
        let fsk = mk_app(mk_app(f, mk_app(sc, nj)), rj);
        let a1 = inst_args(arg1_of4(sb), sargs, 0);
        let a2 = inst_args(arg2_of4(sb), sargs, 0);
        let built = mk_app4(mk2, a1, a2, fsk, rj);
        assert(inst_args(sb, sargs, 0) == built);
        assert(spine_app(step, sargs) == mk_app(mk_app(step, nj), rj)) by {
            reveal_with_fuel(spine_app, 3);
        }
        assert(rn == mk_app4(rc, p, base, step, mk_app(sc, nj)));
        pstep_star_trans(ne, rn, mk_app(mk_app(step, nj), rj), built);
        spine_app4_parts(mk2, a1, a2, fsk, rj);
        crate::beta_model::pstep_star_iota(ne, 0, rn, mk2->Const_0, mk2->Const_1, seq![a1, a2, fsk, rj], 2);
        pstep_star_app_congr(ne, ExprSpec::Proj(0, Box::new(rn)), fsk, y);
        if k == 0 {
            ble_f_succ_zero(ne, f, nj, rj);
            pstep_star_trans(ne, e0, mk_app(fsk, y), bool_const(ne.export, false));
        } else {
            let yk = canon_numeral(ne.export, (k - 1) as nat);
            canon_numeral_closed(ne.export, (k - 1) as nat);
            ble_f_succ_succ(ne, f, nj, rj, yk);
            go_rec_ble(ne, rid, rls, p, base, step, f, j, (k - 1) as nat);
            pstep_star_trans(ne, e0, mk_app(fsk, y), mk_app(ExprSpec::Proj(0, Box::new(rj)), yk));
            pstep_star_trans(ne, e0, mk_app(ExprSpec::Proj(0, Box::new(rj)), yk), bool_const(ne.export, j <= (k - 1) as nat));
        }
    }
}

/// THE EXPORT DECLARES `Nat.ble` AS LEAN DOES: its value, and the values
/// of `Nat.brecOn`, `Nat.brecOn.go`, `Nat.ble._f`, `Nat.ble.match_1` and
/// `Nat.casesOn` it reaches, are Lean's, `Nat.rec`'s rules are Lean's, and
/// `PProd.mk` takes two parameters. Checkable on the declarations.
#[verifier::opaque]
pub open spec fn std_nat_ble_env(ne: EnvSpec, ble: u64) -> bool {
    let (zid, sid) = (crate::expr_arena_bridge::nat_zero_id(ne.export), crate::expr_arena_bridge::nat_succ_id(ne.export));
    let ab = spine_bind(ne[ble].1, 2)->Some_0;
    let (brec, f) = (head_of4(ab), arg3_of4(ab));
    let go = brec_on_go_const(spine_bind(ne[brec->Const_0].1, 3)->Some_0);
    let gb = spine_bind(ne[go->Const_0].1, 3)->Some_0;
    let rc = head_of4(gb);
    &&& ne.contains_key(ble) && ne[ble].0.len() == 0 && std_nat_ble(ne[ble].1)
    &&& linked(ne, brec) && std_brec_on(ne[brec->Const_0].1)
    &&& linked(ne, go) && std_brec_on_go(ne[go->Const_0].1, zid, sid)
    &&& std_nat_rec(ne, rc->Const_0) && rc->Const_1.len() == 1
    &&& ne.ctor_num_params(head_of4(arg2_of4(gb))->Const_0) == Some(2u16)
    &&& ne.ctor_num_params(head_of4(lam_body(lam_body(arg3_of4(gb))))->Const_0) == Some(2u16)
    &&& ble_f_links(ne, f)
}

/// `Nat.ble` is defined where it is declared as Lean does.
pub proof fn std_nat_ble_env_defined(ne: EnvSpec, ble: u64)
    requires
        std_nat_ble_env(ne, ble),
    ensures
        ne.contains_key(ble),
        ne.defs.contains_key(ble),
{
    reveal(std_nat_ble_env);
}

/// The fold-free environment declares `Nat.ble` as the environment does.
pub proof fn std_nat_ble_env_nofold(env: EnvSpec, ble: u64)
    requires
        std_nat_ble_env(env, ble),
    ensures
        std_nat_ble_env(crate::conv_frag::nofold(env), ble),
{
    reveal(std_nat_ble_env);
    let ne = crate::conv_frag::nofold(env);
    assert(forall|id: u64| #[trigger] ne.rec_data(id) == env.rec_data(id));
    assert(forall|id: u64| #[trigger] ne.ctor_num_params(id) == env.ctor_num_params(id));
    assert(ne.defs == env.defs && ne.export == env.export);
}

/// `Nat.ble x y` ON NUMERALS REDUCES, WITHOUT FOLDING, TO WHETHER `x <= y`.
#[verifier::spinoff_prover]
pub proof fn ble_computes(ne: EnvSpec, ble: u64, x: ExprSpec, y: ExprSpec)
    requires
        std_nat_ble_env(ne, ble),
        crate::beta_model::nat_value(ne.export, x) is Some,
        crate::beta_model::nat_value(ne.export, y) is Some,
    ensures
        pstep_star(ne, mk_app(mk_app(ExprSpec::Const(ble, Seq::empty()), x), y),
            bool_const(ne.export, crate::beta_model::nat_value(ne.export, x)->Some_0 <= crate::beta_model::nat_value(ne.export, y)->Some_0)),
{
    reveal(std_nat_ble_env);
    let a = crate::beta_model::nat_value(ne.export, x)->Some_0;
    let b = crate::beta_model::nat_value(ne.export, y)->Some_0;
    let (na, nb) = (canon_numeral(ne.export, a), canon_numeral(ne.export, b));
    numeral_closed(ne.export, x);
    numeral_closed(ne.export, y);
    canon_numeral_closed(ne.export, a);
    canon_numeral_closed(ne.export, b);
    let ab = spine_bind(ne[ble].1, 2)->Some_0;
    let (brec, m, f) = (head_of4(ab), arg1_of4(ab), arg3_of4(ab));
    let e0 = mk_app(mk_app(ExprSpec::Const(ble, Seq::empty()), x), y);
    // `Nat.ble x y` to `Nat.brecOn M x F y`
    ble_unfold(ne, ble, x, y);
    let e1 = mk_app(mk_app(mk_app(mk_app(brec, m), x), f), y);
    // `x` to its canonical numeral
    numeral_star(ne, x);
    pstep_star_app_arg_congr(ne, mk_app(brec, m), x, na);
    pstep_star_app_congr(ne, mk_app(mk_app(brec, m), x), mk_app(mk_app(brec, m), na), f);
    pstep_star_app_congr(ne, mk_app(mk_app(mk_app(brec, m), x), f), mk_app(mk_app(mk_app(brec, m), na), f), y);
    let e2 = mk_app(mk_app(mk_app(mk_app(brec, m), na), f), y);
    // `Nat.brecOn` to `(Nat.brecOn.go M na F).0`
    brec_on_unfold(ne, brec->Const_0, brec->Const_1, m, na, f);
    let go = brec_on_go_const(spine_bind(ne[brec->Const_0].1, 3)->Some_0);
    let gls = crate::level_model::subst_levels_spec(go->Const_1, ne[brec->Const_0].0, brec->Const_1);
    let gc = ExprSpec::Const(go->Const_0, gls);
    let gapp = mk_app(mk_app(mk_app(gc, m), na), f);
    pstep_star_app_congr(ne, mk_app(mk_app(mk_app(brec, m), na), f), ExprSpec::Proj(0, Box::new(gapp)), y);
    let e3 = mk_app(ExprSpec::Proj(0, Box::new(gapp)), y);
    // `Nat.brecOn.go` to `Nat.rec P BASE STEP na`
    brec_on_go_unfold(ne, go->Const_0, gls, m, na, f);
    let gb = spine_bind(ne[go->Const_0].1, 3)->Some_0;
    let r = inst_args(inst_levels(gb, ne[go->Const_0].0, gls), seq![m, na, f], 0);
    pstep_star_proj_congr(ne, 0, gapp, r);
    pstep_star_app_congr(ne, ExprSpec::Proj(0, Box::new(gapp)), ExprSpec::Proj(0, Box::new(r)), y);
    let e4 = mk_app(ExprSpec::Proj(0, Box::new(r)), y);
    // `y` to its canonical numeral, then the recursion
    numeral_star(ne, y);
    pstep_star_app_arg_congr(ne, ExprSpec::Proj(0, Box::new(r)), y, nb);
    let e5 = mk_app(ExprSpec::Proj(0, Box::new(r)), nb);
    let rc = head_of4(gb);
    let rls = crate::level_model::subst_levels_spec(rc->Const_1, ne[go->Const_0].0, gls);
    assert(r == mk_app4(ExprSpec::Const(rc->Const_0, rls), arg1_of4(r), arg2_of4(r), arg3_of4(r), na));
    go_rec_ble(ne, rc->Const_0, rls, arg1_of4(r), arg2_of4(r), arg3_of4(r), f, a, b);
    pstep_star_trans(ne, e0, e1, e2);
    pstep_star_trans(ne, e0, e2, e3);
    pstep_star_trans(ne, e0, e3, e4);
    pstep_star_trans(ne, e0, e4, e5);
    pstep_star_trans(ne, e0, e5, bool_const(ne.export, a <= b));
}

/// THE KERNEL'S `Nat.ble` FOLD IS A REDUCTION OF THE DEFINITION: a ready
/// fold redex headed by `Nat.ble` reduces, without folding, to its folded
/// result.
#[verifier::spinoff_prover]
pub proof fn ble_fold_joins(env: EnvSpec, ble: u64, s: ExprSpec)
    requires
        std_nat_ble_env(env, ble),
        nat_fold_ready(env.export, s),
        spine_head(s) is Const && spine_head(s)->Const_0 == ble,
        crate::expr_arena_bridge::nat_bin_op_of(env.export, ble) == Some(8u8),
    ensures
        pstep_star(crate::conv_frag::nofold(env), s, nat_fold_result(env.export, s)),
{
    let ne = crate::conv_frag::nofold(env);
    std_nat_ble_env_nofold(env, ble);
    let args = spine_args(s);
    let lv = spine_head(s)->Const_1;
    assert(lv =~= Seq::<crate::level_model::LevelSpec>::empty());
    let (x, y) = (args[0], args[1]);
    assert(s == mk_app(mk_app(ExprSpec::Const(ble, Seq::empty()), x), y)) by {
        crate::beta_model::spine_recompose(s);
        reveal_with_fuel(spine_app, 3);
    }
    ble_computes(ne, ble, x, y);
    let a = crate::beta_model::nat_value(env.export, x)->Some_0;
    let b = crate::beta_model::nat_value(env.export, y)->Some_0;
    assert(nat_fold_result(env.export, s) == bool_const(env.export, a <= b));
}

/// A Nat operation the fragment admits declared: `Nat.add` or `Nat.ble`,
/// each declared as Lean does.
pub open spec fn std_nat_op_env(ne: EnvSpec, id: u64) -> bool {
    ||| (crate::expr_arena_bridge::nat_bin_op_of(ne.export, id) == Some(0u8) && std_nat_add_env(ne, id))
    ||| (crate::expr_arena_bridge::nat_bin_op_of(ne.export, id) == Some(8u8) && std_nat_ble_env(ne, id))
}

/// Such an operation is a definition.
pub proof fn std_nat_op_defined(ne: EnvSpec, id: u64)
    requires
        std_nat_op_env(ne, id),
    ensures
        ne.contains_key(id),
        ne.defs.contains_key(id),
{
    if crate::expr_arena_bridge::nat_bin_op_of(ne.export, id) == Some(0u8) && std_nat_add_env(ne, id) {
        std_nat_add_env_defined(ne, id);
    } else {
        std_nat_ble_env_defined(ne, id);
    }
}

/// THE NAT EXTENSION AGREES WITH THE DEFINITIONS (`nat_ext::h_nat_ext`)
/// where every defined Nat operation is `Nat.add` or `Nat.ble` declared as
/// Lean does: their folds are conversions of the definitions
/// (`add_fold_joins`, `ble_fold_joins`), and an operation that is no
/// definition folds in the fold-free environment too.
pub proof fn h_nat_ext_ops(env: EnvSpec)
    requires
        forall|id: u64| #[trigger] crate::expr_arena_bridge::nat_bin_op_of(env.export, id) is Some && env.defs.contains_key(id)
            ==> std_nat_op_env(env, id),
    ensures
        crate::nat_ext::h_nat_ext(env),
{
    let ne = crate::conv_frag::nofold(env);
    assert forall|s: ExprSpec| #[trigger] nat_fold_ready(env.export, s) implies defeq(ne, s, nat_fold_result(env.export, s)) by {
        let id = spine_head(s)->Const_0;
        let r = nat_fold_result(env.export, s);
        if env.defs.contains_key(id) {
            if crate::expr_arena_bridge::nat_bin_op_of(env.export, id) == Some(0u8) && std_nat_add_env(env, id) {
                add_fold_joins(env, id, s);
                let args = spine_args(s);
                let c = canon_numeral(env.export, crate::beta_model::nat_value(env.export, args[0])->Some_0
                    + crate::beta_model::nat_value(env.export, args[1])->Some_0);
                assert(pstep_star(ne, s, c) && pstep_star(ne, r, c));
            } else {
                ble_fold_joins(env, id, s);
                pstep_star_refl(ne, r);
            }
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

} // verus!
