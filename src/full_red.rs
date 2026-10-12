//! THE KERNEL'S REDUCTIONS in Lean's full judgment (docs/TYPED_TARGET.md,
//! "The conditional theorem"): recursor iota by the environment's own
//! rule, Nat-literal folding, quotient reduction, projection of a
//! constructor application, and the literals' unfoldings -- `pstep`'s
//! contractions, each at a redex. The typed rule `RedG` asks one of them
//! with both sides typed; this module carries them through every
//! syntactic operation the judgment's metatheory uses.
#[allow(unused_imports)]
use crate::expr_model::{ExprSpec, NatLitPayload};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::ti_syntax::Sig;
#[cfg(verus_only)]
use crate::beta_model::*;
#[cfg(verus_only)]
use crate::expr_model::{has_fv, nlbv, subst_expr_levels};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{nat_succ_id, nat_zero_id, EnvSpec};
#[cfg(verus_only)]
use crate::tc_model::{quot_ready, quot_result, quot_major_idx, quot_mk_spine};
#[cfg(verus_only)]
use crate::ti_subst::{psub, spsub, Sub, psub_closed, psub_spine_app, psub_spine_const};
#[cfg(verus_only)]
use crate::swap_model::fswap;
#[cfg(verus_only)]
use crate::fclose::fclose;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A Nat literal's unfolding: `Nat.zero`, or `Nat.succ` of its predecessor.
pub open spec fn lit_unfold(export: nat, n: NatLitPayload) -> ExprSpec {
    if n.0@ == 0 {
        const_expr_no_levels(nat_zero_id(export))
    } else {
        ExprSpec::App(
            Box::new(const_expr_no_levels(nat_succ_id(export))),
            Box::new(ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)))),
        )
    }
}

/// `m` contracts to `n` by one of the kernel's reductions beyond beta,
/// delta and zeta.
pub open spec fn full_red(sig: Sig, m: ExprSpec, n: ExprSpec) -> bool {
    let env = sig.ienv;
    ||| rec_ready(env, m) && n == rec_result(env, m)
    ||| env.nat_fold && nat_fold_ready(env.export, m) && n == nat_fold_result(env.export, m)
    ||| quot_ready(env.export, m) && n == quot_result(env.export, m)
    ||| m is Proj && iota_extract(env, m->Proj_0, *m->Proj_1, n)
    ||| m is NatLit && n == lit_unfold(env.export, m->NatLit_0)
    ||| m is StringLit && n == string_lit_expand_model(env.export, m->StringLit_0.0@)
}

/// A literal's type: `Nat` or `String`, as the kernel infers it.
pub open spec fn lit_ty(sig: Sig, m: ExprSpec) -> Option<ExprSpec> {
    match m {
        ExprSpec::NatLit(_) => Some(ExprSpec::Const(crate::expr_arena_bridge::nat_type_id(sig.ienv.export), Seq::empty())),
        ExprSpec::StringLit(_) => Some(ExprSpec::Const(crate::expr_arena_bridge::string_type_id(sig.ienv.export), Seq::empty())),
        _ => None,
    }
}

/// A typed literal and its type are closed and level free.
pub proof fn lit_ty_closed(sig: Sig, m: ExprSpec)
    requires
        lit_ty(sig, m) is Some,
    ensures
        nlbv(m) == 0,
        !has_fv(m),
        crate::level_inst::elp_in(m, Seq::empty()),
        nlbv(lit_ty(sig, m)->Some_0) == 0,
        !has_fv(lit_ty(sig, m)->Some_0),
        crate::level_inst::elp_in(lit_ty(sig, m)->Some_0, Seq::empty()),
{
    reveal_with_fuel(crate::level_inst::elp_in, 2);
    reveal_with_fuel(nlbv, 2);
    reveal_with_fuel(has_fv, 2);
}

/// The unfolded literal is closed and level free.
pub proof fn lit_unfold_closed(export: nat, n: NatLitPayload)
    ensures
        nlbv(lit_unfold(export, n)) == 0,
        !has_fv(lit_unfold(export, n)),
        crate::level_inst::elp_in(lit_unfold(export, n), Seq::empty()),
{
    reveal_with_fuel(nlbv, 3);
    reveal_with_fuel(has_fv, 3);
    reveal_with_fuel(crate::level_inst::elp_in, 3);
}

/// A literal's reduct is closed and level free.
proof fn lit_closed(sig: Sig, m: ExprSpec, n: ExprSpec)
    requires
        full_red(sig, m, n),
        m is NatLit || m is StringLit,
    ensures
        nlbv(n) == 0,
        !has_fv(n),
        crate::level_inst::elp_in(n, Seq::empty()),
{
    if m is NatLit {
        lit_unfold_closed(sig.ienv.export, m->NatLit_0);
    } else {
        string_lit_expand_no_fv(sig.ienv.export, m->StringLit_0.0@);
    }
}

/// A folding redex is closed.
proof fn fold_closed(export: nat, sp: ExprSpec)
    requires
        nat_fold_ready(export, sp),
    ensures
        nlbv(sp) == 0,
        nlbv(nat_fold_result(export, sp)) == 0,
{
    let args = spine_args(sp);
    crate::subst_algebra::nat_value_nlbv(export, args[0]);
    crate::subst_algebra::nat_value_nlbv(export, args[1]);
    spine_recompose(sp);
    let h = spine_head(sp);
    assert(sp == ExprSpec::App(Box::new(ExprSpec::App(Box::new(h), Box::new(args[0]))), Box::new(args[1]))) by {
        assert(args.len() == 2);
        assert(args.subrange(0, 1).subrange(0, 0) =~= Seq::<ExprSpec>::empty());
        assert(args.subrange(0, 1) =~= seq![args[0]]);
        assert(args.subrange(0, 1) == args.subrange(0, 2 - 1));
        assert(args =~= seq![args[0], args[1]]);
        assert(spine_app(h, args) == ExprSpec::App(Box::new(spine_app(h, args.subrange(0, 1))), Box::new(args[1])));
        assert(spine_app(h, args.subrange(0, 1)) == ExprSpec::App(Box::new(spine_app(h, args.subrange(0, 1).subrange(0, 0))), Box::new(args[0])));
    }
    assert(nlbv(sp) == 0) by {
        reveal_with_fuel(nlbv, 3);
    }
    assert(nlbv(nat_fold_result(export, sp)) == 0) by {
        reveal_with_fuel(nlbv, 3);
    }
}

proof fn psub_quot(t: Sub, export: nat, sp: ExprSpec)
    requires
        quot_ready(export, sp),
    ensures
        quot_ready(export, psub(sp, t)),
        psub(quot_result(export, sp), t) == quot_result(export, psub(sp, t)),
{
    psub_spine_const(t, sp);
    let args = spine_args(sp);
    let qi = quot_major_idx(export, sp)->Some_0;
    let m = args[qi as int];
    psub_spine_const(t, m);
    assert(spsub(args, t)[qi as int] == psub(m, t));
    let x = spine_args(m)[2];
    assert(spsub(args, t).skip(qi as int + 1) =~= spsub(args.skip(qi as int + 1), t));
    psub_spine_app(t, ExprSpec::App(Box::new(args[3int]), Box::new(x)), args.skip(qi as int + 1));
}

proof fn psub_iota_extract(t: Sub, env: EnvSpec, pidx: usize, inner2: ExprSpec, e2: ExprSpec)
    requires
        iota_extract(env, pidx, inner2, e2),
    ensures
        iota_extract(env, pidx, psub(inner2, t), psub(e2, t)),
{
    let (cid, lv, args2, np) = choose|cid: u64, lv: Seq<LevelSpec>, args2: Seq<ExprSpec>, np: u16|
        #![trigger spine_app(ExprSpec::Const(cid, lv), args2), args2[(np as nat + pidx as nat) as int]]
        inner2 == spine_app(ExprSpec::Const(cid, lv), args2) && env.ctor_num_params(cid) == Some(np)
            && ((np as nat + pidx as nat) < args2.len()) && (e2 == args2[(np as nat + pidx as nat) as int]);
    psub_spine_app(t, ExprSpec::Const(cid, lv), args2);
    let s2 = spsub(args2, t);
    assert(s2[(np as nat + pidx as nat) as int] == psub(e2, t));
    assert(psub(inner2, t) == spine_app(ExprSpec::Const(cid, lv), s2));
}

/// Substitution keeps a reduction one.
pub proof fn full_red_psub(sig: Sig, m: ExprSpec, n: ExprSpec, t: Sub)
    requires
        full_red(sig, m, n),
    ensures
        full_red(sig, psub(m, t), psub(n, t)),
{
    let env = sig.ienv;
    if rec_ready(env, m) && n == rec_result(env, m) {
        crate::ti_subst::psub_rec(t, env, m);
    } else if env.nat_fold && nat_fold_ready(env.export, m) && n == nat_fold_result(env.export, m) {
        fold_closed(env.export, m);
        psub_closed(m, t);
        psub_closed(n, t);
    } else if quot_ready(env.export, m) && n == quot_result(env.export, m) {
        psub_quot(t, env.export, m);
    } else if m is Proj && iota_extract(env, m->Proj_0, *m->Proj_1, n) {
        psub_iota_extract(t, env, m->Proj_0, *m->Proj_1, n);
    } else {
        lit_closed(sig, m, n);
        psub_closed(n, t);
    }
}

/// So does swapping two locals.
pub proof fn full_red_fswap(sig: Sig, m: ExprSpec, n: ExprSpec, x: nat, y: nat)
    requires
        full_red(sig, m, n),
    ensures
        full_red(sig, fswap(m, x, y), fswap(n, x, y)),
{
    let env = sig.ienv;
    crate::swap_model::fswap_rec(env, m, x, y);
    crate::swap_model::fswap_nat_fold(env.export, m, x, y);
    crate::swap_model::fswap_quot(env.export, m, x, y);
    if rec_ready(env, m) && n == rec_result(env, m) {
    } else if env.nat_fold && nat_fold_ready(env.export, m) && n == nat_fold_result(env.export, m) {
    } else if quot_ready(env.export, m) && n == quot_result(env.export, m) {
    } else if m is Proj && iota_extract(env, m->Proj_0, *m->Proj_1, n) {
        crate::swap_model::fswap_iota_extract(env, m->Proj_0, *m->Proj_1, n, x, y);
    } else {
        lit_closed(sig, m, n);
        crate::swap_model::fswap_closed(n, x, y);
    }
}

/// And closing a local.
pub proof fn full_red_fclose(sig: Sig, k: nat, c: nat, m: ExprSpec, n: ExprSpec)
    requires
        crate::swap_model::env_fv_free(sig.ienv),
        full_red(sig, m, n),
    ensures
        full_red(sig, fclose(k, c, m), fclose(k, c, n)),
{
    let env = sig.ienv;
    if rec_ready(env, m) && n == rec_result(env, m) {
        crate::fclose::fclose_rec(k, c, env, m);
    } else if env.nat_fold && nat_fold_ready(env.export, m) && n == nat_fold_result(env.export, m) {
        crate::fclose::fclose_nat_fold(k, c, env.export, m);
    } else if quot_ready(env.export, m) && n == quot_result(env.export, m) {
        crate::fclose::fclose_quot(k, c, env.export, m);
    } else if m is Proj && iota_extract(env, m->Proj_0, *m->Proj_1, n) {
        crate::fclose::fclose_iota_extract(k, c, env, m->Proj_0, *m->Proj_1, n);
    } else {
        lit_closed(sig, m, n);
        crate::fclose::fclose_closed(k, c, n);
    }
}

/// And a level instance.
pub proof fn full_red_ls(sig: Sig, m: ExprSpec, n: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        crate::level_inst::env_lp_ok(sig.ienv),
        full_red(sig, m, n),
    ensures
        full_red(sig, subst_expr_levels(m, ks, vs), subst_expr_levels(n, ks, vs)),
{
    let env = sig.ienv;
    if rec_ready(env, m) && n == rec_result(env, m) {
        crate::beta_model::rec_ready_u_of(env, m);
        crate::level_inst::li_rec(env, m, ks, vs);
    } else if env.nat_fold && nat_fold_ready(env.export, m) && n == nat_fold_result(env.export, m) {
        crate::level_inst::li_nat_fold(env.export, m, ks, vs);
        crate::level_inst::li_nat_fold_result(env.export, m, ks, vs);
    } else if quot_ready(env.export, m) && n == quot_result(env.export, m) {
        crate::level_inst::li_quot(env.export, m, ks, vs);
    } else if m is Proj && iota_extract(env, m->Proj_0, *m->Proj_1, n) {
        crate::level_inst::li_iota_extract(env, m->Proj_0, *m->Proj_1, n, ks, vs);
    } else {
        lit_closed(sig, m, n);
        crate::level_inst::expr_closed(n, ks, vs);
    }
}

/// And a larger environment.
pub proof fn full_red_sub(sig: Sig, sig2: Sig, m: ExprSpec, n: ExprSpec)
    requires
        sig.ienv.sub(sig2.ienv),
        full_red(sig, m, n),
    ensures
        full_red(sig2, m, n),
{
    let env = sig.ienv;
    if rec_ready(env, m) && n == rec_result(env, m) {
        crate::ti_valid::rec_sub(env, sig2.ienv, m);
    } else if m is Proj && iota_extract(env, m->Proj_0, *m->Proj_1, n) {
        let (cid, lv, args2, np) = choose|cid: u64, lv: Seq<LevelSpec>, args2: Seq<ExprSpec>, np: u16|
            #![trigger spine_app(ExprSpec::Const(cid, lv), args2), args2[(np as nat + m->Proj_0 as nat) as int]]
            *m->Proj_1 == spine_app(ExprSpec::Const(cid, lv), args2) && env.ctor_num_params(cid) == Some(np)
                && ((np as nat + m->Proj_0 as nat) < args2.len()) && (n == args2[(np as nat + m->Proj_0 as nat) as int]);
        assert(sig2.ienv.ctor_num_params(cid) == Some(np));
    }
}

} // verus!
