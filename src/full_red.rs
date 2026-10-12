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
#[cfg(verus_only)]
use crate::rec_canon::{tdoms, tbody, tarity};
#[cfg(verus_only)]
use crate::ti_spine::vsub;
#[cfg(verus_only)]
use crate::level_inst::elp_in;
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

/// STRUCTURE ETA: `y` is a structure's constructor applied to parameters
/// and `x`'s projections. (With both sides typed alike, the parameters and
/// levels are `x`'s type's.)
pub open spec fn eta_g(sig: Sig, x: ExprSpec, y: ExprSpec) -> bool {
    let h = spine_head(y);
    h is Const && sig.ienv.ctor_ind.contains_key(h->Const_0) && {
        let c = h->Const_0;
        let s = sig.ienv.ctor_ind[c];
        let args = spine_args(y);
        &&& sig.ienv.struct_ctor.contains_key(s) && sig.ienv.struct_ctor[s] == c
        &&& sig.ienv.ctor_np.contains_key(c) && sig.ienv.ctor_nf.contains_key(c)
        &&& args.len() == sig.ienv.ctor_np[c] + sig.ienv.ctor_nf[c]
        &&& args.subrange(sig.ienv.ctor_np[c] as int, args.len() as int) == crate::tc_model::eta_projs(x, sig.ienv.ctor_nf[c] as nat)
    }
}

/// A UNIT-LIKE TYPE: a structure without fields, applied.
pub open spec fn unit_ty(sig: Sig, t: ExprSpec) -> bool {
    spine_head(t) is Const && crate::tc_model::unit_like_head(sig.ienv, spine_head(t)->Const_0)
}

/// THE FULL JUDGMENT'S EXTRA CONVERSIONS at type `t`: a kernel reduction,
/// structure eta, or any two terms of a unit-like type.
pub open spec fn full_conv(sig: Sig, m: ExprSpec, n: ExprSpec, t: ExprSpec) -> bool {
    full_red(sig, m, n) || eta_g(sig, m, n) || unit_ty(sig, t)
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

/// Substitution keeps the extra conversions.
pub proof fn full_conv_psub(sig: Sig, m: ExprSpec, n: ExprSpec, t: ExprSpec, q: Sub)
    requires
        full_conv(sig, m, n, t),
    ensures
        full_conv(sig, psub(m, q), psub(n, q), psub(t, q)),
{
    if full_red(sig, m, n) {
        full_red_psub(sig, m, n, q);
    } else if eta_g(sig, m, n) {
        psub_spine_const(q, n);
        let args = spine_args(n);
        let c = spine_head(n)->Const_0;
        let np = sig.ienv.ctor_np[c] as int;
        let nf = sig.ienv.ctor_nf[c] as nat;
        crate::ti_subst::spsub_subrange(args, q, np, args.len() as int);
        let ps = crate::tc_model::eta_projs(m, nf);
        let ps2 = crate::tc_model::eta_projs(psub(m, q), nf);
        assert forall|i: int| 0 <= i < nf implies #[trigger] spsub(ps, q)[i] == ps2[i] by {
            assert(psub(ExprSpec::Proj(i as usize, Box::new(m)), q) == ExprSpec::Proj(i as usize, Box::new(psub(m, q))));
        }
        assert(spsub(ps, q) =~= ps2);
    } else {
        psub_spine_const(q, t);
    }
}

/// So does swapping two locals.
pub proof fn full_conv_fswap(sig: Sig, m: ExprSpec, n: ExprSpec, t: ExprSpec, x: nat, y: nat)
    requires
        full_conv(sig, m, n, t),
    ensures
        full_conv(sig, fswap(m, x, y), fswap(n, x, y), fswap(t, x, y)),
{
    use crate::swap_model::sswap;
    if full_red(sig, m, n) {
        full_red_fswap(sig, m, n, x, y);
    } else if eta_g(sig, m, n) {
        crate::swap_model::fswap_spine(n, x, y);
        let args = spine_args(n);
        let c = spine_head(n)->Const_0;
        let np = sig.ienv.ctor_np[c] as int;
        let nf = sig.ienv.ctor_nf[c] as nat;
        assert(sswap(args, x, y).subrange(np, args.len() as int) =~= sswap(args.subrange(np, args.len() as int), x, y));
        let ps = crate::tc_model::eta_projs(m, nf);
        let ps2 = crate::tc_model::eta_projs(fswap(m, x, y), nf);
        assert forall|i: int| 0 <= i < nf implies #[trigger] sswap(ps, x, y)[i] == ps2[i] by {
            assert(fswap(ExprSpec::Proj(i as usize, Box::new(m)), x, y) == ExprSpec::Proj(i as usize, Box::new(fswap(m, x, y))));
        }
        assert(sswap(ps, x, y) =~= ps2);
    } else {
        crate::swap_model::fswap_spine(t, x, y);
    }
}

/// And closing a local.
pub proof fn full_conv_fclose(sig: Sig, k: nat, c: nat, m: ExprSpec, n: ExprSpec, t: ExprSpec)
    requires
        crate::swap_model::env_fv_free(sig.ienv),
        full_conv(sig, m, n, t),
    ensures
        full_conv(sig, fclose(k, c, m), fclose(k, c, n), fclose(k, c, t)),
{
    use crate::fclose::sclose;
    if full_red(sig, m, n) {
        full_red_fclose(sig, k, c, m, n);
    } else if eta_g(sig, m, n) {
        crate::fclose::fclose_spine_const(k, c, n);
        let args = spine_args(n);
        let cid = spine_head(n)->Const_0;
        let np = sig.ienv.ctor_np[cid] as int;
        let nf = sig.ienv.ctor_nf[cid] as nat;
        assert(sclose(k, c, args).subrange(np, args.len() as int) =~= sclose(k, c, args.subrange(np, args.len() as int)));
        let ps = crate::tc_model::eta_projs(m, nf);
        let ps2 = crate::tc_model::eta_projs(fclose(k, c, m), nf);
        assert forall|i: int| 0 <= i < nf implies #[trigger] sclose(k, c, ps)[i] == ps2[i] by {
            assert(fclose(k, c, ExprSpec::Proj(i as usize, Box::new(m))) == ExprSpec::Proj(i as usize, Box::new(fclose(k, c, m))));
        }
        assert(sclose(k, c, ps) =~= ps2);
    } else {
        crate::fclose::fclose_spine_const(k, c, t);
    }
}

/// And a level instance.
pub proof fn full_conv_ls(sig: Sig, m: ExprSpec, n: ExprSpec, t: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        crate::level_inst::env_lp_ok(sig.ienv),
        full_conv(sig, m, n, t),
    ensures
        full_conv(sig, subst_expr_levels(m, ks, vs), subst_expr_levels(n, ks, vs), subst_expr_levels(t, ks, vs)),
{
    use crate::level_inst::sli;
    if full_red(sig, m, n) {
        full_red_ls(sig, m, n, ks, vs);
    } else if eta_g(sig, m, n) {
        crate::level_inst::li_spine_const(n, ks, vs);
        let args = spine_args(n);
        let c = spine_head(n)->Const_0;
        let np = sig.ienv.ctor_np[c] as int;
        let nf = sig.ienv.ctor_nf[c] as nat;
        assert(sli(args, ks, vs).subrange(np, args.len() as int) =~= sli(args.subrange(np, args.len() as int), ks, vs));
        let ps = crate::tc_model::eta_projs(m, nf);
        let ps2 = crate::tc_model::eta_projs(subst_expr_levels(m, ks, vs), nf);
        assert forall|i: int| 0 <= i < nf implies #[trigger] sli(ps, ks, vs)[i] == ps2[i] by {
            assert(subst_expr_levels(ExprSpec::Proj(i as usize, Box::new(m)), ks, vs) == ExprSpec::Proj(i as usize, Box::new(subst_expr_levels(m, ks, vs))));
        }
        assert(sli(ps, ks, vs) =~= ps2);
    } else {
        crate::level_inst::li_spine_const(t, ks, vs);
    }
}

/// And a larger environment whose constructor tables agree.
pub proof fn full_conv_sub(sig: Sig, sig2: Sig, m: ExprSpec, n: ExprSpec, t: ExprSpec)
    requires
        sig.ienv.sub(sig2.ienv),
        forall|k: u64| #[trigger] sig.ienv.ctor_ind.contains_key(k) ==> sig2.ienv.ctor_ind.contains_key(k) && sig2.ienv.ctor_ind[k] == sig.ienv.ctor_ind[k],
        forall|k: u64| #[trigger] sig.ienv.struct_ctor.contains_key(k) ==> sig2.ienv.struct_ctor.contains_key(k) && sig2.ienv.struct_ctor[k] == sig.ienv.struct_ctor[k],
        forall|k: u64| #[trigger] sig.ienv.ctor_nf.contains_key(k) ==> sig2.ienv.ctor_nf.contains_key(k) && sig2.ienv.ctor_nf[k] == sig.ienv.ctor_nf[k],
        full_conv(sig, m, n, t),
    ensures
        full_conv(sig2, m, n, t),
{
    if full_red(sig, m, n) {
        full_red_sub(sig, sig2, m, n);
    } else if eta_g(sig, m, n) {
        let c = spine_head(n)->Const_0;
        assert(sig2.ienv.ctor_np[c] == sig.ienv.ctor_np[c]);
    } else {
        let id = spine_head(t)->Const_0;
        let c = choose|c: u64| #[trigger] sig.ienv.struct_ctor(id) == Some(c) && sig.ienv.ctor_num_fields(c) == Some(0u16);
        assert(sig2.ienv.struct_ctor(id) == Some(c) && sig2.ienv.ctor_num_fields(c) == Some(0u16));
    }
}

/// A STRUCTURE as the full judgment projects it: a structure-table entry
/// whose constructor is declared with its tables and the structure's
/// level parameters, its type closed, the structure's ending in a sort.
pub open spec fn gstruct(sig: Sig, s: u64) -> bool {
    let c = sig.ienv.struct_ctor[s];
    &&& sig.ienv.struct_ctor.contains_key(s) && sig.consts.contains_key(s) && sig.consts.contains_key(c)
    &&& sig.ienv.ctor_np.contains_key(c) && sig.ienv.ctor_nf.contains_key(c)
    &&& sig.consts[c].lps == sig.consts[s].lps
    &&& nlbv(sig.consts[c].ty) == 0
    &&& tbody(sig.consts[s].ty, tarity(sig.consts[s].ty)) is Sort
}

/// Field `i`'s binder in the constructor's type, at the instance `us`,
/// over the parameters and the earlier fields.
pub open spec fn gfield(sig: Sig, s: u64, i: nat, us: Seq<LevelSpec>) -> ExprSpec {
    let c = sig.ienv.struct_ctor[s];
    let np = sig.ienv.ctor_np[c] as nat;
    subst_expr_levels(tdoms(sig.consts[c].ty, np + i + 1)[(np + i) as int], sig.consts[c].lps, us)
}

/// THE TYPE OF A PROJECTION of any structure, as the kernel's `infer_proj`
/// walks the constructor's type: field `i` at the structure application
/// `st`'s instance, over its parameters and `x`'s earlier projections.
#[verifier::opaque]
pub open spec fn gproj_ty(sig: Sig, st: ExprSpec, i: nat, x: ExprSpec) -> Option<ExprSpec> {
    let h = spine_head(st);
    let ps = spine_args(st);
    if h is Const && gstruct(sig, h->Const_0) {
        let (s, us) = (h->Const_0, h->Const_1);
        let c = sig.ienv.struct_ctor[s];
        let np = sig.ienv.ctor_np[c] as nat;
        if ps.len() == np && i < sig.ienv.ctor_nf[c] && us.len() == sig.consts[c].lps.len()
            && tdoms(sig.consts[c].ty, np + i + 1).len() == np + i + 1 {
            Some(vsub(gfield(sig, s, i, us), ps + crate::ti_syntax::projs(x, i)))
        } else {
            None
        }
    } else {
        None
    }
}

/// A telescope's domains: each mentions only the binders before it, and
/// no local or level parameter the telescope does not.
pub proof fn tdoms_facts(t: ExprSpec, n: nat, c: nat, us: Seq<u64>)
    ensures
        tdoms(t, n).len() <= n,
        forall|k: int| 0 <= k < tdoms(t, n).len() ==>
            (nlbv(t) <= c ==> nlbv(#[trigger] tdoms(t, n)[k]) <= c + k)
            && (!has_fv(t) ==> !has_fv(tdoms(t, n)[k]))
            && (elp_in(t, us) ==> elp_in(tdoms(t, n)[k], us)),
    decreases n,
{
    if n > 0 {
        if let ExprSpec::Bind(crate::expr_model::BinderKind::Pi, a, b) = t {
            tdoms_facts(*b, (n - 1) as nat, c + 1, us);
            let ds = tdoms(t, n);
            assert(ds == seq![*a] + tdoms(*b, (n - 1) as nat));
            assert forall|k: int| 0 <= k < ds.len() implies
                (nlbv(t) <= c ==> nlbv(#[trigger] ds[k]) <= c + k)
                && (!has_fv(t) ==> !has_fv(ds[k]))
                && (elp_in(t, us) ==> elp_in(ds[k], us)) by {
                if k > 0 {
                    assert(ds[k] == tdoms(*b, (n - 1) as nat)[k - 1]);
                }
            }
        }
    }
}

/// A telescope's body mentions no level parameter the telescope does not.
pub proof fn elp_tbody(t: ExprSpec, n: nat, us: Seq<u64>)
    requires
        elp_in(t, us),
    ensures
        elp_in(tbody(t, n), us),
    decreases n,
{
    if n > 0 {
        if let ExprSpec::Bind(crate::expr_model::BinderKind::Pi, a, b) = t {
            elp_tbody(*b, (n - 1) as nat, us);
        }
    }
}

/// The projected field, when the projection is typed: closed over the
/// parameters and earlier fields, and without locals when the constructor
/// has none.
proof fn gfield_facts(sig: Sig, st: ExprSpec, i: nat, x: ExprSpec)
    requires
        gproj_ty(sig, st, i, x) is Some,
    ensures ({
        let (s, us) = (spine_head(st)->Const_0, spine_head(st)->Const_1);
        let c = sig.ienv.struct_ctor[s];
        let f = gfield(sig, s, i, us);
        let xs = spine_args(st) + crate::ti_syntax::projs(x, i);
        &&& spine_head(st) is Const && gstruct(sig, s)
        &&& nlbv(f) <= xs.len()
        &&& (!has_fv(sig.consts[c].ty) ==> !has_fv(f))
        &&& gproj_ty(sig, st, i, x) == Some(vsub(f, xs))
        &&& spine_args(st).len() == sig.ienv.ctor_np[c] && us.len() == sig.consts[c].lps.len()
        &&& i < sig.ienv.ctor_nf[c] && tdoms(sig.consts[c].ty, sig.ienv.ctor_np[c] as nat + i + 1).len() == sig.ienv.ctor_np[c] as nat + i + 1
    }),
{
    reveal(gproj_ty);
    let (s, us) = (spine_head(st)->Const_0, spine_head(st)->Const_1);
    let c = sig.ienv.struct_ctor[s];
    let np = sig.ienv.ctor_np[c] as nat;
    let ct = sig.consts[c].ty;
    tdoms_facts(ct, np + i + 1, 0, sig.consts[c].lps);
    let d = tdoms(ct, np + i + 1)[(np + i) as int];
    crate::tc::subst_levels_nlbv(d, sig.consts[c].lps, us);
    crate::expr_model::subst_expr_levels_has_fv(d, sig.consts[c].lps, us);
}

/// It commutes with substitution.
pub proof fn gproj_ty_psub(sig: Sig, st: ExprSpec, i: nat, x: ExprSpec, t: Sub)
    requires
        gproj_ty(sig, st, i, x) is Some,
    ensures
        gproj_ty(sig, psub(st, t), i, psub(x, t)) == Some(psub(gproj_ty(sig, st, i, x)->Some_0, t)),
        crate::ti_syntax::proj_prop(sig, psub(st, t)) == crate::ti_syntax::proj_prop(sig, st),
{
    gfield_facts(sig, st, i, x);
    reveal(gproj_ty);
    reveal(crate::ti_syntax::proj_prop);
    psub_spine_const(t, st);
    let (s, us) = (spine_head(st)->Const_0, spine_head(st)->Const_1);
    let ps = spine_args(st);
    let f = gfield(sig, s, i, us);
    let xs = ps + crate::ti_syntax::projs(x, i);
    crate::ti_proj::psub_vsub(f, xs, t);
    assert(spsub(xs, t) =~= spsub(ps, t) + crate::ti_syntax::projs(psub(x, t), i));
}

/// So does swapping two locals.
pub proof fn gproj_ty_fswap(sig: Sig, st: ExprSpec, i: nat, x: ExprSpec, xx: nat, yy: nat)
    requires
        crate::ti_locals::sig_fv_free(sig),
        gproj_ty(sig, st, i, x) is Some,
    ensures
        gproj_ty(sig, fswap(st, xx, yy), i, fswap(x, xx, yy)) == Some(fswap(gproj_ty(sig, st, i, x)->Some_0, xx, yy)),
        crate::ti_syntax::proj_prop(sig, fswap(st, xx, yy)) == crate::ti_syntax::proj_prop(sig, st),
{
    gfield_facts(sig, st, i, x);
    reveal(gproj_ty);
    reveal(crate::ti_syntax::proj_prop);
    crate::swap_model::fswap_spine(st, xx, yy);
    let (s, us) = (spine_head(st)->Const_0, spine_head(st)->Const_1);
    let ps = spine_args(st);
    let f = gfield(sig, s, i, us);
    let xs = ps + crate::ti_syntax::projs(x, i);
    assert(sig.consts.contains_key(sig.ienv.struct_ctor[s]));
    crate::swap_model::fswap_closed(f, xx, yy);
    crate::ti_proj::fswap_vsub(f, xs, xx, yy);
    assert(crate::swap_model::sswap(xs, xx, yy) =~= crate::swap_model::sswap(ps, xx, yy) + crate::ti_syntax::projs(fswap(x, xx, yy), i));
}

/// And closing a local.
pub proof fn gproj_ty_fclose(sig: Sig, st: ExprSpec, i: nat, x: ExprSpec, k: nat, c: nat)
    requires
        crate::ti_locals::sig_fv_free(sig),
        gproj_ty(sig, st, i, x) is Some,
    ensures
        gproj_ty(sig, fclose(k, c, st), i, fclose(k, c, x)) == Some(fclose(k, c, gproj_ty(sig, st, i, x)->Some_0)),
        crate::ti_syntax::proj_prop(sig, fclose(k, c, st)) == crate::ti_syntax::proj_prop(sig, st),
{
    gfield_facts(sig, st, i, x);
    reveal(gproj_ty);
    reveal(crate::ti_syntax::proj_prop);
    crate::fclose::fclose_spine_const(k, c, st);
    let (s, us) = (spine_head(st)->Const_0, spine_head(st)->Const_1);
    let ps = spine_args(st);
    let f = gfield(sig, s, i, us);
    let xs = ps + crate::ti_syntax::projs(x, i);
    assert(sig.consts.contains_key(sig.ienv.struct_ctor[s]));
    crate::fclose::fclose_closed(k, c + xs.len(), f);
    crate::ti_proj::fclose_vsub(k, c, f, xs);
    assert(crate::fclose::sclose(k, c, xs) =~= crate::fclose::sclose(k, c, ps) + crate::ti_syntax::projs(fclose(k, c, x), i));
}

/// And a level instance; a proposition stays one.
pub proof fn gproj_ty_ls(sig: Sig, st: ExprSpec, i: nat, x: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        crate::ti_level::sig_lp_ok(sig, ks, vs),
        gproj_ty(sig, st, i, x) is Some,
    ensures
        gproj_ty(sig, subst_expr_levels(st, ks, vs), i, subst_expr_levels(x, ks, vs))
            == Some(subst_expr_levels(gproj_ty(sig, st, i, x)->Some_0, ks, vs)),
        crate::ti_syntax::proj_prop(sig, subst_expr_levels(st, ks, vs)) ==> crate::ti_syntax::proj_prop(sig, st),
{
    gfield_facts(sig, st, i, x);
    reveal(gproj_ty);
    let st2 = subst_expr_levels(st, ks, vs);
    crate::level_inst::li_spine_const(st, ks, vs);
    let (s, us) = (spine_head(st)->Const_0, spine_head(st)->Const_1);
    let us2 = crate::level_model::subst_levels_spec(us, ks, vs);
    let ps = spine_args(st);
    let c = sig.ienv.struct_ctor[s];
    let np = sig.ienv.ctor_np[c] as nat;
    let ct = sig.consts[c].ty;
    let lps = sig.consts[c].lps;
    // the field at the instantiated instance
    assert(elp_in(ct, lps));
    tdoms_facts(ct, np + i + 1, 0, lps);
    let d = tdoms(ct, np + i + 1)[(np + i) as int];
    crate::level_inst::expr_compose(d, lps, us, ks, vs);
    let f = gfield(sig, s, i, us);
    assert(subst_expr_levels(f, ks, vs) == gfield(sig, s, i, us2));
    let xs = ps + crate::ti_syntax::projs(x, i);
    crate::ti_proj::ls_vsub(f, xs, ks, vs);
    assert(crate::level_inst::sli(xs, ks, vs) =~= crate::level_inst::sli(ps, ks, vs) + crate::ti_syntax::projs(subst_expr_levels(x, ks, vs), i));
    // the sort
    reveal(crate::ti_syntax::proj_prop);
    let ts = sig.consts[s].ty;
    let slps = sig.consts[s].lps;
    assert(elp_in(ts, slps));
    elp_tbody(ts, tarity(ts), slps);
    let l0 = tbody(ts, tarity(ts))->Sort_0;
    assert(crate::level_inst::lp_in(l0, slps));
    if us.len() == slps.len() {
        crate::level_inst::lvl_compose(l0, slps, us, ks, vs);
    }
    let l1 = crate::level_model::subst_level_spec(l0, slps, us);
    if crate::ti_syntax::proj_prop(sig, st2) && us.len() == slps.len() {
        let rho = choose|rho: Map<nat, nat>| !(crate::level_model::interp(crate::level_model::subst_level_spec(l0, slps, us2), rho) > 0);
        crate::level_model::subst_level_spec_interp(l1, ks, vs, rho);
        let rho2 = crate::level_model::subst_env(rho, ks, vs);
        assert(!(crate::level_model::interp(l1, rho2) > 0));
    }
}

/// Two signatures with the same constants and tables project alike.
pub proof fn gproj_same(s1: Sig, s2: Sig, st: ExprSpec, i: nat, x: ExprSpec)
    requires
        s1.consts == s2.consts,
        s1.ienv == s2.ienv,
    ensures
        gproj_ty(s2, st, i, x) == gproj_ty(s1, st, i, x),
        crate::ti_syntax::proj_prop(s2, st) == crate::ti_syntax::proj_prop(s1, st),
{
    reveal(gproj_ty);
    reveal(crate::ti_syntax::proj_prop);
}

/// It reads only the constants and the tables.
pub proof fn gproj_congr(s1: Sig, s2: Sig, st: ExprSpec, i: nat, x: ExprSpec)
    requires
        forall|c: u64| #[trigger] s1.consts.contains_key(c) ==> s2.consts.contains_key(c) && s2.consts[c] == s1.consts[c],
        forall|k: u64| #[trigger] s1.ienv.struct_ctor.contains_key(k) ==> s2.ienv.struct_ctor.contains_key(k) && s2.ienv.struct_ctor[k] == s1.ienv.struct_ctor[k],
        forall|k: u64| #[trigger] s1.ienv.ctor_nf.contains_key(k) ==> s2.ienv.ctor_nf.contains_key(k) && s2.ienv.ctor_nf[k] == s1.ienv.ctor_nf[k],
        s1.ienv.sub(s2.ienv),
        gproj_ty(s1, st, i, x) is Some,
    ensures
        gproj_ty(s2, st, i, x) == gproj_ty(s1, st, i, x),
        crate::ti_syntax::proj_prop(s2, st) == crate::ti_syntax::proj_prop(s1, st),
{
    gfield_facts(s1, st, i, x);
    reveal(gproj_ty);
    reveal(crate::ti_syntax::proj_prop);
    let s = spine_head(st)->Const_0;
    let c = s1.ienv.struct_ctor[s];
    assert(s2.ienv.ctor_np[c] == s1.ienv.ctor_np[c]);
    assert(s2.consts[c] == s1.consts[c]);
    assert(s2.consts[s] == s1.consts[s]);
}

} // verus!
