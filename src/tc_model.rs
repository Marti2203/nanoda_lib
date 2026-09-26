//! Exploratory Verus model of `tc.rs`'s `get_rec_rule` and `unfold_def`.
//!
//! `get_rec_rule`: given the recursor rules for an inductive type and the
//! (already-whnf'd) major premise of a recursor application, find the
//! computation rule for the major premise's head constructor. This selects
//! *which* iota-reduction rule fires during recursor unfolding -- a bug
//! here (returning the wrong rule, or failing to find an existing one)
//! would make the type checker apply the wrong reduction, a genuine
//! soundness hole, even though the function itself is just a bounded
//! linear search independent of `whnf`/`def_eq`'s mutual recursion.
//!
//! Both `get_rec_rule` and `unfold_def` are private (no `pub(crate)`), so
//! -- same situation as `parser.rs`'s `go1` in `parser_model.rs` -- these
//! are standalone reimplementations proven correct and conditional on a
//! manual transcription of the real bodies (`tc.rs:201-210`/`tc.rs:1153-
//! 1163`) staying accurate, rather than `assume_specification`s wired
//! directly to the real functions.
//!
//! `get_rec_rule` reuses `util_model.rs`'s `find_index`/`find_index_correct`
//! directly: the search here is exactly "find the first element of a
//! sequence (`rec_rules`, projected to `ctor_name`) equal to a given value
//! (`major_ctor_name`)", the same abstraction `util.rs`'s `alloc_*`
//! functions needed.
//!
//! `unfold_def` composes bridges from three other files: `expr_arena_
//! bridge.rs`'s `verified_unfold_apps`/`verified_subst_expr_levels`/
//! `verified_foldl_apps` (peel the `Const`'s applied args, substitute the
//! definition body's level parameters, reapply the args) and
//! `Env::get_declar_val` (the real declaration lookup, verified against the
//! definitions map) --
//! the capstone connecting real delta reduction to a genuine `pstep_star`
//! step, the way `expr_arena_bridge.rs`'s `verified_whnf_beta_step`/
//! `verified_whnf_zeta_step` already do for beta/zeta.
#[cfg(verus_only)]
use crate::beta_model::pstep_env_weaken;
#[cfg(verus_only)]
use crate::beta_model::size;
#[cfg(verus_only)]
use crate::beta_model::spine_app_concat;
#[cfg(verus_only)]
use crate::beta_model::{const_expr_no_levels, const_expr_no_levels_canonical, defeq, defeq_of_pstep_star, defeq_refl, defeq_symm, depth_le_size, max_var_below, max_var_below_mono, nlbv_bound_implies_max_var_below, nlbv_shift_noop, pstep, pstep_spine_app_star, pstep_star, pstep_star_app_arg_congr, pstep_star_env_weaken, pstep_star_iota, pstep_star_one, pstep_star_refl, pstep_star_trans, shift, spine_app, spine_app_bounds, spine_app_decompose, spine_app_nlbv, spine_bind, spine_bind_depth, spine_bind_nlbv, subst_expr_levels_rel_depth, subst_expr_levels_rel_nlbv, subst_full_depth_bound_n, subst_full_nlbv_bound_n};
#[cfg(verus_only)]
use crate::beta_model::{find_rule, nat_bin_op_eval, nat_fold_ready, nat_fold_result, nat_fold_result_bounds, nat_value, pstep_fold_intro, pstep_rec_intro, pstep_star_proj_congr, pstep_star_spine_update, rec_prefix, rec_ready, rec_result, spine_app_compose_last, spine_app_nlbv_decompose, spine_args, spine_destruct_app, spine_head, subst_full_compose, subst_full_empty, subst_full_nlbv_bound};
use crate::env::ReducibilityHint;
use crate::env::{Env, RecRule};
#[cfg(verus_only)]
use crate::env_model::to_model as reducibility_hint_to_model;
#[cfg(verus_only)]
use crate::env_model::to_model_of_ctor_num_params;
#[cfg(verus_only)]
use crate::env_model::to_model_of_declar_hint;
#[cfg(verus_only)]
use crate::env_model::to_model_of_declar_ty;
#[cfg(verus_only)]
use crate::env_model::to_model_of_env;
#[cfg(verus_only)]
use crate::env_model::{env_model_nofv, env_model_nofv_has, env_model_nofv_sub, rec_rules_model, to_model_of_recursors};
use crate::env_model::{get_constructor_num_params, get_declar_hint, get_declar_info_ty, get_recursor_data, reducibility_hint_as_regular};
use crate::expr::{BinderStyle, Expr};
#[cfg(verus_only)]
use crate::expr_arena_bridge::arena_lctx;
#[cfg(verus_only)]
use crate::expr_arena_bridge::bignum_ptr_value;
use crate::expr_arena_bridge::get_dbj_level_counter;
#[cfg(verus_only)]
use crate::expr_arena_bridge::to_model;
use crate::expr_arena_bridge::verified_size;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{bool_false_id, bool_true_id, nat_repr_is_zero, nat_repr_pred, nat_succ_id, nat_zero_id};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{nat_type_id, string_type_id};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{const_id, const_levels_of, const_levels_vec, const_levels_vec_model, const_name_of, is_const_shape, is_const_shape_model};
#[cfg(verus_only)]
use crate::expr_arena_bridge::quot_kind_of;
use crate::expr_arena_bridge::{expr_as_app, expr_as_lambda, expr_as_local, expr_as_pi, expr_as_proj, expr_as_sort, expr_ptr_eq, fvar_id_eq, verified_inst, verified_whnf_no_unfolding_step_plain};
use crate::expr_arena_bridge::{expr_as_nat_lit, read_bignum_value, verified_foldl_apps, verified_nat_lit_to_constructor, verified_string_free, verified_subst_expr_levels, verified_whnf_no_unfolding_step};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{is_local_shape, local_binder_type_of, local_id_of};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{is_nat_lit_shape, is_nat_lit_shape_model, nat_lit_value};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{RecDataSpec, RecRuleSpec};
#[cfg(verus_only)]
use crate::expr_model::has_fv;
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
use crate::expr_model::BinderKind;
use crate::expr_model::NatLitPayload;
#[cfg(verus_only)]
use crate::expr_model::{abstr_full, depth, fv_absent, nlbv, subst_expr_levels_rel, subst_full, unreach};
#[cfg(verus_only)]
use crate::expr_model::{subst_expr_levels, subst_expr_levels_empty, subst_expr_levels_rel_empty};
#[cfg(verus_only)]
use crate::level_arena_bridge::name_id_injective;
use crate::level_arena_bridge::name_ptr_eq;
use crate::level_arena_bridge::read_levels_vec;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model as level_to_model;
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, to_model_of_levels};
#[cfg(verus_only)]
use crate::level_model::interp;
#[cfg(verus_only)]
use crate::level_model::level_names;
#[cfg(verus_only)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::nat_lit_model::to_nat;
use crate::nat_lit_model::{biguint_add, biguint_eq, biguint_le, biguint_mul, biguint_succ};
use crate::util::LevelPtr;
use crate::util::{nat_div, nat_gcd, nat_land, nat_lor, nat_mod, nat_shl, nat_shr, nat_sub, nat_xor};
use crate::util::{ExprPtr, LevelsPtr, NamePtr, TcCtx};
#[cfg(verus_only)]
use crate::util_model::find_index;
use num_bigint::BigUint;
#[allow(unused_imports)]
use num_traits::Pow;
#[allow(unused_imports)]
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
use vstd::prelude::*;

verus! {

broadcast use crate::util::ptr_eta, crate::util::lemma_export_arena;

/// Which typing the typed leaves of conversion consult. `Real` checks
/// application arguments against the domain; `Infer` is the kernel's
/// `InferOnly` mode, which does not; `InferWt` is `Infer` whose typed leaves
/// also require both sides to be really well-typed (the metatheory's
/// well-typed-chain form, `docs/METATHEORY.md`).
#[derive(PartialEq, Eq, Structural)]
pub enum IoMode {
    Real,
    Infer,
    InferWt,
}

/// `InferWt`'s condition on a term a typed leaf types internally: it has a
/// real type, below the leaf's height.
pub open spec fn wt1(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    e: ExprSpec,
    h: nat,
) -> bool
    decreases h, 2int, 0nat,
{
    io != IoMode::InferWt || exists|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f < h && types_to(dty, denv, lctx, IoMode::Real, e, t, f)
}

pub proof fn wt1_mono(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    e: ExprSpec,
    h1: nat,
    h2: nat,
)
    requires
        wt1(dty, denv, lctx, io, e, h1),
        h1 <= h2,
    ensures
        wt1(dty, denv, lctx, io, e, h2),
{
    if io == IoMode::InferWt {
        let (t, f) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f < h1 && types_to(dty, denv, lctx, IoMode::Real, e, t, f);
        assert(wt_marker(t, f));
    }
}

pub proof fn leaf_wt_mono(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h1: nat,
    h2: nat,
)
    requires
        leaf_wt(dty, denv, lctx, io, x, y, h1),
        h1 <= h2,
    ensures
        leaf_wt(dty, denv, lctx, io, x, y, h2),
{
    if io == IoMode::InferWt {
        let (tx, fx) = choose|tx: ExprSpec, fx: nat| #[trigger] wt_marker(tx, fx) && fx <= h1 && types_to(dty, denv, lctx, IoMode::Real, x, tx, fx);
        let (ty, fy) = choose|ty: ExprSpec, fy: nat| #[trigger] wt_marker(ty, fy) && fy <= h1 && types_to(dty, denv, lctx, IoMode::Real, y, ty, fy);
        assert(wt_marker(tx, fx) && wt_marker(ty, fy));
    }
}

pub proof fn leaf_wt_symm(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
)
    requires
        leaf_wt(dty, denv, lctx, io, x, y, h),
    ensures
        leaf_wt(dty, denv, lctx, io, y, x, h),
{
}

pub open spec fn infers(io: IoMode) -> bool {
    io != IoMode::Real
}

/// Marker trigger for the real-typing witnesses of `leaf_wt` and `wt1`
/// (`types_to` is in their recursive group, so it cannot trigger).
pub open spec fn wt_marker(t: ExprSpec, f: nat) -> bool {
    true
}

/// The leaf condition `InferWt` adds: `x` and `y` both have real types.
pub open spec fn leaf_wt(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
) -> bool
    decreases h, 7int, 0nat,
{
    io != IoMode::InferWt || ((exists|tx: ExprSpec, fx: nat| #[trigger] wt_marker(tx, fx) && fx <= h && types_to(dty, denv, lctx, IoMode::Real, x, tx, fx))
        && (exists|ty: ExprSpec, fy: nat| #[trigger] wt_marker(ty, fy) && fy <= h && types_to(dty, denv, lctx, IoMode::Real, y, ty, fy)))
}


/// TRANSPARENT. Its three fields are already `pub`, so nothing had to change
/// in the kernel: opaque, each accessor needed an uninterpreted `*_of` keyed by
/// value plus an `assume_specification` tying the real getter to it.
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExRecRule<'a>(RecRule<'a>);

/// DEFINED as the field. Kept as a named spec fn rather than inlined because
/// `rec_rule_ctor_names` below triggers on it.
pub open spec fn rec_rule_ctor_name_of<'a>(r: RecRule<'a>) -> NamePtr<'a> {
    r.ctor_name
}




pub open spec fn args_model_of<'t>(xs: Seq<ExprPtr<'t>>) -> Seq<ExprSpec> {
    Seq::new(xs.len(), |i: int| to_model(xs[i]))
}

pub open spec fn rec_rule_ctor_telescope_size_wo_params_of<'a>(r: RecRule<'a>) -> u16 {
    r.ctor_telescope_size_wo_params
}


pub open spec fn rec_rule_val_of<'a>(r: RecRule<'a>) -> ExprPtr<'a> {
    r.val
}


pub open spec fn rec_rule_ctor_names<'a>(rec_rules: Seq<RecRule<'a>>) -> Seq<NamePtr<'a>> {
    Seq::new(rec_rules.len(), |i: int| rec_rule_ctor_name_of(rec_rules[i]))
}










/// Delta-lift CM: `verified_whnf_measured_rounds` over the capped model
// ===========================================================================
// KERNEL-SHAPED WHNF (2026-09-11). Mirrors `tc.rs`'s own two functions
// instead of approximating them with a rounds loop:
//
//   `whnf_no_unfolding_aux`: fire ONE no-unfolding step and tail-call
//   yourself on the result; return the term when no step applies.
//   `whnf`: normalize without unfolding, then try the nat fold and delta;
//   stop exactly when both decline.
//
// The kernel asks no "did the term change?" question at the loop level and
// has no size gates: each recursion follows an actual reduction. So does
// this. What the retired rounds loop needed and this does not: a growth
// ceiling (1500) with a second gate-free path above it, whole-round retries,
// and a knob choosing between an exhaustive and a cheap exit. The one honest
// difference from the kernel is `fuel`, which bounds the recursion the
// kernel bounds by termination of reduction.
// ===========================================================================
/// A pointer's packed representation, as a function of the pointer. The only
/// thing assumed about it is that it IS a function -- the same pointer always
/// gives the same bits -- which is what lets the table below have a
/// specification at all. Nothing about any claim depends on it: a wrong answer
/// here could only send a lookup to the wrong slot, and a lookup only ever
/// returns a certificate that already carries its own proof.
pub open spec fn ptr_raw<'t>(e: ExprPtr<'t>) -> u32 {
    crate::util_model::ptr_raw(e)
}



/// The claim of a shadow INFERENCE certificate: the verified inference
/// derives a type `r` for `e` under the environment's declaration types and
/// the arena's local context, at some fuel. Stated here (rather than in
/// `delta_bound_model`, where inference itself lives) so that the certificate
/// type below can carry it as its type invariant.
pub open spec fn infer_types_to<'t, 'x>(
    env: Env<'x, 't>,
    e: ExprPtr<'t>,
    r: ExprPtr<'t>,
    fuel: nat,
) -> bool {
    types_to(
        to_model_of_declar_ty(env),
        to_model_of_env(env),
        arena_lctx(crate::env_model::env_arena_ids(env)), IoMode::Real,
        to_model(e),
        to_model(r),
        fuel,
    )
}


/// `find_index` hits are in range and hit the value.
pub proof fn find_index_hit<T>(s: Seq<T>, v: T)
    ensures
        match find_index(s, v) {
            Some(i) => i < s.len() && s[i as int] == v,
            None => true,
        },
    decreases s.len(),
{
    if s.len() == 0 {
    } else if s[0] == v {
    } else {
        find_index_hit(s.subrange(1, s.len() as int), v);
    }
}

/// The exec rule scan (`find_index` by constructor NAME) agrees with the
/// model's `find_rule` (by constructor id): `name_id` is injective.
pub proof fn find_rule_of_find_index<'t, 'p, 'a>(c: TcCtx<'t, 'p>, rules: Seq<RecRule<'a>>, cname: NamePtr<'a>)
    requires
        crate::util_model::owns_all(c, rec_rule_ctor_names(rules)),
        crate::util_model::owns(c, cname),
    ensures
        find_rule(rec_rules_model(rules), name_id(cname)) == (match find_index(
            rec_rule_ctor_names(rules),
            cname,
        ) {
            Some(i) => Some(i as int),
            None => None,
        }),
    decreases rules.len(),
{
    let names = rec_rule_ctor_names(rules);
    let model = rec_rules_model(rules);
    if rules.len() == 0 {
        assert(names.len() == 0);
        assert(model.len() == 0);
    } else {
        assert(crate::util_model::owns(c, names[0]));
        name_id_injective(c, rec_rule_ctor_name_of(rules[0]), cname);
        assert(names[0] == rec_rule_ctor_name_of(rules[0]));
        assert(model[0].ctor_id == name_id(rec_rule_ctor_name_of(rules[0])));
        let rest = rules.subrange(1, rules.len() as int);
        assert(names.subrange(1, names.len() as int) =~= rec_rule_ctor_names(rest));
        assert(model.drop_first() =~= rec_rules_model(rest));
        assert forall|i: int| 0 <= i < rec_rule_ctor_names(rest).len() implies #[trigger] crate::util_model::owns(c, rec_rule_ctor_names(rest)[i]) by {
            assert(rec_rule_ctor_names(rest)[i] == names[i + 1]);
        }
        find_rule_of_find_index(c, rest, cname);
    }
}


/// `2^exp`, defined recursively since Verus's `nat` has no built-in
/// exponentiation -- needed to state `Shl`/`Shr`/`Pow`'s semantics
/// cleanly (`util.rs::nat_shl`/`nat_shr` are literally `x * 2^y`/`x / 2^y`,
/// and `do_nat_bin`'s `Pow` case is `x^y` directly). Generalized to
/// `nat_pow(base, exp)` since `Pow` needs an arbitrary base, not just `2`.
/// Lives here (not `nat_lit_model.rs`, where the rest of this file's
/// `BigUint` trust boundary otherwise lives) -- adding new `pub open spec
/// fn`/`assume_specification` items to `nat_lit_model.rs` specifically was
/// observed to silently fail to export them to other modules under plain
/// `cargo build` (reproduced with a minimal, non-recursive repro isolated
/// down to that one file; a plain `pub fn` in the same file worked fine),
/// a real, unexplained tooling quirk worth remembering, not a mistake in
/// how these are written.
pub open spec fn nat_pow(base: nat, exp: nat) -> nat
    decreases exp,
{
    if exp == 0 {
        1
    } else {
        base * nat_pow(base, (exp - 1) as nat)
    }
}

/// Euclidean `gcd`, defined recursively (standard `gcd(a, 0) = a`,
/// `gcd(a, b) = gcd(b, a % b)` for `b > 0`) -- Verus's `nat` has no
/// built-in `gcd` either.
pub open spec fn nat_gcd_spec(a: nat, b: nat) -> nat
    decreases b,
{
    if b == 0 {
        a
    } else {
        nat_gcd_spec(b, (a % b) as nat)
    }
}

pub assume_specification[ <BigUint as num_traits::Pow<BigUint>>::pow ](
    x: BigUint,
    y: BigUint,
) -> (result: BigUint)
    ensures
        to_nat(result) == nat_pow(to_nat(x), to_nat(y)),
;

/// `util.rs::nat_shl`/`nat_shr` (`x * 2^y`/`x / 2^y`) -- trusted directly,
/// same spirit as `nat_sub`/`nat_div`/`nat_mod` (a trivial composition of
/// already-trusted primitives, no independent branching to verify).
pub assume_specification[ crate::util::nat_shl ](x: BigUint, y: BigUint) -> (result: BigUint)
    ensures
        to_nat(result) == to_nat(x) * nat_pow(2, to_nat(y)),
;

pub assume_specification[ crate::util::nat_shr ](x: BigUint, y: BigUint) -> (result: BigUint)
    ensures
        to_nat(result) == to_nat(x) / nat_pow(2, to_nat(y)),
;

pub assume_specification[ crate::util::nat_gcd ](x: &BigUint, y: &BigUint) -> (result: BigUint)
    ensures
        to_nat(result) == nat_gcd_spec(to_nat(*x), to_nat(*y)),
;

/// Bitwise AND/OR/XOR, defined recursively by peeling one bit at a time
/// (`a % 2`/`a / 2`) -- the fundamentally different mathematical
/// structure (bit patterns, not quantities) is exactly why these three
/// `do_nat_bin` ops were deliberately left out of the earlier `Gcd`/
/// `Shl`/`Shr`/`Pow` pass (all four of THOSE stay in "quantity" land:
/// repeated multiplication/division/subtraction). `nat_land_spec` can
/// decrease on `a` alone (it stops the moment EITHER operand hits 0);
/// `nat_lor_spec`/`nat_xor_spec` return the other operand unchanged as
/// soon as one hits 0, so the recursive branch is only ever reached with
/// `a > 0`, and `decreases a` covers all three uniformly.
pub open spec fn nat_land_spec(a: nat, b: nat) -> nat
    decreases a,
{
    if a == 0 || b == 0 {
        0
    } else {
        (if a % 2 == 1 && b % 2 == 1 {
            1nat
        } else {
            0nat
        }) + 2 * nat_land_spec((a / 2) as nat, (b / 2) as nat)
    }
}

pub open spec fn nat_lor_spec(a: nat, b: nat) -> nat
    decreases a,
{
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else {
        (if a % 2 == 1 || b % 2 == 1 {
            1nat
        } else {
            0nat
        }) + 2 * nat_lor_spec((a / 2) as nat, (b / 2) as nat)
    }
}

pub open spec fn nat_xor_spec(a: nat, b: nat) -> nat
    decreases a,
{
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else {
        (if (a % 2 == 1) != (b % 2 == 1) {
            1nat
        } else {
            0nat
        }) + 2 * nat_xor_spec((a / 2) as nat, (b / 2) as nat)
    }
}

// ---------------------------------------------------------------------
// A hidden consistency obligation, now discharged.
//
// `crate::util::nat_gcd`/`nat_land`/`nat_lor`/`nat_xor` each carry an
// `assume_specification` HERE stating them against `*_spec`, while the
// `biguint_*` wrappers in `nat_lit_model.rs` -- which are one-line delegations
// to those same functions -- carry a SECOND `assume_specification` stating them
// against `beta_model`'s own `nat_gcd`/`nat_land`/`nat_lor`/`nat_xor`. Two
// axioms over one value force the two spec functions to agree, and the pairs
// were written independently and are NOT syntactically equal:
//
//   nat_land_spec: (if a%2==1 && b%2==1 {1} else {0}) + 2*rec(a/2, b/2)
//   nat_land     : 2*rec(a/2, b/2) + (a%2)*(b%2)
//
// They do agree, and these four lemmas prove it rather than leaving it as an
// assumption nobody stated. Had any pair disagreed, the axiom set would have
// been INCONSISTENT -- `false` derivable -- with nothing pointing at it.
pub proof fn nat_pow_agrees(a: nat, b: nat)
    ensures
        nat_pow(a, b) == crate::beta_model::nat_pow(a, b),
    decreases b,
{
    if b != 0 {
        nat_pow_agrees(a, (b - 1) as nat);
    }
}

pub proof fn nat_gcd_spec_agrees(a: nat, b: nat)
    ensures
        nat_gcd_spec(a, b) == crate::beta_model::nat_gcd(a, b),
    decreases b,
{
    if b != 0 {
        nat_gcd_spec_agrees(b, (a % b) as nat);
    }
}

pub proof fn nat_land_spec_agrees(a: nat, b: nat)
    ensures
        nat_land_spec(a, b) == crate::beta_model::nat_land(a, b),
    decreases a,
{
    if a != 0 && b != 0 {
        nat_land_spec_agrees((a / 2) as nat, (b / 2) as nat);
    }
}

pub proof fn nat_lor_spec_agrees(a: nat, b: nat)
    ensures
        nat_lor_spec(a, b) == crate::beta_model::nat_lor(a, b),
    decreases a,
{
    if a != 0 && b != 0 {
        nat_lor_spec_agrees((a / 2) as nat, (b / 2) as nat);
    }
}

pub proof fn nat_xor_spec_agrees(a: nat, b: nat)
    ensures
        nat_xor_spec(a, b) == crate::beta_model::nat_xor(a, b),
    decreases a,
{
    if a != 0 && b != 0 {
        nat_xor_spec_agrees((a / 2) as nat, (b / 2) as nat);
    }
}

/// `util.rs::nat_land`/`nat_lor`/`nat_xor` are one-line delegations to
/// `BigUint`'s native `&`/`|`/`^` operators -- trusted directly, same
/// "trust the delegation" convention `nat_gcd` above uses.
pub assume_specification[ crate::util::nat_land ](x: BigUint, y: BigUint) -> (result: BigUint)
    ensures
        to_nat(result) == nat_land_spec(to_nat(x), to_nat(y)),
;

pub assume_specification[ crate::util::nat_lor ](x: BigUint, y: BigUint) -> (result: BigUint)
    ensures
        to_nat(result) == nat_lor_spec(to_nat(x), to_nat(y)),
;

pub assume_specification[ crate::util::nat_xor ](x: &BigUint, y: &BigUint) -> (result: BigUint)
    ensures
        to_nat(result) == nat_xor_spec(to_nat(*x), to_nat(*y)),
;



/// Real-arena counterpart to the START of `tc.rs::TypeChecker::def_eq`'s
/// mutually-recursive cluster (`tc.rs:913-926`, `def_eq_local`/
/// `def_eq_const`, plus `def_eq_proj` at `tc.rs:903-911`) -- the first
/// piece of the cluster that genuinely recurses back into itself
/// (`def_eq_local`/`def_eq_proj` both call `self.def_eq` on a subterm),
/// a step up from `verified_def_eq_sort`/`verified_def_eq_const` (true
/// leaves, no recursion at all). `fuel` bounds the recursion depth --
/// `Some(true)` means the comparison genuinely succeeded within budget,
/// `None` means fuel ran out before a verdict (honestly incomplete, same
/// "None = not yet enough headroom" convention as `verified_whnf_step`
/// etc.), `Some(false)` means every disjunct was tried and failed.
///
/// Deliberately does NOT yet model `def_eq_app`/`def_eq_unit`/
/// `def_eq_nat`/`lazy_delta_step`/`proof_irrel_eq`/`try_eta_*`/`whnf`
/// preprocessing, or `def_eq`'s own top-level `def_eq_quick_check`/whnf
/// dance (`tc.rs:957-1004`) -- this is exactly `def_eq_sort ||
/// def_eq_const || def_eq_local || def_eq_proj`, the same four-way
/// disjunction `tc.rs:982` itself tries right after `lazy_delta_step`
/// (Exhausted case), before falling further into app/eta. `Local`'s
/// identity is `local_id_of` (the real `FVarId` payload), deliberately
/// separate from `expr_id` (pointer identity) -- see
/// `expr_arena_bridge.rs`'s module doc comment. `Proj`'s `ty_name`/`idx`
/// are compared as real exec values (native `usize`/`name_ptr_eq`) but
/// not surfaced in the ensures, since `ExprSpec::Proj` itself erases them
/// (same scoping choice `pstep_star_proj` already made for `idx`).
/// Spine congruence for `deq`: a head-pair and pairwise-`deq` argument
/// pairs lift to `deq` on the whole applied spines, one congruence
/// layer per argument (induction matching `spine_app`'s back-peeling,
/// exactly like `pstep_spine_app_star`). This is the lemma that turns
/// `verified_def_eq_app`'s pairwise `deq_core_claim` facts into a
/// whole-term equality whenever every pair lands on the `deq` disjunct.
pub proof fn deq_spine_app_congr(
    env: EnvSpec,
    fx: ExprSpec,
    fy: ExprSpec,
    ax: Seq<ExprSpec>,
    ay: Seq<ExprSpec>,
    h: nat,
)
    requires
        ax.len() == ay.len(),
        deq(env, fx, fy, h),
        forall|i: int| 0 <= i < ax.len() ==> deq(env, #[trigger] ax[i], ay[i], h),
    ensures
        deq(env, spine_app(fx, ax), spine_app(fy, ay), (h + ax.len()) as nat),
    decreases ax.len(),
{
    if ax.len() == 0 {
        assert(spine_app(fx, ax) == fx);
        assert(spine_app(fy, ay) == fy);
    } else {
        let ax0 = ax.subrange(0, ax.len() - 1);
        let ay0 = ay.subrange(0, ay.len() - 1);
        let lx = ax[ax.len() - 1];
        let ly = ay[ay.len() - 1];
        assert(ax0.len() == ay0.len());
        assert forall|i: int| 0 <= i < ax0.len() implies deq(env, #[trigger] ax0[i], ay0[i], h) by {
            assert(ax0[i] == ax[i]);
            assert(ay0[i] == ay[i]);
            assert(deq(env, ax[i], ay[i], h));
        }
        deq_spine_app_congr(env, fx, fy, ax0, ay0, h);
        assert(deq(env, lx, ly, h));
        deq_mono(env, lx, ly, h, (h + ax0.len()) as nat);
        deq_app_congr(env, spine_app(fx, ax0), spine_app(fy, ay0), lx, ly, (h + ax0.len()) as nat);
        assert(spine_app(fx, ax) == ExprSpec::App(Box::new(spine_app(fx, ax0)), Box::new(lx)));
        assert(spine_app(fy, ay) == ExprSpec::App(Box::new(spine_app(fy, ay0)), Box::new(ly)));
        assert((h + ax0.len()) as nat + 1 == (h + ax.len()) as nat);
    }
}

/// `deq` at SOME height -- the height-erased, consumer-facing form (the
/// height index is well-foundedness plumbing, not semantic content).
/// Non-recursive, so it inlines and both directions (witnessing from any
/// concrete height, extracting via choose) work freely.
pub open spec fn deq_any(env: EnvSpec, x: ExprSpec, y: ExprSpec) -> bool {
    exists|h: nat| #[trigger] deq(env, x, y, h)
}



/// A `nat_repr_pred(e, p)` pair's whole term is `deq_any`-related to the
/// CANONICAL successor application `App(const_expr_no_levels(succ),
/// to_model(p))`: exact equality for the real-`App` representation (its
/// head pinned to the canonical form by `nat_repr_pred`'s empty-levels
/// clause + `const_expr_no_levels_canonical`), one `pstep` (the `NatLit`
/// unfolding rule) for the literal representation. The connecting edge
/// `verified_def_eq_nat`'s pred case needs on each side.
pub proof fn nat_repr_pred_reaches_succ_app<'t>(
    env: EnvSpec,
    e: ExprPtr<'t>,
    p: ExprPtr<'t>,
)
    requires
        nat_repr_pred(env.export, e, p),
    ensures
        deq_any(
            env,
            to_model(e),
            ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id(env.export))), Box::new(to_model(p))),
        ),
{
    let target = ExprSpec::App(
        Box::new(const_expr_no_levels(nat_succ_id(env.export))),
        Box::new(to_model(p)),
    );
    if exists|fun: ExprPtr<'t>|
        to_model(e) == ExprSpec::App(Box::new(to_model(fun)), Box::new(to_model(p)))
            && is_const_shape(fun) && const_id(fun) == nat_succ_id(env.export) && const_levels_vec(fun).len() == 0 {
        let fun = choose|fun: ExprPtr<'t>|
            to_model(e) == ExprSpec::App(Box::new(to_model(fun)), Box::new(to_model(p)))
                && is_const_shape(fun) && const_id(fun) == nat_succ_id(env.export) && const_levels_vec(fun).len() == 0;
        const_levels_vec_model(fun);
        is_const_shape_model(fun);
        assert(const_levels_vec(fun).len() == 0);
        assert(to_model(fun) == ExprSpec::Const(const_id(fun), const_levels_vec(fun)));
        const_expr_no_levels_canonical(to_model(fun), nat_succ_id(env.export));
        assert(to_model(e) == target);
        deq_any_refl(env, to_model(e));
    } else {
        assert(is_nat_lit_shape(e) && nat_lit_value(e) > 0 && is_nat_lit_shape(p) && nat_lit_value(
            p,
        ) == (nat_lit_value(e) - 1) as nat);
        is_nat_lit_shape_model(e);
        is_nat_lit_shape_model(p);
        assert(to_model(e) == ExprSpec::NatLit(NatLitPayload(Ghost(nat_lit_value(e)))));
        assert(to_model(p) == ExprSpec::NatLit(NatLitPayload(Ghost(nat_lit_value(p)))));
        assert((nat_lit_value(e) - 1) as nat == nat_lit_value(p));
        assert(pstep(env, to_model(e), target));
        pstep_star_one(env, to_model(e), target);
        defeq_of_pstep_star(env, to_model(e), target);
        deq_any_of_defeq(env, to_model(e), target);
    }
}

/// The equivalence-relation API at the `deq_any` level -- what
/// consumers actually want (heights erased, monotonicity handled
/// internally via `deq_mono`).
pub proof fn deq_any_of_defeq(env: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        defeq(env, x, y),
    ensures
        deq_any(env, x, y),
{
    deq_of_defeq(env, x, y, 0);
    assert(deq(env, x, y, 0));
}

pub proof fn deq_any_of_leaf(env: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        deq_leaf(x, y),
    ensures
        deq_any(env, x, y),
{
    deq_of_leaf(env, x, y, 0);
    assert(deq(env, x, y, 0));
}

pub proof fn deq_any_refl(env: EnvSpec, x: ExprSpec)
    ensures
        deq_any(env, x, x),
{
    deq_refl(env, x, 0);
    assert(deq(env, x, x, 0));
}

pub proof fn deq_any_symm(env: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        deq_any(env, x, y),
    ensures
        deq_any(env, y, x),
{
    let h = choose|h: nat| deq(env, x, y, h);
    deq_symm(env, x, y, h);
    assert(deq(env, y, x, h));
}

pub proof fn deq_any_trans(
    env: EnvSpec,
    x: ExprSpec,
    y: ExprSpec,
    z: ExprSpec,
)
    requires
        deq_any(env, x, y),
        deq_any(env, y, z),
    ensures
        deq_any(env, x, z),
{
    let h1 = choose|h: nat| deq(env, x, y, h);
    let h2 = choose|h: nat| deq(env, y, z, h);
    let hm = if h1 >= h2 {
        h1
    } else {
        h2
    };
    deq_mono(env, x, y, h1, hm);
    deq_mono(env, y, z, h2, hm);
    deq_trans(env, x, y, z, hm);
    assert(deq(env, x, z, hm));
}

/// Spine congruence for the untyped relation: equal heads and pointwise
/// equal arguments give equal spines. Induction on the argument list, one
/// `deq_any_app_congr` per step.
pub proof fn deq_any_spine_congr(
    env: EnvSpec,
    h1: ExprSpec,
    h2: ExprSpec,
    a1: Seq<ExprSpec>,
    a2: Seq<ExprSpec>,
)
    requires
        deq_any(env, h1, h2),
        a1.len() == a2.len(),
        forall|i: int| 0 <= i < a1.len() ==> deq_any(env, #[trigger] a1[i], a2[i]),
    ensures
        deq_any(env, spine_app(h1, a1), spine_app(h2, a2)),
    decreases a1.len(),
{
    if a1.len() == 0 {
        assert(spine_app(h1, a1) == h1);
        assert(spine_app(h2, a2) == h2);
    } else {
        let n = a1.len() - 1;
        let p1 = a1.subrange(0, n);
        let p2 = a2.subrange(0, n);
        assert forall|i: int| 0 <= i < p1.len() implies deq_any(env, #[trigger] p1[i], p2[i]) by {
            assert(p1[i] == a1[i]);
            assert(p2[i] == a2[i]);
        }
        deq_any_spine_congr(env, h1, h2, p1, p2);
        assert(p1.push(a1[n]) =~= a1);
        assert(p2.push(a2[n]) =~= a2);
        spine_app_compose_last(h1, p1, a1[n]);
        spine_app_compose_last(h2, p2, a2[n]);
        deq_any_app_congr(env, spine_app(h1, p1), spine_app(h2, p2), a1[n], a2[n]);
    }
}

pub proof fn deq_any_app_congr(
    env: EnvSpec,
    f1: ExprSpec,
    f2: ExprSpec,
    a1: ExprSpec,
    a2: ExprSpec,
)
    requires
        deq_any(env, f1, f2),
        deq_any(env, a1, a2),
    ensures
        deq_any(
            env,
            ExprSpec::App(Box::new(f1), Box::new(a1)),
            ExprSpec::App(Box::new(f2), Box::new(a2)),
        ),
{
    let h1 = choose|h: nat| deq(env, f1, f2, h);
    let h2 = choose|h: nat| deq(env, a1, a2, h);
    let hm = if h1 >= h2 {
        h1
    } else {
        h2
    };
    deq_mono(env, f1, f2, h1, hm);
    deq_mono(env, a1, a2, h2, hm);
    deq_app_congr(env, f1, f2, a1, a2, hm);
    assert(deq(
        env,
        ExprSpec::App(Box::new(f1), Box::new(a1)),
        ExprSpec::App(Box::new(f2), Box::new(a2)),
        hm + 1,
    ));
}

pub proof fn deq_any_bind_congr(
    env: EnvSpec,
    t1: ExprSpec,
    t2: ExprSpec,
    b1: ExprSpec,
    b2: ExprSpec,
    bkind: BinderKind,
)
    requires
        deq_any(env, t1, t2),
        deq_any(env, b1, b2),
    ensures
        deq_any(
            env,
            ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)),
            ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2)),
        ),
{
    let h1 = choose|h: nat| deq(env, t1, t2, h);
    let h2 = choose|h: nat| deq(env, b1, b2, h);
    let hm = if h1 >= h2 {
        h1
    } else {
        h2
    };
    deq_mono(env, t1, t2, h1, hm);
    deq_mono(env, b1, b2, h2, hm);
    deq_bind_congr(env, t1, t2, b1, b2, hm, bkind);
    assert(deq(
        env,
        ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)),
        ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2)),
        hm + 1,
    ));
}

pub proof fn deq_any_proj_congr(
    env: EnvSpec,
    pidx: usize,
    s1: ExprSpec,
    s2: ExprSpec,
)
    requires
        deq_any(env, s1, s2),
    ensures
        deq_any(env, ExprSpec::Proj(pidx, Box::new(s1)), ExprSpec::Proj(pidx, Box::new(s2))),
{
    let h = choose|h: nat| deq(env, s1, s2, h);
    deq_proj_congr(env, pidx, s1, s2, h);
    assert(deq(env, ExprSpec::Proj(pidx, Box::new(s1)), ExprSpec::Proj(pidx, Box::new(s2)), h + 1));
}





/// Real-arena counterpart to the START of `tc.rs::TypeChecker::def_eq`
/// itself (`tc.rs:957-1004`) -- composes `verified_def_eq_core` (the
/// sort/const/local/proj leaf cluster) and `verified_def_eq_app` (the
/// later applied-spine stage) behind one entry point, plus the one
/// genuinely trivial piece of `def_eq_quick_check` (`tc.rs:1172-1186`):
/// real `ExprPtr` reflexivity (`x == y`), which needs no lemma at all --
/// `to_model` is a pure function of the pointer, so `x == y` gives
/// `to_model(x) == to_model(y)` by plain SMT congruence.
///
/// Deliberately NOT modeled here, still: `def_eq_quick_check`'s cache
/// lookup and `def_eq_binder_multi` disjunct, the bool-true short-circuit
/// (`tc.rs:965-970`), `proof_irrel_eq`, `lazy_delta_step`, the
/// `whnf_no_unfolding` re-check-and-recurse step (`tc.rs:986-989`), and
/// the final `try_eta_expansion`/`try_eta_struct`/
/// `try_string_lit_expansion`/`def_eq_unit` fallback group (`tc.rs:990-
/// 995`). This is an honest, partial `def_eq`: `Some(true)`/`Some(false)`
/// are genuine verdicts reached via the pieces bridged so far, `None`
/// covers both "ran out of fuel" AND "would need one of the unmodeled
/// pieces to decide" -- so `None` here is a strictly weaker signal than
/// `Some(false)`'s "the modeled pieces establish it's not equal via them",
/// not a claim the real terms are actually unrelated.
/// `requires` a depth cap on `x`/`y` (needed only since this now also
/// tries `verified_def_eq_binder_step`, which recurses into instantiated
/// sub-terms and needs to re-establish a depth bound on them via
/// `subst_full_depth_bound_n` -- see that function's own doc comment).
/// Names the disjunction `verified_def_eq`'s own `Some(true)` case
/// establishes -- factored out so any OTHER function that reaches a
/// genuine `def_eq` verdict on some pair of terms (not necessarily `x`/`y`
/// themselves; e.g. `verified_try_string_lit_expansion_aux`'s freshly-
/// built `lhs` vs. its own `y`) can restate the SAME real fact about ITS
/// pair by calling this, instead of re-deriving or copy-pasting the whole
/// seven-way disjunction at every call site. `open`, so it's purely
/// notational: unfolds for free, changes no proof obligation anywhere
/// this substitutes for the inline form.
pub open spec fn def_eq_witness<'t>(x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
    to_model(x) == to_model(y) || (exists|lx: LevelPtr<'t>, ly: LevelPtr<'t>|
        to_model(x) == ExprSpec::Sort(level_to_model(lx)) && to_model(y) == ExprSpec::Sort(
            level_to_model(ly),
        ) && forall|rho: Map<nat, nat>| #[trigger]
            interp(level_to_model(lx), rho) == interp(level_to_model(ly), rho)) || (is_const_shape(
        x,
    ) && is_const_shape(y) && const_id(x) == const_id(y)) || (is_local_shape(x) && is_local_shape(y)
        && local_id_of(x) == local_id_of(y)) || (exists|
        pidx: usize,
        sx: ExprPtr<'t>,
        sy: ExprPtr<'t>,
    |
        to_model(x) == ExprSpec::Proj(pidx, Box::new(to_model(sx))) && to_model(y)
            == ExprSpec::Proj(pidx, Box::new(to_model(sy)))) || (exists|
        fx: ExprPtr<'t>,
        fy: ExprPtr<'t>,
        argsx: Seq<ExprPtr<'t>>,
        argsy: Seq<ExprPtr<'t>>,
    |
        to_model(x) == spine_app(to_model(fx), args_model_of(argsx)) && to_model(y) == spine_app(
            to_model(fy),
            args_model_of(argsy),
        ) && argsx.len() == argsy.len() && argsx.len() > 0) || (exists|
        t1: ExprPtr<'t>,
        body1: ExprPtr<'t>,
        t2: ExprPtr<'t>,
        body2: ExprPtr<'t>,
        k: BinderKind,
    |
        to_model(x) == ExprSpec::Bind(k, Box::new(to_model(t1)), Box::new(to_model(body1)))
            && to_model(y) == ExprSpec::Bind(k, Box::new(to_model(t2)), Box::new(to_model(body2))))
}

/// The FULL notion of "these two terms are definitionally equal" this
/// codebase currently knows how to STATE (not yet how to fully PROVE for
/// every real `def_eq` code path -- see `feedback_defeq_witness_vs_
/// pstep_star`): either they're joinable via ordinary reduction (`defeq`,
/// `beta_model.rs`), or they're related by `def_eq_witness`'s own leaf-
/// level structural disjunction (Sort-interp-equality, Const-id-equality,
/// etc., none of which are reduction facts and so aren't `defeq`-
/// expressible). Neither alone is universal: `defeq` can't see universe-
/// level-equivalence-without-syntactic-equality (`def_eq_const`'s own
/// case), and `def_eq_witness` can't see delta/NatLit/iota unfolding.
/// This is genuinely just their union, NOT a congruence closure. On the
/// `defeq` DISJUNCT, congruence and transitivity are now proven at the
/// model level (`defeq_app_congr`/`defeq_bind_congr`/`defeq_let_congr`/
/// `defeq_proj_congr`, and `defeq_trans_certified` from the certified-
/// confluence arc, all in `beta_model.rs`) -- so `full_def_eq` facts
/// whose sub-facts are reduction-joinability DO lift structurally. What
/// remains genuinely open is the `def_eq_witness` disjunct: its leaf
/// cases are not reduction facts, so a witness-side sub-fact cannot feed
/// the `defeq` congruences, and a proper inductive definitional-equality
/// relation (closing BOTH disjuncts under congruence/transitivity at
/// once) is still real, substantial future work.
pub open spec fn full_def_eq<'t>(
    env: EnvSpec,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
) -> bool {
    defeq(env, to_model(x), to_model(y)) || def_eq_witness(x, y)
}

/// THE MODEL-LEVEL TYPING RELATION -- `infer_spec` lifted off the arena:
/// pure `ExprSpec`-to-`ExprSpec`, with the arena's implicit local-type
/// lookup replaced by an explicit context map `lctx` (produced as
/// `arena_lctx()` by real callers, via that bridge's one disclosed
/// axiom) and the declaration-type / delta environments as explicit
/// model maps. Mirrors `infer_spec`'s nine disjuncts EXACTLY --
/// including their honest weaknesses (the `App` case's opaque
/// telescoped form; the binder cases' loose fresh-variable discipline:
/// `lid` is existential with no freshness or context-extension
/// tracking, exactly as `infer_spec` leaves the local ptr loose) -- so
/// producer functions can emit both relations from the same branch
/// facts. This is deliberately "what the checker's infer computes,
/// stated over models", NOT an independent declarative type system;
/// tightening it into one (freshness, context extension, arg checking
/// in `App`) is real future metatheory. Its purpose: give `deq` a
/// model-pure way to classify proofs (both operands typed by
/// `Prop`-reaching types), unblocking proof irrelevance and
/// unit-equality as relation cases. Match-based wherever possible; the
/// three remaining existentials carry explicit arithmetic-free triggers
/// (per `docs/verus_recursive_exists_note.md`, so the intro direction
/// producers need actually works).
/// Marker trigger for the fuel witness of `types_to`'s `Let` rule: an
/// exists in a match arm can't be introduced through a trigger that
/// mentions match-bound selectors, so the trigger is this ground marker
/// over the binder alone (see the memo's match-arm exists law).
pub open spec fn fuel_marker(f: nat) -> bool {
    true
}

/// Marker trigger for the `Proj` rule's witnesses (same device).
pub open spec fn proj_marker(
    f2: nat,
    sty: ExprSpec,
    ind_id: u64,
    ls: Seq<LevelSpec>,
    args: Seq<ExprSpec>,
    ctor_id: u64,
    np: u16,
    ctor_ty0: ExprSpec,
) -> bool {
    true
}

/// Marker trigger for one telescope step of `proj_field_type`.
pub open spec fn proj_step_marker(bt: ExprSpec, body: ExprSpec) -> bool {
    true
}

/// The kernel's `infer_proj` telescope walk (`tc.rs`): from the
/// constructor's (level-instantiated) type `cur`, reduce to a `Pi`
/// (`pstep_star`), and either instantiate with the next structure-type
/// argument (`np` params left), or with `Proj(fld, s)` (`remaining`
/// fields left), or -- both exhausted -- read the field type off the
/// binder. Instantiating a closed body is a no-op (`subst_full_noop`),
/// which covers the kernel's "no loose bvars" shortcut.
pub open spec fn proj_field_type(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    h: nat,
    cur: ExprSpec,
    args: Seq<ExprSpec>,
    np: nat,
    fld: usize,
    remaining: nat,
    s: ExprSpec,
    t: ExprSpec,
) -> bool
    decreases h, 3int, np + remaining,
{
    exists|bt: ExprSpec, body: ExprSpec| #[trigger]
        proj_step_marker(bt, body) && deq_p(
            dty,
            denv,
            lctx,
            io,
            cur,
            ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)),
            h,
        ) && (if np > 0 {
            args.len() > 0 && proj_field_type(
                dty,
                denv,
                lctx,
                io,
                h,
                subst_full(body, seq![args[0]], 0),
                args.drop_first(),
                (np - 1) as nat,
                fld,
                remaining,
                s,
                t,
            )
        } else if remaining > 0 {
            proj_field_type(
                dty,
                denv,
                lctx,
                io,
                h,
                subst_full(body, seq![ExprSpec::Proj(fld, Box::new(s))], 0),
                args,
                0,
                (fld + 1) as usize,
                (remaining - 1) as nat,
                s,
                t,
            )
        } else {
            t == bt
        })
}

pub open spec fn types_to(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    e: ExprSpec,
    t: ExprSpec,
    fuel: nat,
) -> bool
    decreases fuel, 6int, crate::expr_model::depth(e),
{
    ||| (match e {
        ExprSpec::Free(lid) => lctx.contains_key(lid) && t == lctx[lid],
        _ => false,
    })
    ||| (match (e, t) {
        (ExprSpec::Sort(l), ExprSpec::Sort(ls)) => ls == LevelSpec::Succ(Box::new(l)),
        _ => false,
    })
    ||| (match e {
        ExprSpec::Const(cid, clevels) => dty.contains_key(cid) && clevels.len() == dty[cid].0.len()
            && subst_expr_levels_rel(dty[cid].1, dty[cid].0, clevels, t),
        _ => false,
    })
    // APPLICATION (2026-09-05, replaces a vacuous "some substitution
    // instance of some body" rule): `f a : B[a]` when `f : T` and `T`
    // reduces to the binder `Bind(A, B)` (the kernel's `infer_app`: infer
    // the function, whnf its type to a Pi, instantiate the codomain).
    // Recursion on the syntactic subterm `f` at the SAME fuel
    // (`decreases fuel, e`); the trigger is the non-recursive reduction fact.
    //
    // The argument check (`types_to .. *a, aty2` + `deq_any aty2 aty`) is
    // load-bearing, and was missing until `0602cfb`. Keeping the account,
    // because it is the one soundness bug the shadow certifier has caught on
    // its own and the reason to keep running it:
    //
    // Without those two conjuncts `aty` was bound by the `exists` and then
    // never used, so the rule said only "f's type reduces to a Pi and t is
    // the instantiated codomain" -- the argument was ignored, and an
    // ill-typed application got a type anyway. That turns into a false
    // CONVERSION through eta: `def_eq_eta` compares `x` against
    // `lambda (_ : t2). x #0`, taking the binder `t2` from the OTHER side's
    // lambda. In the kernel that is sound because `def_eq` is only ever
    // reached on two terms already known to share a type; the shadow
    // certifier has no such invariant, because it is handed whatever pair the
    // kernel happens to be probing. So `x #0` got built with `#0 : t2` even
    // when `x`'s domain was a different proposition, this rule typed it
    // regardless, both sides came out as proofs of `False`, and proof
    // irrelevance equated them -- certifying `h : (head :: tail) != []` equal
    // to a proof of `(a :: head :: tail) != []`. Found 2026-09-14 by the
    // disagreement counter on `Init.Data.List.Lemmas` (see `4bf07bb`).
    ||| (match e {
        ExprSpec::App(f, a) => fuel > 0 && exists|ft: ExprSpec, aty: ExprSpec, bt: ExprSpec, aty2: ExprSpec|
            #![trigger app_marker(ft, aty, bt, aty2)]
            app_marker(ft, aty, bt, aty2) && types_to(dty, denv, lctx, io, *f, ft, fuel) && deq_p(
                dty,
                denv,
                lctx,
                io,
                ft,
                ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)),
                (fuel - 1) as nat,
            )
            // `io` is the kernel's `InferOnly` mode: it never infers the
            // argument, so neither the argument's type nor its agreement with
            // the domain is part of the derivation. `io == false` is real
            // typing. Everything else about the rule is shared.
             && (infers(io) || (types_to(dty, denv, lctx, io, *a, aty2, fuel) && deq_p(
                dty,
                denv,
                lctx,
                io,
                aty2,
                aty,
                (fuel - 1) as nat,
            )))
                && t == subst_full(bt, seq![*a], 0),
        _ => false,
    })
    ||| (matches!(e, ExprSpec::NatLit(_)) && match t {
        ExprSpec::Const(cid, ls) => cid == nat_type_id(denv.export) && ls.len() == 0,
        _ => false,
    })
    ||| (matches!(e, ExprSpec::StringLit(_)) && match t {
        ExprSpec::Const(cid, ls) => cid == string_type_id(denv.export) && ls.len() == 0,
        _ => false,
    })
    ||| (fuel > 0 && match e {
        // Real typing (`io == false`) also checks the annotation, as the
        // kernel's `Check` mode does: it is a type, and the value's type
        // converts to it. `InferOnly` skips both.
        ExprSpec::Let(ty0, val, body) => exists|f2: nat| #[trigger]
            fuel_marker(f2) && f2 < fuel && types_to(
                dty,
                denv,
                lctx, io,
                subst_full(*body, seq![*val], 0),
                t,
                f2,
            ) && (infers(io) || exists|s: ExprSpec, l: LevelSpec, vt: ExprSpec| #[trigger]
                let_check_marker(s, l, vt) && types_to(dty, denv, lctx, io, *ty0, s, f2)
                && deq_p(dty, denv, lctx, io, s, ExprSpec::Sort(l), f2)
                && types_to(dty, denv, lctx, io, *val, vt, f2)
                && deq_p(dty, denv, lctx, io, vt, *ty0, f2)),
        _ => false,
    })
    ||| (fuel > 0 && match e {
        // The body's type is taken up to conversion (`infd ~ bt2`), as the
        // application rule takes its function type: the kernel abstracts the
        // type it INFERRED, which is only convertible to the one a
        // derivation assigns.
        // Real typing also checks the binder type is a type (`Check` mode's
        // `infer_sort_of`); `InferOnly` skips it.
        ExprSpec::Bind(BinderKind::Lam, binder_type, body) => exists|lid: u32, infd: ExprSpec, bt2: ExprSpec| #[trigger]
            bind_marker(lid, infd, bt2) && lctx.contains_key(lid) && lctx[lid] == *binder_type && fv_absent(*body, lid) && unreach(lctx, lid, *binder_type) && unreach(lctx, lid, *body)
            && (infers(io) || exists|s: ExprSpec, l: LevelSpec| #[trigger] sort_check_marker(s, l)
                && types_to(dty, denv, lctx, io, *binder_type, s, (fuel - 1) as nat)
                && deq_p(dty, denv, lctx, io, s, ExprSpec::Sort(l), (fuel - 1) as nat))
            && types_to(
                dty,
                denv,
                lctx, io,
                subst_full(*body, seq![ExprSpec::Free(lid)], 0),
                infd,
                (fuel - 1) as nat,
            ) && deq_p(dty, denv, lctx, io, infd, bt2, (fuel - 1) as nat) && t == ExprSpec::Bind(BinderKind::Pi, 
                Box::new(abstr_full(*binder_type, seq![lid], 0)),
                Box::new(abstr_full(bt2, seq![lid], 0)),
            ),
        _ => false,
    })
    ||| (fuel > 0 && match e {
        ExprSpec::Bind(BinderKind::Pi, binder_type, body) => exists|
            lid: u32,
            bt_ty: ExprSpec,
            dom_level: LevelSpec,
            instd_ty: ExprSpec,
            cod_level: LevelSpec,
        | #[trigger]
            pi_marker(lid, bt_ty, dom_level, instd_ty, cod_level) && lctx.contains_key(lid) && lctx[lid] == *binder_type && fv_absent(*body, lid) && unreach(lctx, lid, *binder_type) && unreach(lctx, lid, *body) && types_to(
                dty,
                denv,
                lctx, io,
                *binder_type,
                bt_ty,
                (fuel - 1) as nat,
            ) && deq_p(dty, denv, lctx, io, bt_ty, ExprSpec::Sort(dom_level), (fuel - 1) as nat) && types_to(
                dty,
                denv,
                lctx, io,
                subst_full(*body, seq![ExprSpec::Free(lid)], 0),
                instd_ty,
                (fuel - 1) as nat,
            ) && deq_p(dty, denv, lctx, io, instd_ty, ExprSpec::Sort(cod_level), (fuel - 1) as nat) && t == ExprSpec::Sort(
                LevelSpec::IMax(Box::new(dom_level), Box::new(cod_level)),
            ),
        _ => false,
    })
    ||| (match e {
        ExprSpec::Proj(idx, s) => exists|
            f2: nat,
            sty: ExprSpec,
            ind_id: u64,
            ls: Seq<LevelSpec>,
            args: Seq<ExprSpec>,
            ctor_id: u64,
            np: u16,
            ctor_ty0: ExprSpec,
        | #[trigger]
            proj_marker(f2, sty, ind_id, ls, args, ctor_id, np, ctor_ty0) && f2 < fuel && types_to(
                dty,
                denv,
                lctx, io,
                *s,
                sty,
                f2,
            ) && deq_p(dty, denv, lctx, io, sty, spine_app(ExprSpec::Const(ind_id, ls), args), f2)
                && denv.struct_ctor(ind_id) == Some(ctor_id) && denv.ctor_num_params(ctor_id) == Some(
                np,
            ) && types_to(dty, denv, lctx, io, ExprSpec::Const(ctor_id, ls), ctor_ty0, f2) && (
            np as nat) <= args.len() && proj_field_type(
                dty,
                denv,
                lctx,
                io,
                f2,
                ctor_ty0,
                args,
                np as nat,
                0,
                idx as nat,
                *s,
                t,
            ),
        _ => false,
    })
}

pub proof fn types_to_nat_lit(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    e: ExprSpec,
    t: ExprSpec,
    fuel: nat,
)
    requires
        matches!(e, ExprSpec::NatLit(_)),
        matches!(t, ExprSpec::Const(_, _)),
        (match t {
            ExprSpec::Const(cid, ls) => cid == nat_type_id(denv.export) && ls.len() == 0,
            _ => false,
        }),
    ensures
        types_to(dty, denv, lctx, io, e, t, fuel),
{
}

pub proof fn types_to_string_lit(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    e: ExprSpec,
    t: ExprSpec,
    fuel: nat,
)
    requires
        matches!(e, ExprSpec::StringLit(_)),
        matches!(t, ExprSpec::Const(_, _)),
        (match t {
            ExprSpec::Const(cid, ls) => cid == string_type_id(denv.export) && ls.len() == 0,
            _ => false,
        }),
    ensures
        types_to(dty, denv, lctx, io, e, t, fuel),
{
}

/// Constructor lemmas for `types_to` -- one per disjunct, the intro API
/// producers use (each is definitional; the two binder cases witness
/// their existentials, validated to encode correctly per the
/// The typing relation is MONOTONE in its derivation-height index. Every
/// rule's premises sit either at the same height on a syntactic subterm or at
/// a strictly smaller height, so a derivation of height `f1` is also one of
/// any greater height. This is what a fuel-free exec inference needs: each
/// recursive call returns a derivation at its own height, and the rule being
/// applied wants them at a common one.
#[verifier::spinoff_prover]
pub proof fn types_to_mono(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    e: ExprSpec,
    t: ExprSpec,
    f1: nat,
    f2: nat,
)
    requires
        types_to(dty, denv, lctx, io, e, t, f1),
        f1 <= f2,
    ensures
        types_to(dty, denv, lctx, io, e, t, f2),
    decreases f1, e,
{
    // App: the premise is on a syntactic subterm at the SAME height.
    if let ExprSpec::App(f, a) = e {
        let (ft, aty, bt, aty2) = choose|ft: ExprSpec, aty: ExprSpec, bt: ExprSpec, aty2: ExprSpec|
            #![trigger app_marker(ft, aty, bt, aty2)]
            app_marker(ft, aty, bt, aty2) && types_to(dty, denv, lctx, io, *f, ft, f1) && deq_p(
                dty,
                denv,
                lctx,
                io,
                ft,
                ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)),
                (f1 - 1) as nat,
            ) && (infers(io) || (types_to(dty, denv, lctx, io, *a, aty2, f1) && deq_p(
                dty,
                denv,
                lctx,
                io,
                aty2,
                aty,
                (f1 - 1) as nat,
            ))) && t == subst_full(bt, seq![*a], 0);
        types_to_mono(dty, denv, lctx, io, *f, ft, f1, f2);
        deq_p_mono(
            dty,
            denv,
            lctx,
            io,
            ft,
            ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)),
            (f1 - 1) as nat,
            (f2 - 1) as nat,
        );
        // the ARGUMENT's derivation has to be lifted too, in the mode that
        // has one
        if !infers(io) {
            types_to_mono(dty, denv, lctx, io, *a, aty2, f1, f2);
            deq_p_mono(dty, denv, lctx, io, aty2, aty, (f1 - 1) as nat, (f2 - 1) as nat);
            assert(types_to(dty, denv, lctx, io, *a, aty2, f2));
        }
        assert(app_marker(ft, aty, bt, aty2));
        assert(types_to(dty, denv, lctx, io, e, t, f2));
    }
    // Leaves: these disjuncts do not mention the height at all, but the goal
    // still has to be unfolded at f2 for the solver to see that.

    match e {
        ExprSpec::Free(_)
        | ExprSpec::Sort(_)
        | ExprSpec::Const(_, _)
        | ExprSpec::NatLit(_)
        | ExprSpec::StringLit(_)
        | ExprSpec::Var(_)
        | ExprSpec::Closed => {
            assert(types_to(dty, denv, lctx, io, e, t, f2));
        },
        _ => {},
    }
    // Let and Proj: the premise sits at a height STRICTLY below f1, so the
    // very same witness serves at f2; it only has to be re-exhibited.
    if let ExprSpec::Let(ty0, val, body) = e {
        let h = choose|h: nat| #[trigger]
            fuel_marker(h) && h < f1 && types_to(
                dty,
                denv,
                lctx, io,
                subst_full(*body, seq![*val], 0),
                t,
                h,
            ) && (infers(io) || exists|s: ExprSpec, l: LevelSpec, vt: ExprSpec| #[trigger]
                let_check_marker(s, l, vt) && types_to(dty, denv, lctx, io, *ty0, s, h)
                && deq_p(dty, denv, lctx, io, s, ExprSpec::Sort(l), h)
                && types_to(dty, denv, lctx, io, *val, vt, h)
                && deq_p(dty, denv, lctx, io, vt, *ty0, h));
        assert(fuel_marker(h));
        assert(types_to(dty, denv, lctx, io, e, t, f2));
    }
    if let ExprSpec::Proj(idx, s) = e {
        let (h, sty, ind_id, ls, args, ctor_id, np, ctor_ty0) = choose|
            h: nat,
            sty: ExprSpec,
            ind_id: u64,
            ls: Seq<LevelSpec>,
            args: Seq<ExprSpec>,
            ctor_id: u64,
            np: u16,
            ctor_ty0: ExprSpec,
        | #[trigger]
            proj_marker(h, sty, ind_id, ls, args, ctor_id, np, ctor_ty0) && h < f1 && types_to(
                dty,
                denv,
                lctx, io,
                *s,
                sty,
                h,
            ) && deq_p(dty, denv, lctx, io, sty, spine_app(ExprSpec::Const(ind_id, ls), args), h)
                && denv.struct_ctor(ind_id) == Some(ctor_id) && denv.ctor_num_params(ctor_id) == Some(
                np,
            ) && types_to(dty, denv, lctx, io, ExprSpec::Const(ctor_id, ls), ctor_ty0, h) && (np as nat)
                <= args.len() && proj_field_type(
                dty,
                denv,
                lctx,
                io,
                h,
                ctor_ty0,
                args,
                np as nat,
                0,
                idx as nat,
                *s,
                t,
            );
        assert(proj_marker(h, sty, ind_id, ls, args, ctor_id, np, ctor_ty0));
        assert(types_to(dty, denv, lctx, io, e, t, f2));
    }
    // Binders: premises one height down, re-exhibited through the markers.

    if let ExprSpec::Bind(bk, binder_type, body) = e {
        assert(f1 > 0);
        let g1 = (f1 - 1) as nat;
        let g2 = (f2 - 1) as nat;
        // the binder's kind says which rule typed it
        if bk == BinderKind::Lam {
            let (lid, infd, bt2) = choose|lid: u32, infd: ExprSpec, bt2: ExprSpec| #[trigger]
                bind_marker(lid, infd, bt2) && lctx.contains_key(lid) && lctx[lid] == *binder_type && fv_absent(*body, lid) && unreach(lctx, lid, *binder_type) && unreach(lctx, lid, *body)
                && (infers(io) || exists|s: ExprSpec, l: LevelSpec| #[trigger] sort_check_marker(s, l)
                && types_to(dty, denv, lctx, io, *binder_type, s, g1)
                && deq_p(dty, denv, lctx, io, s, ExprSpec::Sort(l), g1)) && types_to(
                    dty,
                    denv,
                    lctx, io,
                    subst_full(*body, seq![ExprSpec::Free(lid)], 0),
                    infd,
                    g1,
                ) && deq_p(dty, denv, lctx, io, infd, bt2, g1) && t == ExprSpec::Bind(BinderKind::Pi, 
                    Box::new(abstr_full(*binder_type, seq![lid], 0)),
                    Box::new(abstr_full(bt2, seq![lid], 0)),
                );
            types_to_mono(
                dty,
                denv,
                lctx, io,
                subst_full(*body, seq![ExprSpec::Free(lid)], 0),
                infd,
                g1,
                g2,
            );
            deq_p_mono(dty, denv, lctx, io, infd, bt2, g1, g2);
            if !infers(io) {
                let (s0, l0) = choose|s: ExprSpec, l: LevelSpec| #[trigger] sort_check_marker(s, l)
                    && types_to(dty, denv, lctx, io, *binder_type, s, g1)
                    && deq_p(dty, denv, lctx, io, s, ExprSpec::Sort(l), g1);
                types_to_mono(dty, denv, lctx, io, *binder_type, s0, g1, g2);
                deq_p_mono(dty, denv, lctx, io, s0, ExprSpec::Sort(l0), g1, g2);
                assert(sort_check_marker(s0, l0));
            }
            assert(bind_marker(lid, infd, bt2));
            assert(types_to(dty, denv, lctx, io, e, t, f2));
        } else {
            let (lid, bt_ty, dom_level, instd_ty, cod_level) = choose|
                lid: u32,
                bt_ty: ExprSpec,
                dom_level: LevelSpec,
                instd_ty: ExprSpec,
                cod_level: LevelSpec,
            | #[trigger]
                pi_marker(lid, bt_ty, dom_level, instd_ty, cod_level) && lctx.contains_key(lid) && lctx[lid] == *binder_type && fv_absent(*body, lid) && unreach(lctx, lid, *binder_type) && unreach(lctx, lid, *body) && types_to(
                    dty,
                    denv,
                    lctx, io,
                    *binder_type,
                    bt_ty,
                    g1,
                ) && deq_p(dty, denv, lctx, io, bt_ty, ExprSpec::Sort(dom_level), g1) && types_to(
                    dty,
                    denv,
                    lctx, io,
                    subst_full(*body, seq![ExprSpec::Free(lid)], 0),
                    instd_ty,
                    g1,
                ) && deq_p(dty, denv, lctx, io, instd_ty, ExprSpec::Sort(cod_level), g1) && t == ExprSpec::Sort(
                    LevelSpec::IMax(Box::new(dom_level), Box::new(cod_level)),
                );
            types_to_mono(dty, denv, lctx, io, *binder_type, bt_ty, g1, g2);
            deq_p_mono(dty, denv, lctx, io, bt_ty, ExprSpec::Sort(dom_level), g1, g2);
            deq_p_mono(dty, denv, lctx, io, instd_ty, ExprSpec::Sort(cod_level), g1, g2);
            types_to_mono(
                dty,
                denv,
                lctx, io,
                subst_full(*body, seq![ExprSpec::Free(lid)], 0),
                instd_ty,
                g1,
                g2,
            );
            assert(pi_marker(lid, bt_ty, dom_level, instd_ty, cod_level));
            assert(types_to(dty, denv, lctx, io, *binder_type, bt_ty, (f2 - 1) as nat));
            assert(types_to(
                dty,
                denv,
                lctx, io,
                subst_full(*body, seq![ExprSpec::Free(lid)], 0),
                instd_ty,
                (f2 - 1) as nat,
            ));
            assert(types_to(dty, denv, lctx, io, e, t, f2));
        }
    }
}

/// recursive-exists note).
pub proof fn types_to_free(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    lid: u32,
    fuel: nat,
)
    requires
        lctx.contains_key(lid),
    ensures
        types_to(dty, denv, lctx, io, ExprSpec::Free(lid), lctx[lid], fuel),
{
}

pub proof fn types_to_sort(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    l: LevelSpec,
    fuel: nat,
)
    ensures
        types_to(
            dty,
            denv,
            lctx, io,
            ExprSpec::Sort(l),
            ExprSpec::Sort(LevelSpec::Succ(Box::new(l))),
            fuel,
        ),
{
}

pub proof fn types_to_const(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    cid: u64,
    clevels: Seq<LevelSpec>,
    t: ExprSpec,
    fuel: nat,
)
    requires
        dty.contains_key(cid),
        clevels.len() == dty[cid].0.len(),
        subst_expr_levels_rel(dty[cid].1, dty[cid].0, clevels, t),
    ensures
        types_to(dty, denv, lctx, io, ExprSpec::Const(cid, clevels), t, fuel),
{
}

/// Marker trigger for the application rule's four witnesses. Same idiom as
/// `irrel_marker`/`fuel_marker` elsewhere in this file: a multi-binder
/// `exists` needs one trigger term mentioning every bound variable, and no
/// natural term here mentions all four.
pub open spec fn app_marker(ft: ExprSpec, aty: ExprSpec, bt: ExprSpec, aty2: ExprSpec) -> bool {
    true
}

pub proof fn types_to_app(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    f: ExprSpec,
    a: ExprSpec,
    ft: ExprSpec,
    aty: ExprSpec,
    bt: ExprSpec,
    fuel: nat,
    aty2: ExprSpec,
)
    requires
        fuel > 0,
        types_to(dty, denv, lctx, io, f, ft, fuel),
        deq_p(dty, denv, lctx, io, ft, ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)), (fuel - 1) as nat),
        types_to(dty, denv, lctx, io, a, aty2, fuel),
        deq_p(dty, denv, lctx, io, aty2, aty, (fuel - 1) as nat),
    ensures
        types_to(
            dty,
            denv,
            lctx, io,
            ExprSpec::App(Box::new(f), Box::new(a)),
            subst_full(bt, seq![a], 0),
            fuel,
        ),
{
    assert(app_marker(ft, aty, bt, aty2));
    assert(subst_full(bt, seq![a], 0) == subst_full(bt, seq![a], 0));
}

/// The application rule from a reduction to the binder and an untyped
/// agreement of the argument's type: the heights those carry are lifted to
/// a common one, which is returned.
pub proof fn types_to_app_lift(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    f: ExprSpec,
    a: ExprSpec,
    ft: ExprSpec,
    aty: ExprSpec,
    bt: ExprSpec,
    fuel: nat,
    aty2: ExprSpec,
) -> (f2: nat)
    requires
        types_to(dty, denv, lctx, io, f, ft, fuel),
        pstep_star(denv, ft, ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt))),
        types_to(dty, denv, lctx, io, a, aty2, fuel),
        deq_any(denv, aty2, aty),
    ensures
        f2 >= fuel,
        types_to(
            dty,
            denv,
            lctx, io,
            ExprSpec::App(Box::new(f), Box::new(a)),
            subst_full(bt, seq![a], 0),
            f2,
        ),
{
    let hh = choose|hh: nat| #[trigger] deq(denv, aty2, aty, hh);
    deq_p_of_deq(dty, denv, lctx, io, aty2, aty, hh);
    types_to_app_lift_p(dty, denv, lctx, io, f, a, ft, aty, bt, fuel, aty2)
}

/// The application rule from a reduction to the binder and a typed
/// agreement of the argument's type -- the rule's own premise, so proof
/// irrelevance is admitted there.
pub proof fn types_to_app_lift_p(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    f: ExprSpec,
    a: ExprSpec,
    ft: ExprSpec,
    aty: ExprSpec,
    bt: ExprSpec,
    fuel: nat,
    aty2: ExprSpec,
) -> (f2: nat)
    requires
        types_to(dty, denv, lctx, io, f, ft, fuel),
        pstep_star(denv, ft, ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt))),
        types_to(dty, denv, lctx, io, a, aty2, fuel),
        deq_p_any(dty, denv, lctx, io, aty2, aty),
    ensures
        f2 >= fuel,
        types_to(
            dty,
            denv,
            lctx, io,
            ExprSpec::App(Box::new(f), Box::new(a)),
            subst_full(bt, seq![a], 0),
            f2,
        ),
{
    let hh = choose|hh: nat| #[trigger] deq_p(dty, denv, lctx, io, aty2, aty, hh);
    let f2: nat = (if fuel >= hh { fuel } else { hh }) + 1;
    types_to_mono(dty, denv, lctx, io, f, ft, fuel, f2);
    types_to_mono(dty, denv, lctx, io, a, aty2, fuel, f2);
    deq_p_mono(dty, denv, lctx, io, aty2, aty, hh, (f2 - 1) as nat);
    deq_p_of_pstep_star(dty, denv, lctx, io, ft, ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)), (f2 - 1) as nat);
    types_to_app(dty, denv, lctx, io, f, a, ft, aty, bt, f2, aty2);
    f2
}

pub proof fn types_to_let(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    ty0: ExprSpec,
    val: ExprSpec,
    body: ExprSpec,
    t: ExprSpec,
    f2: nat,
    fuel: nat,
)
    requires
        infers(io),
        f2 < fuel,
        types_to(dty, denv, lctx, io, subst_full(body, seq![val], 0), t, f2),
    ensures
        types_to(
            dty,
            denv,
            lctx, io,
            ExprSpec::Let(Box::new(ty0), Box::new(val), Box::new(body)),
            t,
            fuel,
        ),
{
    assert(fuel_marker(f2));
}

/// Constructor lemma for the `Proj` rule.
pub proof fn types_to_proj(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    idx: usize,
    s: ExprSpec,
    t: ExprSpec,
    f2: nat,
    sty: ExprSpec,
    ind_id: u64,
    ls: Seq<LevelSpec>,
    args: Seq<ExprSpec>,
    ctor_id: u64,
    np: u16,
    ctor_ty0: ExprSpec,
    fuel: nat,
)
    requires
        f2 < fuel,
        types_to(dty, denv, lctx, io, s, sty, f2),
        pstep_star(denv, sty, spine_app(ExprSpec::Const(ind_id, ls), args)),
        denv.struct_ctor(ind_id) == Some(ctor_id),
        denv.ctor_num_params(ctor_id) == Some(np),
        types_to(dty, denv, lctx, io, ExprSpec::Const(ctor_id, ls), ctor_ty0, f2),
        (np as nat) <= args.len(),
        proj_field_type(dty, denv, lctx, io, f2, ctor_ty0, args, np as nat, 0, idx as nat, s, t),
    ensures
        types_to(dty, denv, lctx, io, ExprSpec::Proj(idx, Box::new(s)), t, fuel),
{
    deq_p_of_pstep_star(dty, denv, lctx, io, sty, spine_app(ExprSpec::Const(ind_id, ls), args), f2);
    assert(proj_marker(f2, sty, ind_id, ls, args, ctor_id, np, ctor_ty0));
}

/// `proj_field_type` is monotone in its height: every step is a `deq_p` at it.
pub proof fn proj_field_type_mono(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    h1: nat,
    h2: nat,
    cur: ExprSpec,
    args: Seq<ExprSpec>,
    np: nat,
    fld: usize,
    remaining: nat,
    s: ExprSpec,
    t: ExprSpec,
)
    requires
        proj_field_type(dty, denv, lctx, io, h1, cur, args, np, fld, remaining, s, t),
        h1 <= h2,
    ensures
        proj_field_type(dty, denv, lctx, io, h2, cur, args, np, fld, remaining, s, t),
    decreases np + remaining,
{
    let (bt, body) = choose|bt: ExprSpec, body: ExprSpec| #[trigger]
        proj_step_marker(bt, body) && deq_p(
            dty,
            denv,
            lctx,
            io,
            cur,
            ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)),
            h1,
        ) && (if np > 0 {
            args.len() > 0 && proj_field_type(
                dty,
                denv,
                lctx,
                io,
                h1,
                subst_full(body, seq![args[0]], 0),
                args.drop_first(),
                (np - 1) as nat,
                fld,
                remaining,
                s,
                t,
            )
        } else if remaining > 0 {
            proj_field_type(
                dty,
                denv,
                lctx,
                io,
                h1,
                subst_full(body, seq![ExprSpec::Proj(fld, Box::new(s))], 0),
                args,
                0,
                (fld + 1) as usize,
                (remaining - 1) as nat,
                s,
                t,
            )
        } else {
            t == bt
        });
    deq_p_mono(dty, denv, lctx, io, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h1, h2);
    if np > 0 {
        proj_field_type_mono(
            dty,
            denv,
            lctx,
            io,
            h1,
            h2,
            subst_full(body, seq![args[0]], 0),
            args.drop_first(),
            (np - 1) as nat,
            fld,
            remaining,
            s,
            t,
        );
    } else if remaining > 0 {
        proj_field_type_mono(
            dty,
            denv,
            lctx,
            io,
            h1,
            h2,
            subst_full(body, seq![ExprSpec::Proj(fld, Box::new(s))], 0),
            args,
            0,
            (fld + 1) as usize,
            (remaining - 1) as nat,
            s,
            t,
        );
    }
    assert(proj_step_marker(bt, body));
}

/// The three steps of `proj_field_type` from a typed conversion to the binder.
pub proof fn proj_field_type_param_step_p(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    h: nat,
    cur: ExprSpec,
    bt: ExprSpec,
    body: ExprSpec,
    args: Seq<ExprSpec>,
    np: nat,
    fld: usize,
    remaining: nat,
    s: ExprSpec,
    t: ExprSpec,
)
    requires
        np > 0,
        args.len() > 0,
        deq_p(dty, denv, lctx, io, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h),
        proj_field_type(
            dty,
            denv,
            lctx,
            io,
            h,
            subst_full(body, seq![args[0]], 0),
            args.drop_first(),
            (np - 1) as nat,
            fld,
            remaining,
            s,
            t,
        ),
    ensures
        proj_field_type(dty, denv, lctx, io, h, cur, args, np, fld, remaining, s, t),
{
    assert(proj_step_marker(bt, body));
}

pub proof fn proj_field_type_field_step_p(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    h: nat,
    cur: ExprSpec,
    bt: ExprSpec,
    body: ExprSpec,
    args: Seq<ExprSpec>,
    fld: usize,
    remaining: nat,
    s: ExprSpec,
    t: ExprSpec,
)
    requires
        remaining > 0,
        deq_p(dty, denv, lctx, io, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h),
        proj_field_type(
            dty,
            denv,
            lctx,
            io,
            h,
            subst_full(body, seq![ExprSpec::Proj(fld, Box::new(s))], 0),
            args,
            0,
            (fld + 1) as usize,
            (remaining - 1) as nat,
            s,
            t,
        ),
    ensures
        proj_field_type(dty, denv, lctx, io, h, cur, args, 0, fld, remaining, s, t),
{
    assert(proj_step_marker(bt, body));
}

pub proof fn proj_field_type_final_p(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    h: nat,
    cur: ExprSpec,
    bt: ExprSpec,
    body: ExprSpec,
    args: Seq<ExprSpec>,
    fld: usize,
    s: ExprSpec,
)
    requires
        deq_p(dty, denv, lctx, io, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h),
    ensures
        proj_field_type(dty, denv, lctx, io, h, cur, args, 0, fld, 0, s, bt),
{
    assert(proj_step_marker(bt, body));
}

/// One parameter step of `proj_field_type`.
pub proof fn proj_field_type_param_step(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    h: nat,
    cur: ExprSpec,
    bt: ExprSpec,
    body: ExprSpec,
    args: Seq<ExprSpec>,
    np: nat,
    fld: usize,
    remaining: nat,
    s: ExprSpec,
    t: ExprSpec,
)
    requires
        np > 0,
        args.len() > 0,
        pstep_star(denv, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body))),
        proj_field_type(
            dty,
            denv,
            lctx,
            io,
            h,
            subst_full(body, seq![args[0]], 0),
            args.drop_first(),
            (np - 1) as nat,
            fld,
            remaining,
            s,
            t,
        ),
    ensures
        proj_field_type(dty, denv, lctx, io, h, cur, args, np, fld, remaining, s, t),
{
    deq_p_of_pstep_star(dty, denv, lctx, io, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h);
    assert(proj_step_marker(bt, body));
}

/// One field step of `proj_field_type`.
pub proof fn proj_field_type_field_step(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    h: nat,
    cur: ExprSpec,
    bt: ExprSpec,
    body: ExprSpec,
    args: Seq<ExprSpec>,
    fld: usize,
    remaining: nat,
    s: ExprSpec,
    t: ExprSpec,
)
    requires
        remaining > 0,
        pstep_star(denv, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body))),
        proj_field_type(
            dty,
            denv,
            lctx,
            io,
            h,
            subst_full(body, seq![ExprSpec::Proj(fld, Box::new(s))], 0),
            args,
            0,
            (fld + 1) as usize,
            (remaining - 1) as nat,
            s,
            t,
        ),
    ensures
        proj_field_type(dty, denv, lctx, io, h, cur, args, 0, fld, remaining, s, t),
{
    deq_p_of_pstep_star(dty, denv, lctx, io, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h);
    assert(proj_step_marker(bt, body));
}

/// The final step of `proj_field_type`: the field type is the binder type.
pub proof fn proj_field_type_final(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    h: nat,
    cur: ExprSpec,
    bt: ExprSpec,
    body: ExprSpec,
    args: Seq<ExprSpec>,
    fld: usize,
    s: ExprSpec,
)
    requires
        pstep_star(denv, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body))),
    ensures
        proj_field_type(dty, denv, lctx, io, h, cur, args, 0, fld, 0, s, bt),
{
    deq_p_of_pstep_star(dty, denv, lctx, io, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h);
    assert(proj_step_marker(bt, body));
}

pub proof fn types_to_lambda(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    binder_type: ExprSpec,
    body: ExprSpec,
    lid: u32,
    infd: ExprSpec,
    fuel: nat,
)
    requires
        infers(io),
        fuel > 0,
        lctx.contains_key(lid),
        lctx[lid] == binder_type,
        fv_absent(body, lid),
        unreach(lctx, lid, binder_type),
        unreach(lctx, lid, body),
        types_to(
            dty,
            denv,
            lctx, io,
            subst_full(body, seq![ExprSpec::Free(lid)], 0),
            infd,
            (fuel - 1) as nat,
        ),
    ensures
        types_to(
            dty,
            denv,
            lctx, io,
            ExprSpec::Bind(BinderKind::Lam, Box::new(binder_type), Box::new(body)),
            ExprSpec::Bind(BinderKind::Pi, 
                Box::new(abstr_full(binder_type, seq![lid], 0)),
                Box::new(abstr_full(infd, seq![lid], 0)),
            ),
            fuel,
        ),
{
    deq_p_refl(dty, denv, lctx, io, infd, (fuel - 1) as nat);
    assert(bind_marker(lid, infd, infd));
}

pub proof fn types_to_pi(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    binder_type: ExprSpec,
    body: ExprSpec,
    lid: u32,
    bt_ty: ExprSpec,
    dom_level: LevelSpec,
    instd_ty: ExprSpec,
    cod_level: LevelSpec,
    fuel: nat,
)
    requires
        fuel > 0,
        lctx.contains_key(lid),
        lctx[lid] == binder_type,
        fv_absent(body, lid),
        unreach(lctx, lid, binder_type),
        unreach(lctx, lid, body),
        types_to(dty, denv, lctx, io, binder_type, bt_ty, (fuel - 1) as nat),
        pstep_star(denv, bt_ty, ExprSpec::Sort(dom_level)),
        types_to(
            dty,
            denv,
            lctx, io,
            subst_full(body, seq![ExprSpec::Free(lid)], 0),
            instd_ty,
            (fuel - 1) as nat,
        ),
        pstep_star(denv, instd_ty, ExprSpec::Sort(cod_level)),
    ensures
        types_to(
            dty,
            denv,
            lctx, io,
            ExprSpec::Bind(BinderKind::Pi, Box::new(binder_type), Box::new(body)),
            ExprSpec::Sort(LevelSpec::IMax(Box::new(dom_level), Box::new(cod_level))),
            fuel,
        ),
{
    deq_p_of_pstep_star(dty, denv, lctx, io, bt_ty, ExprSpec::Sort(dom_level), (fuel - 1) as nat);
    deq_p_of_pstep_star(dty, denv, lctx, io, instd_ty, ExprSpec::Sort(cod_level), (fuel - 1) as nat);
    assert(pi_marker(lid, bt_ty, dom_level, instd_ty, cod_level));
}

/// THE MODEL-LEVEL PROOF-IRRELEVANCE FACT: `x` and `y` are both PROOFS
/// -- each typed (via `types_to`, so the type-of link is a checked
/// relation, not caller trust) by a type reaching a `Prop`-level `Sort`
/// -- of `deq_any`-related propositions. This is the honest semantic
/// content a proof-irrelevance verdict SHOULD carry, and the exact
/// ingredient a future `deq_p` (typed definitional equality with the
/// irrelevance case) consumes. Non-recursive; clean triggers.
/// Marker trigger for `proof_irrel_pair`'s witnesses.
pub open spec fn irrel_marker(tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat) -> bool {
    true
}

/// Marker trigger for `is_proof_type_m`'s witnesses.
pub open spec fn proof_type_marker(a: ExprSpec, tt: ExprSpec, f: nat, l: LevelSpec) -> bool {
    true
}

/// "`ty` is the type of a PROOF": it is convertible to some `a` whose own
/// type is a `Prop`-level sort (the model-side twin of
/// `delta_bound_model::is_proof_type_claim`). Up to conversion, as the unit
/// and structure conditions already are: the kernel knows its INFERRED type
/// is a proposition, and a derivation's type is only convertible to that.
pub open spec fn is_proof_type_m(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    ty: ExprSpec,
    h: nat,
) -> bool
    decreases h, 3int, 0nat,
{
    exists|a: ExprSpec, tt: ExprSpec, f: nat, l: LevelSpec| #[trigger]
        proof_type_marker(a, tt, f, l) && deq_p(dty, denv, lctx, io, ty, a, h) && f < h && types_to(dty, denv, lctx, io, a, tt, f) && wt1(dty, denv, lctx, io, a, h) && deq_p(
            dty,
            denv,
            lctx,
            io,
            tt,
            ExprSpec::Sort(l),
            h,
        ) && (forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) <= 0)
}

/// Proof irrelevance: `x` and `y` are PROOFS (their types' types are
/// `Prop`-level sorts) of convertible propositions. (Fixed 2026-09-06: the
/// previous form tested the types themselves against `Prop`, i.e. made `x`
/// and `y` propositions rather than proofs -- the same slip the exec
/// shadow route once had; nothing on the live certifier read the old form.)
pub open spec fn proof_irrel_pair(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
) -> bool
    decreases h, 4int, 0nat,
{
    exists|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
        irrel_marker(tx, ty2, fx, fy) && fx < h && fy < h && types_to(dty, denv, lctx, io, x, tx, fx) && types_to(
            dty,
            denv,
            lctx, io,
            y,
            ty2,
            fy,
        ) && is_proof_type_m(dty, denv, lctx, io, tx, h) && is_proof_type_m(dty, denv, lctx, io, ty2, h) && deq_p(
            dty,
            denv,
            lctx, io,
            tx,
            ty2,
            h,
        )
}

/// Marker triggers for `types_to`'s two BINDER rules. Without them those
/// rules' existential witnesses are write-only: an `exists` inside a match
/// arm whose trigger mentions the arm's own bound variables cannot be
/// re-introduced from outside, which is why the `Let` and `Proj` rules
/// already trigger on `fuel_marker`/`proj_marker` instead. Monotonicity in
/// the derivation height needs to re-exhibit these witnesses, so the binder
/// rules now carry markers of their own.
pub open spec fn bind_marker(lid: u32, infd: ExprSpec, bt2: ExprSpec) -> bool {
    true
}

/// Marker triggers for the real-typing checks the `Let` and lambda rules
/// make when `io == false`.
pub open spec fn let_check_marker(s: ExprSpec, l: LevelSpec, vt: ExprSpec) -> bool {
    true
}

pub open spec fn sort_check_marker(s: ExprSpec, l: LevelSpec) -> bool {
    true
}

pub open spec fn pi_marker(
    lid: u32,
    bt_ty: ExprSpec,
    dom_level: LevelSpec,
    instd_ty: ExprSpec,
    cod_level: LevelSpec,
) -> bool {
    true
}

/// Marker trigger for `unit_pair`'s witnesses, the same device
/// `irrel_marker` plays for proof irrelevance.
pub open spec fn unit_marker(tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat) -> bool {
    true
}

/// "This constant names a structure with one constructor that takes no
/// fields" -- a type with exactly one element.
pub open spec fn unit_like_head(denv: EnvSpec, id: u64) -> bool {
    exists|c: u64| #[trigger] denv.struct_ctor(id) == Some(c) && denv.ctor_num_fields(c) == Some(0u16)
}

/// The same, up to reduction: the kernel whnfs the inferred type before
/// looking at its head, so the rule's real side condition is that the type
/// REDUCES to such a structure.
pub open spec fn unit_like_type_m(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    h: nat,
) -> bool
    decreases h, 3int, 0nat,
{
    exists|r: ExprSpec| #[trigger] unit_like_marker(r) && deq_p(dty, denv, lctx, io, tx, r, h) && unit_like_type(denv, r)
}

/// Marker triggers for the two type conditions: their witnesses sit under
/// `deq_p`, which is in the same recursive group and so cannot trigger.
pub open spec fn unit_like_marker(r: ExprSpec) -> bool {
    true
}

pub open spec fn struct_type_marker(ils: Seq<LevelSpec>, rest: Seq<ExprSpec>) -> bool {
    true
}

/// "This type is such a structure, applied to whatever parameters."
pub open spec fn unit_like_type(denv: EnvSpec, tx: ExprSpec) -> bool {
    exists|id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>| #[trigger]
        spine_app(ExprSpec::Const(id, ls), args) == tx && unit_like_head(denv, id)
}

/// The shadow's untyped forms of the two type conditions: the certified
/// routes establish them by reduction and untyped conversion, and the lift
/// lemmas below place them at a height in the typed family.
pub open spec fn unit_like_type_u(denv: EnvSpec, tx: ExprSpec) -> bool {
    exists|r: ExprSpec| #[trigger] pstep_star(denv, tx, r) && unit_like_type(denv, r)
}

pub open spec fn struct_type_of_u(
    denv: EnvSpec,
    tx: ExprSpec,
    ind: u64,
    params: Seq<ExprSpec>,
) -> bool {
    exists|ils: Seq<LevelSpec>, rest: Seq<ExprSpec>| #[trigger]
        deq_any(denv, tx, spine_app(ExprSpec::Const(ind, ils), params + rest))
}

/// Reduction to a unit-like type holds at every height.
pub proof fn unit_like_type_of_u(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    h: nat,
)
    requires
        unit_like_type_u(denv, tx),
    ensures
        unit_like_type_m(dty, denv, lctx, io, tx, h),
{
    let r = choose|r: ExprSpec| #[trigger] pstep_star(denv, tx, r) && unit_like_type(denv, r);
    deq_p_of_pstep_star(dty, denv, lctx, io, tx, r, h);
    assert(unit_like_marker(r));
}

/// An untyped structure-type fact holds from some height on; this returns one.
pub proof fn struct_type_of_lift(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    ind: u64,
    params: Seq<ExprSpec>,
) -> (h: nat)
    requires
        struct_type_of_u(denv, tx, ind, params),
    ensures
        struct_type_of(dty, denv, lctx, io, tx, ind, params, h),
{
    let (ils, rest) = choose|ils: Seq<LevelSpec>, rest: Seq<ExprSpec>| #[trigger]
        deq_any(denv, tx, spine_app(ExprSpec::Const(ind, ils), params + rest));
    let target = spine_app(ExprSpec::Const(ind, ils), params + rest);
    let hh = choose|hh: nat| #[trigger] deq(denv, tx, target, hh);
    deq_p_of_deq(dty, denv, lctx, io, tx, target, hh);
    assert(struct_type_marker(ils, rest));
    hh
}

/// Marker trigger for `eta_struct_expand`'s witnesses.
pub open spec fn eta_struct_marker(
    tx: ExprSpec,
    f: nat,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    params: Seq<ExprSpec>,
    nf: nat,
) -> bool {
    true
}

/// "`tx` is CONVERTIBLE to the structure `ind` applied to `params` (and
/// possibly more)".
///
/// Convertible, not merely reducible: the kernel's `try_eta_struct_aux` reads
/// the constructor and parameters off the OTHER side -- which is already a
/// constructor application -- and establishes this side by checking the two
/// types are definitionally equal. Requiring `tx` to reduce to the structure
/// on its own is strictly stronger, and it was rejecting pairs the kernel
/// accepts, because `tx` need not whnf to a constant-headed application.
pub open spec fn struct_type_of(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    ind: u64,
    params: Seq<ExprSpec>,
    h: nat,
) -> bool
    decreases h, 3int, 0nat,
{
    exists|ils: Seq<LevelSpec>, rest: Seq<ExprSpec>| #[trigger]
        struct_type_marker(ils, rest) && deq_p(dty, denv, lctx, io, tx, spine_app(ExprSpec::Const(ind, ils), params + rest), h)
}

pub open spec fn eta_ctor_marker(cls: Seq<LevelSpec>, fields: Seq<ExprSpec>, ty0: ExprSpec, f0: nat) -> bool {
    true
}

/// "`tx` is convertible to the type of SOME application of the constructor
/// `cid` to `params` and `nf` fields" -- what the kernel's `try_eta_struct`
/// knows about the side it expands: its type agrees with the type of the
/// other side, which is such an application. Inverting that application's
/// typing gives the structure applied to `params`, so this says what
/// `struct_type_of` says, from the facts the kernel actually has.
#[verifier::opaque]
pub open spec fn ctor_typed_like(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    cid: u64,
    params: Seq<ExprSpec>,
    nf: nat,
    h: nat,
) -> bool
    decreases h, 3int, 0nat,
{
    exists|cls: Seq<LevelSpec>, fields: Seq<ExprSpec>, ty0: ExprSpec, f0: nat| #[trigger]
        eta_ctor_marker(cls, fields, ty0, f0) && fields.len() == nf && f0 < h && types_to(
            dty,
            denv,
            lctx,
            io,
            spine_app(ExprSpec::Const(cid, cls), params + fields),
            ty0,
            f0,
        ) && wt1(dty, denv, lctx, io, spine_app(ExprSpec::Const(cid, cls), params + fields), h) && deq_p(dty, denv, lctx, io, tx, ty0, h)
}

pub proof fn ctor_typed_like_mono(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    cid: u64,
    params: Seq<ExprSpec>,
    nf: nat,
    h1: nat,
    h2: nat,
)
    requires
        ctor_typed_like(dty, env, lctx, io, tx, cid, params, nf, h1),
        h1 <= h2,
    ensures
        ctor_typed_like(dty, env, lctx, io, tx, cid, params, nf, h2),
    decreases h1, 2int,
{
    reveal_with_fuel(ctor_typed_like, 1);
    let (cls, fields, ty0, f0) = choose|cls: Seq<LevelSpec>, fields: Seq<ExprSpec>, ty0: ExprSpec, f0: nat| #[trigger]
        eta_ctor_marker(cls, fields, ty0, f0) && fields.len() == nf && f0 < h1 && types_to(
            dty,
            env,
            lctx,
            io,
            spine_app(ExprSpec::Const(cid, cls), params + fields),
            ty0,
            f0,
        ) && wt1(dty, env, lctx, io, spine_app(ExprSpec::Const(cid, cls), params + fields), h1) && deq_p(dty, env, lctx, io, tx, ty0, h1);
    wt1_mono(dty, env, lctx, io, spine_app(ExprSpec::Const(cid, cls), params + fields), h1, h2);
    deq_p_mono(dty, env, lctx, io, tx, ty0, h1, h2);
    assert(eta_ctor_marker(cls, fields, ty0, f0));
}

/// STRUCTURE ETA, the kernel's `try_eta_struct`, in the same shape the
/// function-eta leaf uses: `x` is definitionally equal to its OWN eta
/// expansion, `Ctor params* x.0 x.1 .. x.(n-1)`. The route builds that
/// expansion and compares it with the other side by ordinary congruence,
/// exactly as it does for `fun a => f a`.
///
/// The typing premise is what makes this sound rather than nonsense: the
/// expansion is only equal to `x` when `x` really does inhabit that
/// structure, so the leaf carries `x`'s type and the fact that it reduces
/// to the structure whose sole constructor is the one being applied.
pub open spec fn eta_struct_expand(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
) -> bool
    decreases h, 4int, 0nat,
{
    exists|
        tx: ExprSpec,
        f: nat,
        ind: u64,
        cid: u64,
        ls: Seq<LevelSpec>,
        params: Seq<ExprSpec>,
        nf: nat,
    | #[trigger]
        eta_struct_marker(tx, f, ind, cid, ls, params, nf) && f < h && types_to(dty, denv, lctx, io, x, tx, f)
            && (struct_type_of(dty, denv, lctx, io, tx, ind, params, h) || ctor_typed_like(
            dty,
            denv,
            lctx,
            io,
            tx,
            cid,
            params,
            nf,
            h,
        )) && denv.struct_ctor(ind) == Some(cid)
            && denv.ctor_num_fields(cid) == Some(nf as u16) && y == spine_app(
            ExprSpec::Const(cid, ls),
            params + Seq::new(nf, |i: int| ExprSpec::Proj(i as usize, Box::new(x))),
        )
}

/// Symmetric, for the same reason the unit leaf is: `deq_p_c_symm` inverts
/// every disjunct, and either side may be the one being expanded.
pub open spec fn eta_struct_pair(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
) -> bool
    decreases h, 5int, 0nat,
{
    eta_struct_expand(dty, denv, lctx, io, x, y, h) || eta_struct_expand(dty, denv, lctx, io, y, x, h)
}

/// THE UNIT RULE, the kernel's `def_eq_unit`: if `x`'s type is a structure
/// whose single constructor takes no fields, and `y`'s type is convertible
/// to it, then `x` and `y` are definitionally equal -- the type has one
/// element, so there is nothing to distinguish them. Like proof
/// irrelevance, this is a rule ABOUT TYPING rather than about reduction,
/// so it lives in the `_p` family beside `proof_irrel_pair` and is stated
/// the same way, with a marker trigger over its four witnesses.
pub open spec fn unit_pair(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
) -> bool
    decreases h, 4int, 0nat,
{
    exists|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
        unit_marker(tx, ty2, fx, fy) && fx < h && fy < h && types_to(dty, denv, lctx, io, x, tx, fx) && types_to(
            dty,
            denv,
            lctx, io,
            y,
            ty2,
            fy,
        )
        // EITHER side being the unit-like one is enough, and stating it that
        // way keeps the leaf symmetric, which `deq_p_c_symm` inverts. The
        // kernel only ever inspects `x`'s type, but the rule is symmetric in
        // truth: the two types are convertible, so if one has a single
        // element so does the other.
         && (unit_like_type_m(dty, denv, lctx, io, tx, h) || unit_like_type_m(dty, denv, lctx, io, ty2, h))
            && deq_p(dty, denv, lctx, io, tx, ty2, h)
}

/// The NON-REDUCTION leaf equalities of definitional equality: two
/// `Sort`s whose levels agree under every level-variable assignment, or
/// two `Const`s with the same id and pointwise interp-equal level lists.
/// These are exactly the equalities `defeq` (reduction joinability) can
/// never see -- levels don't reduce -- and, unlike `def_eq_witness`'s
/// leaf disjuncts, they are stated over the MODEL (`ExprSpec`) and carry
/// the REAL semantic content (`def_eq_witness`'s `Const` case only
/// compares ids, its `Sort` case only relates ptr-shaped occurrences).
/// `Free`/`Var`/literal leaf equality needs no case here: syntactic
/// equality is already `defeq` via reflexivity.
pub open spec fn deq_leaf(x: ExprSpec, y: ExprSpec) -> bool {
    match (x, y) {
        (ExprSpec::Sort(l1), ExprSpec::Sort(l2)) => forall|rho: Map<nat, nat>| #[trigger]
            interp(l1, rho) == interp(l2, rho),
        (ExprSpec::Const(id1, ls1), ExprSpec::Const(id2, ls2)) => id1 == id2 && ls1.len()
            == ls2.len() && (forall|i: int, rho: Map<nat, nat>|
            0 <= i < ls1.len() ==> #[trigger] interp(ls1[i], rho) == interp(ls2[i], rho)),
        _ => false,
    }
}

/// `lam` is the eta-expansion of `f`: a lambda (of ANY binder type --
/// the relation is untyped, like `defeq`; in a well-typed term the type
/// is determined, and the eventual typed-soundness statement is where
/// that re-enters) whose body applies the WEAKENED `f` to `Var(0)`. Only
/// a lambda: a Pi is never an eta-expansion.
/// `shift(1, 0, f)` is the general de-Bruijn-correct form; for closed
/// `f` (`nlbv <= 0`, every real checker operand here) `shift` is the
/// identity via `nlbv_shift_noop`. Match-based, no existential.
pub open spec fn eta_expands_to(lam: ExprSpec, f: ExprSpec) -> bool {
    match lam {
        ExprSpec::Bind(BinderKind::Lam, _t, b) => *b == ExprSpec::App(
            Box::new(shift(1, 0, f)),
            Box::new(ExprSpec::Var(0)),
        ),
        _ => false,
    }
}

/// The ETA leaf of definitional equality: either side is the other's
/// eta-expansion. Symmetric by construction, height-free -- enters
/// `deq_c` as a disjunct exactly like `deq_leaf` (eta is not a
/// reduction in `pstep`, so joinability can never see it; it is a
/// genuine additional equality generator, matching Lean's own defeq).
pub open spec fn deq_eta(x: ExprSpec, y: ExprSpec) -> bool {
    eta_expands_to(x, y) || eta_expands_to(y, x)
}

/// ONE PARALLEL STEP of the inductive definitional-equality relation:
/// the congruence closure of (reduction joinability `defeq` ∪ the leaf
/// level equalities `deq_leaf`), height-indexed for well-foundedness --
/// NO transitivity here. `deq_c(env, x, y, 0)` degenerates to
/// `defeq || deq_leaf`; each extra height unit allows one more layer of
/// congruence (at every `ExprSpec` shape with sub-positions, mirroring
/// `pstep`'s own congruence arms). Transitivity lives one level up in
/// `deq` as EXPLICIT CHAINS of these steps -- deliberately the exact
/// architecture `pstep`/`pstep_chain_valid`/`pstep_star` already use,
/// and for the same encoding reason: an inlined transitivity
/// existential inside a RECURSIVE spec fn is unusable (Verus cannot
/// bridge separately-written alpha-equivalent quantifiers, and a
/// recursive fn's body is fuel-guarded rather than inlined -- found
/// empirically via probe lemmas after both the direct and the
/// named-helper formulations failed), while a chain existential in a
/// NON-recursive wrapper spec fn inlines and works, as the whole
/// `pstep_star` lemma family demonstrates. A classic normalization
/// argument says chains of congruence steps lose no generality vs.
/// arbitrarily interleaved congruence/transitivity derivations: a
/// congruence node OVER a transitive composition flattens into a chain
/// of whole-term congruence steps (e.g. `App(f1, a) ~ App(f2, a) ~
/// App(f3, a)` for `f1 ~ f2 ~ f3`).
/// The body of a binder opened with the free variable `k` (locally
/// nameless "open"): `inst_free(b, k) == b[Var 0 := Free k]`.
pub open spec fn inst_free(b: ExprSpec, k: u32) -> ExprSpec {
    subst_full(b, seq![ExprSpec::Free(k)], 0)
}

/// Marker trigger for the fresh-instance rule's existential (a trigger
/// must not mention match-bound variables -- see the match-arm exists
/// trigger law in the project memory).
pub open spec fn fresh_marker(k: u32) -> bool {
    true
}

/// QUOTIENT COMPUTATION (2026-09-11), the kernel's `reduce_quot`
/// (`tc.rs`): `Quot.lift A r B f h (Quot.mk A r a) rest..` and
/// `Quot.ind A r B p (Quot.mk A r a) rest..` contract to `f a rest..` /
/// `p a rest..`. Lean's quotient constants are AXIOMS, so this rule is a
/// primitive of the theory rather than a consequence of delta/beta/iota:
/// it enters the model as a LEAF of definitional equality, exactly as
/// `deq_eta` does, not as a reduction rule (`pstep` has no case for it and
/// the confluence family is untouched). Disclosed trust of the same
/// character as the constructor/recursor data bridges.
pub open spec fn quot_mk_spine(export: nat, e: ExprSpec) -> bool {
    match spine_head(e) {
        ExprSpec::Const(id, _) => quot_kind_of(export, id) == Some(2u8) && spine_args(e).len() == 3,
        _ => false,
    }
}

/// Index of the major premise (the `Quot.mk` argument) and of the first
/// trailing argument: `Quot.lift` takes `{A} {r} {B} f h q`, `Quot.ind`
/// takes `{A} {r} {B} p q`; both take the function at index 3.
pub open spec fn quot_major_idx(export: nat, s: ExprSpec) -> Option<nat> {
    match spine_head(s) {
        ExprSpec::Const(id, _) => match quot_kind_of(export, id) {
            Some(0u8) => Some(5nat),
            Some(1u8) => Some(4nat),
            _ => None,
        },
        _ => None,
    }
}

pub open spec fn quot_ready(export: nat, s: ExprSpec) -> bool {
    match quot_major_idx(export, s) {
        Some(qi) => {
            let args = spine_args(s);
            args.len() > qi && quot_mk_spine(export, args[qi as int])
        },
        None => false,
    }
}

pub open spec fn quot_result(export: nat, s: ExprSpec) -> ExprSpec {
    let args = spine_args(s);
    let qi = quot_major_idx(export, s)->Some_0;
    let a = spine_args(args[qi as int])[2];
    spine_app(ExprSpec::App(Box::new(args[3int]), Box::new(a)), args.skip(qi as int + 1))
}

/// The symmetric leaf, shaped like `deq_eta`.
pub open spec fn deq_quot(export: nat, x: ExprSpec, y: ExprSpec) -> bool {
    (quot_ready(export, x) && y == quot_result(export, x)) || (quot_ready(export, y) && x == quot_result(export, y))
}

/// The recursor leaf, uncapped: a recursor applied to a constructor spine in
/// its major position converts to the rule instance -- `reduce_rec`'s step.
/// Symmetric like `deq_quot`.
pub open spec fn deq_rec(denv: EnvSpec, x: ExprSpec, y: ExprSpec) -> bool {
    (crate::beta_model::rec_ready_u(denv, x) && y == crate::beta_model::rec_result(denv, x)) || (
    crate::beta_model::rec_ready_u(denv, y) && x == crate::beta_model::rec_result(denv, y))
}

/// Introduction for the quotient leaf: from the spine shapes alone, the
/// contracted term is `quot_result`. Extracted from the exec producer,
/// whose single query exceeded the resource limit with this inline.
#[verifier::spinoff_prover]
pub proof fn deq_quot_intro(
    export: nat,
    head_m: ExprSpec,
    args2: Seq<ExprSpec>,
    qi: nat,
    mk_head: ExprSpec,
    mk_args: Seq<ExprSpec>,
    r: ExprSpec,
)
    requires
        matches!(head_m, ExprSpec::Const(_, _)),
        quot_major_idx(export, spine_app(head_m, args2)) == Some(qi),
        args2.len() > qi,
        qi >= 4,
        matches!(mk_head, ExprSpec::Const(_, _)),
        quot_kind_of(export, mk_head->Const_0) == Some(2u8),
        args2[qi as int] == spine_app(mk_head, mk_args),
        mk_args.len() == 3,
        r == spine_app(
            ExprSpec::App(Box::new(args2[3int]), Box::new(mk_args[2int])),
            args2.skip(qi as int + 1),
        ),
    ensures
        deq_quot(export, spine_app(head_m, args2), r),
{
    let sp = spine_app(head_m, args2);
    spine_destruct_app(head_m, args2);
    assert(spine_head(sp) == head_m);
    assert(spine_args(sp) =~= args2);
    spine_destruct_app(mk_head, mk_args);
    assert(spine_head(args2[qi as int]) == mk_head);
    assert(spine_args(args2[qi as int]) =~= mk_args);
    assert(quot_mk_spine(export, args2[qi as int]));
    assert(quot_ready(export, sp));
    assert(spine_args(args2[qi as int])[2] == mk_args[2int]);
    assert(quot_result(export, sp) == r);
}

pub open spec fn deq_c(
    env: EnvSpec,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
) -> bool
    decreases h, 0int,
{
    ||| defeq(env, x, y)
    ||| deq_leaf(x, y)
    ||| deq_eta(x, y)
    ||| deq_quot(env.export, x, y)
    ||| deq_rec(env, x, y)
    ||| (h > 0 && match (x, y) {
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => deq_c(env, *f1, *f2, (h - 1) as nat)
            && deq_c(env, *a1, *a2, (h - 1) as nat),
        // Binder congruence, two forms: on the RAW bodies (loose `Var 0`
        // and all), or -- the standard locally-nameless rule, which the
        // real checker uses -- on the bodies OPENED with one fresh free
        // variable `k` (absent from both bodies), related by a `deq`
        // CHAIN one height down (chains, not a single step: the opened
        // bodies may need reduction steps that raw bodies cannot take).
        (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => bk1 == bk2 && deq_c(env, *t1, *t2, (h - 1) as nat)
            && (deq_c(env, *b1, *b2, (h - 1) as nat) || (exists|k: u32| #[trigger]
            fresh_marker(k) && fv_absent(*b1, k) && fv_absent(*b2, k) && deq(
                env,
                inst_free(*b1, k),
                inst_free(*b2, k),
                (h - 1) as nat,
            ))),
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => deq_c(
            env,
            *t1,
            *t2,
            (h - 1) as nat,
        ) && deq_c(env, *v1, *v2, (h - 1) as nat) && deq_c(env, *b1, *b2, (h - 1) as nat),
        (ExprSpec::Proj(pidx1, s1), ExprSpec::Proj(pidx2, s2)) => pidx1 == pidx2 && deq_c(
            env,
            *s1,
            *s2,
            (h - 1) as nat,
        ),
        _ => false,
    })
}

/// A chain of `deq_c` steps at height `h` -- `pstep_chain_valid`'s
/// direct analogue.
pub open spec fn deq_chain_valid(
    env: EnvSpec,
    ch: Seq<ExprSpec>,
    h: nat,
) -> bool
    decreases h, 1int,
{
    forall|i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 ==> deq_c(env, ch[i], ch[i + 1], h)
}

/// THE INDUCTIVE DEFINITIONAL-EQUALITY RELATION -- the "proper
/// inductive definitional-equality relation, not a flat disjunction"
/// that `full_def_eq`'s doc comment names as the honest target:
/// chain-witnessed transitive closure of `deq_c` (see its doc for why
/// chains rather than a transitivity constructor). Reflexive (length-1
/// chain), symmetric (`deq_symm`, chain reversal + per-link `deq_c_symm`),
/// transitive (`deq_trans`, chain concatenation -- free, exactly like
/// `pstep_star_trans`), congruent (`deq_app_congr` etc.), and subsumes
/// both `defeq` and the leaf equalities (length-2 chains).
pub open spec fn deq(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat) -> bool
    decreases h, 2int,
{
    exists|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_chain_valid(env, ch, h)
}

/// `deq_c` is monotone in its height index.
pub proof fn deq_c_mono(
    env: EnvSpec,
    x: ExprSpec,
    y: ExprSpec,
    h1: nat,
    h2: nat,
)
    requires
        deq_c(env, x, y, h1),
        h1 <= h2,
    ensures
        deq_c(env, x, y, h2),
    decreases h1, 0int,
{
    if defeq(env, x, y) || deq_leaf(x, y) || deq_eta(x, y) || deq_quot(env.export, x, y) || deq_rec(env, x, y) {
    } else {
        assert(h1 > 0);
        match (x, y) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                assert(deq_c(env, *f1, *f2, (h1 - 1) as nat) && deq_c(
                    env,
                    *a1,
                    *a2,
                    (h1 - 1) as nat,
                ));
                deq_c_mono(env, *f1, *f2, (h1 - 1) as nat, (h2 - 1) as nat);
                deq_c_mono(env, *a1, *a2, (h1 - 1) as nat, (h2 - 1) as nat);
                assert(h2 > 0 && deq_c(env, *f1, *f2, (h2 - 1) as nat) && deq_c(
                    env,
                    *a1,
                    *a2,
                    (h2 - 1) as nat,
                ));
                assert(deq_c(env, x, y, h2));
            },
            (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => {
                assert(deq_c(env, *t1, *t2, (h1 - 1) as nat));
                deq_c_mono(env, *t1, *t2, (h1 - 1) as nat, (h2 - 1) as nat);
                if deq_c(env, *b1, *b2, (h1 - 1) as nat) {
                    deq_c_mono(env, *b1, *b2, (h1 - 1) as nat, (h2 - 1) as nat);
                    assert(h2 > 0 && deq_c(env, *t1, *t2, (h2 - 1) as nat) && deq_c(
                        env,
                        *b1,
                        *b2,
                        (h2 - 1) as nat,
                    ));
                } else {
                    let k = choose|k: u32| #[trigger]
                        fresh_marker(k) && fv_absent(*b1, k) && fv_absent(*b2, k) && deq(
                            env,
                            inst_free(*b1, k),
                            inst_free(*b2, k),
                            (h1 - 1) as nat,
                        );
                    deq_mono(
                        env,
                        inst_free(*b1, k),
                        inst_free(*b2, k),
                        (h1 - 1) as nat,
                        (h2 - 1) as nat,
                    );
                    assert(fresh_marker(k));
                    assert(fresh_marker(k) && fv_absent(*b1, k) && fv_absent(*b2, k) && deq(
                        env,
                        inst_free(*b1, k),
                        inst_free(*b2, k),
                        (h2 - 1) as nat,
                    ));
                }
                assert(deq_c(env, x, y, h2));
            },
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                assert(deq_c(env, *t1, *t2, (h1 - 1) as nat) && deq_c(
                    env,
                    *v1,
                    *v2,
                    (h1 - 1) as nat,
                ) && deq_c(env, *b1, *b2, (h1 - 1) as nat));
                deq_c_mono(env, *t1, *t2, (h1 - 1) as nat, (h2 - 1) as nat);
                deq_c_mono(env, *v1, *v2, (h1 - 1) as nat, (h2 - 1) as nat);
                deq_c_mono(env, *b1, *b2, (h1 - 1) as nat, (h2 - 1) as nat);
                assert(h2 > 0 && deq_c(env, *t1, *t2, (h2 - 1) as nat) && deq_c(
                    env,
                    *v1,
                    *v2,
                    (h2 - 1) as nat,
                ) && deq_c(env, *b1, *b2, (h2 - 1) as nat));
                assert(deq_c(env, x, y, h2));
            },
            (ExprSpec::Proj(pidx1, s1), ExprSpec::Proj(pidx2, s2)) => {
                assert(deq_c(env, *s1, *s2, (h1 - 1) as nat));
                deq_c_mono(env, *s1, *s2, (h1 - 1) as nat, (h2 - 1) as nat);
                assert(h2 > 0 && deq_c(env, *s1, *s2, (h2 - 1) as nat));
                assert(deq_c(env, x, y, h2));
            },
            _ => {
                assert(false);
            },
        }
    }
}

/// `deq_c` is symmetric, height-preserving: `defeq` by its own lemma,
/// `deq_leaf` by the symmetry of its interp equalities, congruence by
/// the IH on sub-derivations.
pub proof fn deq_c_symm(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat)
    requires
        deq_c(env, x, y, h),
    ensures
        deq_c(env, y, x, h),
    decreases h, 0int,
{
    if defeq(env, x, y) {
        defeq_symm(env, x, y);
    } else if deq_leaf(x, y) {
        assert(deq_leaf(y, x));
    } else if deq_eta(x, y) {
        assert(deq_eta(y, x));
    } else if deq_quot(env.export, x, y) {
        assert(deq_quot(env.export, y, x));
    } else if deq_rec(env, x, y) {
        assert(deq_rec(env, y, x));
    } else {
        assert(h > 0);
        match (x, y) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                assert(deq_c(env, *f1, *f2, (h - 1) as nat) && deq_c(
                    env,
                    *a1,
                    *a2,
                    (h - 1) as nat,
                ));
                deq_c_symm(env, *f1, *f2, (h - 1) as nat);
                deq_c_symm(env, *a1, *a2, (h - 1) as nat);
                assert(h > 0 && deq_c(env, *f2, *f1, (h - 1) as nat) && deq_c(
                    env,
                    *a2,
                    *a1,
                    (h - 1) as nat,
                ));
                assert(deq_c(env, y, x, h));
            },
            (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => {
                assert(deq_c(env, *t1, *t2, (h - 1) as nat));
                deq_c_symm(env, *t1, *t2, (h - 1) as nat);
                if deq_c(env, *b1, *b2, (h - 1) as nat) {
                    deq_c_symm(env, *b1, *b2, (h - 1) as nat);
                    assert(h > 0 && deq_c(env, *t2, *t1, (h - 1) as nat) && deq_c(
                        env,
                        *b2,
                        *b1,
                        (h - 1) as nat,
                    ));
                } else {
                    let k = choose|k: u32| #[trigger]
                        fresh_marker(k) && fv_absent(*b1, k) && fv_absent(*b2, k) && deq(
                            env,
                            inst_free(*b1, k),
                            inst_free(*b2, k),
                            (h - 1) as nat,
                        );
                    deq_symm(env, inst_free(*b1, k), inst_free(*b2, k), (h - 1) as nat);
                    assert(fresh_marker(k));
                    assert(fresh_marker(k) && fv_absent(*b2, k) && fv_absent(*b1, k) && deq(
                        env,
                        inst_free(*b2, k),
                        inst_free(*b1, k),
                        (h - 1) as nat,
                    ));
                }
                assert(deq_c(env, y, x, h));
            },
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                assert(deq_c(env, *t1, *t2, (h - 1) as nat) && deq_c(env, *v1, *v2, (h - 1) as nat)
                    && deq_c(env, *b1, *b2, (h - 1) as nat));
                deq_c_symm(env, *t1, *t2, (h - 1) as nat);
                deq_c_symm(env, *v1, *v2, (h - 1) as nat);
                deq_c_symm(env, *b1, *b2, (h - 1) as nat);
                assert(h > 0 && deq_c(env, *t2, *t1, (h - 1) as nat) && deq_c(
                    env,
                    *v2,
                    *v1,
                    (h - 1) as nat,
                ) && deq_c(env, *b2, *b1, (h - 1) as nat));
                assert(deq_c(env, y, x, h));
            },
            (ExprSpec::Proj(pidx1, s1), ExprSpec::Proj(pidx2, s2)) => {
                assert(deq_c(env, *s1, *s2, (h - 1) as nat));
                deq_c_symm(env, *s1, *s2, (h - 1) as nat);
                assert(h > 0 && deq_c(env, *s2, *s1, (h - 1) as nat));
                assert(deq_c(env, y, x, h));
            },
            _ => {
                assert(false);
            },
        }
    }
}

/// A single `deq_c` step is a `deq` fact: the length-2 chain.
pub proof fn deq_of_deq_c(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat)
    requires
        deq_c(env, x, y, h),
    ensures
        deq(env, x, y, h),
{
    let ch = seq![x, y];
    assert(ch.len() == 2);
    assert(ch[0] == x);
    assert(ch[ch.len() - 1] == y);
    assert(deq_chain_valid(env, ch, h)) by {
        assert forall|i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies deq_c(
            env,
            ch[i],
            ch[i + 1],
            h,
        ) by {
            assert(i == 0);
        }
    }
}

/// Constructor lemma: joinability is `deq` at any height.
pub proof fn deq_of_defeq(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat)
    requires
        defeq(env, x, y),
    ensures
        deq(env, x, y, h),
{
    deq_of_deq_c(env, x, y, h);
}

/// Constructor lemma: a leaf level-equality is `deq` at any height.
pub proof fn deq_of_leaf(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat)
    requires
        deq_leaf(x, y),
    ensures
        deq(env, x, y, h),
{
    deq_of_deq_c(env, x, y, h);
}

/// Constructor lemma: an eta pair is `deq` at any height.
pub proof fn deq_of_quot(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat)
    requires
        deq_quot(env.export, x, y),
    ensures
        deq(env, x, y, h),
{
    deq_of_deq_c(env, x, y, h);
}

/// Constructor lemma: a recursor step is `deq` at any height.
pub proof fn deq_of_rec(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat)
    requires
        deq_rec(env, x, y),
    ensures
        deq(env, x, y, h),
{
    deq_of_deq_c(env, x, y, h);
}

pub proof fn deq_any_of_quot(env: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        deq_quot(env.export, x, y),
    ensures
        deq_any(env, x, y),
{
    deq_of_quot(env, x, y, 0);
    assert(deq(env, x, y, 0));
}

pub proof fn deq_of_eta(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat)
    requires
        deq_eta(x, y),
    ensures
        deq(env, x, y, h),
{
    deq_of_deq_c(env, x, y, h);
}

/// `deq_any` form of the eta constructor.
pub proof fn deq_any_of_eta(env: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        deq_eta(x, y),
    ensures
        deq_any(env, x, y),
{
    deq_of_eta(env, x, y, 0);
    assert(deq(env, x, y, 0));
}

/// `deq` is reflexive at every height: the length-1 chain.
pub proof fn deq_refl(env: EnvSpec, x: ExprSpec, h: nat)
    ensures
        deq(env, x, x, h),
{
    let ch = seq![x];
    assert(ch.len() == 1);
    assert(ch[0] == x);
    assert(ch[ch.len() - 1] == x);
    assert(deq_chain_valid(env, ch, h));
}

/// `deq` is monotone in its height index: per-link `deq_c_mono` over
/// the witness chain.
pub proof fn deq_mono(
    env: EnvSpec,
    x: ExprSpec,
    y: ExprSpec,
    h1: nat,
    h2: nat,
)
    requires
        deq(env, x, y, h1),
        h1 <= h2,
    ensures
        deq(env, x, y, h2),
    decreases h1, 1int,
{
    let ch = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_chain_valid(env, ch, h1);
    assert(deq_chain_valid(env, ch, h2)) by {
        assert forall|i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies deq_c(
            env,
            ch[i],
            ch[i + 1],
            h2,
        ) by {
            assert(deq_c(env, ch[i], ch[i + 1], h1));
            deq_c_mono(env, ch[i], ch[i + 1], h1, h2);
        }
    }
}

/// `deq` is symmetric, height-preserving: reverse the witness chain and
/// flip each link with `deq_c_symm`.
pub proof fn deq_symm(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat)
    requires
        deq(env, x, y, h),
    ensures
        deq(env, y, x, h),
    decreases h, 1int,
{
    let ch = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_chain_valid(env, ch, h);
    let n = ch.len();
    let rev = Seq::new(n, |i: int| ch[n - 1 - i]);
    assert(rev.len() == n);
    assert(rev[0] == ch[n - 1]);
    assert(rev[rev.len() - 1] == ch[0]);
    assert(deq_chain_valid(env, rev, h)) by {
        assert forall|i: int| #![trigger rev[i]] 0 <= i < rev.len() - 1 implies deq_c(
            env,
            rev[i],
            rev[i + 1],
            h,
        ) by {
            assert(rev[i] == ch[n - 1 - i]);
            assert(rev[i + 1] == ch[n - 2 - i]);
            assert(deq_c(env, ch[n - 2 - i], ch[n - 1 - i], h));
            deq_c_symm(env, ch[n - 2 - i], ch[n - 1 - i], h);
        }
    }
}

/// `deq` is transitive -- for FREE, by chain concatenation, exactly like
/// `pstep_star_trans` (and unlike every attempt to keep transitivity as
/// a constructor inside a recursive relation, see `deq_c`'s doc).
pub proof fn deq_trans(
    env: EnvSpec,
    x: ExprSpec,
    y: ExprSpec,
    z: ExprSpec,
    h: nat,
)
    requires
        deq(env, x, y, h),
        deq(env, y, z, h),
    ensures
        deq(env, x, z, h),
{
    let ch1 = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_chain_valid(env, ch, h);
    let ch2 = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == y && ch[ch.len() - 1] == z && deq_chain_valid(env, ch, h);
    let n1 = ch1.len();
    let ch2_tail = ch2.subrange(1, ch2.len() as int);
    let ch = ch1 + ch2_tail;
    assert(ch.len() == n1 + ch2.len() - 1);
    assert(ch[0] == ch1[0]);
    if ch2.len() == 1 {
        assert(ch2_tail =~= Seq::<ExprSpec>::empty());
        assert(ch =~= ch1);
        assert(ch[ch.len() - 1] == y);
        assert(y == z);
    } else {
        assert(ch[ch.len() - 1] == ch2_tail[ch2_tail.len() - 1]);
        assert(ch2_tail[ch2_tail.len() - 1] == ch2[ch2.len() - 1]);
    }
    assert(deq_chain_valid(env, ch, h)) by {
        assert forall|i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies deq_c(
            env,
            ch[i],
            ch[i + 1],
            h,
        ) by {
            if i < n1 - 1 {
                assert(ch[i] == ch1[i]);
                assert(ch[i + 1] == ch1[i + 1]);
                assert(deq_c(env, ch1[i], ch1[i + 1], h));
            } else if i == n1 - 1 {
                assert(ch[i] == ch1[n1 - 1]);
                assert(ch1[n1 - 1] == y);
                assert(ch[i + 1] == ch2_tail[0]);
                assert(ch2_tail[0] == ch2[1]);
                assert(deq_c(env, ch2[0], ch2[1], h));
                assert(ch2[0] == y);
            } else {
                assert(ch[i] == ch2_tail[i - n1]);
                assert(ch[i + 1] == ch2_tail[i + 1 - n1]);
                assert(ch2_tail[i - n1] == ch2[i - n1 + 1]);
                assert(ch2_tail[i + 1 - n1] == ch2[i + 2 - n1]);
                assert(deq_c(env, ch2[i - n1 + 1], ch2[i - n1 + 2], h));
            }
        }
    }
}

/// `deq` congruence at `App`, both positions varying: map `App(-, a1)`
/// over the function-side chain, `App(f2, -)` over the argument-side
/// chain, and concatenate -- each mapped link is a `deq_c` congruence
/// step one height up (the fixed side rides along via `deq_c`
/// reflexivity through `defeq`).
pub proof fn deq_app_congr(
    env: EnvSpec,
    f1: ExprSpec,
    f2: ExprSpec,
    a1: ExprSpec,
    a2: ExprSpec,
    h: nat,
)
    requires
        deq(env, f1, f2, h),
        deq(env, a1, a2, h),
    ensures
        deq(
            env,
            ExprSpec::App(Box::new(f1), Box::new(a1)),
            ExprSpec::App(Box::new(f2), Box::new(a2)),
            h + 1,
        ),
{
    let chf = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == f1 && ch[ch.len() - 1] == f2 && deq_chain_valid(env, ch, h);
    let cha = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == a1 && ch[ch.len() - 1] == a2 && deq_chain_valid(env, ch, h);
    let mf = Seq::new(chf.len(), |i: int| ExprSpec::App(Box::new(chf[i]), Box::new(a1)));
    let ma = Seq::new(cha.len(), |i: int| ExprSpec::App(Box::new(f2), Box::new(cha[i])));
    assert(deq_chain_valid(env, mf, h + 1)) by {
        assert forall|i: int| #![trigger mf[i]] 0 <= i < mf.len() - 1 implies deq_c(
            env,
            mf[i],
            mf[i + 1],
            h + 1,
        ) by {
            assert(deq_c(env, chf[i], chf[i + 1], h));
            defeq_refl(env, a1);
            assert(deq_c(env, a1, a1, h));
            assert(mf[i] == ExprSpec::App(Box::new(chf[i]), Box::new(a1)));
            assert(mf[i + 1] == ExprSpec::App(Box::new(chf[i + 1]), Box::new(a1)));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_c(env, mf[i], mf[i + 1], h + 1));
        }
    }
    assert(deq_chain_valid(env, ma, h + 1)) by {
        assert forall|i: int| #![trigger ma[i]] 0 <= i < ma.len() - 1 implies deq_c(
            env,
            ma[i],
            ma[i + 1],
            h + 1,
        ) by {
            assert(deq_c(env, cha[i], cha[i + 1], h));
            defeq_refl(env, f2);
            assert(deq_c(env, f2, f2, h));
            assert(ma[i] == ExprSpec::App(Box::new(f2), Box::new(cha[i])));
            assert(ma[i + 1] == ExprSpec::App(Box::new(f2), Box::new(cha[i + 1])));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_c(env, ma[i], ma[i + 1], h + 1));
        }
    }
    assert(mf[0] == ExprSpec::App(Box::new(f1), Box::new(a1)));
    assert(mf[mf.len() - 1] == ExprSpec::App(Box::new(f2), Box::new(a1)));
    assert(ma[0] == ExprSpec::App(Box::new(f2), Box::new(a1)));
    assert(ma[ma.len() - 1] == ExprSpec::App(Box::new(f2), Box::new(a2)));
    assert(deq(
        env,
        ExprSpec::App(Box::new(f1), Box::new(a1)),
        ExprSpec::App(Box::new(f2), Box::new(a1)),
        h + 1,
    ));
    assert(deq(
        env,
        ExprSpec::App(Box::new(f2), Box::new(a1)),
        ExprSpec::App(Box::new(f2), Box::new(a2)),
        h + 1,
    ));
    deq_trans(
        env,
        ExprSpec::App(Box::new(f1), Box::new(a1)),
        ExprSpec::App(Box::new(f2), Box::new(a1)),
        ExprSpec::App(Box::new(f2), Box::new(a2)),
        h + 1,
    );
}

/// `deq` congruence at `Bind`, both positions varying (same two-segment
/// chain-mapping as `deq_app_congr`).
pub proof fn deq_bind_congr(
    env: EnvSpec,
    t1: ExprSpec,
    t2: ExprSpec,
    b1: ExprSpec,
    b2: ExprSpec,
    h: nat,
    bkind: BinderKind,
)
    requires
        deq(env, t1, t2, h),
        deq(env, b1, b2, h),
    ensures
        deq(
            env,
            ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)),
            ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2)),
            h + 1,
        ),
{
    let cht = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == t1 && ch[ch.len() - 1] == t2 && deq_chain_valid(env, ch, h);
    let chb = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == b1 && ch[ch.len() - 1] == b2 && deq_chain_valid(env, ch, h);
    let mt = Seq::new(cht.len(), |i: int| ExprSpec::Bind(bkind, Box::new(cht[i]), Box::new(b1)));
    let mb = Seq::new(chb.len(), |i: int| ExprSpec::Bind(bkind, Box::new(t2), Box::new(chb[i])));
    assert(deq_chain_valid(env, mt, h + 1)) by {
        assert forall|i: int| #![trigger mt[i]] 0 <= i < mt.len() - 1 implies deq_c(
            env,
            mt[i],
            mt[i + 1],
            h + 1,
        ) by {
            assert(deq_c(env, cht[i], cht[i + 1], h));
            defeq_refl(env, b1);
            assert(deq_c(env, b1, b1, h));
            assert(mt[i] == ExprSpec::Bind(bkind, Box::new(cht[i]), Box::new(b1)));
            assert(mt[i + 1] == ExprSpec::Bind(bkind, Box::new(cht[i + 1]), Box::new(b1)));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_c(env, mt[i], mt[i + 1], h + 1));
        }
    }
    assert(deq_chain_valid(env, mb, h + 1)) by {
        assert forall|i: int| #![trigger mb[i]] 0 <= i < mb.len() - 1 implies deq_c(
            env,
            mb[i],
            mb[i + 1],
            h + 1,
        ) by {
            assert(deq_c(env, chb[i], chb[i + 1], h));
            defeq_refl(env, t2);
            assert(deq_c(env, t2, t2, h));
            assert(mb[i] == ExprSpec::Bind(bkind, Box::new(t2), Box::new(chb[i])));
            assert(mb[i + 1] == ExprSpec::Bind(bkind, Box::new(t2), Box::new(chb[i + 1])));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_c(env, mb[i], mb[i + 1], h + 1));
        }
    }
    assert(mt[0] == ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)));
    assert(mt[mt.len() - 1] == ExprSpec::Bind(bkind, Box::new(t2), Box::new(b1)));
    assert(mb[0] == ExprSpec::Bind(bkind, Box::new(t2), Box::new(b1)));
    assert(mb[mb.len() - 1] == ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2)));
    assert(deq(
        env,
        ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)),
        ExprSpec::Bind(bkind, Box::new(t2), Box::new(b1)),
        h + 1,
    ));
    assert(deq(
        env,
        ExprSpec::Bind(bkind, Box::new(t2), Box::new(b1)),
        ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2)),
        h + 1,
    ));
    deq_trans(
        env,
        ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)),
        ExprSpec::Bind(bkind, Box::new(t2), Box::new(b1)),
        ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2)),
        h + 1,
    );
}

/// Binder INTRODUCTION by a fresh instance (the locally-nameless rule):
/// binder types related by a chain, bodies opened with a free variable
/// `k` absent from both related by a chain -- gives the binders related
/// one height up. No abstraction of chain elements is ever needed: the
/// fresh-instance disjunct of `deq_c`'s `Bind` case takes the opened-body
/// chain as is.
pub proof fn deq_bind_fresh(
    env: EnvSpec,
    t1: ExprSpec,
    t2: ExprSpec,
    b1: ExprSpec,
    b2: ExprSpec,
    k: u32,
    h: nat,
    bkind: BinderKind,
)
    requires
        deq(env, t1, t2, h),
        fv_absent(b1, k),
        fv_absent(b2, k),
        deq(env, inst_free(b1, k), inst_free(b2, k), h),
    ensures
        deq(
            env,
            ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)),
            ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2)),
            h + 1,
        ),
{
    let cht = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == t1 && ch[ch.len() - 1] == t2 && deq_chain_valid(env, ch, h);
    let mt = Seq::new(cht.len(), |i: int| ExprSpec::Bind(bkind, Box::new(cht[i]), Box::new(b1)));
    assert(deq_chain_valid(env, mt, h + 1)) by {
        assert forall|i: int| #![trigger mt[i]] 0 <= i < mt.len() - 1 implies deq_c(
            env,
            mt[i],
            mt[i + 1],
            h + 1,
        ) by {
            assert(deq_c(env, cht[i], cht[i + 1], h));
            defeq_refl(env, b1);
            assert(deq_c(env, b1, b1, h));
            assert(mt[i] == ExprSpec::Bind(bkind, Box::new(cht[i]), Box::new(b1)));
            assert(mt[i + 1] == ExprSpec::Bind(bkind, Box::new(cht[i + 1]), Box::new(b1)));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_c(env, mt[i], mt[i + 1], h + 1));
        }
    }
    assert(mt[0] == ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)));
    assert(mt[mt.len() - 1] == ExprSpec::Bind(bkind, Box::new(t2), Box::new(b1)));
    assert(deq(
        env,
        ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)),
        ExprSpec::Bind(bkind, Box::new(t2), Box::new(b1)),
        h + 1,
    ));
    // The fresh-instance link.
    let bx = ExprSpec::Bind(bkind, Box::new(t2), Box::new(b1));
    let by = ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2));
    defeq_refl(env, t2);
    assert(deq_c(env, t2, t2, h));
    assert(fresh_marker(k));
    assert(fresh_marker(k) && fv_absent(b1, k) && fv_absent(b2, k) && deq(
        env,
        inst_free(b1, k),
        inst_free(b2, k),
        h,
    ));
    assert(((h + 1) - 1) as nat == h);
    assert(deq_c(env, bx, by, h + 1));
    let link = seq![bx, by];
    assert(link.len() == 2 && link[0] == bx && link[1] == by);
    assert(deq_chain_valid(env, link, h + 1)) by {
        assert forall|i: int| #![trigger link[i]] 0 <= i < link.len() - 1 implies deq_c(
            env,
            link[i],
            link[i + 1],
            h + 1,
        ) by {
            assert(i == 0);
        }
    }
    assert(deq(env, bx, by, h + 1));
    deq_trans(env, ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)), bx, by, h + 1);
}

/// `deq_any` form of `deq_bind_fresh` (heights joined by `deq_mono`).
pub proof fn deq_any_bind_fresh(
    env: EnvSpec,
    t1: ExprSpec,
    t2: ExprSpec,
    b1: ExprSpec,
    b2: ExprSpec,
    k: u32,
    bkind: BinderKind,
)
    requires
        deq_any(env, t1, t2),
        fv_absent(b1, k),
        fv_absent(b2, k),
        deq_any(env, inst_free(b1, k), inst_free(b2, k)),
    ensures
        deq_any(
            env,
            ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)),
            ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2)),
        ),
{
    let h1 = choose|h: nat| deq(env, t1, t2, h);
    let h2 = choose|h: nat| deq(env, inst_free(b1, k), inst_free(b2, k), h);
    let hm = if h1 >= h2 {
        h1
    } else {
        h2
    };
    deq_mono(env, t1, t2, h1, hm);
    deq_mono(env, inst_free(b1, k), inst_free(b2, k), h2, hm);
    deq_bind_fresh(env, t1, t2, b1, b2, k, hm, bkind);
    assert(deq(
        env,
        ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)),
        ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2)),
        hm + 1,
    ));
}

/// `deq` congruence at `Proj` (single mapped chain).
pub proof fn deq_proj_congr(
    env: EnvSpec,
    pidx: usize,
    s1: ExprSpec,
    s2: ExprSpec,
    h: nat,
)
    requires
        deq(env, s1, s2, h),
    ensures
        deq(env, ExprSpec::Proj(pidx, Box::new(s1)), ExprSpec::Proj(pidx, Box::new(s2)), h + 1),
{
    let chs = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == s1 && ch[ch.len() - 1] == s2 && deq_chain_valid(env, ch, h);
    let ms = Seq::new(chs.len(), |i: int| ExprSpec::Proj(pidx, Box::new(chs[i])));
    assert(deq_chain_valid(env, ms, h + 1)) by {
        assert forall|i: int| #![trigger ms[i]] 0 <= i < ms.len() - 1 implies deq_c(
            env,
            ms[i],
            ms[i + 1],
            h + 1,
        ) by {
            assert(deq_c(env, chs[i], chs[i + 1], h));
            assert(ms[i] == ExprSpec::Proj(pidx, Box::new(chs[i])));
            assert(ms[i + 1] == ExprSpec::Proj(pidx, Box::new(chs[i + 1])));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_c(env, ms[i], ms[i + 1], h + 1));
        }
    }
    assert(ms[0] == ExprSpec::Proj(pidx, Box::new(s1)));
    assert(ms[ms.len() - 1] == ExprSpec::Proj(pidx, Box::new(s2)));
    assert(deq(env, ExprSpec::Proj(pidx, Box::new(s1)), ExprSpec::Proj(pidx, Box::new(s2)), h + 1));
}

/// ONE PARALLEL STEP of TYPED definitional equality (v1, STRATIFIED):
/// the untyped step `deq_c` wholesale, OR a proof-irrelevance pair, OR
/// congruence over `deq_p_c` itself -- the third disjunct is what makes
/// this a separate relation rather than "deq_c or irrel at the top":
/// irrelevant-proof pairs must compose UNDER every shape (two `App`s
/// whose arguments are irrelevantly-equal proofs), and `deq_c`'s own
/// congruence arms recurse into `deq_c`, not here. STRATIFICATION,
/// disclosed: `proof_irrel_pair`'s proposition-equality conjunct is the
/// UNTYPED `deq_any` -- folding irrelevance into `deq_c` itself would
/// be a definitional cycle (`deq_c -> proof_irrel_pair -> deq_any ->
/// deq -> deq_c`), and the genuine mutual fixpoint of typing and
/// conversion is the deep kernel metatheory this deliberately stops
/// short of: propositions differing only by EMBEDDED proof terms are
/// not identified at the type-comparison layer here.
pub open spec fn deq_p_c(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
) -> bool
    decreases h, 0int, 0nat,
{
    ||| deq_c(env, x, y, h)
    ||| (h > 0 && proof_irrel_pair(dty, env, lctx, io, x, y, (h - 1) as nat) && leaf_wt(dty, env, lctx, io, x, y, (h - 1) as nat))
    ||| (h > 0 && unit_pair(dty, env, lctx, io, x, y, (h - 1) as nat) && leaf_wt(dty, env, lctx, io, x, y, (h - 1) as nat))
    ||| (h > 0 && eta_struct_pair(dty, env, lctx, io, x, y, (h - 1) as nat) && leaf_wt(dty, env, lctx, io, x, y, (h - 1) as nat))
    ||| (h > 0 && match (x, y) {
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => deq_p_c(
            dty,
            env,
            lctx, io,
            *f1,
            *f2,
            (h - 1) as nat,
        ) && deq_p_c(dty, env, lctx, io, *a1, *a2, (h - 1) as nat),
        // Binder congruence, two forms as in `deq_c`: raw bodies, or the
        // bodies opened with one fresh free variable related by a `deq_p`
        // chain one height down (2026-09-06: lets proof irrelevance apply
        // UNDER binders, the kernel's shape). The fresh variable has one of
        // the two binder types (convertible to each other; the kernel opens
        // with the first, `def_eq_binder_aux`, and the rule is symmetric), so
        // a typed leaf under the binder types it correctly.
        (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => bk1 == bk2 && deq_p_c(
            dty,
            env,
            lctx, io,
            *t1,
            *t2,
            (h - 1) as nat,
        ) && (deq_p_c(dty, env, lctx, io, *b1, *b2, (h - 1) as nat) || (exists|k: u32| #[trigger]
            fresh_marker(k) && fv_absent(*b1, k) && fv_absent(*b2, k) && unreach(lctx, k, *t1) && unreach(lctx, k, *t2) && unreach(lctx, k, *b1) && unreach(lctx, k, *b2) && lctx.contains_key(k) && (lctx[k] == *t1 || lctx[k] == *t2) && deq_p(
                dty,
                env,
                lctx, io,
                inst_free(*b1, k),
                inst_free(*b2, k),
                (h - 1) as nat,
            ))),
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => deq_p_c(
            dty,
            env,
            lctx, io,
            *t1,
            *t2,
            (h - 1) as nat,
        ) && deq_p_c(dty, env, lctx, io, *v1, *v2, (h - 1) as nat) && deq_p_c(
            dty,
            env,
            lctx, io,
            *b1,
            *b2,
            (h - 1) as nat,
        ),
        (ExprSpec::Proj(pidx1, s1), ExprSpec::Proj(pidx2, s2)) => pidx1 == pidx2 && deq_p_c(
            dty,
            env,
            lctx, io,
            *s1,
            *s2,
            (h - 1) as nat,
        ),
        _ => false,
    })
}

/// A chain of `deq_p_c` steps -- `deq_chain_valid`'s typed analogue.
pub open spec fn deq_p_chain_valid(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    ch: Seq<ExprSpec>,
    h: nat,
) -> bool
    decreases h, 1int, 0nat,
{
    forall|i: int|
        #![trigger ch[i]]
        0 <= i < ch.len() - 1 ==> deq_p_c(dty, env, lctx, io, ch[i], ch[i + 1], h)
}

/// TYPED definitional equality (v1): chain-witnessed transitive closure
/// of `deq_p_c` -- `deq` plus proof irrelevance, closed under
/// congruence and transitivity. Same chain architecture as `deq` for
/// the same encoding reasons.
pub open spec fn deq_p(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
) -> bool
    decreases h, 2int, 0nat,
{
    exists|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_p_chain_valid(
            dty,
            env,
            lctx, io,
            ch,
            h,
        )
}

/// Height-erased form, like `deq_any`.
pub open spec fn deq_p_any(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
) -> bool {
    exists|h: nat| #[trigger] deq_p(dty, env, lctx, io, x, y, h)
}

/// `deq_p_c` subsumes `deq_c` (first disjunct, definitional).
pub proof fn deq_p_c_of_deq_c(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
)
    requires
        deq_c(env, x, y, h),
    ensures
        deq_p_c(dty, env, lctx, io, x, y, h),
{
}

/// `deq_p_c` is monotone in its height index.
pub proof fn deq_p_c_mono(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h1: nat,
    h2: nat,
)
    requires
        deq_p_c(dty, env, lctx, io, x, y, h1),
        h1 <= h2,
    ensures
        deq_p_c(dty, env, lctx, io, x, y, h2),
    decreases h1, 0int,
{
    if deq_c(env, x, y, h1) {
        deq_c_mono(env, x, y, h1, h2);
    } else if h1 > 0 && proof_irrel_pair(dty, env, lctx, io, x, y, (h1 - 1) as nat) && leaf_wt(dty, env, lctx, io, x, y, (h1 - 1) as nat) {
        leaf_wt_mono(dty, env, lctx, io, x, y, (h1 - 1) as nat, (h2 - 1) as nat);
        proof_irrel_pair_mono(dty, env, lctx, io, x, y, (h1 - 1) as nat, (h2 - 1) as nat);
    } else if h1 > 0 && unit_pair(dty, env, lctx, io, x, y, (h1 - 1) as nat) && leaf_wt(dty, env, lctx, io, x, y, (h1 - 1) as nat) {
        leaf_wt_mono(dty, env, lctx, io, x, y, (h1 - 1) as nat, (h2 - 1) as nat);
        unit_pair_mono(dty, env, lctx, io, x, y, (h1 - 1) as nat, (h2 - 1) as nat);
    } else if h1 > 0 && eta_struct_pair(dty, env, lctx, io, x, y, (h1 - 1) as nat) && leaf_wt(dty, env, lctx, io, x, y, (h1 - 1) as nat) {
        leaf_wt_mono(dty, env, lctx, io, x, y, (h1 - 1) as nat, (h2 - 1) as nat);
        eta_struct_pair_mono(dty, env, lctx, io, x, y, (h1 - 1) as nat, (h2 - 1) as nat);
    } else {
        assert(h1 > 0);
        match (x, y) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                assert(deq_p_c(dty, env, lctx, io, *f1, *f2, (h1 - 1) as nat) && deq_p_c(
                    dty,
                    env,
                    lctx, io,
                    *a1,
                    *a2,
                    (h1 - 1) as nat,
                ));
                deq_p_c_mono(dty, env, lctx, io, *f1, *f2, (h1 - 1) as nat, (h2 - 1) as nat);
                deq_p_c_mono(dty, env, lctx, io, *a1, *a2, (h1 - 1) as nat, (h2 - 1) as nat);
                assert(h2 > 0 && deq_p_c(dty, env, lctx, io, *f1, *f2, (h2 - 1) as nat) && deq_p_c(
                    dty,
                    env,
                    lctx, io,
                    *a1,
                    *a2,
                    (h2 - 1) as nat,
                ));
                assert(deq_p_c(dty, env, lctx, io, x, y, h2));
            },
            (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => {
                assert(deq_p_c(dty, env, lctx, io, *t1, *t2, (h1 - 1) as nat));
                deq_p_c_mono(dty, env, lctx, io, *t1, *t2, (h1 - 1) as nat, (h2 - 1) as nat);
                if deq_p_c(dty, env, lctx, io, *b1, *b2, (h1 - 1) as nat) {
                    deq_p_c_mono(dty, env, lctx, io, *b1, *b2, (h1 - 1) as nat, (h2 - 1) as nat);
                    assert(h2 > 0 && deq_p_c(dty, env, lctx, io, *t1, *t2, (h2 - 1) as nat) && deq_p_c(
                        dty,
                        env,
                        lctx, io,
                        *b1,
                        *b2,
                        (h2 - 1) as nat,
                    ));
                } else {
                    let k = choose|k: u32| #[trigger]
                        fresh_marker(k) && fv_absent(*b1, k) && fv_absent(*b2, k) && unreach(lctx, k, *t1) && unreach(lctx, k, *t2) && unreach(lctx, k, *b1) && unreach(lctx, k, *b2) && lctx.contains_key(k) && (lctx[k] == *t1 || lctx[k] == *t2) && deq_p(
                            dty,
                            env,
                            lctx, io,
                            inst_free(*b1, k),
                            inst_free(*b2, k),
                            (h1 - 1) as nat,
                        );
                    deq_p_mono(
                        dty,
                        env,
                        lctx, io,
                        inst_free(*b1, k),
                        inst_free(*b2, k),
                        (h1 - 1) as nat,
                        (h2 - 1) as nat,
                    );
                    assert(fresh_marker(k));
                    assert(fresh_marker(k) && fv_absent(*b1, k) && fv_absent(*b2, k) && unreach(lctx, k, *t1) && unreach(lctx, k, *t2) && unreach(lctx, k, *b1) && unreach(lctx, k, *b2) && lctx.contains_key(k) && (lctx[k] == *t1 || lctx[k] == *t2) && deq_p(
                        dty,
                        env,
                        lctx, io,
                        inst_free(*b1, k),
                        inst_free(*b2, k),
                        (h2 - 1) as nat,
                    ));
                }
                assert(deq_p_c(dty, env, lctx, io, x, y, h2));
            },
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                assert(deq_p_c(dty, env, lctx, io, *t1, *t2, (h1 - 1) as nat) && deq_p_c(
                    dty,
                    env,
                    lctx, io,
                    *v1,
                    *v2,
                    (h1 - 1) as nat,
                ) && deq_p_c(dty, env, lctx, io, *b1, *b2, (h1 - 1) as nat));
                deq_p_c_mono(dty, env, lctx, io, *t1, *t2, (h1 - 1) as nat, (h2 - 1) as nat);
                deq_p_c_mono(dty, env, lctx, io, *v1, *v2, (h1 - 1) as nat, (h2 - 1) as nat);
                deq_p_c_mono(dty, env, lctx, io, *b1, *b2, (h1 - 1) as nat, (h2 - 1) as nat);
                assert(h2 > 0 && deq_p_c(dty, env, lctx, io, *t1, *t2, (h2 - 1) as nat) && deq_p_c(
                    dty,
                    env,
                    lctx, io,
                    *v1,
                    *v2,
                    (h2 - 1) as nat,
                ) && deq_p_c(dty, env, lctx, io, *b1, *b2, (h2 - 1) as nat));
                assert(deq_p_c(dty, env, lctx, io, x, y, h2));
            },
            (ExprSpec::Proj(pidx1, s1), ExprSpec::Proj(pidx2, s2)) => {
                assert(deq_p_c(dty, env, lctx, io, *s1, *s2, (h1 - 1) as nat));
                deq_p_c_mono(dty, env, lctx, io, *s1, *s2, (h1 - 1) as nat, (h2 - 1) as nat);
                assert(h2 > 0 && deq_p_c(dty, env, lctx, io, *s1, *s2, (h2 - 1) as nat));
                assert(deq_p_c(dty, env, lctx, io, x, y, h2));
            },
            _ => {
                assert(false);
            },
        }
    }
}

/// `deq_p_c` is symmetric, height-preserving: `deq_c` by its lemma,
/// the irrelevance pair by swapping its witnesses (+ `deq_any_symm` for
/// the proposition-equality conjunct), congruence by the IH.
pub proof fn deq_p_c_symm(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
)
    requires
        deq_p_c(dty, env, lctx, io, x, y, h),
    ensures
        deq_p_c(dty, env, lctx, io, y, x, h),
    decreases h, 0int,
{
    if deq_c(env, x, y, h) {
        deq_c_symm(env, x, y, h);
    } else if h > 0 && proof_irrel_pair(dty, env, lctx, io, x, y, (h - 1) as nat) && leaf_wt(dty, env, lctx, io, x, y, (h - 1) as nat) {
        leaf_wt_symm(dty, env, lctx, io, x, y, (h - 1) as nat);
        let hp = (h - 1) as nat;
        let (tx, ty2, fx, fy) = choose|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
            irrel_marker(tx, ty2, fx, fy) && fx < hp && fy < hp && types_to(dty, env, lctx, io, x, tx, fx) && types_to(
                dty,
                env,
                lctx, io,
                y,
                ty2,
                fy,
            ) && is_proof_type_m(dty, env, lctx, io, tx, hp) && is_proof_type_m(dty, env, lctx, io, ty2, hp)
                && deq_p(dty, env, lctx, io, tx, ty2, hp);
        deq_p_symm(dty, env, lctx, io, tx, ty2, hp);
        assert(irrel_marker(ty2, tx, fy, fx));
        assert(proof_irrel_pair(dty, env, lctx, io, y, x, hp));
    } else if h > 0 && unit_pair(dty, env, lctx, io, x, y, (h - 1) as nat) && leaf_wt(dty, env, lctx, io, x, y, (h - 1) as nat) {
        leaf_wt_symm(dty, env, lctx, io, x, y, (h - 1) as nat);
        let hp = (h - 1) as nat;
        let (tx, ty2, fx, fy) = choose|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
            unit_marker(tx, ty2, fx, fy) && fx < hp && fy < hp && types_to(dty, env, lctx, io, x, tx, fx)
                && types_to(dty, env, lctx, io, y, ty2, fy) && (unit_like_type_m(dty, env, lctx, io, tx, hp)
                || unit_like_type_m(dty, env, lctx, io, ty2, hp)) && deq_p(dty, env, lctx, io, tx, ty2, hp);
        deq_p_symm(dty, env, lctx, io, tx, ty2, hp);
        assert(unit_marker(ty2, tx, fy, fx));
        assert(unit_pair(dty, env, lctx, io, y, x, hp));
    } else if h > 0 && eta_struct_pair(dty, env, lctx, io, x, y, (h - 1) as nat) && leaf_wt(dty, env, lctx, io, x, y, (h - 1) as nat) {
        leaf_wt_symm(dty, env, lctx, io, x, y, (h - 1) as nat);
        assert(eta_struct_pair(dty, env, lctx, io, y, x, (h - 1) as nat));
    } else {
        assert(h > 0);
        match (x, y) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                assert(deq_p_c(dty, env, lctx, io, *f1, *f2, (h - 1) as nat) && deq_p_c(
                    dty,
                    env,
                    lctx, io,
                    *a1,
                    *a2,
                    (h - 1) as nat,
                ));
                deq_p_c_symm(dty, env, lctx, io, *f1, *f2, (h - 1) as nat);
                deq_p_c_symm(dty, env, lctx, io, *a1, *a2, (h - 1) as nat);
                assert(h > 0 && deq_p_c(dty, env, lctx, io, *f2, *f1, (h - 1) as nat) && deq_p_c(
                    dty,
                    env,
                    lctx, io,
                    *a2,
                    *a1,
                    (h - 1) as nat,
                ));
                assert(deq_p_c(dty, env, lctx, io, y, x, h));
            },
            (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => {
                assert(deq_p_c(dty, env, lctx, io, *t1, *t2, (h - 1) as nat));
                deq_p_c_symm(dty, env, lctx, io, *t1, *t2, (h - 1) as nat);
                if deq_p_c(dty, env, lctx, io, *b1, *b2, (h - 1) as nat) {
                    deq_p_c_symm(dty, env, lctx, io, *b1, *b2, (h - 1) as nat);
                    assert(h > 0 && deq_p_c(dty, env, lctx, io, *t2, *t1, (h - 1) as nat) && deq_p_c(
                        dty,
                        env,
                        lctx, io,
                        *b2,
                        *b1,
                        (h - 1) as nat,
                    ));
                } else {
                    let k = choose|k: u32| #[trigger]
                        fresh_marker(k) && fv_absent(*b1, k) && fv_absent(*b2, k) && unreach(lctx, k, *t1) && unreach(lctx, k, *t2) && unreach(lctx, k, *b1) && unreach(lctx, k, *b2) && lctx.contains_key(k) && (lctx[k] == *t1 || lctx[k] == *t2) && deq_p(
                            dty,
                            env,
                            lctx, io,
                            inst_free(*b1, k),
                            inst_free(*b2, k),
                            (h - 1) as nat,
                        );
                    deq_p_symm(
                        dty,
                        env,
                        lctx, io,
                        inst_free(*b1, k),
                        inst_free(*b2, k),
                        (h - 1) as nat,
                    );
                    assert(fresh_marker(k));
                    assert(fresh_marker(k) && fv_absent(*b2, k) && fv_absent(*b1, k) && unreach(lctx, k, *t2) && unreach(lctx, k, *t1) && unreach(lctx, k, *b2) && unreach(lctx, k, *b1) && lctx.contains_key(k) && (lctx[k] == *t2 || lctx[k] == *t1) && deq_p(
                        dty,
                        env,
                        lctx, io,
                        inst_free(*b2, k),
                        inst_free(*b1, k),
                        (h - 1) as nat,
                    ));
                }
                assert(deq_p_c(dty, env, lctx, io, y, x, h));
            },
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                assert(deq_p_c(dty, env, lctx, io, *t1, *t2, (h - 1) as nat) && deq_p_c(
                    dty,
                    env,
                    lctx, io,
                    *v1,
                    *v2,
                    (h - 1) as nat,
                ) && deq_p_c(dty, env, lctx, io, *b1, *b2, (h - 1) as nat));
                deq_p_c_symm(dty, env, lctx, io, *t1, *t2, (h - 1) as nat);
                deq_p_c_symm(dty, env, lctx, io, *v1, *v2, (h - 1) as nat);
                deq_p_c_symm(dty, env, lctx, io, *b1, *b2, (h - 1) as nat);
                assert(h > 0 && deq_p_c(dty, env, lctx, io, *t2, *t1, (h - 1) as nat) && deq_p_c(
                    dty,
                    env,
                    lctx, io,
                    *v2,
                    *v1,
                    (h - 1) as nat,
                ) && deq_p_c(dty, env, lctx, io, *b2, *b1, (h - 1) as nat));
                assert(deq_p_c(dty, env, lctx, io, y, x, h));
            },
            (ExprSpec::Proj(pidx1, s1), ExprSpec::Proj(pidx2, s2)) => {
                assert(deq_p_c(dty, env, lctx, io, *s1, *s2, (h - 1) as nat));
                deq_p_c_symm(dty, env, lctx, io, *s1, *s2, (h - 1) as nat);
                assert(h > 0 && deq_p_c(dty, env, lctx, io, *s2, *s1, (h - 1) as nat));
                assert(deq_p_c(dty, env, lctx, io, y, x, h));
            },
            _ => {
                assert(false);
            },
        }
    }
}

/// A single typed step is a `deq_p` fact: the length-2 chain.
pub proof fn deq_p_of_deq_p_c(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
)
    requires
        deq_p_c(dty, env, lctx, io, x, y, h),
    ensures
        deq_p(dty, env, lctx, io, x, y, h),
{
    let ch = seq![x, y];
    assert(ch.len() == 2);
    assert(ch[0] == x);
    assert(ch[ch.len() - 1] == y);
    assert(deq_p_chain_valid(dty, env, lctx, io, ch, h)) by {
        assert forall|i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies deq_p_c(
            dty,
            env,
            lctx, io,
            ch[i],
            ch[i + 1],
            h,
        ) by {
            assert(i == 0);
        }
    }
}

/// Reduction is typed conversion, at any height: the reduct is a `defeq`
/// partner, which `deq_c` admits outright.
pub proof fn deq_p_of_pstep_star(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
)
    requires
        pstep_star(env, x, y),
    ensures
        deq_p(dty, env, lctx, io, x, y, h),
{
    crate::beta_model::defeq_of_pstep_star(env, x, y);
    assert(deq_c(env, x, y, h));
    deq_p_c_of_deq_c(dty, env, lctx, io, x, y, h);
    deq_p_of_deq_p_c(dty, env, lctx, io, x, y, h);
}

/// `deq_p` subsumes the untyped `deq`: per-link `deq_p_c_of_deq_c` over
/// the witness chain.
pub proof fn deq_p_of_deq(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
)
    requires
        deq(env, x, y, h),
    ensures
        deq_p(dty, env, lctx, io, x, y, h),
{
    let ch = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_chain_valid(env, ch, h);
    assert(deq_p_chain_valid(dty, env, lctx, io, ch, h)) by {
        assert forall|i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies deq_p_c(
            dty,
            env,
            lctx, io,
            ch[i],
            ch[i + 1],
            h,
        ) by {
            assert(deq_c(env, ch[i], ch[i + 1], h));
        }
    }
}

/// The irrelevance leaf is monotone in its own height: its only height-
/// dependent conjunct is the typed conversion between the two propositions,
/// and that is `deq_p_mono`.
pub proof fn proof_irrel_pair_mono(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h1: nat,
    h2: nat,
)
    requires
        proof_irrel_pair(dty, env, lctx, io, x, y, h1),
        h1 <= h2,
    ensures
        proof_irrel_pair(dty, env, lctx, io, x, y, h2),
    decreases h1, 3int,
{
    let (tx, ty2, fx, fy) = choose|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
        irrel_marker(tx, ty2, fx, fy) && fx < h1 && fy < h1 && types_to(dty, env, lctx, io, x, tx, fx) && types_to(
            dty,
            env,
            lctx, io,
            y,
            ty2,
            fy,
        ) && is_proof_type_m(dty, env, lctx, io, tx, h1) && is_proof_type_m(dty, env, lctx, io, ty2, h1) && deq_p(
            dty,
            env,
            lctx, io,
            tx,
            ty2,
            h1,
        );
    deq_p_mono(dty, env, lctx, io, tx, ty2, h1, h2);
    is_proof_type_m_mono(dty, env, lctx, io, tx, h1, h2);
    is_proof_type_m_mono(dty, env, lctx, io, ty2, h1, h2);
    assert(irrel_marker(tx, ty2, fx, fy));
}

/// The typed-rule helpers are monotone in their height, like `deq_p`: each
/// asks for a derivation below it and a conversion at it.
pub proof fn is_proof_type_m_mono(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    ty: ExprSpec,
    h1: nat,
    h2: nat,
)
    requires
        is_proof_type_m(dty, env, lctx, io, ty, h1),
        h1 <= h2,
    ensures
        is_proof_type_m(dty, env, lctx, io, ty, h2),
    decreases h1, 2int,
{
    let (a, tt, f, l) = choose|a: ExprSpec, tt: ExprSpec, f: nat, l: LevelSpec| #[trigger]
        proof_type_marker(a, tt, f, l) && deq_p(dty, env, lctx, io, ty, a, h1) && f < h1 && types_to(dty, env, lctx, io, a, tt, f) && wt1(dty, env, lctx, io, a, h1) && deq_p(
            dty,
            env,
            lctx,
            io,
            tt,
            ExprSpec::Sort(l),
            h1,
        ) && (forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) <= 0);
    deq_p_mono(dty, env, lctx, io, tt, ExprSpec::Sort(l), h1, h2);
    deq_p_mono(dty, env, lctx, io, ty, a, h1, h2);
    wt1_mono(dty, env, lctx, io, a, h1, h2);
    assert(proof_type_marker(a, tt, f, l));
}

pub proof fn unit_like_type_m_mono(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    h1: nat,
    h2: nat,
)
    requires
        unit_like_type_m(dty, env, lctx, io, tx, h1),
        h1 <= h2,
    ensures
        unit_like_type_m(dty, env, lctx, io, tx, h2),
    decreases h1, 2int,
{
    let r = choose|r: ExprSpec| #[trigger] unit_like_marker(r) && deq_p(dty, env, lctx, io, tx, r, h1) && unit_like_type(env, r);
    deq_p_mono(dty, env, lctx, io, tx, r, h1, h2);
    assert(unit_like_marker(r));
}

pub proof fn struct_type_of_mono(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    ind: u64,
    params: Seq<ExprSpec>,
    h1: nat,
    h2: nat,
)
    requires
        struct_type_of(dty, env, lctx, io, tx, ind, params, h1),
        h1 <= h2,
    ensures
        struct_type_of(dty, env, lctx, io, tx, ind, params, h2),
    decreases h1, 2int,
{
    let (ils, rest) = choose|ils: Seq<LevelSpec>, rest: Seq<ExprSpec>| #[trigger]
        struct_type_marker(ils, rest) && deq_p(dty, env, lctx, io, tx, spine_app(ExprSpec::Const(ind, ils), params + rest), h1);
    deq_p_mono(dty, env, lctx, io, tx, spine_app(ExprSpec::Const(ind, ils), params + rest), h1, h2);
    assert(struct_type_marker(ils, rest));
}

pub proof fn unit_pair_mono(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h1: nat,
    h2: nat,
)
    requires
        unit_pair(dty, env, lctx, io, x, y, h1),
        h1 <= h2,
    ensures
        unit_pair(dty, env, lctx, io, x, y, h2),
    decreases h1, 3int,
{
    let (tx, ty2, fx, fy) = choose|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
        unit_marker(tx, ty2, fx, fy) && fx < h1 && fy < h1 && types_to(dty, env, lctx, io, x, tx, fx)
            && types_to(dty, env, lctx, io, y, ty2, fy) && (unit_like_type_m(dty, env, lctx, io, tx, h1)
            || unit_like_type_m(dty, env, lctx, io, ty2, h1)) && deq_p(dty, env, lctx, io, tx, ty2, h1);
    deq_p_mono(dty, env, lctx, io, tx, ty2, h1, h2);
    if unit_like_type_m(dty, env, lctx, io, tx, h1) {
        unit_like_type_m_mono(dty, env, lctx, io, tx, h1, h2);
    } else {
        unit_like_type_m_mono(dty, env, lctx, io, ty2, h1, h2);
    }
    assert(unit_marker(tx, ty2, fx, fy));
}

pub proof fn eta_struct_expand_mono(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h1: nat,
    h2: nat,
)
    requires
        eta_struct_expand(dty, env, lctx, io, x, y, h1),
        h1 <= h2,
    ensures
        eta_struct_expand(dty, env, lctx, io, x, y, h2),
    decreases h1, 3int,
{
    reveal_with_fuel(ctor_typed_like, 1);
    let (tx, f, ind, cid, ls, params, nf) = choose|
        tx: ExprSpec,
        f: nat,
        ind: u64,
        cid: u64,
        ls: Seq<LevelSpec>,
        params: Seq<ExprSpec>,
        nf: nat,
    | #[trigger]
        eta_struct_marker(tx, f, ind, cid, ls, params, nf) && f < h1 && types_to(dty, env, lctx, io, x, tx, f)
            && (struct_type_of(dty, env, lctx, io, tx, ind, params, h1) || ctor_typed_like(
            dty,
            env,
            lctx,
            io,
            tx,
            cid,
            params,
            nf,
            h1,
        )) && env.struct_ctor(ind) == Some(cid)
            && env.ctor_num_fields(cid) == Some(nf as u16) && y == spine_app(
            ExprSpec::Const(cid, ls),
            params + Seq::new(nf, |i: int| ExprSpec::Proj(i as usize, Box::new(x))),
        );
    if struct_type_of(dty, env, lctx, io, tx, ind, params, h1) {
        struct_type_of_mono(dty, env, lctx, io, tx, ind, params, h1, h2);
    } else {
        ctor_typed_like_mono(dty, env, lctx, io, tx, cid, params, nf, h1, h2);
    }
    assert(eta_struct_marker(tx, f, ind, cid, ls, params, nf));
}

pub proof fn eta_struct_pair_mono(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h1: nat,
    h2: nat,
)
    requires
        eta_struct_pair(dty, env, lctx, io, x, y, h1),
        h1 <= h2,
    ensures
        eta_struct_pair(dty, env, lctx, io, x, y, h2),
    decreases h1, 4int,
{
    if eta_struct_expand(dty, env, lctx, io, x, y, h1) {
        eta_struct_expand_mono(dty, env, lctx, io, x, y, h1, h2);
    } else {
        eta_struct_expand_mono(dty, env, lctx, io, y, x, h1, h2);
    }
}

/// An irrelevance pair at height `hi` is `deq_p` at any height above it.
pub proof fn deq_p_of_irrel(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    hi: nat,
    h: nat,
)
    requires
        proof_irrel_pair(dty, env, lctx, io, x, y, hi),
        h > hi,
        leaf_wt(dty, env, lctx, io, x, y, hi),
    ensures
        deq_p(dty, env, lctx, io, x, y, h),
{
    proof_irrel_pair_mono(dty, env, lctx, io, x, y, hi, (h - 1) as nat);
    leaf_wt_mono(dty, env, lctx, io, x, y, hi, (h - 1) as nat);
    assert(deq_p_c(dty, env, lctx, io, x, y, h));
    deq_p_of_deq_p_c(dty, env, lctx, io, x, y, h);
}

/// The unit rule lifts into `deq_p` at any height, exactly as proof
/// irrelevance does: it is a leaf of `deq_p_c`, and a leaf is a length-2
/// chain.
pub proof fn deq_p_of_unit(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    hi: nat,
    h: nat,
)
    requires
        unit_pair(dty, env, lctx, io, x, y, hi),
        h > hi,
        leaf_wt(dty, env, lctx, io, x, y, hi),
    ensures
        deq_p(dty, env, lctx, io, x, y, h),
{
    unit_pair_mono(dty, env, lctx, io, x, y, hi, (h - 1) as nat);
    leaf_wt_mono(dty, env, lctx, io, x, y, hi, (h - 1) as nat);
    assert(deq_p_c(dty, env, lctx, io, x, y, h));
    deq_p_of_deq_p_c(dty, env, lctx, io, x, y, h);
}

pub proof fn deq_p_any_of_unit(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    hi: nat,
)
    requires
        unit_pair(dty, env, lctx, io, x, y, hi),
        leaf_wt(dty, env, lctx, io, x, y, hi),
    ensures
        deq_p_any(dty, env, lctx, io, x, y),
{
    deq_p_of_unit(dty, env, lctx, io, x, y, hi, hi + 1);
    assert(deq_p(dty, env, lctx, io, x, y, hi + 1));
}

/// Structure eta lifts into `deq_p` at any height, as the other typed
/// leaves do.
pub proof fn deq_p_of_eta_struct(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    hi: nat,
    h: nat,
)
    requires
        eta_struct_pair(dty, env, lctx, io, x, y, hi),
        h > hi,
        leaf_wt(dty, env, lctx, io, x, y, hi),
    ensures
        deq_p(dty, env, lctx, io, x, y, h),
{
    eta_struct_pair_mono(dty, env, lctx, io, x, y, hi, (h - 1) as nat);
    leaf_wt_mono(dty, env, lctx, io, x, y, hi, (h - 1) as nat);
    assert(deq_p_c(dty, env, lctx, io, x, y, h));
    deq_p_of_deq_p_c(dty, env, lctx, io, x, y, h);
}

pub proof fn deq_p_any_of_eta_struct(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    hi: nat,
)
    requires
        eta_struct_pair(dty, env, lctx, io, x, y, hi),
        leaf_wt(dty, env, lctx, io, x, y, hi),
    ensures
        deq_p_any(dty, env, lctx, io, x, y),
{
    deq_p_of_eta_struct(dty, env, lctx, io, x, y, hi, hi + 1);
    assert(deq_p(dty, env, lctx, io, x, y, hi + 1));
}

/// `deq_p` is reflexive at every height: the length-1 chain.
pub proof fn deq_p_refl(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    h: nat,
)
    ensures
        deq_p(dty, env, lctx, io, x, x, h),
{
    let ch = seq![x];
    assert(ch.len() == 1);
    assert(ch[0] == x);
    assert(ch[ch.len() - 1] == x);
    assert(deq_p_chain_valid(dty, env, lctx, io, ch, h));
}

/// `deq_p` is monotone in its height index.
pub proof fn deq_p_mono(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h1: nat,
    h2: nat,
)
    requires
        deq_p(dty, env, lctx, io, x, y, h1),
        h1 <= h2,
    ensures
        deq_p(dty, env, lctx, io, x, y, h2),
    decreases h1, 1int,
{
    let ch = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_p_chain_valid(
            dty,
            env,
            lctx, io,
            ch,
            h1,
        );
    assert(deq_p_chain_valid(dty, env, lctx, io, ch, h2)) by {
        assert forall|i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies deq_p_c(
            dty,
            env,
            lctx, io,
            ch[i],
            ch[i + 1],
            h2,
        ) by {
            assert(deq_p_c(dty, env, lctx, io, ch[i], ch[i + 1], h1));
            deq_p_c_mono(dty, env, lctx, io, ch[i], ch[i + 1], h1, h2);
        }
    }
}

/// `deq_p` is symmetric, height-preserving: chain reversal.
pub proof fn deq_p_symm(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
)
    requires
        deq_p(dty, env, lctx, io, x, y, h),
    ensures
        deq_p(dty, env, lctx, io, y, x, h),
    decreases h, 1int,
{
    let ch = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_p_chain_valid(
            dty,
            env,
            lctx, io,
            ch,
            h,
        );
    let n = ch.len();
    let rev = Seq::new(n, |i: int| ch[n - 1 - i]);
    assert(rev.len() == n);
    assert(rev[0] == ch[n - 1]);
    assert(rev[rev.len() - 1] == ch[0]);
    assert(deq_p_chain_valid(dty, env, lctx, io, rev, h)) by {
        assert forall|i: int| #![trigger rev[i]] 0 <= i < rev.len() - 1 implies deq_p_c(
            dty,
            env,
            lctx, io,
            rev[i],
            rev[i + 1],
            h,
        ) by {
            assert(rev[i] == ch[n - 1 - i]);
            assert(rev[i + 1] == ch[n - 2 - i]);
            assert(deq_p_c(dty, env, lctx, io, ch[n - 2 - i], ch[n - 1 - i], h));
            deq_p_c_symm(dty, env, lctx, io, ch[n - 2 - i], ch[n - 1 - i], h);
        }
    }
}

/// `deq_p` is transitive -- for FREE, by chain concatenation.
pub proof fn deq_p_trans(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    z: ExprSpec,
    h: nat,
)
    requires
        deq_p(dty, env, lctx, io, x, y, h),
        deq_p(dty, env, lctx, io, y, z, h),
    ensures
        deq_p(dty, env, lctx, io, x, z, h),
{
    let ch1 = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_p_chain_valid(
            dty,
            env,
            lctx, io,
            ch,
            h,
        );
    let ch2 = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == y && ch[ch.len() - 1] == z && deq_p_chain_valid(
            dty,
            env,
            lctx, io,
            ch,
            h,
        );
    let n1 = ch1.len();
    let ch2_tail = ch2.subrange(1, ch2.len() as int);
    let ch = ch1 + ch2_tail;
    assert(ch.len() == n1 + ch2.len() - 1);
    assert(ch[0] == ch1[0]);
    if ch2.len() == 1 {
        assert(ch2_tail =~= Seq::<ExprSpec>::empty());
        assert(ch =~= ch1);
        assert(ch[ch.len() - 1] == y);
        assert(y == z);
    } else {
        assert(ch[ch.len() - 1] == ch2_tail[ch2_tail.len() - 1]);
        assert(ch2_tail[ch2_tail.len() - 1] == ch2[ch2.len() - 1]);
    }
    assert(deq_p_chain_valid(dty, env, lctx, io, ch, h)) by {
        assert forall|i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies deq_p_c(
            dty,
            env,
            lctx, io,
            ch[i],
            ch[i + 1],
            h,
        ) by {
            if i < n1 - 1 {
                assert(ch[i] == ch1[i]);
                assert(ch[i + 1] == ch1[i + 1]);
                assert(deq_p_c(dty, env, lctx, io, ch1[i], ch1[i + 1], h));
            } else if i == n1 - 1 {
                assert(ch[i] == ch1[n1 - 1]);
                assert(ch1[n1 - 1] == y);
                assert(ch[i + 1] == ch2_tail[0]);
                assert(ch2_tail[0] == ch2[1]);
                assert(deq_p_c(dty, env, lctx, io, ch2[0], ch2[1], h));
                assert(ch2[0] == y);
            } else {
                assert(ch[i] == ch2_tail[i - n1]);
                assert(ch[i + 1] == ch2_tail[i + 1 - n1]);
                assert(ch2_tail[i - n1] == ch2[i - n1 + 1]);
                assert(ch2_tail[i + 1 - n1] == ch2[i + 2 - n1]);
                assert(deq_p_c(dty, env, lctx, io, ch2[i - n1 + 1], ch2[i - n1 + 2], h));
            }
        }
    }
}

/// `deq_p` congruence at `App`, both positions varying -- same
/// two-segment chain mapping as `deq_app_congr`, with the fixed side
/// riding along via `defeq` reflexivity (a `deq_c`, hence `deq_p_c`,
/// fact).
pub proof fn deq_p_app_congr(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    f1: ExprSpec,
    f2: ExprSpec,
    a1: ExprSpec,
    a2: ExprSpec,
    h: nat,
)
    requires
        deq_p(dty, env, lctx, io, f1, f2, h),
        deq_p(dty, env, lctx, io, a1, a2, h),
    ensures
        deq_p(
            dty,
            env,
            lctx, io,
            ExprSpec::App(Box::new(f1), Box::new(a1)),
            ExprSpec::App(Box::new(f2), Box::new(a2)),
            h + 1,
        ),
{
    let chf = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == f1 && ch[ch.len() - 1] == f2 && deq_p_chain_valid(
            dty,
            env,
            lctx, io,
            ch,
            h,
        );
    let cha = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == a1 && ch[ch.len() - 1] == a2 && deq_p_chain_valid(
            dty,
            env,
            lctx, io,
            ch,
            h,
        );
    let mf = Seq::new(chf.len(), |i: int| ExprSpec::App(Box::new(chf[i]), Box::new(a1)));
    let ma = Seq::new(cha.len(), |i: int| ExprSpec::App(Box::new(f2), Box::new(cha[i])));
    assert(deq_p_chain_valid(dty, env, lctx, io, mf, h + 1)) by {
        assert forall|i: int| #![trigger mf[i]] 0 <= i < mf.len() - 1 implies deq_p_c(
            dty,
            env,
            lctx, io,
            mf[i],
            mf[i + 1],
            h + 1,
        ) by {
            assert(deq_p_c(dty, env, lctx, io, chf[i], chf[i + 1], h));
            defeq_refl(env, a1);
            assert(deq_c(env, a1, a1, h));
            assert(deq_p_c(dty, env, lctx, io, a1, a1, h));
            assert(mf[i] == ExprSpec::App(Box::new(chf[i]), Box::new(a1)));
            assert(mf[i + 1] == ExprSpec::App(Box::new(chf[i + 1]), Box::new(a1)));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_p_c(dty, env, lctx, io, mf[i], mf[i + 1], h + 1));
        }
    }
    assert(deq_p_chain_valid(dty, env, lctx, io, ma, h + 1)) by {
        assert forall|i: int| #![trigger ma[i]] 0 <= i < ma.len() - 1 implies deq_p_c(
            dty,
            env,
            lctx, io,
            ma[i],
            ma[i + 1],
            h + 1,
        ) by {
            assert(deq_p_c(dty, env, lctx, io, cha[i], cha[i + 1], h));
            defeq_refl(env, f2);
            assert(deq_c(env, f2, f2, h));
            assert(deq_p_c(dty, env, lctx, io, f2, f2, h));
            assert(ma[i] == ExprSpec::App(Box::new(f2), Box::new(cha[i])));
            assert(ma[i + 1] == ExprSpec::App(Box::new(f2), Box::new(cha[i + 1])));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_p_c(dty, env, lctx, io, ma[i], ma[i + 1], h + 1));
        }
    }
    assert(mf[0] == ExprSpec::App(Box::new(f1), Box::new(a1)));
    assert(mf[mf.len() - 1] == ExprSpec::App(Box::new(f2), Box::new(a1)));
    assert(ma[0] == ExprSpec::App(Box::new(f2), Box::new(a1)));
    assert(ma[ma.len() - 1] == ExprSpec::App(Box::new(f2), Box::new(a2)));
    assert(deq_p(
        dty,
        env,
        lctx, io,
        ExprSpec::App(Box::new(f1), Box::new(a1)),
        ExprSpec::App(Box::new(f2), Box::new(a1)),
        h + 1,
    ));
    assert(deq_p(
        dty,
        env,
        lctx, io,
        ExprSpec::App(Box::new(f2), Box::new(a1)),
        ExprSpec::App(Box::new(f2), Box::new(a2)),
        h + 1,
    ));
    deq_p_trans(
        dty,
        env,
        lctx, io,
        ExprSpec::App(Box::new(f1), Box::new(a1)),
        ExprSpec::App(Box::new(f2), Box::new(a1)),
        ExprSpec::App(Box::new(f2), Box::new(a2)),
        h + 1,
    );
}

/// `deq_p` congruence at `Bind`.
pub proof fn deq_p_bind_congr(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    t1: ExprSpec,
    t2: ExprSpec,
    b1: ExprSpec,
    b2: ExprSpec,
    h: nat,
    bkind: BinderKind,
)
    requires
        deq_p(dty, env, lctx, io, t1, t2, h),
        deq_p(dty, env, lctx, io, b1, b2, h),
    ensures
        deq_p(
            dty,
            env,
            lctx, io,
            ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)),
            ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2)),
            h + 1,
        ),
{
    let cht = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == t1 && ch[ch.len() - 1] == t2 && deq_p_chain_valid(
            dty,
            env,
            lctx, io,
            ch,
            h,
        );
    let chb = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == b1 && ch[ch.len() - 1] == b2 && deq_p_chain_valid(
            dty,
            env,
            lctx, io,
            ch,
            h,
        );
    let mt = Seq::new(cht.len(), |i: int| ExprSpec::Bind(bkind, Box::new(cht[i]), Box::new(b1)));
    let mb = Seq::new(chb.len(), |i: int| ExprSpec::Bind(bkind, Box::new(t2), Box::new(chb[i])));
    assert(deq_p_chain_valid(dty, env, lctx, io, mt, h + 1)) by {
        assert forall|i: int| #![trigger mt[i]] 0 <= i < mt.len() - 1 implies deq_p_c(
            dty,
            env,
            lctx, io,
            mt[i],
            mt[i + 1],
            h + 1,
        ) by {
            assert(deq_p_c(dty, env, lctx, io, cht[i], cht[i + 1], h));
            defeq_refl(env, b1);
            assert(deq_c(env, b1, b1, h));
            assert(deq_p_c(dty, env, lctx, io, b1, b1, h));
            assert(mt[i] == ExprSpec::Bind(bkind, Box::new(cht[i]), Box::new(b1)));
            assert(mt[i + 1] == ExprSpec::Bind(bkind, Box::new(cht[i + 1]), Box::new(b1)));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_p_c(dty, env, lctx, io, mt[i], mt[i + 1], h + 1));
        }
    }
    assert(deq_p_chain_valid(dty, env, lctx, io, mb, h + 1)) by {
        assert forall|i: int| #![trigger mb[i]] 0 <= i < mb.len() - 1 implies deq_p_c(
            dty,
            env,
            lctx, io,
            mb[i],
            mb[i + 1],
            h + 1,
        ) by {
            assert(deq_p_c(dty, env, lctx, io, chb[i], chb[i + 1], h));
            defeq_refl(env, t2);
            assert(deq_c(env, t2, t2, h));
            assert(deq_p_c(dty, env, lctx, io, t2, t2, h));
            assert(mb[i] == ExprSpec::Bind(bkind, Box::new(t2), Box::new(chb[i])));
            assert(mb[i + 1] == ExprSpec::Bind(bkind, Box::new(t2), Box::new(chb[i + 1])));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_p_c(dty, env, lctx, io, mb[i], mb[i + 1], h + 1));
        }
    }
    assert(mt[0] == ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)));
    assert(mt[mt.len() - 1] == ExprSpec::Bind(bkind, Box::new(t2), Box::new(b1)));
    assert(mb[0] == ExprSpec::Bind(bkind, Box::new(t2), Box::new(b1)));
    assert(mb[mb.len() - 1] == ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2)));
    assert(deq_p(
        dty,
        env,
        lctx, io,
        ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)),
        ExprSpec::Bind(bkind, Box::new(t2), Box::new(b1)),
        h + 1,
    ));
    assert(deq_p(
        dty,
        env,
        lctx, io,
        ExprSpec::Bind(bkind, Box::new(t2), Box::new(b1)),
        ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2)),
        h + 1,
    ));
    deq_p_trans(
        dty,
        env,
        lctx, io,
        ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)),
        ExprSpec::Bind(bkind, Box::new(t2), Box::new(b1)),
        ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2)),
        h + 1,
    );
}

/// `deq_p` congruence at `Proj`.
pub proof fn deq_p_proj_congr(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    pidx: usize,
    s1: ExprSpec,
    s2: ExprSpec,
    h: nat,
)
    requires
        deq_p(dty, env, lctx, io, s1, s2, h),
    ensures
        deq_p(
            dty,
            env,
            lctx, io,
            ExprSpec::Proj(pidx, Box::new(s1)),
            ExprSpec::Proj(pidx, Box::new(s2)),
            h + 1,
        ),
{
    let chs = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == s1 && ch[ch.len() - 1] == s2 && deq_p_chain_valid(
            dty,
            env,
            lctx, io,
            ch,
            h,
        );
    let ms = Seq::new(chs.len(), |i: int| ExprSpec::Proj(pidx, Box::new(chs[i])));
    assert(deq_p_chain_valid(dty, env, lctx, io, ms, h + 1)) by {
        assert forall|i: int| #![trigger ms[i]] 0 <= i < ms.len() - 1 implies deq_p_c(
            dty,
            env,
            lctx, io,
            ms[i],
            ms[i + 1],
            h + 1,
        ) by {
            assert(deq_p_c(dty, env, lctx, io, chs[i], chs[i + 1], h));
            assert(ms[i] == ExprSpec::Proj(pidx, Box::new(chs[i])));
            assert(ms[i + 1] == ExprSpec::Proj(pidx, Box::new(chs[i + 1])));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_p_c(dty, env, lctx, io, ms[i], ms[i + 1], h + 1));
        }
    }
    assert(ms[0] == ExprSpec::Proj(pidx, Box::new(s1)));
    assert(ms[ms.len() - 1] == ExprSpec::Proj(pidx, Box::new(s2)));
    assert(deq_p(
        dty,
        env,
        lctx, io,
        ExprSpec::Proj(pidx, Box::new(s1)),
        ExprSpec::Proj(pidx, Box::new(s2)),
        h + 1,
    ));
}

/// `deq_p_any` API -- height-erased typed equality, mirroring `deq_any`'s.
pub proof fn deq_p_any_of_deq_any(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
)
    requires
        deq_any(env, x, y),
    ensures
        deq_p_any(dty, env, lctx, io, x, y),
{
    let h = choose|h: nat| deq(env, x, y, h);
    deq_p_of_deq(dty, env, lctx, io, x, y, h);
    assert(deq_p(dty, env, lctx, io, x, y, h));
}

pub proof fn deq_p_any_of_defeq(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
)
    requires
        defeq(env, x, y),
    ensures
        deq_p_any(dty, env, lctx, io, x, y),
{
    deq_any_of_defeq(env, x, y);
    deq_p_any_of_deq_any(dty, env, lctx, io, x, y);
}

pub proof fn deq_p_any_of_irrel(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    hi: nat,
)
    requires
        proof_irrel_pair(dty, env, lctx, io, x, y, hi),
        leaf_wt(dty, env, lctx, io, x, y, hi),
    ensures
        deq_p_any(dty, env, lctx, io, x, y),
{
    deq_p_of_irrel(dty, env, lctx, io, x, y, hi, hi + 1);
    assert(deq_p(dty, env, lctx, io, x, y, hi + 1));
}

/// `deq_p_any` congruences: lift the height-indexed `deq_p_*_congr` through
/// `deq_p_mono` to a common height (2026-09-06, for the conversion route).
pub proof fn deq_p_any_app_congr(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    f1: ExprSpec,
    f2: ExprSpec,
    a1: ExprSpec,
    a2: ExprSpec,
)
    requires
        deq_p_any(dty, env, lctx, io, f1, f2),
        deq_p_any(dty, env, lctx, io, a1, a2),
    ensures
        deq_p_any(
            dty,
            env,
            lctx, io,
            ExprSpec::App(Box::new(f1), Box::new(a1)),
            ExprSpec::App(Box::new(f2), Box::new(a2)),
        ),
{
    let h1 = choose|h: nat| #[trigger] deq_p(dty, env, lctx, io, f1, f2, h);
    let h2 = choose|h: nat| #[trigger] deq_p(dty, env, lctx, io, a1, a2, h);
    let h = if h1 >= h2 {
        h1
    } else {
        h2
    };
    deq_p_mono(dty, env, lctx, io, f1, f2, h1, h);
    deq_p_mono(dty, env, lctx, io, a1, a2, h2, h);
    deq_p_app_congr(dty, env, lctx, io, f1, f2, a1, a2, h);
    assert(deq_p(
        dty,
        env,
        lctx, io,
        ExprSpec::App(Box::new(f1), Box::new(a1)),
        ExprSpec::App(Box::new(f2), Box::new(a2)),
        h + 1,
    ));
}

pub proof fn deq_p_any_bind_congr(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    t1: ExprSpec,
    t2: ExprSpec,
    b1: ExprSpec,
    b2: ExprSpec,
    bkind: BinderKind,
)
    requires
        deq_p_any(dty, env, lctx, io, t1, t2),
        deq_p_any(dty, env, lctx, io, b1, b2),
    ensures
        deq_p_any(
            dty,
            env,
            lctx, io,
            ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)),
            ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2)),
        ),
{
    let h1 = choose|h: nat| #[trigger] deq_p(dty, env, lctx, io, t1, t2, h);
    let h2 = choose|h: nat| #[trigger] deq_p(dty, env, lctx, io, b1, b2, h);
    let h = if h1 >= h2 {
        h1
    } else {
        h2
    };
    deq_p_mono(dty, env, lctx, io, t1, t2, h1, h);
    deq_p_mono(dty, env, lctx, io, b1, b2, h2, h);
    deq_p_bind_congr(dty, env, lctx, io, t1, t2, b1, b2, h, bkind);
    assert(deq_p(
        dty,
        env,
        lctx, io,
        ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)),
        ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2)),
        h + 1,
    ));
}

pub proof fn deq_p_any_proj_congr(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    pidx: usize,
    s1: ExprSpec,
    s2: ExprSpec,
)
    requires
        deq_p_any(dty, env, lctx, io, s1, s2),
    ensures
        deq_p_any(
            dty,
            env,
            lctx, io,
            ExprSpec::Proj(pidx, Box::new(s1)),
            ExprSpec::Proj(pidx, Box::new(s2)),
        ),
{
    let h1 = choose|h: nat| #[trigger] deq_p(dty, env, lctx, io, s1, s2, h);
    deq_p_proj_congr(dty, env, lctx, io, pidx, s1, s2, h1);
    assert(deq_p(
        dty,
        env,
        lctx, io,
        ExprSpec::Proj(pidx, Box::new(s1)),
        ExprSpec::Proj(pidx, Box::new(s2)),
        h1 + 1,
    ));
}

pub proof fn deq_p_any_of_leaf(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
)
    requires
        deq_leaf(x, y),
    ensures
        deq_p_any(dty, env, lctx, io, x, y),
{
    deq_any_of_leaf(env, x, y);
    deq_p_any_of_deq_any(dty, env, lctx, io, x, y);
}

/// Binder INTRODUCTION by a fresh instance (the locally-nameless rule):
/// binder types related by a chain, bodies opened with a free variable
/// `k` absent from both related by a chain -- gives the binders related
/// one height up. No abstraction of chain elements is ever needed: the
/// (deq_p twin, 2026-09-06) fresh-instance disjunct of `deq_p_c`'s `Bind` case takes the opened-body
/// chain as is.
#[verifier::spinoff_prover]
/// Binder congruence on the binder type alone: the body stays put.
pub proof fn deq_p_bind_type_chain(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    t1: ExprSpec,
    t2: ExprSpec,
    b: ExprSpec,
    h: nat,
    bkind: BinderKind,
)
    requires
        deq_p(dty, env, lctx, io, t1, t2, h),
    ensures
        deq_p(dty, env, lctx, io, ExprSpec::Bind(bkind, Box::new(t1), Box::new(b)), ExprSpec::Bind(bkind, Box::new(t2), Box::new(b)), h + 1),
{
    let cht = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == t1 && ch[ch.len() - 1] == t2 && deq_p_chain_valid(dty, env, lctx, io, ch, h);
    let mt = Seq::new(cht.len(), |i: int| ExprSpec::Bind(bkind, Box::new(cht[i]), Box::new(b)));
    assert(deq_p_chain_valid(dty, env, lctx, io, mt, h + 1)) by {
        assert forall|i: int| #![trigger mt[i]] 0 <= i < mt.len() - 1 implies deq_p_c(dty, env, lctx, io, mt[i], mt[i + 1], h + 1) by {
            assert(deq_p_c(dty, env, lctx, io, cht[i], cht[i + 1], h));
            defeq_refl(env, b);
            assert(deq_c(env, b, b, h));
            deq_p_c_of_deq_c(dty, env, lctx, io, b, b, h);
            assert(mt[i] == ExprSpec::Bind(bkind, Box::new(cht[i]), Box::new(b)));
            assert(mt[i + 1] == ExprSpec::Bind(bkind, Box::new(cht[i + 1]), Box::new(b)));
            assert(((h + 1) - 1) as nat == h);
        }
    }
    assert(mt[0] == ExprSpec::Bind(bkind, Box::new(t1), Box::new(b)));
    assert(mt[mt.len() - 1] == ExprSpec::Bind(bkind, Box::new(t2), Box::new(b)));
}

/// Binder congruence on the bodies alone, opened with a fresh local of the
/// binder's type.
pub proof fn deq_p_bind_link(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    t: ExprSpec,
    b1: ExprSpec,
    b2: ExprSpec,
    k: u32,
    h: nat,
    bkind: BinderKind,
)
    requires
        fv_absent(b1, k),
        fv_absent(b2, k),
        unreach(lctx, k, t),
        unreach(lctx, k, b1),
        unreach(lctx, k, b2),
        lctx.contains_key(k),
        lctx[k] == t,
        deq_p(dty, env, lctx, io, inst_free(b1, k), inst_free(b2, k), h),
    ensures
        deq_p(dty, env, lctx, io, ExprSpec::Bind(bkind, Box::new(t), Box::new(b1)), ExprSpec::Bind(bkind, Box::new(t), Box::new(b2)), h + 1),
{
    let bx = ExprSpec::Bind(bkind, Box::new(t), Box::new(b1));
    let by = ExprSpec::Bind(bkind, Box::new(t), Box::new(b2));
    defeq_refl(env, t);
    assert(deq_c(env, t, t, h));
    deq_p_c_of_deq_c(dty, env, lctx, io, t, t, h);
    assert(fresh_marker(k));
    assert(((h + 1) - 1) as nat == h);
    assert(deq_p_c(dty, env, lctx, io, bx, by, h + 1));
    let link = seq![bx, by];
    assert(deq_p_chain_valid(dty, env, lctx, io, link, h + 1)) by {
        assert forall|i: int| #![trigger link[i]] 0 <= i < link.len() - 1 implies deq_p_c(dty, env, lctx, io, link[i], link[i + 1], h + 1) by {
            assert(i == 0);
        }
    }
}

/// Binder congruence through a fresh local, typed with either binder's type
/// (the kernel opens with the first).
pub proof fn deq_p_bind_fresh(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    t1: ExprSpec,
    t2: ExprSpec,
    b1: ExprSpec,
    b2: ExprSpec,
    k: u32,
    h: nat,
    bkind: BinderKind,
)
    requires
        deq_p(dty, env, lctx, io, t1, t2, h),
        fv_absent(b1, k),
        fv_absent(b2, k),
        unreach(lctx, k, t1),
        unreach(lctx, k, t2),
        unreach(lctx, k, b1),
        unreach(lctx, k, b2),
        lctx.contains_key(k),
        lctx[k] == t1 || lctx[k] == t2,
        deq_p(dty, env, lctx, io, inst_free(b1, k), inst_free(b2, k), h),
    ensures
        deq_p(
            dty,
            env,
            lctx, io,
            ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)),
            ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2)),
            h + 1,
        ),
{
    let x = ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1));
    let y = ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2));
    if lctx[k] == t1 {
        let m = ExprSpec::Bind(bkind, Box::new(t1), Box::new(b2));
        deq_p_bind_link(dty, env, lctx, io, t1, b1, b2, k, h, bkind);
        deq_p_bind_type_chain(dty, env, lctx, io, t1, t2, b2, h, bkind);
        deq_p_trans(dty, env, lctx, io, x, m, y, h + 1);
    } else {
        let m = ExprSpec::Bind(bkind, Box::new(t2), Box::new(b1));
        deq_p_bind_type_chain(dty, env, lctx, io, t1, t2, b1, h, bkind);
        deq_p_bind_link(dty, env, lctx, io, t2, b1, b2, k, h, bkind);
        deq_p_trans(dty, env, lctx, io, x, m, y, h + 1);
    }
}

/// `deq_p_any` face of `deq_p_bind_fresh`.
pub proof fn deq_p_any_bind_fresh(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    t1: ExprSpec,
    t2: ExprSpec,
    b1: ExprSpec,
    b2: ExprSpec,
    k: u32,
    bkind: BinderKind,
)
    requires
        deq_p_any(dty, env, lctx, io, t1, t2),
        fv_absent(b1, k),
        fv_absent(b2, k),
        unreach(lctx, k, t1),
        unreach(lctx, k, t2),
        unreach(lctx, k, b1),
        unreach(lctx, k, b2),
        lctx.contains_key(k),
        lctx[k] == t1 || lctx[k] == t2,
        deq_p_any(dty, env, lctx, io, inst_free(b1, k), inst_free(b2, k)),
    ensures
        deq_p_any(
            dty,
            env,
            lctx, io,
            ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)),
            ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2)),
        ),
{
    let h1 = choose|h: nat| #[trigger] deq_p(dty, env, lctx, io, t1, t2, h);
    let h2 = choose|h: nat| #[trigger] deq_p(dty, env, lctx, io, inst_free(b1, k), inst_free(b2, k), h);
    let hm = if h1 >= h2 {
        h1
    } else {
        h2
    };
    deq_p_mono(dty, env, lctx, io, t1, t2, h1, hm);
    deq_p_mono(dty, env, lctx, io, inst_free(b1, k), inst_free(b2, k), h2, hm);
    deq_p_bind_fresh(dty, env, lctx, io, t1, t2, b1, b2, k, hm, bkind);
    assert(deq_p(
        dty,
        env,
        lctx, io,
        ExprSpec::Bind(bkind, Box::new(t1), Box::new(b1)),
        ExprSpec::Bind(bkind, Box::new(t2), Box::new(b2)),
        hm + 1,
    ));
}

/// `deq_p_any` congruence along a spine, argument by argument.
pub proof fn deq_p_any_spine_congr_args(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    h1: ExprSpec,
    h2: ExprSpec,
    a1: Seq<ExprSpec>,
    a2: Seq<ExprSpec>,
)
    requires
        deq_p_any(dty, env, lctx, io, h1, h2),
        a1.len() == a2.len(),
        forall|i: int| 0 <= i < a1.len() ==> deq_p_any(dty, env, lctx, io, #[trigger] a1[i], a2[i]),
    ensures
        deq_p_any(dty, env, lctx, io, spine_app(h1, a1), spine_app(h2, a2)),
    decreases a1.len(),
{
    if a1.len() == 0 {
        assert(spine_app(h1, a1) == h1);
        assert(spine_app(h2, a2) == h2);
    } else {
        let n = a1.len() - 1;
        let p1 = a1.subrange(0, n);
        let p2 = a2.subrange(0, n);
        assert forall|i: int| 0 <= i < p1.len() implies deq_p_any(dty, env, lctx, io, #[trigger] p1[i], p2[i]) by {
            assert(p1[i] == a1[i]);
            assert(p2[i] == a2[i]);
        }
        deq_p_any_spine_congr_args(dty, env, lctx, io, h1, h2, p1, p2);
        assert(p1.push(a1[n]) =~= a1);
        assert(p2.push(a2[n]) =~= a2);
        spine_app_compose_last(h1, p1, a1[n]);
        spine_app_compose_last(h2, p2, a2[n]);
        deq_p_any_app_congr(dty, env, lctx, io, spine_app(h1, p1), spine_app(h2, p2), a1[n], a2[n]);
    }
}

/// `deq_p_any` congruence along a spine of unchanged arguments (2026-09-08,
/// K-like recursor leaf): `x ~ y` gives `x args ~ y args`.
pub proof fn deq_p_any_spine_congr(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    rest: Seq<ExprSpec>,
)
    requires
        deq_p_any(dty, env, lctx, io, x, y),
    ensures
        deq_p_any(dty, env, lctx, io, spine_app(x, rest), spine_app(y, rest)),
    decreases rest.len(),
{
    if rest.len() == 0 {
        assert(spine_app(x, rest) == x);
        assert(spine_app(y, rest) == y);
    } else {
        let front = rest.subrange(0, rest.len() as int - 1);
        let last = rest[rest.len() as int - 1];
        assert(rest =~= front.push(last));
        spine_app_compose_last(x, front, last);
        spine_app_compose_last(y, front, last);
        deq_p_any_spine_congr(dty, env, lctx, io, x, y, front);
        deq_p_any_refl(dty, env, lctx, io, last);
        deq_p_any_app_congr(dty, env, lctx, io, spine_app(x, front), spine_app(y, front), last, last);
    }
}

/// One argument of a spine replaced by a `deq_p_any`-related term (the
/// `pstep_star_spine_update` twin).
pub proof fn deq_p_any_spine_update(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    head: ExprSpec,
    args: Seq<ExprSpec>,
    i: int,
    y: ExprSpec,
)
    requires
        0 <= i < args.len(),
        deq_p_any(dty, env, lctx, io, args[i], y),
    ensures
        deq_p_any(dty, env, lctx, io, spine_app(head, args), spine_app(head, args.update(i, y))),
{
    let args2 = args.update(i, y);
    let pre = args.subrange(0, i);
    let rest = args.subrange(i + 1, args.len() as int);
    assert(args =~= pre.push(args[i]) + rest);
    assert(args2 =~= pre.push(y) + rest);
    let x = spine_app(head, pre);
    spine_app_concat(head, pre.push(args[i]), rest);
    spine_app_concat(head, pre.push(y), rest);
    spine_app_compose_last(head, pre, args[i]);
    spine_app_compose_last(head, pre, y);
    deq_p_any_refl(dty, env, lctx, io, x);
    deq_p_any_app_congr(dty, env, lctx, io, x, x, args[i], y);
    deq_p_any_spine_congr(
        dty,
        env,
        lctx, io,
        ExprSpec::App(Box::new(x), Box::new(args[i])),
        ExprSpec::App(Box::new(x), Box::new(y)),
        rest,
    );
}

pub proof fn deq_p_any_refl(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
)
    ensures
        deq_p_any(dty, env, lctx, io, x, x),
{
    deq_p_refl(dty, env, lctx, io, x, 0);
    assert(deq_p(dty, env, lctx, io, x, x, 0));
}

pub proof fn deq_p_any_symm(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
)
    requires
        deq_p_any(dty, env, lctx, io, x, y),
    ensures
        deq_p_any(dty, env, lctx, io, y, x),
{
    let h = choose|h: nat| deq_p(dty, env, lctx, io, x, y, h);
    deq_p_symm(dty, env, lctx, io, x, y, h);
    assert(deq_p(dty, env, lctx, io, y, x, h));
}

pub proof fn deq_p_any_trans(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    z: ExprSpec,
)
    requires
        deq_p_any(dty, env, lctx, io, x, y),
        deq_p_any(dty, env, lctx, io, y, z),
    ensures
        deq_p_any(dty, env, lctx, io, x, z),
{
    let h1 = choose|h: nat| deq_p(dty, env, lctx, io, x, y, h);
    let h2 = choose|h: nat| deq_p(dty, env, lctx, io, y, z, h);
    let hm = if h1 >= h2 {
        h1
    } else {
        h2
    };
    deq_p_mono(dty, env, lctx, io, x, y, h1, hm);
    deq_p_mono(dty, env, lctx, io, y, z, h2, hm);
    deq_p_trans(dty, env, lctx, io, x, y, z, hm);
    assert(deq_p(dty, env, lctx, io, x, z, hm));
}

/// `nat_repr_is_zero(e)` (EITHER a `NatLit` valued 0, or a `Const` named
/// `Nat.zero`) always `pstep_star`-reaches the ONE canonical empty-levels
/// form `pstep`'s own `NatLit` rule targets, for ANY `env` (this fact
/// needs no delta lookup). The `NatLit` case is one real `pstep` step
/// (matching `pstep`'s own rule literally); the `Const`-shape case is
/// ZERO steps (`pstep_star_refl`): `nat_repr_is_zero` pins its levels
/// down to empty, letting `const_expr_no_levels_canonical`
/// identify it with the canonical value directly. This is the connecting
/// lemma `verified_def_eq_nat`'s "both sides are some zero
/// representation" disjunct needs to lift to a real `full_def_eq(x, y)`
/// claim (see `feedback_defeq_witness_vs_pstep_star` for why this
/// couldn't just reuse `def_eq_witness`).
pub proof fn nat_repr_is_zero_reaches_canonical<'t>(
    env: EnvSpec,
    e: ExprPtr<'t>,
)
    requires
        nat_repr_is_zero(env.export, e),
    ensures
        pstep_star(env, to_model(e), const_expr_no_levels(nat_zero_id(env.export))),
{
    if is_nat_lit_shape(e) && nat_lit_value(e) == 0 {
        is_nat_lit_shape_model(e);
        assert(to_model(e) == ExprSpec::NatLit(NatLitPayload(Ghost(nat_lit_value(e)))));
        assert(pstep(env, to_model(e), const_expr_no_levels(nat_zero_id(env.export))));
        pstep_star_one(env, to_model(e), const_expr_no_levels(nat_zero_id(env.export)));
    } else {
        assert(is_const_shape(e));
        assert(const_id(e) == nat_zero_id(env.export));
        is_const_shape_model(e);
        const_levels_vec_model(e);
        assert(const_levels_vec(e).len() == 0);
        assert(to_model(e) == ExprSpec::Const(const_id(e), const_levels_vec(e)));
        const_expr_no_levels_canonical(to_model(e), nat_zero_id(env.export));
        pstep_star_refl(env, to_model(e));
    }
}











} // verus!
