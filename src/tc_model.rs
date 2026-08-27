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
//! definition body's level parameters, reapply the args) and `env_model.rs`'s
//! `Env::get_declar_val` trust boundary (the real declaration lookup) --
//! the capstone connecting real delta reduction to a genuine `pstep_star`
//! step, the way `expr_arena_bridge.rs`'s `verified_whnf_beta_step`/
//! `verified_whnf_zeta_step` already do for beta/zeta.

#[allow(unused_imports)]
use vstd::prelude::*;
use crate::env::{RecRule, Env};
use crate::util::{ExprPtr, NamePtr, LevelsPtr, TcCtx};
use crate::expr::{Expr, BinderStyle};
use crate::level_arena_bridge::name_ptr_eq;
use crate::level_arena_bridge::{verified_eq_antisymm, verified_eq_antisymm_many};
use crate::util::LevelPtr;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model as level_to_model;
#[cfg(verus_only)]
use crate::level_model::interp;
use crate::expr_arena_bridge::{expr_as_const, expr_as_app, expr_as_sort, expr_as_local, expr_as_proj, fvar_id_eq, expr_ptr_eq, expr_as_pi, expr_as_lambda, verified_inst, verified_peel_pis};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{is_local_shape, local_id_of, local_binder_type_of};
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[cfg(verus_only)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{is_const_shape, const_name_of, const_levels_of, const_id, const_levels_vec, is_const_shape_model, const_levels_vec_model};
#[cfg(verus_only)]
use crate::util_model::find_index;
#[cfg(verus_only)]
use crate::expr_arena_bridge::to_model;
use crate::expr_arena_bridge::{verified_unfold_apps, verified_subst_expr_levels, verified_foldl_apps, verified_whnf_no_unfolding_step, verified_whnf_no_unfolding_fixpoint, expr_as_nat_lit, read_bignum_value};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{whnf_fixpoint_ok, is_nat_lit_shape, nat_lit_value, is_nat_lit_shape_model};
use crate::nat_lit_model::{biguint_succ, biguint_add, biguint_mul, biguint_eq, biguint_le};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{bool_true_id, bool_false_id, nat_zero_id, nat_succ_id, nat_repr_is_zero, nat_repr_pred};
use crate::util::{nat_sub, nat_div, nat_mod};
#[cfg(verus_only)]
use crate::nat_lit_model::to_nat;
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, to_model_of_levels};
use crate::level_arena_bridge::read_levels_vec;
#[cfg(verus_only)]
use crate::level_model::level_names;
#[cfg(verus_only)]
use crate::env_model::to_model_of_env;
use crate::env_model::{get_constructor_num_params, get_recursor_data, get_declar_hint, reducibility_hint_as_regular, get_declar_info_ty};
#[cfg(verus_only)]
use crate::env_model::to_model_of_declar_ty;
#[cfg(verus_only)]
use crate::env_model::to_model_of_ctor_num_params;
#[cfg(verus_only)]
use crate::env_model::to_model_of_declar_hint;
#[cfg(verus_only)]
use crate::env_model::to_model as reducibility_hint_to_model;
use crate::env::ReducibilityHint;
#[cfg(verus_only)]
use crate::beta_model::{pstep, pstep_star, pstep_star_one, pstep_spine_app_star, spine_app, pstep_star_proj, max_var_below, pstep_star_env_weaken, pstep_star_trans, subst_full_depth_bound_n, spine_bind, spine_bind_depth};
#[cfg(verus_only)]
use crate::expr_model::{nlbv, depth, subst_expr_levels_rel, subst_full};

#[allow(dead_code)]
pub(crate) fn rec_rule_ctor_name<'t>(r: &RecRule<'t>) -> NamePtr<'t> {
    r.ctor_name
}

#[allow(dead_code)]
pub(crate) fn rec_rule_ctor_telescope_size_wo_params<'t>(r: &RecRule<'t>) -> u16 {
    r.ctor_telescope_size_wo_params
}

#[allow(dead_code)]
pub(crate) fn rec_rule_val<'t>(r: &RecRule<'t>) -> ExprPtr<'t> {
    r.val
}

verus! {

#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRecRule<'a>(RecRule<'a>);

/// `RecRule::ctor_name`, keyed by value (like `Ptr::raw`'s `ptr_raw`) since
/// `RecRule` is `external_body`.
pub uninterp spec fn rec_rule_ctor_name_of<'a>(r: RecRule<'a>) -> NamePtr<'a>;

pub assume_specification<'t> [rec_rule_ctor_name] (r: &RecRule<'t>) -> (result: NamePtr<'t>)
    ensures result == rec_rule_ctor_name_of(*r);

/// Small helper so `verified_reduce_rec_step`'s `ensures` can use `.
/// subrange(...)` (a valid quantifier trigger) instead of a fresh
/// `Seq::new(...)` closure at each slicing point (not a valid trigger).
pub open spec fn args_model_of<'t>(xs: Seq<ExprPtr<'t>>) -> Seq<ExprSpec> {
    Seq::new(xs.len(), |i: int| to_model(xs[i]))
}

pub uninterp spec fn rec_rule_ctor_telescope_size_wo_params_of<'a>(r: RecRule<'a>) -> u16;
pub assume_specification<'t> [rec_rule_ctor_telescope_size_wo_params] (r: &RecRule<'t>) -> (result: u16)
    ensures result == rec_rule_ctor_telescope_size_wo_params_of(*r);

pub uninterp spec fn rec_rule_val_of<'a>(r: RecRule<'a>) -> ExprPtr<'a>;
pub assume_specification<'t> [rec_rule_val] (r: &RecRule<'t>) -> (result: ExprPtr<'t>)
    ensures result == rec_rule_val_of(*r);

pub open spec fn rec_rule_ctor_names<'a>(rec_rules: Seq<RecRule<'a>>) -> Seq<NamePtr<'a>> {
    Seq::new(rec_rules.len(), |i: int| rec_rule_ctor_name_of(rec_rules[i]))
}

/// Mirrors the `for` loop in `get_rec_rule`'s real body (`tc.rs:203-207`):
/// front-to-back linear scan, returning the first matching rule.
/// Recursion instead of a loop (matching `find_index`'s own recursive
/// shape directly, same trick `verified_find_pos_from_end` used in
/// `expr_arena_bridge.rs`) sidesteps needing a hand-rolled loop invariant.
pub fn verified_find_rec_rule<'t>(rec_rules: &[RecRule<'t>], major_ctor_name: NamePtr<'t>) -> (result: Option<RecRule<'t>>)
    ensures match find_index(rec_rule_ctor_names(rec_rules@), major_ctor_name) {
        Some(i) => result == Some(rec_rules@[i as int]),
        None => result is None,
    }
    decreases rec_rules.len()
{
    let ghost names = rec_rule_ctor_names(rec_rules@);
    if rec_rules.len() == 0 {
        assert(names =~= Seq::<NamePtr<'t>>::empty());
        None
    } else {
        let first = rec_rules[0];
        let first_name = rec_rule_ctor_name(&first);
        assert(first_name == names[0]);
        if name_ptr_eq(first_name, major_ctor_name) {
            assert(names[0] == major_ctor_name);
            assert(rec_rules@[0] == first);
            Some(first)
        } else {
            assert(names[0] != major_ctor_name);
            assert(rec_rules.len() >= 1);
            let sub = &rec_rules[1..rec_rules.len()];
            assert(sub@ =~= rec_rules@.subrange(1, rec_rules@.len() as int));
            let ghost sub_names = rec_rule_ctor_names(sub@);
            assert(sub_names =~= names.subrange(1, names.len() as int));
            assert(find_index(names, major_ctor_name) == match find_index(sub_names, major_ctor_name) {
                Some(i) => Some((i + 1) as nat),
                None => None,
            });
            let result = verified_find_rec_rule(sub, major_ctor_name);
            assert(match find_index(sub_names, major_ctor_name) {
                Some(i) => result == Some(sub@[i as int]),
                None => result is None,
            });
            proof {
                if let Some(i) = find_index(sub_names, major_ctor_name) {
                    crate::util_model::find_index_correct(sub_names, major_ctor_name);
                    assert(i < sub_names.len());
                    assert(i < sub@.len());
                    assert(sub@[i as int] == rec_rules@.subrange(1, rec_rules@.len() as int)[i as int]);
                    assert(rec_rules@.subrange(1, rec_rules@.len() as int)[i as int] == rec_rules@[(i + 1) as int]);
                }
            }
            result
        }
    }
}

/// The full `get_rec_rule` pattern: check `major_const` denotes a `Const`
/// first (mirroring the real `if let Const { name, .. } = ...` guard),
/// falling back to `None` if not, else delegating to
/// `verified_find_rec_rule`.
pub fn verified_get_rec_rule<'t>(major_const_el: &Expr<'t>, major_const: ExprPtr<'t>, rec_rules: &[RecRule<'t>]) -> (result: Option<RecRule<'t>>)
    ensures ({
        if is_const_shape(major_const) {
            match find_index(rec_rule_ctor_names(rec_rules@), const_name_of(major_const)) {
                Some(i) => result == Some(rec_rules@[i as int]),
                None => result is None,
            }
        } else {
            result is None
        }
    })
{
    match expr_as_const(major_const, major_const_el) {
        Some((major_ctor_name, _levels)) => verified_find_rec_rule(rec_rules, major_ctor_name),
        None => None,
    }
}

/// Manual transcription of real `unfold_def` (`tc.rs:1153-1163`): peel the
/// expression's applied-`Const` head via `verified_unfold_apps`, look up
/// the constant's definition in the real environment, substitute the
/// definition's level parameters by the `Const`'s own level arguments via
/// `verified_subst_expr_levels`, and reapply the peeled args via
/// `verified_foldl_apps` -- exactly the real algorithm, with the same
/// early-outs (not applied to a `Const` at all; the name isn't a known
/// definition/theorem; the level-argument count doesn't match the
/// definition's own parameter count).
///
/// The result is packaged as a genuine `pstep_star` delta step in a
/// singleton `env` containing exactly the one definition unfolded --
/// `env_declar_singleton_wf` (`env_model.rs`) gives this `env_wf`, and
/// `pstep`'s `Const` disjunct plus `pstep_spine_app_star` (both
/// `beta_model.rs`) lift that single-step fact on the bare `Const` node up
/// to the whole applied spine, matching `verified_whnf_beta_step`/
/// `verified_whnf_zeta_step`'s existing pattern for beta/zeta.
pub fn verified_unfold_def_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32) -> (result: Option<ExprPtr<'t>>)
    ensures match result {
        Some(r) => exists |id: u64, ks: Seq<u64>, val: ExprSpec| {
            &&& to_model_of_env(*env).contains_key(id)
            &&& to_model_of_env(*env)[id] == (ks, val)
            &&& pstep_star(
                    Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val)),
                    to_model(e),
                    to_model(r),
                )
        },
        None => true,
    }
{
    let (fun, args) = match verified_unfold_apps(ctx, e, fuel) {
        Some(p) => p,
        None => return None,
    };
    let fun_el = ctx.read_expr(fun);
    let (name, levels) = match expr_as_const(fun, &fun_el) {
        Some(p) => p,
        None => return None,
    };
    let (def_uparams, def_value) = match env.get_declar_val(&name) {
        Some(p) => p,
        None => return None,
    };
    let levels_vec = read_levels_vec(ctx, levels);
    let uparams_vec = read_levels_vec(ctx, def_uparams);
    if levels_vec.len() != uparams_vec.len() {
        return None;
    }
    assert(to_model_of_levels(levels).len() == to_model_of_levels(def_uparams).len());
    match verified_subst_expr_levels(ctx, def_value, def_uparams, levels, fuel) {
        Some(def_val) => {
            let ghost id = name_id(name);
            let ghost ks = level_names(to_model_of_levels(def_uparams));
            let ghost val = to_model(def_value);
            assert(to_model_of_env(*env).contains_key(id));
            assert(to_model_of_env(*env)[id] == (ks, val));
            proof {
                is_const_shape_model(fun);
                const_levels_vec_model(fun);
            }
            assert(to_model(fun) == ExprSpec::Const(const_id(fun), const_levels_vec(fun)));
            assert(const_id(fun) == id);
            assert(const_levels_vec(fun)@ =~= to_model_of_levels(levels));
            proof {
                assert(pstep(
                    Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val)),
                    to_model(fun),
                    to_model(def_val),
                ));
                pstep_star_one(
                    Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val)),
                    to_model(fun),
                    to_model(def_val),
                );
                pstep_spine_app_star(
                    Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val)),
                    to_model(fun),
                    to_model(def_val),
                    Seq::new(args@.len(), |i: int| to_model(args@[i])),
                );
            }
            let result = verified_foldl_apps(ctx, def_val, &args);
            assert(to_model(e) == spine_app(to_model(fun), Seq::new(args@.len(), |i: int| to_model(args@[i]))));
            assert(to_model(result) == spine_app(to_model(def_val), Seq::new(args@.len(), |i: int| to_model(args@[i]))));
            Some(result)
        }
        None => None,
    }
}

/// Manual transcription of real `reduce_proj`'s "cheap" path (`tc.rs:447-
/// 458`, `cheap_proj == true`, i.e. `structure`'s WHNF is computed via
/// `whnf_no_unfolding_cheap_proj`/`verified_whnf_no_unfolding_step`, not
/// the full `whnf` -- the full-`whnf` path needs `try_reduce_nat`/
/// `unfold_def`/`reduce_quot`/`reduce_rec` composed in too, not yet done):
/// reduce `structure` to WHNF, peel its applied-`Const` head, look up the
/// name as a constructor in the real environment (`get_constructor_num_
/// params`, `env_model.rs`), and index `num_params + idx` into the peeled
/// args -- exactly the real algorithm, MINUS the `StringLit`-to-
/// constructor conversion step (`str_lit_to_ctor_reducing`, not yet
/// bridged -- if `structure` whnf's to a `StringLit`, this conservatively
/// returns `None` rather than the real function's literal-to-constructor
/// rewrite).
///
/// The result is packaged as `pstep_star_proj` (`beta_model.rs`), the
/// dedicated proj-iota relation -- `is_const_shape_model`/`const_levels_
/// vec_model`/`const_id`/`const_levels_vec` connect the peeled `Const`
/// node's `to_model` to `pstep_star_proj`'s existential witness the same
/// way `verified_unfold_def_step` already does for delta.
pub fn verified_reduce_proj_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, structure: ExprPtr<'t>, idx: usize, fuel: u32, bound: nat, d: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(structure)) <= 0,
        max_var_below(to_model(structure), bound),
        depth(to_model(structure)) <= d,
        d <= 60000,
        bound + d * d * d + d * d + d + 10 <= 0xFFFF_0000,
        idx <= 0xFFFF_0000,
    ensures match result {
        Some(r) => pstep_star_proj(
            Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
            to_model_of_ctor_num_params(*env),
            to_model(structure),
            idx as nat,
            to_model(r),
        ),
        None => true,
    }
{
    let whnfd = match verified_whnf_no_unfolding_step(ctx, structure, fuel, bound, d) {
        Some(w) => w,
        None => return None,
    };
    let (fun, args) = match verified_unfold_apps(ctx, whnfd, fuel) {
        Some(p) => p,
        None => return None,
    };
    let fun_el = ctx.read_expr(fun);
    let (name, _levels) = match expr_as_const(fun, &fun_el) {
        Some(p) => p,
        None => return None,
    };
    match get_constructor_num_params(env, &name) {
        Some(num_params) => {
            let i = num_params as usize + idx;
            if i < args.len() {
                let r = args[i];
                let ghost args_model = Seq::new(args@.len(), |j: int| to_model(args@[j]));
                proof {
                    is_const_shape_model(fun);
                    const_levels_vec_model(fun);
                }
                assert(to_model(fun) == ExprSpec::Const(const_id(fun), const_levels_vec(fun)));
                assert(to_model(whnfd) == spine_app(to_model(fun), args_model));
                assert(const_id(fun) == name_id(name));
                assert(to_model_of_ctor_num_params(*env).contains_key(name_id(name)));
                assert(to_model_of_ctor_num_params(*env)[name_id(name)] == num_params);
                assert(args_model[i as int] == to_model(r));
                assert(pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(structure), to_model(whnfd)));
                assert((num_params as nat) + (idx as nat) < args_model.len());
                assert(pstep_star_proj(
                    Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
                    to_model_of_ctor_num_params(*env),
                    to_model(structure),
                    idx as nat,
                    to_model(r),
                )) by {
                    assert(to_model(whnfd) == spine_app(ExprSpec::Const(const_id(fun), const_levels_vec(fun)), args_model));
                }
                Some(r)
            } else {
                None
            }
        }
        None => None,
    }
}

/// Manual transcription of ONE round of real `whnf`'s outer loop
/// (`tc.rs:764-783`): `whnf_no_unfolding` (here, `verified_whnf_no_
/// unfolding_fixpoint`, up to `n` telescoped beta/zeta steps) followed by
/// ONE attempt at delta-unfolding (`verified_unfold_def_step`). Does NOT
/// yet model `try_reduce_nat` (nat-literal arithmetic reduction -- a
/// genuinely new relation, not yet started, see the project memory) or
/// repeating this whole round more than once (the real loop repeats
/// until NEITHER nat-reduction NOR delta-unfolding apply) -- both
/// honestly incomplete, not unsound: when delta-unfolding fails, this
/// returns the no-unfolding result unchanged (`Some(whnfd)`), exactly
/// like the real loop's own final `return whnfd` when both its checks
/// fail, so a single round is already a faithful (if not necessarily
/// maximal) WHNF step whenever nat-reduction doesn't apply.
///
/// The real payoff is composing `verified_whnf_no_unfolding_fixpoint`'s
/// `Map::empty()`-env `pstep_star` fact with `verified_unfold_def_step`'s
/// non-empty singleton-env one into ONE chain under `to_model_of_env`'s
/// FULL real environment -- `pstep_env_weaken`/`pstep_star_env_weaken`
/// (`beta_model.rs`) make this free: both the empty env (vacuously) and
/// the one-definition singleton env (directly, since `verified_unfold_
/// def_step`'s own existential witness is already drawn from `to_model_
/// of_env(*env)`) are subsets of the real env's own model, so both
/// `pstep_star` facts weaken into it without needing a growing synthetic
/// environment assembled by hand.
pub fn verified_whnf_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => pstep_star(to_model_of_env(*env), to_model(e), to_model(r)),
        None => true,
    }
{
    match verified_whnf_no_unfolding_fixpoint(ctx, e, fuel, bound, d, n) {
        Some(whnfd) => {
            proof {
                assert forall |k: u64| #[trigger] Map::<u64, (Seq<u64>, ExprSpec)>::empty().contains_key(k) implies
                    to_model_of_env(*env).contains_key(k)
                    && Map::<u64, (Seq<u64>, ExprSpec)>::empty()[k] == to_model_of_env(*env)[k]
                by {}
                pstep_star_env_weaken(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model_of_env(*env), to_model(e), to_model(whnfd));
            }
            match verified_unfold_def_step(ctx, env, whnfd, fuel) {
                Some(r) => {
                    proof {
                        let (id, ks, val) = choose |id: u64, ks: Seq<u64>, val: ExprSpec| {
                            &&& to_model_of_env(*env).contains_key(id)
                            &&& to_model_of_env(*env)[id] == (ks, val)
                            &&& pstep_star(
                                    Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val)),
                                    to_model(whnfd),
                                    to_model(r),
                                )
                        };
                        let singleton = Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val));
                        assert forall |k: u64| #[trigger] singleton.contains_key(k) implies
                            to_model_of_env(*env).contains_key(k) && singleton[k] == to_model_of_env(*env)[k]
                        by {
                            assert(k == id);
                        }
                        pstep_star_env_weaken(singleton, to_model_of_env(*env), to_model(whnfd), to_model(r));
                        pstep_star_trans(to_model_of_env(*env), to_model(e), to_model(whnfd), to_model(r));
                    }
                    Some(r)
                }
                None => Some(whnfd),
            }
        }
        None => None,
    }
}

/// `verified_reduce_proj_step`'s non-cheap counterpart: uses `verified_
/// whnf_step` (beta/zeta* THEN one delta attempt) instead of bare `
/// verified_whnf_no_unfolding_step` to reduce `structure` -- a real,
/// honest step up from the cheap path (now covers definitions that need
/// ONE constant unfolded before exposing their constructor head), though
/// still not the full real `reduce_proj(cheap=false)` (needs `try_reduce_
/// nat` and possibly repeated delta rounds, neither modeled yet). `env`'s
/// FULL model (`to_model_of_env`) is what `pstep_star_proj`'s own `env`
/// parameter carries here, rather than `Map::empty()` -- exactly what
/// `verified_whnf_step`'s `pstep_star` conclusion is already stated over.
pub fn verified_reduce_proj_step_full<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, structure: ExprPtr<'t>, idx: usize, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(structure)) <= 0,
        max_var_below(to_model(structure), bound),
        depth(to_model(structure)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
        idx <= 0xFFFF_0000,
    ensures match result {
        Some(r) => pstep_star_proj(
            to_model_of_env(*env),
            to_model_of_ctor_num_params(*env),
            to_model(structure),
            idx as nat,
            to_model(r),
        ),
        None => true,
    }
{
    let whnfd = match verified_whnf_step(ctx, env, structure, fuel, bound, d, n) {
        Some(w) => w,
        None => return None,
    };
    let (fun, args) = match verified_unfold_apps(ctx, whnfd, fuel) {
        Some(p) => p,
        None => return None,
    };
    let fun_el = ctx.read_expr(fun);
    let (name, _levels) = match expr_as_const(fun, &fun_el) {
        Some(p) => p,
        None => return None,
    };
    match get_constructor_num_params(env, &name) {
        Some(num_params) => {
            let i = num_params as usize + idx;
            if i < args.len() {
                let r = args[i];
                let ghost args_model = Seq::new(args@.len(), |j: int| to_model(args@[j]));
                proof {
                    is_const_shape_model(fun);
                    const_levels_vec_model(fun);
                }
                assert(to_model(fun) == ExprSpec::Const(const_id(fun), const_levels_vec(fun)));
                assert(to_model(whnfd) == spine_app(to_model(fun), args_model));
                assert(const_id(fun) == name_id(name));
                assert(to_model_of_ctor_num_params(*env).contains_key(name_id(name)));
                assert(to_model_of_ctor_num_params(*env)[name_id(name)] == num_params);
                assert(args_model[i as int] == to_model(r));
                assert(pstep_star(to_model_of_env(*env), to_model(structure), to_model(whnfd)));
                assert((num_params as nat) + (idx as nat) < args_model.len());
                assert(pstep_star_proj(
                    to_model_of_env(*env),
                    to_model_of_ctor_num_params(*env),
                    to_model(structure),
                    idx as nat,
                    to_model(r),
                )) by {
                    assert(to_model(whnfd) == spine_app(ExprSpec::Const(const_id(fun), const_levels_vec(fun)), args_model));
                }
                Some(r)
            } else {
                None
            }
        }
        None => None,
    }
}

/// Manual transcription of `tc.rs`'s `try_reduce_nat`'s FIRST branch
/// (`Nat.succ` applied to one argument, `tc.rs:404-407`) composed with
/// its callee `expr.rs::get_bignum_succ_from_expr`'s `NatLit` case
/// (`tc.rs:597-599`; the `Const Nat.zero []` representation of zero,
/// `get_bignum_succ_from_expr`'s OTHER branch, is not modeled -- returns
/// `None` conservatively): whnf `arg` (via `verified_whnf_step`, one
/// round -- same honest incompleteness as `verified_reduce_proj_step_
/// full`), extract its `BigUint` value, add one, and reconstruct.
///
/// Does NOT model the outer dispatch (`Some(name) == self.ctx.export_
/// file.name_cache.nat_succ`, i.e. "is this application's head actually
/// the `Nat.succ` constant") -- that's a real-`Env`/`export_file`-config
/// lookup, a separate piece of plumbing from the arithmetic content this
/// models. Callers are expected to have already established `arg` is
/// `Nat.succ`'s argument by other means; this only proves the succ
/// computation itself sound.
///
/// The result is a genuine `pstep_star` fact (from `verified_whnf_step`)
/// PLUS a real `BigUint`-arithmetic fact (`nat_lit_value(r) == nat_lit_
/// value(v) + 1`, via `nat_lit_model.rs`'s `biguint_succ`/`to_nat` trust
/// boundary) -- the first bridge in this codebase connecting `whnf`
/// composition to the nat-literal kernel extension at all.
pub fn verified_try_reduce_nat_succ_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, arg: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(arg)) <= 0,
        max_var_below(to_model(arg), bound),
        depth(to_model(arg)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |v: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(arg), to_model(v))
            && is_nat_lit_shape(v)
            && is_nat_lit_shape(r)
            && nat_lit_value(r) == nat_lit_value(v) + 1,
        None => true,
    }
{
    let v_expr = match verified_whnf_step(ctx, env, arg, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let v_el = ctx.read_expr(v_expr);
    let ptr = match expr_as_nat_lit(v_expr, &v_el) {
        Some(p) => p,
        None => return None,
    };
    let bn = match read_bignum_value(ctx, ptr) {
        Some(b) => b,
        None => return None,
    };
    let succ_bn = biguint_succ(bn);
    ctx.mk_nat_lit_quick(succ_bn)
}

/// `tc.rs::do_nat_bin`'s `Add` case (`tc.rs:372-375`): whnf BOTH operands
/// (via `verified_whnf_step`, one round each), extract their `BigUint`
/// values, add via the now-bridged `biguint_add`, reconstruct. Same
/// honest scope as `verified_try_reduce_nat_succ_step`: doesn't model
/// `try_reduce_nat`'s outer dispatch (matching `x`/`y`'s head against a
/// specific `NatBinOp`-cached constant name).
pub fn verified_do_nat_bin_add_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy) && is_nat_lit_shape(r)
            && nat_lit_value(r) == nat_lit_value(vx) + nat_lit_value(vy),
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let sum = biguint_add(bx, by);
    ctx.mk_nat_lit_quick(sum)
}

/// `tc.rs::do_nat_bin`'s `Mul` case (`tc.rs:377`), same shape as `Add`.
pub fn verified_do_nat_bin_mul_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy) && is_nat_lit_shape(r)
            && nat_lit_value(r) == nat_lit_value(vx) * nat_lit_value(vy),
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let prod = biguint_mul(bx, by);
    ctx.mk_nat_lit_quick(prod)
}

/// `tc.rs::do_nat_bin`'s `Sub` case (`tc.rs:376`): Lean's `Nat.sub`
/// saturates at zero rather than underflowing -- `crate::util::nat_sub`
/// (bridged in `nat_lit_model.rs`, an earlier session's work) already
/// proves this branching correct; this composes it with `verified_whnf_
/// step` the same way `Add`/`Mul` do.
pub fn verified_do_nat_bin_sub_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy) && is_nat_lit_shape(r)
            && nat_lit_value(r) == if nat_lit_value(vy) > nat_lit_value(vx) { 0 } else { (nat_lit_value(vx) - nat_lit_value(vy)) as nat },
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let diff = nat_sub(bx, by);
    ctx.mk_nat_lit_quick(diff)
}

/// `tc.rs::do_nat_bin`'s `Div` case (`tc.rs:379`): Lean's `Nat.div`
/// defines division by zero as `0` -- `crate::util::nat_div` (bridged in
/// `nat_lit_model.rs`) already proves this branching correct.
pub fn verified_do_nat_bin_div_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy) && is_nat_lit_shape(r)
            && nat_lit_value(r) == if nat_lit_value(vy) == 0 { 0 } else { (nat_lit_value(vx) / nat_lit_value(vy)) as nat },
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let quot = nat_div(bx, by);
    ctx.mk_nat_lit_quick(quot)
}

/// `tc.rs::do_nat_bin`'s `Mod` case (`tc.rs:380`): Lean's `Nat.mod`
/// defines mod by zero as the dividend -- `crate::util::nat_mod`
/// (bridged in `nat_lit_model.rs`) already proves this branching correct.
pub fn verified_do_nat_bin_mod_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy) && is_nat_lit_shape(r)
            && nat_lit_value(r) == if nat_lit_value(vy) == 0 { nat_lit_value(vx) } else { (nat_lit_value(vx) % nat_lit_value(vy)) as nat },
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let rem = nat_mod(bx, by);
    ctx.mk_nat_lit_quick(rem)
}

/// Manual transcription of `tc.rs::reduce_quot`'s CORE reduction content
/// (`tc.rs:1104-1130`) -- the quot-iota rule: once `qmk_arg` whnf's to a
/// saturated 3-argument application of `Quot.mk`, `Quot.lift`/`Quot.ind`
/// applied to it reduce to `f` applied to `Quot.mk`'s third argument
/// (the "underlying" value), refolded with whatever args came after the
/// `qmk`/`f` positions in the original application.
///
/// Does NOT model the OUTER dispatch real `reduce_quot` does first
/// (checking `c_name` is actually a `Declar::Quot`, matching it against
/// `name_cache.quot_lift`/`quot_ind` to pick WHICH argument position is
/// `qmk` vs `rest_idx` vs `f`) -- same scoping choice as `try_reduce_
/// nat`'s bridges this session: that's a separate `Env`/config lookup
/// from the reduction's actual computational content, which is what this
/// models. Callers are expected to have already picked out `qmk_arg`
/// (the un-whnf'd `Quot.mk`-application argument), `f` (`args[3]` in
/// BOTH the `lift` and `ind` cases -- the one thing shared between them),
/// and `rest` (whatever args came after) by other means.
///
/// New reduction rule, same category as `pstep_star_proj` (proj-iota):
/// genuinely not a `pstep` disjunct (constant identity is an `Env`-
/// adjacent, not `ExprSpec`-level, fact) -- but unlike `pstep_star_proj`,
/// stated directly in this function's own `ensures` rather than as a
/// separately-named relation, since nothing else needs to refer to it yet.
pub fn verified_reduce_quot_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, qmk_arg: ExprPtr<'t>, quot_mk_name: NamePtr<'t>, f: ExprPtr<'t>, rest: &[ExprPtr<'t>], fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(qmk_arg)) <= 0,
        max_var_below(to_model(qmk_arg), bound),
        depth(to_model(qmk_arg)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |reduced: ExprSpec, levels: Vec<LevelSpec>, qmk_args: Seq<ExprSpec>|
            pstep_star(to_model_of_env(*env), to_model(qmk_arg), reduced)
            && reduced == spine_app(ExprSpec::Const(name_id(quot_mk_name), levels), qmk_args)
            && qmk_args.len() == 3
            && to_model(r) == spine_app(
                ExprSpec::App(Box::new(to_model(f)), Box::new(qmk_args[2])),
                Seq::new(rest@.len(), |i: int| to_model(rest@[i])),
            ),
        None => true,
    }
{
    let qmk = match verified_whnf_step(ctx, env, qmk_arg, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let (qmk_const, qmk_args) = match verified_unfold_apps(ctx, qmk, fuel) {
        Some(p) => p,
        None => return None,
    };
    if qmk_args.len() != 3 {
        return None;
    }
    let qmk_const_el = ctx.read_expr(qmk_const);
    let (name, _levels) = match expr_as_const(qmk_const, &qmk_const_el) {
        Some(p) => p,
        None => return None,
    };
    if !name_ptr_eq(name, quot_mk_name) {
        return None;
    }
    let qmk_el = ctx.read_expr(qmk);
    let (_qmk_fun, arg) = match expr_as_app(&qmk_el) {
        Some(p) => p,
        None => return None,
    };
    let appd = ctx.mk_app(f, arg);
    let result = verified_foldl_apps(ctx, appd, rest);
    proof {
        is_const_shape_model(qmk_const);
        const_levels_vec_model(qmk_const);
        assert(name == quot_mk_name);
        assert(const_id(qmk_const) == name_id(quot_mk_name));
        let ghost qmk_args_model = Seq::new(qmk_args@.len(), |i: int| to_model(qmk_args@[i]));
        assert(to_model(qmk) == spine_app(to_model(qmk_const), qmk_args_model));
        assert(to_model(qmk_const) == ExprSpec::Const(const_id(qmk_const), const_levels_vec(qmk_const)));
        assert(to_model(qmk) == spine_app(ExprSpec::Const(name_id(quot_mk_name), const_levels_vec(qmk_const)), qmk_args_model));
        assert(qmk_args_model.len() == 3);
        assert(qmk_args_model == qmk_args_model.subrange(0, 2) + seq![qmk_args_model[2]]);
        assert(spine_app(to_model(qmk_const), qmk_args_model)
            == ExprSpec::App(Box::new(spine_app(to_model(qmk_const), qmk_args_model.subrange(0, 2))), Box::new(qmk_args_model[2])));
        assert(to_model(qmk) == ExprSpec::App(Box::new(spine_app(to_model(qmk_const), qmk_args_model.subrange(0, 2))), Box::new(qmk_args_model[2])));
        assert(to_model(qmk) == ExprSpec::App(Box::new(to_model(_qmk_fun)), Box::new(to_model(arg))));
        assert(to_model(arg) == qmk_args_model[2]);
        assert(to_model(appd) == ExprSpec::App(Box::new(to_model(f)), Box::new(to_model(arg))));
        assert(to_model(result) == spine_app(to_model(appd), Seq::new(rest@.len(), |i: int| to_model(rest@[i]))));
        assert(pstep_star(to_model_of_env(*env), to_model(qmk_arg), to_model(qmk)));
    }
    Some(result)
}

/// The CORE composition inside `tc.rs::reduce_rec` (`tc.rs:1098-1101`):
/// once the matching computation rule (`rec_rule`) for the major
/// premise's constructor has been found, its value gets the recursor's
/// own universe-level arguments substituted in, then gets refolded with
/// THREE separate argument groups in sequence -- the recursor's own
/// leading params/motives/minors, the major premise constructor's own
/// (params-stripped) arguments, and whatever args came after the major
/// premise in the original application.
///
/// Deliberately scoped to just this composition -- the trickiest
/// arithmetic piece, and the one with no precedent yet in this codebase
/// (`verified_unfold_def_step` only ever needed ONE `foldl_apps`, not
/// three in sequence) -- NOT the surrounding prelude (`whnf`-ing the
/// major premise, `unfold_apps` to expose its constructor head, `get_rec_
/// rule` to find `rec_rule`, `to_ctor_when_k`/`nat_lit_to_constructor`/
/// `str_lit_to_ctor_reducing`/`iota_try_eta_struct`'s special-case
/// conversions), all of which are either already-verified building
/// blocks this doesn't re-derive (`verified_whnf_step`, `verified_get_
/// rec_rule`/`verified_find_rec_rule`) or not yet modeled at all (the K-
/// reduction/structure-eta/literal-to-constructor conversions). Composing
/// this with those pieces into a single `verified_reduce_rec_step` is
/// real remaining work, not attempted this session.
///
/// Unlike `verified_reduce_proj_step`/`verified_reduce_quot_step`, this
/// is NOT wrapped in a `pstep_star`-style reduction-soundness claim --
/// same reason `get_rec_rule`'s own doc comment gives for why it's a
/// manual TRANSCRIPTION rather than a reduction rule: there's no existing,
/// independently-motivated notion of "recursor iota reduction" in this
/// codebase to relate the computation to (unlike proj/quot-iota, which
/// this session defined as clean, self-evidently-correct new relations).
/// This proves the computation matches a precisely-stated FORMULA, which
/// is the same value proposition `get_rec_rule` itself already has: a bug
/// in transcribing this composition would make the type checker apply
/// the wrong reduction, a real soundness hole, independent of whether
/// it's phrased as a `pstep_star` fact.
pub fn verified_reduce_rec_core<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    rec_rule_val: ExprPtr<'t>,
    uparams: LevelsPtr<'t>,
    const_levels: LevelsPtr<'t>,
    prefix_args: &[ExprPtr<'t>],
    ctor_args_wo_params: &[ExprPtr<'t>],
    post_args: &[ExprPtr<'t>],
    fuel: u32,
) -> (result: Option<ExprPtr<'t>>)
    requires
        to_model_of_levels(uparams).len() == to_model_of_levels(const_levels).len(),
        forall |j: int| 0 <= j < to_model_of_levels(uparams).len() ==> #[trigger] to_model_of_levels(uparams)[j] is Param,
    ensures match result {
        Some(r) => exists |subst_val: ExprSpec|
            subst_expr_levels_rel(
                to_model(rec_rule_val),
                level_names(to_model_of_levels(uparams)),
                to_model_of_levels(const_levels),
                subst_val,
            )
            && to_model(r) == spine_app(
                spine_app(
                    spine_app(subst_val, Seq::new(prefix_args@.len(), |i: int| to_model(prefix_args@[i]))),
                    Seq::new(ctor_args_wo_params@.len(), |i: int| to_model(ctor_args_wo_params@[i])),
                ),
                Seq::new(post_args@.len(), |i: int| to_model(post_args@[i])),
            ),
        None => true,
    }
{
    match verified_subst_expr_levels(ctx, rec_rule_val, uparams, const_levels, fuel) {
        Some(subst_val) => {
            let r1 = verified_foldl_apps(ctx, subst_val, prefix_args);
            let r2 = verified_foldl_apps(ctx, r1, ctor_args_wo_params);
            let r3 = verified_foldl_apps(ctx, r2, post_args);
            Some(r3)
        }
        None => None,
    }
}

/// Glues `verified_reduce_rec_core`'s composition to the real `Env`
/// lookup (`get_recursor_data`, `env_model.rs`) and the prelude
/// `reduce_rec` performs first: `whnf` the major premise (`verified_
/// whnf_step`, one round -- same honest incompleteness as elsewhere this
/// session), peel its applied-`Const` head, and find the matching
/// computation rule (`verified_find_rec_rule`, an earlier session's
/// work). Still does NOT model `to_ctor_when_k`/`nat_lit_to_constructor`/
/// `str_lit_to_ctor_reducing`/`iota_try_eta_struct`'s special-case
/// conversions -- if the major premise's `whnf` doesn't ALREADY directly
/// expose a matching constructor `Const` head (no K-reduction, literal
/// conversion, or structure-eta needed), this returns `None`
/// conservatively rather than the real function's fuller behavior.
///
/// `major_idx`/`num_params`/`num_motives`/`num_minors` come from `get_
/// recursor_data`, used only for REAL slicing (`args.get`/`args[..]`) --
/// no separate model fact is needed for them, since (like `get_rec_rule`)
/// this isn't claiming a `pstep_star`-style reduction-soundness fact for
/// the WHOLE step, only that the composition matches a precisely-stated
/// formula (the same value proposition `verified_reduce_rec_core` itself
/// already has), PLUS a genuine `pstep_star` fact for the major premise's
/// own reduction to whnf.
pub fn verified_reduce_rec_step<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    const_name: NamePtr<'t>,
    const_levels: LevelsPtr<'t>,
    args: &[ExprPtr<'t>],
    fuel: u32,
    bound: nat,
    d: nat,
    n: u32,
) -> (result: Option<ExprPtr<'t>>)
    requires
        forall |i: int| 0 <= i < args@.len() ==>
            nlbv(to_model(args@[i])) <= 0 && max_var_below(to_model(args@[i]), bound) && depth(to_model(args@[i])) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |major_idx: nat, reduced_major: ExprSpec, ctor_id: u64, levels: Vec<LevelSpec>, ctor_args: Seq<ExprSpec>, rec_rule_val: ExprSpec, ks: Seq<u64>, subst_val: ExprSpec, num_extra: nat, prefix_len: nat|
            #![trigger pstep_star(to_model_of_env(*env), to_model(args@[major_idx as int]), reduced_major), spine_app(ExprSpec::Const(ctor_id, levels), ctor_args), subst_expr_levels_rel(rec_rule_val, ks, to_model_of_levels(const_levels), subst_val), ctor_args.subrange(num_extra as int, ctor_args.len() as int), args_model_of(args@).subrange(0, prefix_len as int)]
            major_idx < args@.len()
            && pstep_star(to_model_of_env(*env), to_model(args@[major_idx as int]), reduced_major)
            && reduced_major == spine_app(ExprSpec::Const(ctor_id, levels), ctor_args)
            && num_extra <= ctor_args.len()
            && prefix_len <= args_model_of(args@).len()
            && subst_expr_levels_rel(rec_rule_val, ks, to_model_of_levels(const_levels), subst_val)
            && to_model(r) == spine_app(
                spine_app(
                    spine_app(subst_val, args_model_of(args@).subrange(0, prefix_len as int)),
                    ctor_args.subrange(num_extra as int, ctor_args.len() as int),
                ),
                args_model_of(args@).subrange((major_idx + 1) as int, args@.len() as int),
            ),
        None => true,
    }
{
    let (num_params, num_motives, num_minors, major_idx, uparams, rec_rules) = match get_recursor_data(env, &const_name) {
        Some(p) => p,
        None => return None,
    };
    if major_idx >= args.len() {
        return None;
    }
    let major_arg = args[major_idx];
    let major = match verified_whnf_step(ctx, env, major_arg, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let (major_ctor, major_ctor_args) = match verified_unfold_apps(ctx, major, fuel) {
        Some(p) => p,
        None => return None,
    };
    let major_ctor_el = ctx.read_expr(major_ctor);
    let (major_ctor_name, _levels) = match expr_as_const(major_ctor, &major_ctor_el) {
        Some(p) => p,
        None => return None,
    };
    let rec_rule = match verified_find_rec_rule(&rec_rules, major_ctor_name) {
        Some(rr) => rr,
        None => return None,
    };
    let telescope_size = rec_rule_ctor_telescope_size_wo_params(&rec_rule);
    let num_extra_params_to_major = match major_ctor_args.len().checked_sub(telescope_size as usize) {
        Some(k) => k,
        None => return None,
    };
    // NOTE: `RangeTo`/`RangeFrom` slice indexing (`&s[..n]`/`&s[n..]`) does
    // not reliably discharge its precondition in this Verus/vstd fork,
    // confirmed via an isolated minimal repro completely independent of
    // this function (reproduces even for `&args[..0]` with NO other
    // preconditions involved). Full `Range<usize>` syntax (`&s[a..b]`,
    // matching e.g. `verified_whnf_beta_step`'s own established slicing)
    // verifies fine -- used throughout below for exactly that reason.
    let major_ctor_args_wo_params = &major_ctor_args[num_extra_params_to_major..major_ctor_args.len()];
    let num_prefix = (num_params as usize) + (num_motives as usize) + (num_minors as usize);
    if num_prefix > args.len() {
        return None;
    }
    let prefix_args = &args[0..num_prefix];
    let post_args = &args[(major_idx + 1)..args.len()];
    let rule_val = rec_rule_val(&rec_rule);
    let uparams_vec = read_levels_vec(ctx, uparams);
    let const_levels_vec_local = read_levels_vec(ctx, const_levels);
    if uparams_vec.len() != const_levels_vec_local.len() {
        return None;
    }
    assert(to_model_of_levels(uparams).len() == to_model_of_levels(const_levels).len());
    match verified_reduce_rec_core(ctx, rule_val, uparams, const_levels, prefix_args, major_ctor_args_wo_params, post_args, fuel) {
        Some(r) => {
            proof {
                is_const_shape_model(major_ctor);
                const_levels_vec_model(major_ctor);
                let ghost ctor_args_model = args_model_of(major_ctor_args@);
                assert(to_model(major) == spine_app(ExprSpec::Const(const_id(major_ctor), const_levels_vec(major_ctor)), ctor_args_model));
                assert(pstep_star(to_model_of_env(*env), to_model(args@[major_idx as int]), to_model(major)));
                assert(major_ctor_args_wo_params@ =~= major_ctor_args@.subrange(num_extra_params_to_major as int, major_ctor_args@.len() as int));
                assert(prefix_args@ =~= args@.subrange(0, num_prefix as int));
                assert(post_args@ =~= args@.subrange((major_idx + 1) as int, args@.len() as int));
                let ghost subst_val = choose |sv: ExprSpec|
                    subst_expr_levels_rel(
                        to_model(rule_val),
                        level_names(to_model_of_levels(uparams)),
                        to_model_of_levels(const_levels),
                        sv,
                    )
                    && to_model(r) == spine_app(
                        spine_app(
                            spine_app(sv, args_model_of(prefix_args@)),
                            args_model_of(major_ctor_args_wo_params@),
                        ),
                        args_model_of(post_args@),
                    );
                assert(args_model_of(prefix_args@) =~= args_model_of(args@).subrange(0, num_prefix as int));
                assert(args_model_of(post_args@) =~= args_model_of(args@).subrange((major_idx + 1) as int, args@.len() as int));
                assert(args_model_of(major_ctor_args_wo_params@)
                    =~= ctor_args_model.subrange(num_extra_params_to_major as int, ctor_args_model.len() as int));
                assert((major_idx as nat) < args@.len());
                assert((num_extra_params_to_major as nat) <= ctor_args_model.len());
                assert((num_prefix as nat) <= args_model_of(args@).len());
                assert(subst_expr_levels_rel(to_model(rule_val), level_names(to_model_of_levels(uparams)), to_model_of_levels(const_levels), subst_val));
                assert(to_model(r) == spine_app(
                    spine_app(
                        spine_app(subst_val, args_model_of(args@).subrange(0, num_prefix as int)),
                        ctor_args_model.subrange(num_extra_params_to_major as int, ctor_args_model.len() as int),
                    ),
                    args_model_of(args@).subrange((major_idx + 1) as int, args@.len() as int),
                ));
            }
            Some(r)
        }
        None => None,
    }
}

/// `tc.rs::do_nat_bin`'s `Beq` case (`tc.rs:387`): whnf both operands,
/// extract their `BigUint` values, compare via the now-bridged
/// `biguint_eq`, reconstruct via `bool_to_expr` (`expr_arena_bridge.rs`'s
/// `bool_true_id`/`bool_false_id` trust boundary) instead of `mk_nat_lit_
/// quick` -- the one shape difference from `Add`/`Sub`/etc. among this
/// session's `do_nat_bin` bridges, everything else identical.
pub fn verified_do_nat_bin_beq_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy)
            && is_const_shape(r)
            && const_id(r) == if nat_lit_value(vx) == nat_lit_value(vy) { bool_true_id() } else { bool_false_id() },
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let eq = biguint_eq(&bx, &by);
    ctx.bool_to_expr(eq)
}

/// `tc.rs::do_nat_bin`'s `Ble` case (`tc.rs:388`), same shape as `Beq`.
pub fn verified_do_nat_bin_ble_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy)
            && is_const_shape(r)
            && const_id(r) == if nat_lit_value(vx) <= nat_lit_value(vy) { bool_true_id() } else { bool_false_id() },
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let le = biguint_le(&bx, &by);
    ctx.bool_to_expr(le)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::def_eq_sort`
/// (`tc.rs:1165-1170`): `Sort(l) def_eq Sort(r) <=> eq_antisymm(l,r)` --
/// the one genuine LEAF of `def_eq`'s whole mutually-recursive cluster
/// (no further `def_eq` recursion inside it at all), and the first piece
/// of that cluster bridged. Was unreachable before `verified_leq`/
/// `verified_eq_antisymm` (previous commit) existed, since `eq_antisymm`
/// is exactly what this bottoms out in.
pub fn verified_def_eq_sort<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    ensures match result {
        Some(r) => exists |lx: LevelPtr<'t>, ly: LevelPtr<'t>|
            to_model(x) == ExprSpec::Sort(level_to_model(lx))
            && to_model(y) == ExprSpec::Sort(level_to_model(ly))
            && (r ==> forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(lx), rho) == interp(level_to_model(ly), rho)),
        None => true,
    }
{
    let x_el = ctx.read_expr(x);
    let lx = match expr_as_sort(&x_el) {
        Some(l) => l,
        None => return None,
    };
    let y_el = ctx.read_expr(y);
    let ly = match expr_as_sort(&y_el) {
        Some(l) => l,
        None => return None,
    };
    let r = verified_eq_antisymm(ctx, lx, ly, fuel);
    Some(r)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::def_eq_const`
/// (`tc.rs:920-926`): `Const(x_name,x_levels) def_eq Const(y_name,y_levels)
/// <=> x_name == y_name && eq_antisymm_many(x_levels,y_levels)` -- the
/// second leaf of `def_eq`'s cluster (again no further `def_eq` recursion
/// inside it), unlocked by `verified_eq_antisymm_many` (two commits back).
/// Name equality is real `NamePtr` pointer equality (`name_ptr_eq`), which
/// by `name_id_injective` gives `const_id(x) == const_id(y)` for free.
pub fn verified_def_eq_const<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32) -> (result: bool)
    ensures result ==> is_const_shape(x) && is_const_shape(y)
        && const_id(x) == const_id(y)
        && to_model_of_levels(const_levels_of(x)).len() == to_model_of_levels(const_levels_of(y)).len()
        && forall |i: int| #![trigger to_model_of_levels(const_levels_of(x))[i]] 0 <= i < to_model_of_levels(const_levels_of(x)).len() ==>
            forall |rho: Map<nat, nat>| #[trigger] interp(to_model_of_levels(const_levels_of(x))[i], rho) == interp(to_model_of_levels(const_levels_of(y))[i], rho)
{
    let x_el = ctx.read_expr(x);
    let (x_name, x_levels) = match expr_as_const(x, &x_el) {
        Some(p) => p,
        None => return false,
    };
    let y_el = ctx.read_expr(y);
    let (y_name, y_levels) = match expr_as_const(y, &y_el) {
        Some(p) => p,
        None => return false,
    };
    if !name_ptr_eq(x_name, y_name) {
        return false;
    }
    verified_eq_antisymm_many(ctx, x_levels, y_levels, fuel)
}

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
pub fn verified_def_eq_core<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    ensures match result {
        Some(true) =>
            (exists |lx: LevelPtr<'t>, ly: LevelPtr<'t>|
                to_model(x) == ExprSpec::Sort(level_to_model(lx))
                && to_model(y) == ExprSpec::Sort(level_to_model(ly))
                && forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(lx), rho) == interp(level_to_model(ly), rho))
            || (is_const_shape(x) && is_const_shape(y) && const_id(x) == const_id(y))
            || (is_local_shape(x) && is_local_shape(y) && local_id_of(x) == local_id_of(y))
            || (exists |sx: ExprPtr<'t>, sy: ExprPtr<'t>|
                to_model(x) == ExprSpec::Proj(Box::new(to_model(sx)))
                && to_model(y) == ExprSpec::Proj(Box::new(to_model(sy)))),
        _ => true,
    }
    decreases fuel
{
    if let Some(r) = verified_def_eq_sort(ctx, x, y, fuel) {
        if r {
            return Some(true);
        }
    }
    if verified_def_eq_const(ctx, x, y, fuel) {
        return Some(true);
    }
    let x_el = ctx.read_expr(x);
    if let Some((x_id, x_ty)) = expr_as_local(x, &x_el) {
        let y_el = ctx.read_expr(y);
        if let Some((y_id, y_ty)) = expr_as_local(y, &y_el) {
            if fvar_id_eq(x_id, y_id) {
                if fuel == 0 {
                    return None;
                }
                if let Some(true) = verified_def_eq_core(ctx, x_ty, y_ty, fuel - 1) {
                    return Some(true);
                }
                return Some(false);
            }
        }
        return Some(false);
    }
    if let Some((x_ty_name, x_idx, x_struct)) = expr_as_proj(&x_el) {
        let y_el = ctx.read_expr(y);
        if let Some((y_ty_name, y_idx, y_struct)) = expr_as_proj(&y_el) {
            if name_ptr_eq(x_ty_name, y_ty_name) && x_idx == y_idx {
                if fuel == 0 {
                    return None;
                }
                if let Some(true) = verified_def_eq_core(ctx, x_struct, y_struct, fuel - 1) {
                    return Some(true);
                }
            }
        }
        return Some(false);
    }
    Some(false)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::def_eq_app`
/// (`tc.rs:928-953`): both sides must unfold to a genuine (nonempty)
/// applied spine of matching arg count, every arg pair `def_eq`, and the
/// two heads `def_eq`. Unlike `def_eq_sort`/`def_eq_const`/`def_eq_local`/
/// `def_eq_proj` (all tried together right after `lazy_delta_step` is
/// exhausted, `tc.rs:982`), the real `def_eq_app` is a LATER, separate
/// stage of `def_eq` (only reached after a further `whnf_no_unfolding`
/// round confirms neither side reduces further, `tc.rs:986-990`) -- kept
/// as its own standalone bridge rather than folded into
/// `verified_def_eq_core`, for the same reason `verified_whnf_beta_step`/
/// `verified_whnf_zeta_step`/`verified_unfold_def_step` were built
/// separately before being composed into `verified_whnf_step`: each stage
/// bridges cleanly on its own, and composing them into a faithful
/// top-level `def_eq` is future work, not assumed here.
///
/// Every arg/head comparison routes through `verified_def_eq_core`, so
/// this can only certify args/heads related by the sort/const/local/proj
/// leaf cluster -- an arg that itself needs `def_eq_app` (nested
/// application equality) isn't covered, same honest incompleteness as
/// everywhere else in this arc (`None` = ran out of fuel before a
/// verdict, not "definitely unequal").
pub fn verified_def_eq_app<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    ensures match result {
        Some(true) => exists |fx: ExprPtr<'t>, fy: ExprPtr<'t>, argsx: Seq<ExprPtr<'t>>, argsy: Seq<ExprPtr<'t>>|
            to_model(x) == spine_app(to_model(fx), args_model_of(argsx))
            && to_model(y) == spine_app(to_model(fy), args_model_of(argsy))
            && argsx.len() == argsy.len() && argsx.len() > 0,
        _ => true,
    }
{
    let (f1, args1) = match verified_unfold_apps(ctx, x, fuel) {
        Some(p) => p,
        None => return None,
    };
    if args1.len() == 0 {
        return Some(false);
    }
    let (f2, args2) = match verified_unfold_apps(ctx, y, fuel) {
        Some(p) => p,
        None => return None,
    };
    if args2.len() == 0 {
        return Some(false);
    }
    if args1.len() != args2.len() {
        return Some(false);
    }
    let mut i: usize = 0;
    while i < args1.len()
        invariant
            i <= args1.len(),
            args1.len() == args2.len(),
        decreases args1.len() - i
    {
        match verified_def_eq_core(ctx, args1[i], args2[i], fuel) {
            Some(true) => {},
            Some(false) => { return Some(false); },
            None => { return None; },
        }
        i += 1;
    }
    match verified_def_eq_core(ctx, f1, f2, fuel) {
        Some(true) => {
            assert(to_model(x) == spine_app(to_model(f1), args_model_of(args1@)));
            assert(to_model(y) == spine_app(to_model(f2), args_model_of(args2@)));
            assert(args1@.len() == args2@.len());
            assert(args1@.len() > 0);
            Some(true)
        },
        Some(false) => Some(false),
        None => None,
    }
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
pub fn verified_def_eq<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    requires
        depth(to_model(x)) <= 60000,
        depth(to_model(y)) <= 60000,
    ensures match result {
        Some(true) =>
            to_model(x) == to_model(y)
            || (exists |lx: LevelPtr<'t>, ly: LevelPtr<'t>|
                to_model(x) == ExprSpec::Sort(level_to_model(lx))
                && to_model(y) == ExprSpec::Sort(level_to_model(ly))
                && forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(lx), rho) == interp(level_to_model(ly), rho))
            || (is_const_shape(x) && is_const_shape(y) && const_id(x) == const_id(y))
            || (is_local_shape(x) && is_local_shape(y) && local_id_of(x) == local_id_of(y))
            || (exists |sx: ExprPtr<'t>, sy: ExprPtr<'t>|
                to_model(x) == ExprSpec::Proj(Box::new(to_model(sx)))
                && to_model(y) == ExprSpec::Proj(Box::new(to_model(sy))))
            || (exists |fx: ExprPtr<'t>, fy: ExprPtr<'t>, argsx: Seq<ExprPtr<'t>>, argsy: Seq<ExprPtr<'t>>|
                to_model(x) == spine_app(to_model(fx), args_model_of(argsx))
                && to_model(y) == spine_app(to_model(fy), args_model_of(argsy))
                && argsx.len() == argsy.len() && argsx.len() > 0)
            || (exists |t1: ExprPtr<'t>, body1: ExprPtr<'t>, t2: ExprPtr<'t>, body2: ExprPtr<'t>|
                to_model(x) == ExprSpec::Bind(Box::new(to_model(t1)), Box::new(to_model(body1)))
                && to_model(y) == ExprSpec::Bind(Box::new(to_model(t2)), Box::new(to_model(body2)))),
        _ => true,
    }
    decreases fuel
{
    if expr_ptr_eq(x, y) {
        return Some(true);
    }
    match verified_def_eq_core(ctx, x, y, fuel) {
        Some(true) => return Some(true),
        Some(false) => {},
        None => return None,
    }
    if fuel == 0 {
        return None;
    }
    match verified_def_eq_binder_step(ctx, x, y, fuel - 1) {
        Some(true) => return Some(true),
        Some(false) => {},
        None => return None,
    }
    verified_def_eq_app(ctx, x, y, fuel)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::def_eq_binder_aux`'s
/// FULL telescoping loop (`tc.rs:873-901`, called from `def_eq_binder_
/// multi`, `tc.rs:864-870`): peels every matching Pi/Pi or Lambda/Lambda
/// binder layer in sequence (curried types like `A -> B -> C` peel THREE
/// times, not just once), opening each with a fresh local (`mk_dbj_
/// level`), checking each layer's (instantiated) binder types `def_eq`,
/// then finally checking the (instantiated) trailing bodies `def_eq`
/// once no more matching binder layers remain.
///
/// An earlier version of this function only peeled ONE layer, reasoning
/// that telescoping would need a NEW freshness/distinctness trust
/// boundary for `mk_dbj_level` (to justify that multiple fresh locals
/// don't alias). That reasoning was too cautious: every fact this bridge
/// states is purely STRUCTURAL (shape and `depth`), never dependent on
/// distinctness -- `verified_inst`'s own contract doesn't care whether
/// `substs` contains repeated/aliased values, it substitutes by position
/// regardless. What telescoping genuinely needs is just a termination
/// argument for the loop, which falls out for free: every substituted
/// local has `depth == 0` (via `ExprSpec::Free`'s depth formula, see
/// `mk_dbj_level`'s own doc comment), so `subst_full_depth_bound_n` gives
/// `depth(inst(body, locals)) <= depth(body) + 0 == depth(body)` --
/// instantiation NEVER grows depth when every substituted value has depth
/// 0, at ANY accumulated `locals` length -- and the RAW (uninstantiated)
/// next-iteration body is always strictly SHALLOWER than the current
/// term (`depth(Bind(t,b)) == 1 + max(depth(t),depth(b)) > depth(b)`), so
/// `depth(to_model(cur_x))` is a genuine, always-decreasing loop measure.
///
/// The ensures is proven once, from the FIRST binder layer only (which
/// `def_eq_binder_multi`'s own gate guarantees exists) -- since
/// `to_model(x)`/`to_model(y)` never change, nothing about LATER layers
/// needs to be threaded through the loop's own invariants.
///
/// Wired into `verified_def_eq`'s own dispatch (mirrors `def_eq_binder_
/// multi` being tried inside `def_eq_quick_check`). Every call into
/// `verified_def_eq` (one per binder layer, plus the final trailing-body
/// check) uses a strictly decreasing `fuel_left < fuel`, so `verified_
/// def_eq`'s own `decreases fuel` clause is satisfied at every one of
/// these mutually-recursive call sites, not just once.
#[allow(while_true)]
pub fn verified_def_eq_binder_step<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    requires
        depth(to_model(x)) <= 60000,
        depth(to_model(y)) <= 60000,
    ensures match result {
        Some(true) => exists |t1: ExprPtr<'t>, body1: ExprPtr<'t>, t2: ExprPtr<'t>, body2: ExprPtr<'t>|
            to_model(x) == ExprSpec::Bind(Box::new(to_model(t1)), Box::new(to_model(body1)))
            && to_model(y) == ExprSpec::Bind(Box::new(to_model(t2)), Box::new(to_model(body2))),
        _ => true,
    }
    decreases fuel
{
    let x_el = ctx.read_expr(x);
    let y_el = ctx.read_expr(y);
    let first: Option<(NamePtr<'t>, BinderStyle, ExprPtr<'t>, ExprPtr<'t>, ExprPtr<'t>, ExprPtr<'t>)> =
        if let Some((name, style, t1, body1)) = expr_as_pi(&x_el) {
            match expr_as_pi(&y_el) {
                Some((_, _, t2, body2)) => Some((name, style, t1, body1, t2, body2)),
                None => None,
            }
        } else if let Some((name, style, t1, body1)) = expr_as_lambda(&x_el) {
            match expr_as_lambda(&y_el) {
                Some((_, _, t2, body2)) => Some((name, style, t1, body1, t2, body2)),
                None => None,
            }
        } else {
            None
        };
    let (name, style, t1, body1, t2, body2) = match first {
        Some(p) => p,
        None => return None,
    };
    // Ensures witness established here, from the FIRST layer only --
    // to_model(x)/to_model(y) never change again below.
    assert(depth(to_model(t1)) <= 60000);
    assert(depth(to_model(t2)) <= 60000);
    let empty_substs: &[ExprPtr<'t>] = &[];
    let t1i = match verified_inst(ctx, t1, empty_substs, 0, fuel) {
        Some(v) => v,
        None => return None,
    };
    let t2i = match verified_inst(ctx, t2, empty_substs, 0, fuel) {
        Some(v) => v,
        None => return None,
    };
    proof {
        subst_full_depth_bound_n(to_model(t1), Seq::new(empty_substs@.len(), |i: int| to_model(empty_substs@[i])), 0, 0);
        subst_full_depth_bound_n(to_model(t2), Seq::new(empty_substs@.len(), |i: int| to_model(empty_substs@[i])), 0, 0);
    }
    let mut fuel_left = fuel;
    if fuel_left == 0 {
        return None;
    }
    fuel_left = fuel_left - 1;
    if verified_def_eq(ctx, t1i, t2i, fuel_left) != Some(true) {
        return Some(false);
    }
    let local = ctx.mk_dbj_level(name, style, t1i);
    assert(depth(to_model(local)) == 0);
    assert(depth(to_model(body1)) <= 60000);
    assert(depth(to_model(body2)) <= 60000);

    let mut locals: Vec<ExprPtr<'t>> = Vec::new();
    locals.push(local);
    let mut cur_x = body1;
    let mut cur_y = body2;

    // Telescoping loop: peel additional Pi/Pi or Lambda/Lambda layers,
    // one fresh local per layer, until neither side matches anymore.
    while true
        invariant
            depth(to_model(cur_x)) <= 60000,
            depth(to_model(cur_y)) <= 60000,
            forall |i: int| 0 <= i < locals@.len() ==> #[trigger] depth(to_model(locals@[i])) == 0,
            fuel_left < fuel,
        decreases depth(to_model(cur_x))
    {
        let cx_el = ctx.read_expr(cur_x);
        let cy_el = ctx.read_expr(cur_y);
        let next: Option<(NamePtr<'t>, BinderStyle, ExprPtr<'t>, ExprPtr<'t>, ExprPtr<'t>, ExprPtr<'t>)> =
            if let Some((n, s, nt1, nb1)) = expr_as_pi(&cx_el) {
                match expr_as_pi(&cy_el) {
                    Some((_, _, nt2, nb2)) => Some((n, s, nt1, nb1, nt2, nb2)),
                    None => None,
                }
            } else if let Some((n, s, nt1, nb1)) = expr_as_lambda(&cx_el) {
                match expr_as_lambda(&cy_el) {
                    Some((_, _, nt2, nb2)) => Some((n, s, nt1, nb1, nt2, nb2)),
                    None => None,
                }
            } else {
                None
            };
        let (n, s, nt1, nb1, nt2, nb2) = match next {
            Some(p) => p,
            None => break,
        };
        assert(depth(to_model(nt1)) <= 60000);
        assert(depth(to_model(nt2)) <= 60000);
        let nt1i = match verified_inst(ctx, nt1, locals.as_slice(), 0, fuel) {
            Some(v) => v,
            None => return None,
        };
        let nt2i = match verified_inst(ctx, nt2, locals.as_slice(), 0, fuel) {
            Some(v) => v,
            None => return None,
        };
        proof {
            let substs_model: Seq<ExprSpec> = Seq::new(locals@.len(), |i: int| to_model(locals@[i]));
            subst_full_depth_bound_n(to_model(nt1), substs_model, 0, 0);
            subst_full_depth_bound_n(to_model(nt2), substs_model, 0, 0);
        }
        if fuel_left == 0 {
            return None;
        }
        fuel_left = fuel_left - 1;
        if verified_def_eq(ctx, nt1i, nt2i, fuel_left) != Some(true) {
            return Some(false);
        }
        let nlocal = ctx.mk_dbj_level(n, s, nt1i);
        assert(depth(to_model(nlocal)) == 0);
        assert(depth(to_model(nb1)) <= 60000);
        assert(depth(to_model(nb2)) <= 60000);
        locals.push(nlocal);
        cur_x = nb1;
        cur_y = nb2;
    }

    let cxi = match verified_inst(ctx, cur_x, locals.as_slice(), 0, fuel) {
        Some(v) => v,
        None => return None,
    };
    let cyi = match verified_inst(ctx, cur_y, locals.as_slice(), 0, fuel) {
        Some(v) => v,
        None => return None,
    };
    proof {
        let substs_model: Seq<ExprSpec> = Seq::new(locals@.len(), |i: int| to_model(locals@[i]));
        subst_full_depth_bound_n(to_model(cur_x), substs_model, 0, 0);
        subst_full_depth_bound_n(to_model(cur_y), substs_model, 0, 0);
    }
    if fuel_left == 0 {
        return None;
    }
    fuel_left = fuel_left - 1;
    verified_def_eq(ctx, cxi, cyi, fuel_left)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::def_eq_nat`
/// (`tc.rs:849-862`) -- the first piece of `lazy_delta_step`'s own
/// `delta_try_nat` sub-check (`tc.rs:1250-1262`), and independently
/// scoped since (unlike everything else `lazy_delta_step` touches) it
/// needs no new subsystem: `is_nat_zero`/`pred_of_nat_succ` are plain
/// shape/value checks, not `infer`-dependent. Three cases, mirroring the
/// real function exactly: both sides are SOME representation of zero
/// (`NatLit` valued 0, or the cached `Const Nat.zero []`); both sides are
/// `NatLit`s (compared by real pointer equality, matching hash-consing --
/// `x == y` in the real code); or both sides have a `Nat` predecessor
/// (peeling `Nat.succ` or decrementing a nonzero `NatLit`), recursing via
/// `verified_def_eq` on the two predecessors. NOT yet wired into `lazy_
/// delta_step`'s own composition (that needs `try_reduce_nat` too, for
/// `delta_try_nat`'s second half) -- standalone for now, same "build the
/// piece, wire it in later" pattern as `verified_def_eq_app`/`_binder_
/// step` originally were.
pub fn verified_def_eq_nat<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    requires
        depth(to_model(x)) <= 60000,
        depth(to_model(y)) <= 60000,
    ensures match result {
        Some(true) =>
            (nat_repr_is_zero(x) && nat_repr_is_zero(y))
            || (is_nat_lit_shape(x) && is_nat_lit_shape(y) && to_model(x) == to_model(y))
            || (exists |xp: ExprPtr<'t>, yp: ExprPtr<'t>| nat_repr_pred(x, xp) && nat_repr_pred(y, yp)),
        _ => true,
    }
    decreases fuel
{
    if ctx.is_nat_zero(x) && ctx.is_nat_zero(y) {
        return Some(true);
    }
    let x_el = ctx.read_expr(x);
    let y_el = ctx.read_expr(y);
    if expr_as_nat_lit(x, &x_el).is_some() && expr_as_nat_lit(y, &y_el).is_some() {
        return Some(expr_ptr_eq(x, y));
    }
    let x_pred = ctx.pred_of_nat_succ(x);
    let y_pred = ctx.pred_of_nat_succ(y);
    match (x_pred, y_pred) {
        (Some(xp), Some(yp)) => {
            assert(depth(to_model(xp)) <= 60000) by {
                if is_nat_lit_shape(xp) {
                    is_nat_lit_shape_model(xp);
                }
            }
            assert(depth(to_model(yp)) <= 60000) by {
                if is_nat_lit_shape(yp) {
                    is_nat_lit_shape_model(yp);
                }
            }
            if fuel == 0 {
                return None;
            }
            verified_def_eq(ctx, xp, yp, fuel - 1)
        }
        _ => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::get_applied_def`
/// (`tc.rs:1133-1142`) -- the SECOND piece of `lazy_delta_step`'s
/// machinery (alongside `verified_def_eq_nat`), and the one that decides
/// which side of `x`/`y` is "further" from being fully unfolded. Peels
/// the applied spine (`verified_unfold_apps`), checks the head is a real
/// `Const`, then looks up its reducibility hint via `get_declar_hint`
/// (`env_model.rs`, new this commit) -- `None` covers both "not an
/// applied Const at all" and "that Const isn't a Definition/Theorem"
/// (e.g. it's an Axiom, Inductive, Constructor, ...), matching the real
/// function's own single `Option` return exactly.
pub fn verified_get_applied_def<'t, 'p: 't, 'x>(ctx: &TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32) -> (result: Option<(NamePtr<'t>, ReducibilityHint)>)
    ensures match result {
        Some((_, hint)) =>
            exists |fun: ExprPtr<'t>, args: Seq<ExprPtr<'t>>|
                to_model(e) == spine_app(to_model(fun), args_model_of(args))
                && is_const_shape(fun)
                && to_model_of_declar_hint(*env).contains_key(const_id(fun))
                && to_model_of_declar_hint(*env)[const_id(fun)] == reducibility_hint_to_model(hint),
        None => true,
    }
{
    let (fun, _args) = match verified_unfold_apps(ctx, e, fuel) {
        Some(p) => p,
        None => return None,
    };
    let fun_el = ctx.read_expr(fun);
    let (name, _levels) = match expr_as_const(fun, &fun_el) {
        Some(p) => p,
        None => return None,
    };
    match get_declar_hint(env, &name) {
        Some((info_name, hint)) => {
            assert(to_model(e) == spine_app(to_model(fun), args_model_of(_args@)));
            Some((info_name, hint))
        }
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::try_eq_const_app`
/// (`tc.rs:1196-1238`) -- the THIRD piece of `lazy_delta_step`'s
/// machinery: a specialized congruence fast-path for "same applied
/// definition on both sides" (`f a_0 .. a_N` vs `f b_0 .. b_N`, same
/// `f`), used to avoid unfolding `f` at all when its arguments already
/// match. Fires only when both def names agree, both hints are `Regular`
/// with the SAME regularity number (`reducibility_hint_as_regular`,
/// avoiding a separate `ReducibilityHint::==` bridge), every arg pairwise
/// `def_eq`s (via `verified_def_eq_core`, same leaf-cluster-only
/// limitation `verified_def_eq_app` already has), and the heads' level
/// arguments are `eq_antisymm_many`. Does NOT model the real function's
/// `failure_cache` (a pure memoization optimization -- skipping it just
/// means this bridge may recompute what the real code would have
/// short-circuited, never a soundness difference) or its final `_ =>
/// panic!()` arm (structurally unreachable once both heads are confirmed
/// `Const`-shaped, so `None` here covers it harmlessly). Simplified from
/// the real `Option<DeltaResult<'t>>` to `Option<bool>` -- this bridge
/// only ever produces the `FoundEqResult(true)` case, never `Exhausted`.
pub fn verified_try_eq_const_app<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    x: ExprPtr<'t>, x_defname: NamePtr<'t>, x_hint: ReducibilityHint,
    y: ExprPtr<'t>, y_defname: NamePtr<'t>, y_hint: ReducibilityHint,
    fuel: u32,
) -> (result: Option<bool>)
    ensures match result {
        Some(true) => exists |fx: ExprPtr<'t>, fy: ExprPtr<'t>, argsx: Seq<ExprPtr<'t>>, argsy: Seq<ExprPtr<'t>>|
            to_model(x) == spine_app(to_model(fx), args_model_of(argsx))
            && to_model(y) == spine_app(to_model(fy), args_model_of(argsy))
            && argsx.len() == argsy.len()
            && is_const_shape(fx) && is_const_shape(fy) && const_id(fx) == const_id(fy),
        _ => true,
    }
{
    if !name_ptr_eq(x_defname, y_defname) {
        return None;
    }
    let xn = match reducibility_hint_as_regular(&x_hint) {
        Some(n) => n,
        None => return None,
    };
    let yn = match reducibility_hint_as_regular(&y_hint) {
        Some(n) => n,
        None => return None,
    };
    if xn != yn {
        return None;
    }
    let (l_fun, l_args) = match verified_unfold_apps(ctx, x, fuel) {
        Some(p) => p,
        None => return None,
    };
    let (r_fun, r_args) = match verified_unfold_apps(ctx, y, fuel) {
        Some(p) => p,
        None => return None,
    };
    let l_fun_el = ctx.read_expr(l_fun);
    let (l_name, l_levels) = match expr_as_const(l_fun, &l_fun_el) {
        Some(p) => p,
        None => return None,
    };
    let r_fun_el = ctx.read_expr(r_fun);
    let (r_name, r_levels) = match expr_as_const(r_fun, &r_fun_el) {
        Some(p) => p,
        None => return None,
    };
    if !name_ptr_eq(l_name, r_name) {
        return None;
    }
    if l_args.len() != r_args.len() {
        return None;
    }
    let mut i: usize = 0;
    while i < l_args.len()
        invariant
            i <= l_args.len(),
            l_args.len() == r_args.len(),
        decreases l_args.len() - i
    {
        match verified_def_eq_core(ctx, l_args[i], r_args[i], fuel) {
            Some(true) => {},
            _ => return None,
        }
        i += 1;
    }
    if !verified_eq_antisymm_many(ctx, l_levels, r_levels, fuel) {
        return None;
    }
    assert(to_model(x) == spine_app(to_model(l_fun), args_model_of(l_args@)));
    assert(to_model(y) == spine_app(to_model(r_fun), args_model_of(r_args@)));
    Some(true)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::try_unfold_proj_app`
/// (`tc.rs:1240-1248`) -- the FOURTH piece of `lazy_delta_step`'s
/// machinery: when a side is applying a `Proj`-headed spine (`s.1 a_0 ..
/// a_N`), try reducing through the projection instead of unfolding a
/// definition. Deliberately uses ONE application of `verified_whnf_no_
/// unfolding_step`, not the real function's actual behavior (which
/// recurses to an genuine FIXPOINT -- `whnf_no_unfolding_aux` calls
/// itself again on a successfully-reduced result, `tc.rs:794-799`) --
/// same "one round first" scoping choice as `verified_whnf_beta_step`/
/// `verified_def_eq_binder_step` before their own fixpoint/telescoping
/// extensions. Honestly incomplete (a deeper Proj-of-Proj chain won't
/// fully reduce here), not unsound: every `Some(r)` this returns is a
/// genuine `pstep_star` step that ACTUALLY changed something (mirrors
/// the real function's own `eprime != e` check via real pointer
/// inequality), never a fabricated claim of "no further reduction
/// possible."
pub fn verified_try_unfold_proj_app<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, fuel: u32, bound: nat, d: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        d <= 60000,
        bound + d * d * d + d * d + d + 10 <= 0xFFFF_0000,
    ensures match result {
        Some(r) => {
            &&& pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(e), to_model(r))
            &&& r != e
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), bound + d * d * d + d * d)
            &&& depth(to_model(r)) <= d * d + 4 * d
        },
        None => true,
    }
{
    let (fun, _args) = match verified_unfold_apps(ctx, e, fuel) {
        Some(p) => p,
        None => return None,
    };
    let fun_el = ctx.read_expr(fun);
    if expr_as_proj(&fun_el).is_none() {
        return None;
    }
    match verified_whnf_no_unfolding_step(ctx, e, fuel, bound, d) {
        Some(r) => {
            if expr_ptr_eq(e, r) {
                None
            } else {
                Some(r)
            }
        }
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::infer`'s `Local` arm
/// (`tc.rs:522`): trivial, no computation -- a `Local`'s type IS its
/// stored `binder_type` field. First piece of the `infer` subsystem
/// bridged (needed for `proof_irrel_eq`/`try_eta_expansion`/`try_eta_
/// struct`/`def_eq_unit`, all of which depend on `infer`/`infer_then_
/// whnf` -- a completely separate, previously zero-coverage subsystem in
/// this whole arc). Only the `InferOnly` flag is modeled anywhere in this
/// subsystem so far -- `Check` mode's extra well-formedness assertions
/// (`all_uparams_defined` etc.) are not.
pub fn verified_infer_local<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>) -> (result: Option<ExprPtr<'t>>)
    ensures match result {
        Some(r) => is_local_shape(e) && local_binder_type_of(e) == r,
        None => !is_local_shape(e),
    }
{
    let el = ctx.read_expr(e);
    match expr_as_local(e, &el) {
        Some((_, ty)) => Some(ty),
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::infer_sort`
/// (`tc.rs:552-558`), `InferOnly` case: `Sort(l) : Sort(succ(l))`.
/// `TcCtx::succ`/`TcCtx::mk_sort` are both already bridged (`level_arena_
/// bridge.rs`/`quot_model.rs`), so this composes directly with no new
/// trust boundary.
pub fn verified_infer_sort<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>) -> (result: ExprPtr<'t>)
    ensures to_model(result) == ExprSpec::Sort(LevelSpec::Succ(Box::new(level_to_model(l))))
{
    let out = ctx.succ(l);
    ctx.mk_sort(out)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::infer_const`
/// (`tc.rs:221-231`), `InferOnly` case: look up the declaration's TYPE
/// (`Declar::info().ty`, via the new `get_declar_info_ty` bridge in
/// `env_model.rs` -- broader than `get_declar_val`'s Definition/Theorem-
/// only domain, since EVERY declaration kind has a type), then
/// level-substitute it by the `Const`'s own level arguments -- exactly
/// `subst_declar_info_levels`'s real composition (`expr.rs:393-399`),
/// reusing `verified_subst_expr_levels` unchanged. The length-mismatch
/// check (`uparams_vec.len() != c_uparams_vec.len()`) mirrors `verified_
/// unfold_def_step`'s own defensive check for the analogous situation --
/// a well-formed export file never actually hits it, but nothing in this
/// bridge's trust boundary rules it out structurally.
pub fn verified_infer_const<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, c_name: NamePtr<'t>, c_uparams: LevelsPtr<'t>, fuel: u32) -> (result: Option<ExprPtr<'t>>)
    ensures match result {
        Some(r) => exists |uparams: LevelsPtr<'t>, ty: ExprPtr<'t>|
            to_model_of_declar_ty(*env).contains_key(name_id(c_name))
            && to_model_of_declar_ty(*env)[name_id(c_name)] == (level_names(to_model_of_levels(uparams)), to_model(ty))
            && subst_expr_levels_rel(to_model(ty), level_names(to_model_of_levels(uparams)), to_model_of_levels(c_uparams), to_model(r)),
        None => true,
    }
{
    let (uparams, ty) = match get_declar_info_ty(env, &c_name) {
        Some(p) => p,
        None => return None,
    };
    let uparams_vec = read_levels_vec(ctx, uparams);
    let c_uparams_vec = read_levels_vec(ctx, c_uparams);
    if uparams_vec.len() != c_uparams_vec.len() {
        return None;
    }
    verified_subst_expr_levels(ctx, ty, uparams, c_uparams, fuel)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::infer_app`'s own
/// (commented-out, reference) single-argument simplification
/// (`tc.rs:597-621`: `self.ctx.inst(body, &[arg])` once `fun`'s type is
/// confirmed `Pi`-shaped) -- the CORE piece `infer_app`'s real multi-arg
/// telescoping loop (`tc.rs:560-595`) repeats once per argument. Takes
/// `fun_ty` (the CALLEE's already-inferred type) as an explicit
/// parameter rather than computing it via a full `infer` dispatch
/// internally.
///
/// **Genuine open problem surfaced while scoping this, not specific to
/// `infer_app`:** composing this with `verified_infer_dispatch`/`verified_
/// infer_const` to get `fun_ty` automatically needs `depth(to_model(
/// fun_ty)) <= d` for SOME `d` -- but `verified_infer_const`'s result
/// (a declaration's TYPE, substituted) has NO depth bound in its own
/// ensures, for the exact same reason `verified_unfold_def_step`'s
/// result doesn't: a declaration's type can be arbitrarily large, and
/// nothing in this bridge's trust boundary caps it (adding a blanket
/// "types are always <= 60000 deep" axiom would be exactly the kind of
/// arbitrary cap the user's standing directive rules out -- it isn't a
/// structural guarantee the way `nlbv == 0` is, just an untrue-in-general
/// practical assumption). This is the SAME global-environment-depth-cap
/// problem already blocking `lazy_delta_step`'s outer loop, confirmed
/// here to be a MORE PERVASIVE blocker than that scoping first suggested
/// -- it also stands between `infer_app`'s full composition and being
/// buildable, not just delta-unfolding. `d`/`fun_ty` are therefore left
/// as explicit parameters here rather than internally derived, matching
/// the `verified_def_eq`/`verified_def_eq_binder_step` precedent of
/// threading depth bounds in from the caller rather than deriving them.
pub fn verified_infer_app_single<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, fun_ty: ExprPtr<'t>, arg: ExprPtr<'t>, fuel: u32, d: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        depth(to_model(fun_ty)) <= d,
        d <= 60000,
    ensures match result {
        Some(r) => exists |binder_type: ExprPtr<'t>, body: ExprPtr<'t>|
            to_model(fun_ty) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body)))
            && to_model(r) == subst_full(to_model(body), seq![to_model(arg)], 0),
        None => true,
    }
{
    let fun_ty_el = ctx.read_expr(fun_ty);
    let (_, _, _binder_type, body) = match expr_as_pi(&fun_ty_el) {
        Some(p) => p,
        None => return None,
    };
    assert(depth(to_model(body)) <= d);
    let arg_slice: &[ExprPtr<'t>] = &[arg];
    let result = verified_inst(ctx, body, arg_slice, 0, fuel);
    proof {
        assert(Seq::new(arg_slice@.len(), |i: int| to_model(arg_slice@[i])) =~= seq![to_model(arg)]);
    }
    result
}

/// Telescopes `verified_infer_app_single` from ONE argument to arbitrarily
/// many, matching `infer_app`'s own peeling loop (`tc.rs:560-597`) for the
/// "happy path" where `fun_ty`'s Pi-telescope has AT LEAST as many layers
/// as there are args -- i.e. `read_expr(fun)` stays literally `Pi`-shaped
/// at every step, never falling into the `ensure_pi`/WHNF-forcing
/// fallback branch (`tc.rs:584-595`, itself not modeled: it would need a
/// full `infer`+`whnf` composition this arc's `infer` dispatcher doesn't
/// cover yet). Also skips `Check`-mode's `assert_def_eq` well-formedness
/// checking of each argument against its binder type (`InferOnly`-only,
/// consistent with this whole arc's convention). `None` conflates "ran
/// out of fuel" with "would need the `ensure_pi` fallback" -- both honest
/// incompleteness, not unsoundness.
///
/// Reuses `verified_peel_pis` (`expr_arena_bridge.rs`'s real-arena Pi
/// analogue of `verified_peel_lambdas`) and `spine_bind_depth` (peeling
/// binders never increases `depth`, needed to re-establish `verified_
/// inst`'s own depth precondition on the peeled body). Deliberately
/// states its ensures directly via `subst_full` -- exactly `verified_
/// infer_app_single`'s own shape, generalized from a one-element `seq!`
/// to `args`' whole `Seq` -- rather than routing through `spine_reduce`/
/// `spine_reduce_eq_subst_full` (which `verified_whnf_beta_step` needs):
/// `verified_inst` already proves the `subst_full` equation unconditionally,
/// with NO closedness/`max_var_below` requirement on `args` at all, so
/// adding one here would only narrow this function's callers for no
/// benefit -- the same reason `verified_infer_app_single` never needed one
/// either.
pub fn verified_infer_app_telescoped<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, fun_ty: ExprPtr<'t>, args: &[ExprPtr<'t>], fuel: u32, d: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        depth(to_model(fun_ty)) <= d,
        d <= 60000,
    ensures match result {
        Some(r) => exists |body: ExprSpec|
            spine_bind(to_model(fun_ty), args.len() as nat) == Some(body)
            && to_model(r) == subst_full(body, Seq::new(args@.len(), |i: int| to_model(args@[i])), 0),
        None => true,
    }
{
    match verified_peel_pis(ctx, fun_ty, args.len(), fuel) {
        Some((peeled, n)) => {
            if n != args.len() {
                return None;
            }
            proof {
                spine_bind_depth(to_model(fun_ty), n as nat, to_model(peeled));
            }
            verified_inst(ctx, peeled, args, 0, fuel)
        }
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::try_eta_expansion_aux`
/// (`tc.rs:1346-1357`), given the `Pi`-shaped, ALREADY `infer_then_whnf`'d
/// components of `y`'s type (`binder_name`/`binder_style`/`binder_type`)
/// as EXPLICIT parameters -- same "hard-to-derive value as an explicit
/// externally-bounded parameter" pattern `verified_infer_sort_of`/
/// `verified_is_prop_of_type` (`delta_bound_model.rs`) already established
/// for this exact reason: composing with a general `infer`+`whnf` call
/// internally would need a depth bound on the extracted `binder_type`,
/// which `verified_whnf_step`'s own (`pstep_star`-only) postcondition
/// doesn't expose.
///
/// Checks `x` is `Lambda`-shaped (the real function's own guard -- returns
/// `Some(false)` immediately if not, matching its literal `false` return,
/// though this doesn't carry a SOUND "definitely not eta-equal" claim any
/// more than `verified_def_eq`'s own `Some(false)` does, since the two
/// `Some(false)` sources aren't distinguished in the result type), then
/// builds `new_lambda := Lambda(binder_type, App(y, Var(0)))` via the
/// already-bridged `mk_var`/`mk_app`/`mk_lambda` and defers to `verified_
/// def_eq(x, new_lambda, fuel)`. Doesn't restate `verified_def_eq`'s own
/// big disjunction (same "don't re-derive what a composed call already
/// proved" convention as `verified_proof_irrel_eq_of_types`) -- just
/// confirms what `new_lambda` actually IS, so the fact isn't vacuous.
pub fn verified_try_eta_expansion_aux<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, x: ExprPtr<'t>, y: ExprPtr<'t>, binder_name: NamePtr<'t>, binder_style: BinderStyle, binder_type: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    requires
        depth(to_model(x)) <= 60000,
        depth(to_model(binder_type)) + depth(to_model(y)) + 10 <= 60000,
    ensures match result {
        Some(true) => exists |new_lambda: ExprPtr<'t>|
            to_model(new_lambda) == ExprSpec::Bind(
                Box::new(to_model(binder_type)),
                Box::new(ExprSpec::App(Box::new(to_model(y)), Box::new(ExprSpec::Var(0)))),
            ),
        _ => true,
    }
{
    let el = ctx.read_expr(x);
    if expr_as_lambda(&el).is_none() {
        return Some(false);
    }
    let v0 = ctx.mk_var(0);
    let new_body = ctx.mk_app(y, v0);
    let new_lambda = ctx.mk_lambda(binder_name, binder_style, binder_type, new_body);
    assert(depth(to_model(new_body)) == 1 + if depth(to_model(y)) >= depth(to_model(v0)) { depth(to_model(y)) } else { depth(to_model(v0)) });
    assert(depth(to_model(v0)) == 0);
    assert(depth(to_model(new_lambda)) == 1 + if depth(to_model(binder_type)) >= depth(to_model(new_body)) { depth(to_model(binder_type)) } else { depth(to_model(new_body)) });
    assert(depth(to_model(new_lambda)) <= 60000);
    verified_def_eq(ctx, x, new_lambda, fuel)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::try_eta_expansion`
/// (`tc.rs:1342-1344`): `try_eta_expansion_aux(x, y) || try_eta_expansion_
/// aux(y, x)` -- tries BOTH directions (`x` eta-expanding to match `y`'s
/// type, then `y` eta-expanding to match `x`'s type), since the real
/// function doesn't know a priori which side (if either) is the `Lambda`.
/// Takes each direction's already-`infer_then_whnf`'d `Pi` components as
/// separate explicit parameters (`y_binder_*` for the first attempt,
/// `x_binder_*` for the second) -- same reason as `verified_try_eta_
/// expansion_aux` itself.
///
/// The real `||` is a plain boolean short-circuit; since each side here
/// can independently report `None` (ran out of fuel / `verified_def_eq`
/// incomplete), this tries BOTH regardless of the first's outcome, unlike
/// a real short-circuiting `||` -- a deliberate strengthening for
/// completeness (never masks the second attempt's possible `Some(true)`
/// behind the first's `None`), consistent with reporting `None` overall
/// only when BOTH attempts are genuinely inconclusive.
pub fn verified_try_eta_expansion<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
    y_binder_name: NamePtr<'t>,
    y_binder_style: BinderStyle,
    y_binder_type: ExprPtr<'t>,
    x_binder_name: NamePtr<'t>,
    x_binder_style: BinderStyle,
    x_binder_type: ExprPtr<'t>,
    fuel: u32,
) -> (result: Option<bool>)
    requires
        depth(to_model(x)) <= 60000,
        depth(to_model(y)) <= 60000,
        depth(to_model(y_binder_type)) + depth(to_model(y)) + 10 <= 60000,
        depth(to_model(x_binder_type)) + depth(to_model(x)) + 10 <= 60000,
    ensures match result {
        Some(true) => {
            ||| (exists |new_lambda: ExprPtr<'t>|
                    to_model(new_lambda) == ExprSpec::Bind(
                        Box::new(to_model(y_binder_type)),
                        Box::new(ExprSpec::App(Box::new(to_model(y)), Box::new(ExprSpec::Var(0)))),
                    ))
            ||| (exists |new_lambda: ExprPtr<'t>|
                    to_model(new_lambda) == ExprSpec::Bind(
                        Box::new(to_model(x_binder_type)),
                        Box::new(ExprSpec::App(Box::new(to_model(x)), Box::new(ExprSpec::Var(0)))),
                    ))
        },
        _ => true,
    }
{
    let r1 = verified_try_eta_expansion_aux(ctx, x, y, y_binder_name, y_binder_style, y_binder_type, fuel);
    if let Some(true) = r1 {
        return Some(true);
    }
    let r2 = verified_try_eta_expansion_aux(ctx, y, x, x_binder_name, x_binder_style, x_binder_type, fuel);
    match (r1, r2) {
        (_, Some(true)) => Some(true),
        (None, _) => None,
        (_, None) => None,
        _ => Some(false),
    }
}

}
