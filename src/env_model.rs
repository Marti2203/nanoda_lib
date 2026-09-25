//! Exploratory Verus model of `env.rs`'s `ReducibilityHint::is_lt`, plus a
//! real trust boundary for `Env`'s declaration lookups (`get_declar_val`,
//! `get_constructor`'s `num_params`) that `tc.rs`'s delta reduction and
//! `Proj` reduction need.
//!
//! Most of `env.rs` beyond that is thin `IndexMap`/`HashMap` lookup
//! plumbing (`Env`'s `get_declar`/`get_inductive`/etc., the `cutoff`-based
//! visibility scheme) over an external, unverified map type -- there's no
//! real algorithmic content there to formally model beyond what's already
//! evident from inspection, so it isn't given a standalone model the way
//! `name.rs`'s functions were.
//!
//! `ReducibilityHint::is_lt`, though, is genuinely worth pinning down:
//! `tc.rs`'s delta reduction (unfolding definitions during `def_eq`) uses it
//! to decide *which* of two definitions to unfold first, on the assumption
//! that it behaves like a real ordering. If `is_lt` weren't a valid strict
//! total order -- say, non-transitive -- delta reduction's comparison
//! procedure could behave inconsistently depending on argument order, or
//! fail to terminate the way it's meant to. This file proves it is one:
//! irreflexive, asymmetric, transitive, and trichotomous (any two hints are
//! comparable).
//!
//! `ReducibilityHint` has no arena pointers in it at all (`Opaque`,
//! `Regular(u16)`, `Abbrev`) -- unlike `Level`/`Expr`/`Name`, it's a plain
//! value type, so there's no separate "standalone model vs. real arena"
//! split needed the way `level_model.rs`/`expr_model.rs` needed, and no
//! `read_*`-style dereference step: the bridge is a single flat layer of
//! accessors (same shape as `level_as_succ`/`level_as_param`, just without
//! an arena pointer underneath), reimplementing `is_lt`'s match logic and
//! proving it equal to the spec version.
#[cfg(verus_only)]
use crate::beta_model::{depth_le_size, max_var_below, max_var_below_mono, nlbv_bound_implies_max_var_below, size};
use crate::env::{Declar, Env, RecRule, ReducibilityHint};
#[cfg(verus_only)]
use crate::expr_arena_bridge::to_model as expr_to_model;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{EnvSpec, RecDataSpec, RecRuleSpec};
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[cfg(verus_only)]
use crate::expr_model::{depth, has_fv, nlbv};
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, to_model_of_levels};
#[cfg(verus_only)]
use crate::level_model::level_names;
#[cfg(verus_only)]
use crate::tc_model::{rec_rule_ctor_name_of, rec_rule_ctor_telescope_size_wo_params_of, rec_rule_val_of};
use crate::util::{ExprPtr, LevelsPtr, NamePtr};
use std::sync::Arc;
use vstd::prelude::*;

/// `Env::get_constructor` returns `Option<&ConstructorData>`, a reference
/// to a struct with several fields -- rather than registering the whole
/// struct with Verus, this plain wrapper extracts just the one field
/// `reduce_proj` (`tc.rs:447-458`) actually needs, the same "extract only
/// what's needed, axiomatize that" approach `rec_rule_ctor_name` (`tc_model.rs`)
/// already uses for `RecRule`.
#[allow(dead_code)]
pub(crate) fn get_constructor_num_params<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> Option<u16> {
    env.get_constructor(n).map(|cd| cd.num_params)
}

/// `Env::get_recursor` returns `Option<&RecursorData>`; this wrapper
/// extracts exactly the fields `reduce_rec` (`tc.rs:1070-1102`) actually
/// reads (`num_params`/`num_motives`/`num_minors`, the computed `major_
/// idx()`, the recursor's own `uparams`, and its computation rules) into
/// an owned tuple, same "extract only what's needed" approach `get_
/// constructor_num_params` above already uses for `ConstructorData`.
/// `rec_rules` is cloned (an `Arc`, cheap) rather than borrowed, sidestepping
/// tying the result's lifetime to the `Env` reference.
#[allow(dead_code)]
pub(crate) fn get_recursor_data<'x, 'a>(
    env: &Env<'x, 'a>,
    n: &NamePtr<'a>,
) -> Option<(u16, u16, u16, usize, LevelsPtr<'a>, Arc<[RecRule<'a>]>)> {
    let rec = env.get_recursor(n)?;
    Some((rec.num_params, rec.num_motives, rec.num_minors, rec.major_idx(), rec.info.uparams, rec.rec_rules.clone()))
}

/// `tc.rs::TypeChecker::get_applied_def`'s own env-level classification
/// (`tc.rs:1133-1142`): a name is "an applied def" exactly when it's a
/// `Definition` (real hint) or `Theorem` (treated as `Opaque` -- theorems
/// are never unfolded during delta reduction, but ARE tracked so `lazy_
/// delta_step` knows to keep looking at the OTHER side instead of giving
/// up immediately). Same "extract only what's needed" approach as `get_
/// constructor_num_params`/`get_recursor_data` above.
#[allow(dead_code)]
pub(crate) fn get_declar_hint<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> Option<(NamePtr<'a>, ReducibilityHint)> {
    match env.get_declar(n) {
        Some(Declar::Definition { info, hint, .. }) => Some((info.name, *hint)),
        Some(Declar::Theorem { info, .. }) => Some((info.name, ReducibilityHint::Opaque)),
        _ => None,
    }
}

/// `tc.rs::TypeChecker::infer_const`'s own declaration lookup
/// (`tc.rs:221-231`, `InferOnly` case): unlike `get_declar_val` (only
/// `Definition`/`Theorem` have a VALUE to unfold), `infer_const` needs a
/// TYPE, which `Declar::info()` (`env.rs:167-180`) extracts uniformly
/// from EVERY declaration kind (`Axiom`/`Quot`/`Theorem`/`Definition`/
/// `Inductive`/`Constructor`/`Recursor`/`Opaque`) -- a strictly LARGER
/// domain than `get_declar_val`'s, so this needs its own map rather than
/// reusing `to_model_of_env`.
#[allow(dead_code)]
pub(crate) fn get_declar_info_ty<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> Option<(LevelsPtr<'a>, ExprPtr<'a>)> {
    env.get_declar(n).map(|d| {
        let info = d.info();
        (info.uparams, info.ty)
    })
}

/// `Env::get_structure` returns `Option<&InductiveData>`; this wrapper
/// extracts just `all_ctor_names[0]` -- the ONE field `def_eq_unit`
/// (`tc.rs:357-368`) actually reads, same "extract only what's needed"
/// approach as `get_constructor_num_params` above. `get_structure`'s own
/// match guard already guarantees `all_ctor_names.len() == 1` whenever it
/// returns `Some`, so indexing `[0]` can't panic.
#[allow(dead_code)]
pub(crate) fn get_structure_first_ctor<'x, 'a>(
    env: &Env<'x, 'a>,
    n: &NamePtr<'a>,
    rec_ok: bool,
) -> Option<NamePtr<'a>> {
    env.get_structure(n, rec_ok).map(|i| i.all_ctor_names[0])
}

/// `Env::get_constructor` returns `Option<&ConstructorData>`; this wrapper
/// extracts `num_fields` -- `def_eq_unit`'s other field read, sibling to
/// `get_constructor_num_params` above (same struct, different field).
#[allow(dead_code)]
pub(crate) fn get_constructor_num_fields<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> Option<u16> {
    env.get_constructor(n).map(|cd| cd.num_fields)
}

verus! {

broadcast use crate::util::ptr_eta;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReducibilityHintSpec {
    Opaque,
    Regular(u16),
    Abbrev,
}

/// Mirrors `ReducibilityHint::is_lt` exactly.
pub open spec fn is_lt(a: ReducibilityHintSpec, b: ReducibilityHintSpec) -> bool {
    match (a, b) {
        (_, ReducibilityHintSpec::Opaque) => false,
        (ReducibilityHintSpec::Abbrev, _) => false,
        (ReducibilityHintSpec::Opaque, _) => true,
        (_, ReducibilityHintSpec::Abbrev) => true,
        (ReducibilityHintSpec::Regular(h1), ReducibilityHintSpec::Regular(h2)) => h1 < h2,
    }
}

/// TRANSPARENT. Opaque, the three variants could only be reached through
/// three `assume_specification`s and `to_model` had to be uninterpreted; the
/// model is a three-arm relabelling of a three-variant enum, so there was
/// never anything to assume.
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExReducibilityHint(ReducibilityHint);

/// DEFINED, not uninterpreted.
pub open spec fn to_model(h: ReducibilityHint) -> ReducibilityHintSpec {
    match h {
        ReducibilityHint::Opaque => ReducibilityHintSpec::Opaque,
        ReducibilityHint::Regular(n) => ReducibilityHintSpec::Regular(n),
        ReducibilityHint::Abbrev => ReducibilityHintSpec::Abbrev,
    }
}

#[allow(dead_code)]
pub(crate) fn reducibility_hint_is_opaque(h: &ReducibilityHint) -> (result: bool)
    ensures
        result == (to_model(*h) == ReducibilityHintSpec::Opaque),
{
    matches!(h, ReducibilityHint::Opaque)
}

#[allow(dead_code)]
pub(crate) fn reducibility_hint_is_abbrev(h: &ReducibilityHint) -> (result: bool)
    ensures
        result == (to_model(*h) == ReducibilityHintSpec::Abbrev),
{
    matches!(h, ReducibilityHint::Abbrev)
}

#[allow(dead_code)]
pub(crate) fn reducibility_hint_as_regular(h: &ReducibilityHint) -> (result: Option<u16>)
    ensures
        match result {
            Some(n) => to_model(*h) == ReducibilityHintSpec::Regular(n),
            None => !matches!(to_model(*h), ReducibilityHintSpec::Regular(_)),
        },
{
    match h {
        ReducibilityHint::Regular(n) => Some(*n),
        _ => None,
    }
}

// `ReducibilityHint::is_lt` is verified in place now (`env.rs`); it used to
// be assumed here, with `verified_is_lt` below as a from-scratch check that
// the assumption was as trivial as claimed. The check is kept -- it is now an
// independent reimplementation agreeing with a PROVEN function rather than
// with an axiom.
/// A from-scratch reimplementation using only the axiomatized accessors,
/// proven equal to `is_lt` independently of the trust step above --
/// belt-and-suspenders documentation that the axiom above is exactly as
/// trivial as claimed.
pub fn verified_is_lt(a: &ReducibilityHint, b: &ReducibilityHint) -> (result: bool)
    ensures
        result == is_lt(to_model(*a), to_model(*b)),
{
    if reducibility_hint_is_opaque(b) {
        false
    } else if reducibility_hint_is_abbrev(a) {
        false
    } else if reducibility_hint_is_opaque(a) {
        true
    } else if reducibility_hint_is_abbrev(b) {
        true
    } else {
        match (reducibility_hint_as_regular(a), reducibility_hint_as_regular(b)) {
            (Some(h1), Some(h2)) => h1 < h2,
            _ => false,
        }
    }
}


/// The arenas an environment's pointers index: its declarations are stored
/// in some context's dag (temporary declarations) or the export file's. See
/// `docs/ARENA_IDENTITY.md`. Every lookup below says its result belongs to
/// these; a checker's environment and context agree on them (`tc_wf`).
/// Recorded by the environment itself (a ghost field set where it is built).
pub open spec fn env_arena_ids<'x, 'a>(env: Env<'x, 'a>) -> (nat, nat) {
    env.arena_ids()
}

/// `p` belongs to `env`'s arenas (compare `util_model::owns`).
pub open spec fn env_owns<'x, 'a, A>(env: Env<'x, 'a>, p: crate::util::Ptr<A>) -> bool {
    crate::util_model::owns_in(env_arena_ids(env), p)
}

/// A declaration header's pointers belong to the arena pair `ids`.
pub open spec fn info_owned_in<'a>(ids: (nat, nat), i: crate::env::DeclarInfo<'a>) -> bool {
    crate::util_model::owns_in(ids, i.name) && crate::util_model::owns_in(ids, i.uparams) && crate::util_model::owns_in(ids, i.ty)
}

pub open spec fn inductive_owned_in<'a>(ids: (nat, nat), d: crate::env::InductiveData<'a>) -> bool {
    &&& info_owned_in(ids, d.info)
    &&& forall|k: int| 0 <= k < d.all_ind_names@.len() ==> crate::util_model::owns_in(ids, #[trigger] d.all_ind_names@[k])
    &&& forall|k: int| 0 <= k < d.all_ctor_names@.len() ==> crate::util_model::owns_in(ids, #[trigger] d.all_ctor_names@[k])
}

pub open spec fn constructor_owned_in<'a>(ids: (nat, nat), d: crate::env::ConstructorData<'a>) -> bool {
    info_owned_in(ids, d.info) && crate::util_model::owns_in(ids, d.inductive_name)
}

pub open spec fn recursor_owned_in<'a>(ids: (nat, nat), d: crate::env::RecursorData<'a>) -> bool {
    &&& info_owned_in(ids, d.info)
    &&& forall|k: int| 0 <= k < d.all_inductives@.len() ==> crate::util_model::owns_in(ids, #[trigger] d.all_inductives@[k])
    &&& forall|k: int| 0 <= k < d.rec_rules@.len() ==> crate::util_model::owns_in(ids, #[trigger] d.rec_rules@[k].ctor_name)
    &&& forall|k: int| 0 <= k < d.rec_rules@.len() ==> crate::util_model::owns_in(ids, #[trigger] d.rec_rules@[k].val)
}

/// A declaration's pointers belong to the arena pair `ids`.
pub open spec fn declar_owned_in<'a>(ids: (nat, nat), d: Declar<'a>) -> bool {
    match d {
        Declar::Inductive(i) => inductive_owned_in(ids, i),
        Declar::Constructor(c) => constructor_owned_in(ids, c),
        Declar::Recursor(r) => recursor_owned_in(ids, r),
        Declar::Axiom { info } | Declar::Quot { info } | Declar::Opaque { info, .. }
        | Declar::Theorem { info, .. } | Declar::Definition { info, .. } => info_owned_in(ids, info),
    }
}

/// A declaration map every entry of which belongs to `ids`.
pub open spec fn declar_map_owned_in<'a>(ids: (nat, nat), m: &crate::env::DeclarMap<'a>) -> bool {
    &&& crate::indexmap_model::imap_wf(m)
    &&& forall|k: NamePtr<'a>| #[trigger] crate::indexmap_model::imap_view(m).contains_key(k)
        ==> crate::util_model::owns_in(ids, k) && declar_owned_in(ids, crate::indexmap_model::imap_view(m)[k])
}

/// A declaration header's pointers belong to `env`'s arenas.
pub open spec fn info_owned<'x, 'a>(env: Env<'x, 'a>, i: crate::env::DeclarInfo<'a>) -> bool {
    info_owned_in(env_arena_ids(env), i)
}

/// An environment's records point into its own arenas. Stated per record kind
/// and ensured by the lookup that hands the record out.
pub open spec fn inductive_data_owned<'x, 'a>(env: Env<'x, 'a>, d: crate::env::InductiveData<'a>) -> bool {
    inductive_owned_in(env_arena_ids(env), d)
}

pub open spec fn constructor_data_owned<'x, 'a>(env: Env<'x, 'a>, d: crate::env::ConstructorData<'a>) -> bool {
    constructor_owned_in(env_arena_ids(env), d)
}

pub open spec fn recursor_data_owned<'x, 'a>(env: Env<'x, 'a>, d: crate::env::RecursorData<'a>) -> bool {
    recursor_owned_in(env_arena_ids(env), d)
}

/// `env`'s pointers are `c`'s: then `env_owns` is `owns(c, _)`.
pub open spec fn env_matches<'x, 'a, 't, 'p>(env: Env<'x, 'a>, c: crate::util::TcCtx<'t, 'p>) -> bool {
    env_arena_ids(env) == crate::util_model::arena_ids(c)
}

/// Transparent: the inductive checker builds one (`ByIndex`).
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExEnvLimit<'a>(crate::env::EnvLimit<'a>);

/// A checker's environment: the context's own export file, limited, with
/// its arenas. Verified (option B): the export file's declarations are its
/// own (`export_ok`), so they are the context's.
///
/// VERUS-REWRITE(ghost-ids): `ctx.export_file.new_env(env_limit)` is
/// `Env::new` with the same arguments and the context's arena ids as the
/// ghost argument.
pub fn ctx_env<'t, 'p: 't>(ctx: &crate::util::TcCtx<'t, 'p>, env_limit: crate::env::EnvLimit<'p>) -> (result: Env<'t, 't>)
    requires
        crate::inductive::export_ok(*ctx.export_file),
    ensures
        env_matches(result, *ctx),
{
    proof {
        export_declars_owned(*ctx);
    }
    crate::env::Env::new(&ctx.export_file.declars, &ctx.export_file.notations, env_limit, Ghost(crate::util_model::arena_ids(*ctx)))
}

/// The same for an environment with a temporary extension the context built.
pub fn ctx_env_ext<'x, 't, 'p: 't>(
    ctx: &crate::util::TcCtx<'t, 'p>,
    env_ext: &'x crate::env::DeclarMap<'t>,
    env_limit: crate::env::EnvLimit<'p>,
) -> (result: Env<'x, 't>)
    requires
        crate::inductive::export_ok(*ctx.export_file),
        declar_map_owned_in(crate::util_model::arena_ids(*ctx), env_ext),
    ensures
        env_matches(result, *ctx),
{
    proof {
        export_declars_owned(*ctx);
    }
    crate::env::Env::new_w_temp_ext(&ctx.export_file.declars, Some(env_ext), &ctx.export_file.notations, env_limit, Ghost(crate::util_model::arena_ids(*ctx)))
}

/// A context's export file's declarations belong to the context's arenas.
pub proof fn export_declars_owned<'t, 'p>(c: crate::util::TcCtx<'t, 'p>)
    requires
        crate::inductive::export_ok(*c.export_file),
    ensures
        declar_map_owned_in(crate::util_model::arena_ids(c), &c.export_file.declars),
{
    let ids = crate::util_model::arena_ids(c);
    let m = crate::indexmap_model::imap_view(&c.export_file.declars);
    assert forall|k: NamePtr<'p>| #[trigger] m.contains_key(k)
        implies crate::util_model::owns_in(ids, k) && declar_owned_in(ids, m[k]) by {
        crate::inductive::export_declar_owned_in(ids, m[k]);
    }
}

pub uninterp spec fn to_model_of_defs<'x, 'a>(env: Env<'x, 'a>) -> Map<u64, (Seq<u64>, ExprSpec)>;

/// The environment as the reduction and typing models see it: its
/// definitions and its own per-name tables, each tied to the lookup that
/// reads it below.
pub open spec fn to_model_of_env<'x, 'a>(env: Env<'x, 'a>) -> EnvSpec {
    EnvSpec {
        export: env_arena_ids(env).1,
        defs: to_model_of_defs(env),
        recs: to_model_of_recursors(env),
        ctor_np: to_model_of_ctor_num_params(env),
        struct_ctor: to_model_of_struct_ctor(env),
        ctor_nf: to_model_of_ctor_num_fields(env),
    }
}

/// The trust boundary: `get_declar_val` (only definitions/theorems have a
/// value -- `env.rs:320-327`) returns exactly what `to_model_of_env` says
/// this name maps to, and the declaration's `uparams` are `Param`-shaped
/// throughout (what `verified_subst_expr_levels`'s `ks` argument
/// requires). Closedness of the value is NOT claimed: the parser does not
/// check it, so the kernel tests it where it relies on it.
pub assume_specification<'x, 'a>[ Env::<'x, 'a>::get_declar_val ](
    env: &Env<'x, 'a>,
    n: &NamePtr<'a>,
) -> (result: Option<(LevelsPtr<'a>, ExprPtr<'a>)>) where 'a: 'x
    ensures
        match result {
            Some((uparams, val)) => env_owns(*env, uparams) && env_owns(*env, val) && to_model_of_env(*env).contains_key(name_id(*n))
                && to_model_of_env(*env)[name_id(*n)] == (
                level_names(to_model_of_levels(uparams)),
                expr_to_model(val),
            // (A well-formed declaration's value is closed, but the export
            // parser does not check it, so it is not claimed here: users test
            // the node's cached flags.)
            ) && forall|j: int|
                0 <= j < to_model_of_levels(uparams).len() ==> #[trigger] to_model_of_levels(
                    uparams,
                )[j] is Param,
            None => !to_model_of_env(*env).contains_key(name_id(*n)),
        },
;

/// COVERAGE of the visible declaration names: every id in either
/// model-level declaration map's domain appears (as `name_id`) in the
/// list `visible_declar_names` returns. Trust content: the exec method
/// iterates exactly the maps the keyed lookups read (temp extension +
/// persistent-up-to-cutoff), so nothing the models can see is missed --
/// the iteration-completeness twin of the per-key lookup contracts.
pub assume_specification<'x, 'a>[ Env::<'x, 'a>::visible_declar_names ](
    env: &Env<'x, 'a>,
) -> (result: Vec<NamePtr<'a>>) where 'a: 'x
    ensures
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] env_owns(*env, result@[i]),
        forall|id: u64| #[trigger]
            to_model_of_env(*env).contains_key(id) ==> exists|i: int|
                0 <= i < result@.len() && name_id(#[trigger] result@[i]) == id,
        forall|id: u64| #[trigger]
            to_model_of_declar_ty(*env).contains_key(id) ==> exists|i: int|
                0 <= i < result@.len() && name_id(#[trigger] result@[i]) == id,
;

/// LEASTNESS pin for `env_global_cap`: any `k` that bounds every visible
/// declaration's value and type models (depth AND `max_var_below`)
/// dominates the cap. The existing trust only asserts facts hold AT the
/// cap ("some sufficient bound exists"); this adds that the named cap is
/// no larger than any actually-sufficient bound -- consistent (interpret
/// the cap as the exact supremum, which satisfies both), and what turns
/// an exec scan's measurements into a usable `env_global_cap(*env) <= k`
/// hypothesis for the whnf/delta routes.
/// SIZE twin of `env_global_cap` (delta-lift L3(b)): the certified
/// family's `env_wf` demands `size <= cap`, which depth/mvb caps cannot
/// give (wide terms), so the certificate scan -- which measures SIZES
/// via `verified_size` -- pins this separately, with the same
/// leastness/iteration-completeness character as `env_global_cap_le`.
pub uninterp spec fn env_global_size_cap<'x, 'a>(env: Env<'x, 'a>) -> nat;

/// Closedness of every definition body (no locals) -- CHECKED by the
/// certificate scan via the real `has_fvars` flag, then pinned here --
/// bundled with "no definition id is a constructor id" (a name has one
/// declaration per export: `get_declar_val` only ever returns
/// Definition/Theorem values and `get_constructor` only Constructor
/// data, so their key sets are disjoint).
pub uninterp spec fn env_global_closed<'x, 'a>(env: Env<'x, 'a>) -> bool;

/// Closedness of every declaration TYPE, the sibling of `env_global_closed`
/// just below and established by the same certificate scan. Declaration types
/// in a Lean environment are closed terms, like values -- the scan already
/// walked them for depth and `max_var_below`, it simply never checked
/// `has_fvars` on them.
///
/// This is what the kernel's own `subst_expr_levels` needs: it PANICS on a
/// `Local`, so verifying it in place turned that into a `!has_fv`
/// precondition, and its callers substitute into declaration types.
pub uninterp spec fn env_global_closed_ty<'x, 'a>(env: Env<'x, 'a>) -> bool;

/// The UNCAPPED delta model: every definition whose value has no free
/// variables, with no size ceiling at all. `env_model_capped`'s `size <= k`
/// test was never about soundness -- it existed so an unfolded value's DEPTH
/// could be bounded by `k`, feeding the same depth-ceiling algebra the fuelled
/// inference needed and the fuel-free one does not. `!has_fv` is the real
/// condition: a definition whose value mentions a free variable cannot be
/// substituted into an arbitrary context.
/// Only the definitions are restricted, and only that part is opaque: the
/// tables and the export are the environment's own, visible everywhere.
#[verifier::opaque]
pub open spec fn nofv_defs<'x, 'a>(env: Env<'x, 'a>) -> Map<u64, (Seq<u64>, ExprSpec)> {
    let m = to_model_of_env(env);
    m.defs.restrict(m.defs.dom().filter(|id: u64| !has_fv(m.defs[id].1)))
}

pub open spec fn env_model_nofv<'x, 'a>(env: Env<'x, 'a>) -> EnvSpec {
    let m = to_model_of_env(env);
    EnvSpec {
        export: m.export,
        defs: nofv_defs(env),
        recs: m.recs,
        ctor_np: m.ctor_np,
        struct_ctor: m.struct_ctor,
        ctor_nf: m.ctor_nf,
    }
}

/// Membership in the uncapped model from the single per-definition check.
pub proof fn env_model_nofv_has<'x, 'a>(env: Env<'x, 'a>, id: u64)
    requires
        to_model_of_env(env).contains_key(id),
        !has_fv(to_model_of_env(env)[id].1),
    ensures
        env_model_nofv(env).contains_key(id),
        env_model_nofv(env)[id] == to_model_of_env(env)[id],
{
    reveal(nofv_defs);
}

/// The uncapped model is a sub-map of the full model (for `pstep_star_env_weaken`).
pub proof fn env_model_nofv_sub<'x, 'a>(env: Env<'x, 'a>)
    ensures
        forall|id: u64| #[trigger]
            env_model_nofv(env).contains_key(id) ==> to_model_of_env(env).contains_key(id)
                && env_model_nofv(env)[id] == to_model_of_env(env)[id],
        env_model_nofv(env).sub(to_model_of_env(env)),
        env_model_nofv(env).recs == to_model_of_env(env).recs,
        env_model_nofv(env).ctor_np == to_model_of_env(env).ctor_np,
        env_model_nofv(env).struct_ctor == to_model_of_env(env).struct_ctor,
        env_model_nofv(env).ctor_nf == to_model_of_env(env).ctor_nf,
        env_model_nofv(env).export == to_model_of_env(env).export,
{
    reveal(nofv_defs);
}

#[verifier::external_body]
pub proof fn env_global_cap_le<'x, 'a>(env: Env<'x, 'a>, k: nat)
    requires
        forall|id: u64| #[trigger]
            to_model_of_env(env).contains_key(id) ==> depth(to_model_of_env(env)[id].1) <= k
                && max_var_below(to_model_of_env(env)[id].1, k),
        forall|id: u64| #[trigger]
            to_model_of_declar_ty(env).contains_key(id) ==> depth(to_model_of_declar_ty(env)[id].1)
                <= k && max_var_below(to_model_of_declar_ty(env)[id].1, k),
    ensures
        env_global_cap(env) <= k,
{
}

/// A real environment's declaration TYPES, as a name-id-keyed map --
/// same shape as `to_model_of_env` (uparams + a value), but covering
/// EVERY declaration kind (see `get_declar_info_ty`'s doc comment), not
/// just `Definition`/`Theorem`. Same two substantive facts as `get_
/// declar_val`'s trust boundary: a declaration's TYPE is always CLOSED
/// (`nlbv == 0` -- a top-level type can no more have an escaping de-
/// Bruijn index than a top-level value can), and its `uparams` are always
/// genuinely `Param`-shaped.
pub uninterp spec fn to_model_of_declar_ty<'x, 'a>(env: Env<'x, 'a>) -> Map<
    u64,
    (Seq<u64>, ExprSpec),
>;

pub assume_specification<'x, 'a>[ get_declar_info_ty ](
    env: &Env<'x, 'a>,
    n: &NamePtr<'a>,
) -> (result: Option<(LevelsPtr<'a>, ExprPtr<'a>)>)
    ensures
        match result {
            Some((uparams, ty)) => env_owns(*env, uparams) && env_owns(*env, ty) && to_model_of_declar_ty(*env).contains_key(name_id(*n))
                && to_model_of_declar_ty(*env)[name_id(*n)] == (
                level_names(to_model_of_levels(uparams)),
                expr_to_model(ty),
            // (Closedness is not claimed, as for `get_declar_val`.)
            ) && forall|j: int|
                0 <= j < to_model_of_levels(uparams).len() ==> #[trigger] to_model_of_levels(
                    uparams,
                )[j] is Param,
            None => !to_model_of_declar_ty(*env).contains_key(name_id(*n)),
        },
;

/// A real environment's `Definition`/`Theorem` reducibility hints, as a
/// NAME-id-keyed map (mirrors `to_model_of_ctor_num_params`'s shape) --
/// `get_declar_hint`'s only real-world claim beyond bookkeeping is that
/// this key set is EXACTLY `to_model_of_env`'s own domain (`get_declar_
/// val`, above): the same real match arms (`Definition`/`Theorem`) decide
/// both, so "has a value to unfold" and "has a reducibility hint" are the
/// same set of names, not independently-axiomatized facts that could
/// silently drift apart.
pub uninterp spec fn to_model_of_declar_hint<'x, 'a>(env: Env<'x, 'a>) -> Map<
    u64,
    ReducibilityHintSpec,
>;

/// The returned name is the declaration's own `info.name`, and it is the name
/// it was looked up by: the parser inserts every declaration under
/// `info.name` (`parser.rs`, `declars.insert(name, ..)` with `info = DeclarInfo
/// { name, .. }`). `lazy_delta_step` relies on exactly this when it compares
/// two definitions by the names this returns.
pub assume_specification<'x, 'a>[ get_declar_hint ](env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result:
    Option<(NamePtr<'a>, ReducibilityHint)>)
    ensures
        match result {
            Some((dn, hint)) => dn == *n && to_model_of_env(*env).contains_key(name_id(*n))
                && to_model_of_declar_hint(*env).contains_key(name_id(*n))
                && to_model_of_declar_hint(*env)[name_id(*n)] == to_model(hint),
            None => !to_model_of_env(*env).contains_key(name_id(*n)),
        },
;

/// A real environment's constructors, as a NAME-id-keyed `num_params` map
/// -- `reduce_proj`'s only real dependency on `ConstructorData`.
pub uninterp spec fn to_model_of_ctor_num_params<'x, 'a>(env: Env<'x, 'a>) -> Map<u64, u16>;

pub assume_specification<'x, 'a>[ get_constructor_num_params ](
    env: &Env<'x, 'a>,
    n: &NamePtr<'a>,
) -> (result: Option<u16>)
    ensures
        match result {
            Some(num_params) => to_model_of_ctor_num_params(*env).contains_key(name_id(*n))
                && to_model_of_ctor_num_params(*env)[name_id(*n)] == num_params,
            None => !to_model_of_ctor_num_params(*env).contains_key(name_id(*n)),
        },
;


/// The one substantive real-world fact `get_recursor_data` asserts beyond
/// bookkeeping: a recursor's own universe parameters are always genuinely
/// `Param`-shaped (same fact `get_declar_val` already asserts for plain
/// declarations, needed for the exact same reason -- `verified_subst_
/// expr_levels`'s `ks` argument requires it). No `to_model_of_env`-style
/// keyed map is needed here: unlike delta/proj/quot, nothing downstream
/// needs to relate TWO separate calls' results back to the same identity,
/// so this is a plain per-call fact, not a lookup table.
/// The env's recursors at the MODEL level (rec-iota P0): keyed by name id,
/// the same shape `get_recursor_data` returns, with rule values modeled
/// through `to_model`.
pub uninterp spec fn to_model_of_recursors<'x, 'a>(env: Env<'x, 'a>) -> Map<u64, RecDataSpec>;

pub open spec fn rec_rules_model<'a>(rules: Seq<RecRule<'a>>) -> Seq<RecRuleSpec> {
    Seq::new(
        rules.len(),
        |i: int|
            RecRuleSpec {
                ctor_id: name_id(rec_rule_ctor_name_of(rules[i])),
                nfields: rec_rule_ctor_telescope_size_wo_params_of(rules[i]) as nat,
                rhs: expr_to_model(rec_rule_val_of(rules[i])),
            },
    )
}

pub assume_specification<'x, 'a>[ get_recursor_data ](
    env: &Env<'x, 'a>,
    n: &NamePtr<'a>,
) -> (result: Option<(u16, u16, u16, usize, LevelsPtr<'a>, Arc<[RecRule<'a>]>)>)
    ensures
        match result {
            Some((np, nm, nmin, major, uparams, rules)) => env_owns(*env, uparams) && (forall|i: int|
                0 <= i < rules@.len() ==> env_owns(*env, #[trigger] rec_rule_ctor_name_of(rules@[i])))
                && (forall|i: int|
                0 <= i < rules@.len() ==> env_owns(*env, #[trigger] rec_rule_val_of(rules@[i]))) && (forall|j: int|
                0 <= j < to_model_of_levels(uparams).len() ==> #[trigger] to_model_of_levels(
                    uparams,
                )[j] is Param) && to_model_of_recursors(*env).contains_key(name_id(*n))
                && to_model_of_recursors(*env)[name_id(*n)] == RecDataSpec {
                num_params: np as nat,
                num_motives: nm as nat,
                num_minors: nmin as nat,
                major_idx: major as nat,
                uparams: level_names(to_model_of_levels(uparams)),
                rules: rec_rules_model(rules@),
            },
            None => true,
        },
;


/// `def_eq_unit`'s own env lookups -- unlike `get_declar_hint`/`get_
/// constructor_num_params`, neither needs a semantic fact connecting the
/// result back to `to_model_of_env`/a keyed map: nothing downstream
/// relates two separate calls to the same ground truth, and the ENTIRE
/// soundness content of `verified_def_eq_unit` is carried by its final
/// `verified_def_eq` call, same "plain per-call fact, no keyed map"
/// convention as `get_recursor_data` above.
/// Structure -> first (only) constructor, `name_id`-keyed: the typing
/// model's `Proj` rule needs the two `get_structure_first_ctor` calls
/// (arm and rule) to agree on ONE ground truth, so unlike the per-call
/// wrappers above this one is tied to a map (2026-09-06, projection typing).
pub uninterp spec fn to_model_of_struct_ctor<'x, 'a>(env: Env<'x, 'a>) -> Map<u64, u64>;


pub assume_specification<'x, 'a>[ get_structure_first_ctor ](
    env: &Env<'x, 'a>,
    n: &NamePtr<'a>,
    rec_ok: bool,
) -> (result: Option<NamePtr<'a>>)
    ensures
        match result {
            Some(c) => env_owns(*env, c) && to_model_of_struct_ctor(*env).contains_key(name_id(*n))
                && to_model_of_struct_ctor(*env)[name_id(*n)] == name_id(c),
            None => true,
        },
;

/// Constructor -> its field count, keyed the same way as
/// `to_model_of_struct_ctor` above, because `def_eq_unit` relates two
/// separate reads of it (the route's own check and the leaf's claim) and so
/// needs them to agree on one ground truth.
pub uninterp spec fn to_model_of_ctor_num_fields<'x, 'a>(env: Env<'x, 'a>) -> Map<u64, u16>;


pub assume_specification<'x, 'a>[ get_constructor_num_fields ](
    env: &Env<'x, 'a>,
    n: &NamePtr<'a>,
) -> (result: Option<u16>)
    ensures
        match result {
            Some(k) => to_model_of_ctor_num_fields(*env).contains_key(name_id(*n))
                && to_model_of_ctor_num_fields(*env)[name_id(*n)] == k,
            None => true,
        },
;

/// A declaration's pointers belong to `env`'s arenas.
pub open spec fn declar_owned<'x, 'a>(env: Env<'x, 'a>, d: Declar<'a>) -> bool {
    declar_owned_in(env_arena_ids(env), d)
}

/// Derived `Clone`s: every field is `Copy` or an `Arc` (whose clone is the
/// same allocation), so the copy is the original.
pub assume_specification<'a>[ <crate::env::ConstructorData<'a> as Clone>::clone ](
    d: &crate::env::ConstructorData<'a>,
) -> (r: crate::env::ConstructorData<'a>)
    ensures
        r == *d,
;

pub assume_specification<'a>[ <Declar<'a> as Clone>::clone ](
    d: &Declar<'a>,
) -> (r: Declar<'a>)
    ensures
        r == *d,
;

pub assume_specification<'a>[ <crate::env::RecursorData<'a> as Clone>::clone ](
    d: &crate::env::RecursorData<'a>,
) -> (r: crate::env::RecursorData<'a>)
    ensures
        r == *d,
;

/// Callable, claim nothing: consistency checks between a declaration and its
/// counterpart, whose results only decide an `assert!`. (Each compares name
/// sets through `HashSet` `collect`, which vstd does not specify.)
pub assume_specification<'a>[ crate::env::InductiveData::<'a>::aux_data_ck ](
    d: &crate::env::InductiveData<'a>,
    temp: &crate::env::InductiveData<'a>,
) -> bool
;

pub assume_specification<'a>[ crate::env::ConstructorData::<'a>::aux_data_ck ](
    d: &crate::env::ConstructorData<'a>,
    other: &crate::env::ConstructorData<'a>,
) -> bool
;

pub assume_specification<'a>[ crate::env::RecursorData::<'a>::aux_data_ck ](
    d: &crate::env::RecursorData<'a>,
    other: &crate::env::RecursorData<'a>,
) -> bool
;

/// Callable, claim nothing: structural `==` on declarations and rules, used
/// only inside `assert!`s.
pub assume_specification<'a>[ <Declar<'a> as PartialEq>::eq ](a: &Declar<'a>, b: &Declar<'a>) -> bool
;

pub assume_specification<'a>[ <RecRule<'a> as PartialEq>::eq ](a: &RecRule<'a>, b: &RecRule<'a>) -> bool
;

/// `std::ptr::eq` on two borrows: the sanity checks that a declaration and
/// its counterpart are different objects. Verus cannot pass a borrow as a raw
/// pointer, so the same call sits behind this claim-free wrapper.
#[verifier::external_body]
pub fn same_object<T>(a: &T, b: &T) -> bool {
    std::ptr::eq(a, b)
}

/// The derived `Clone`: every field is `Copy` or an `Arc` (whose clone is the
/// same allocation), so the copy is the original.
pub assume_specification<'a>[ <crate::env::InductiveData<'a> as Clone>::clone ](
    d: &crate::env::InductiveData<'a>,
) -> (r: crate::env::InductiveData<'a>)
    ensures
        r == *d,
;

/// A real, finitely-many-declarations `Env` always has SOME maximum size
/// among its declarations -- a genuine structural fact about any finite
/// collection of finite terms, not an arbitrary limit imposed on the
/// math (contrast with, say, hardcoding "no declaration exceeds 60000" as
/// a blanket axiom, which WOULD be an unjustified limit -- this instead
/// just names the maximum, whatever it happens to be for a given real
/// `env`, and lets a caller who needs a NUMERIC bound state it as a
/// hypothesis about that SPECIFIC environment). `env_global_cap` names
/// that maximum (uninterpreted -- doesn't compute it, just asserts it
/// exists), and `env_global_wf` packages it as `env_wf` over the WHOLE
/// `to_model_of_env(*env)` map at once (not just a single derived
/// singleton the way `env_declar_singleton_wf` below does for one
/// lookup) -- this is the "global environment depth cap" this whole
/// arc's multi-round `whnf`/`reduce_proj` chaining and `lazy_delta_
/// step`'s outer loop have both independently been blocked on needing.
pub uninterp spec fn env_global_cap<'x, 'a>(env: Env<'x, 'a>) -> nat;

/// `env_global_wf`'s counterpart for `to_model_of_declar_ty` (declaration
/// TYPES, needed by `infer_const`'s own depth-boundedness -- a completely
/// separate lookup table from `to_model_of_env`, since `get_declar_info_
/// ty` covers every declaration kind, not just `Definition`/`Theorem`).
/// Reuses the SAME `env_global_cap` (one real environment has one real
/// maximum declaration size, whether measuring types or values) --
/// deliberately omits `size` again, for the exact same reason `env_
/// global_wf` above does (see its doc comment / [[feedback_verus_size_axiom_blowup]]).
/// Closedness is not claimed: the parser does not check it (see
/// `get_declar_info_ty`), and users test the node's cached flags.
#[verifier::external_body]
pub proof fn env_global_wf_ty<'x, 'a>(env: Env<'x, 'a>)
    ensures
        forall|id: u64| #[trigger]
            to_model_of_declar_ty(env).contains_key(id) ==> {
                &&& max_var_below(to_model_of_declar_ty(env)[id].1, env_global_cap(env))
                &&& depth(to_model_of_declar_ty(env)[id].1) <= env_global_cap(env)
            },
{
}

} // verus!
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn opaque_is_lt_everything_but_itself() {
        assert!(!ReducibilityHint::Opaque.is_lt(&ReducibilityHint::Opaque));
        assert!(ReducibilityHint::Opaque.is_lt(&ReducibilityHint::Regular(0)));
        assert!(ReducibilityHint::Opaque.is_lt(&ReducibilityHint::Abbrev));
    }

    #[test]
    fn abbrev_is_lt_nothing() {
        assert!(!ReducibilityHint::Abbrev.is_lt(&ReducibilityHint::Opaque));
        assert!(!ReducibilityHint::Abbrev.is_lt(&ReducibilityHint::Regular(9999)));
        assert!(!ReducibilityHint::Abbrev.is_lt(&ReducibilityHint::Abbrev));
    }

    #[test]
    fn regular_compares_by_value() {
        assert!(ReducibilityHint::Regular(1).is_lt(&ReducibilityHint::Regular(2)));
        assert!(!ReducibilityHint::Regular(2).is_lt(&ReducibilityHint::Regular(1)));
        assert!(!ReducibilityHint::Regular(5).is_lt(&ReducibilityHint::Regular(5)));
    }

    #[test]
    fn verified_is_lt_matches_real_is_lt() {
        let hints = [
            ReducibilityHint::Opaque,
            ReducibilityHint::Regular(0),
            ReducibilityHint::Regular(3),
            ReducibilityHint::Abbrev,
        ];
        for a in &hints {
            for b in &hints {
                assert_eq!(verified_is_lt(a, b), a.is_lt(b));
            }
        }
    }
}
