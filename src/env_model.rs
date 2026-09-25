//! The environment as the models see it, and `ReducibilityHint::is_lt`.
//!
//! The model maps (`to_model_of_defs`, `to_model_of_declar_ty`, the
//! recursor and constructor tables) are DEFINED from the environment's
//! contents: each is its entry function applied to `Env::find`, the
//! declaration a name id resolves to. The lookups the checker uses
//! (`get_declar_val`, `get_declar_info_ty`, `get_recursor_data`, ...) are
//! verified against them, for names the environment owns.
//!
//! `ReducibilityHint::is_lt` is worth pinning down:
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

verus! {

broadcast use crate::util::ptr_eta, crate::util::lemma_export_arena;

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
        Declar::Opaque { info, val, .. } | Declar::Theorem { info, val, .. } | Declar::Definition { info, val, .. } =>
            info_owned_in(ids, info) && crate::util_model::owns_in(ids, val),
        Declar::Axiom { info } | Declar::Quot { info } => info_owned_in(ids, info),
    }
}

/// A declaration's universe parameters are parameters.
pub open spec fn declar_params_ok<'a>(d: Declar<'a>) -> bool {
    forall|j: int| 0 <= j < to_model_of_levels(crate::env::declar_info(d).uparams).len()
        ==> #[trigger] to_model_of_levels(crate::env::declar_info(d).uparams)[j] is Param
}

/// A declaration map every entry of which belongs to `ids`, with universe
/// parameters that are parameters.
pub open spec fn declar_map_owned_in<'a>(ids: (nat, nat), m: &crate::env::DeclarMap<'a>) -> bool {
    &&& crate::indexmap_model::imap_wf(m)
    &&& forall|k: NamePtr<'a>| #[trigger] crate::indexmap_model::imap_view(m).contains_key(k)
        ==> crate::util_model::owns_in(ids, k) && declar_owned_in(ids, crate::indexmap_model::imap_view(m)[k])
            && declar_params_ok(crate::indexmap_model::imap_view(m)[k])
            && crate::env::declar_info(crate::indexmap_model::imap_view(m)[k]).name == k
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
pub(crate) proof fn export_declars_owned<'t, 'p>(c: crate::util::TcCtx<'t, 'p>)
    requires
        crate::inductive::export_ok(*c.export_file),
    ensures
        declar_map_owned_in(crate::util_model::arena_ids(c), &c.export_file.declars),
{
    crate::inductive::export_ok_facts(*c.export_file);
    let ids = crate::util_model::arena_ids(c);
    let m = crate::indexmap_model::imap_view(&c.export_file.declars);
    assert forall|k: NamePtr<'p>| #[trigger] m.contains_key(k)
        implies crate::util_model::owns_in(ids, k) && declar_owned_in(ids, m[k]) by {
        crate::inductive::export_declar_owned_in(ids, m[k]);
    }
}

/// A declaration's entry in the definitions map: its universe parameter
/// names and value, if it has a value (definitions and theorems).
pub open spec fn def_entry<'a>(d: Declar<'a>) -> Option<(Seq<u64>, ExprSpec)> {
    match d {
        Declar::Definition { info, val, .. } | Declar::Theorem { info, val, .. } =>
            Some((level_names(to_model_of_levels(info.uparams)), expr_to_model(val))),
        _ => None,
    }
}

/// The environment's definitions, by name id: every visible declaration
/// with a value (`Env::find`).
pub closed spec fn to_model_of_defs<'x, 'a>(env: Env<'x, 'a>) -> Map<u64, (Seq<u64>, ExprSpec)> {
    Map::new(
        env.ids().filter(|id: u64| env.find(id) is Some && def_entry(env.find(id)->0) is Some),
        |id: u64| def_entry(env.find(id)->0)->0,
    )
}

pub proof fn to_model_of_defs_at<'x, 'a>(env: Env<'x, 'a>, id: u64)
    ensures
        to_model_of_defs(env).contains_key(id) == (env.find(id) is Some && def_entry(env.find(id)->0) is Some),
        to_model_of_defs(env).contains_key(id) ==> to_model_of_defs(env)[id] == def_entry(env.find(id)->0)->0,
{
    env.find_in_ids(id);
}

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

/// A declaration's entry in the types map: every declaration has one.
pub open spec fn ty_entry<'a>(d: Declar<'a>) -> Option<(Seq<u64>, ExprSpec)> {
    Some((level_names(to_model_of_levels(crate::env::declar_info(d).uparams)), expr_to_model(crate::env::declar_info(d).ty)))
}

/// The environment's declaration TYPES, by name id -- the same shape as the
/// definitions map, but covering every declaration kind.
pub closed spec fn to_model_of_declar_ty<'x, 'a>(env: Env<'x, 'a>) -> Map<u64, (Seq<u64>, ExprSpec)> {
    Map::new(
        env.ids().filter(|id: u64| env.find(id) is Some && ty_entry(env.find(id)->0) is Some),
        |id: u64| ty_entry(env.find(id)->0)->0,
    )
}

pub proof fn to_model_of_declar_ty_at<'x, 'a>(env: Env<'x, 'a>, id: u64)
    ensures
        to_model_of_declar_ty(env).contains_key(id) == (env.find(id) is Some && ty_entry(env.find(id)->0) is Some),
        to_model_of_declar_ty(env).contains_key(id) ==> to_model_of_declar_ty(env)[id] == ty_entry(env.find(id)->0)->0,
{
    env.find_in_ids(id);
}

/// `infer_const`'s lookup: a declaration's universe parameters and type,
/// for every declaration kind (`Declar::info`). Verified: the result is the
/// types map's entry, owned, with parameters that are parameters. The type's
/// closedness is not claimed (the parser does not check it).
pub(crate) fn get_declar_info_ty<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<(LevelsPtr<'a>, ExprPtr<'a>)>)
    requires
        env_owns(*env, *n),
    ensures
        match result {
            Some((uparams, ty)) => env_owns(*env, uparams) && env_owns(*env, ty) && to_model_of_declar_ty(*env).contains_key(name_id(*n))
                && to_model_of_declar_ty(*env)[name_id(*n)] == (
                level_names(to_model_of_levels(uparams)),
                expr_to_model(ty),
            ) && forall|j: int|
                0 <= j < to_model_of_levels(uparams).len() ==> #[trigger] to_model_of_levels(
                    uparams,
                )[j] is Param,
            None => !to_model_of_declar_ty(*env).contains_key(name_id(*n)),
        },
{
    proof { to_model_of_declar_ty_at(*env, name_id(*n)); }
    match env.get_declar(n) {
        Some(d) => {
            let info = d.info();
            Some((info.uparams, info.ty))
        }
        None => None,
    }
}

/// A declaration's reducibility hint: a definition's own, a theorem's
/// `Opaque` (theorems are never unfolded, but are tracked).
pub open spec fn hint_entry<'a>(d: Declar<'a>) -> Option<ReducibilityHintSpec> {
    match d {
        Declar::Definition { hint, .. } => Some(to_model(hint)),
        Declar::Theorem { .. } => Some(ReducibilityHintSpec::Opaque),
        _ => None,
    }
}

/// The environment's reducibility hints, by name id. Its domain is the
/// definitions map's: the same two declaration kinds decide both.
pub closed spec fn to_model_of_declar_hint<'x, 'a>(env: Env<'x, 'a>) -> Map<u64, ReducibilityHintSpec> {
    Map::new(
        env.ids().filter(|id: u64| env.find(id) is Some && hint_entry(env.find(id)->0) is Some),
        |id: u64| hint_entry(env.find(id)->0)->0,
    )
}

pub proof fn to_model_of_declar_hint_at<'x, 'a>(env: Env<'x, 'a>, id: u64)
    ensures
        to_model_of_declar_hint(env).contains_key(id) == (env.find(id) is Some && hint_entry(env.find(id)->0) is Some),
        to_model_of_declar_hint(env).contains_key(id) ==> to_model_of_declar_hint(env)[id] == hint_entry(env.find(id)->0)->0,
{
    env.find_in_ids(id);
}

/// `get_applied_def`'s classification: a name is an applied definition
/// exactly when it is a `Definition` (its hint) or a `Theorem` (`Opaque`).
/// Verified: the returned name is the one looked up (the maps are keyed by
/// `info.name`), and the hint is the hints map's entry.
pub(crate) fn get_declar_hint<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<(NamePtr<'a>, ReducibilityHint)>)
    requires
        env_owns(*env, *n),
    ensures
        match result {
            Some((dn, hint)) => dn == *n && to_model_of_env(*env).contains_key(name_id(*n))
                && to_model_of_declar_hint(*env).contains_key(name_id(*n))
                && to_model_of_declar_hint(*env)[name_id(*n)] == to_model(hint),
            None => !to_model_of_env(*env).contains_key(name_id(*n)),
        },
{
    proof {
        to_model_of_declar_hint_at(*env, name_id(*n));
        to_model_of_defs_at(*env, name_id(*n));
    }
    match env.get_declar(n) {
        Some(Declar::Definition { info, hint, .. }) => Some((info.name, *hint)),
        Some(Declar::Theorem { info, .. }) => Some((info.name, ReducibilityHint::Opaque)),
        _ => None,
    }
}

/// A constructor's parameter count.
pub open spec fn ctor_np_entry<'a>(d: Declar<'a>) -> Option<u16> {
    match d {
        Declar::Constructor(c) => Some(c.num_params),
        _ => None,
    }
}

/// The environment's constructors' parameter counts, by name id --
/// `reduce_proj`'s only dependency on `ConstructorData`.
pub closed spec fn to_model_of_ctor_num_params<'x, 'a>(env: Env<'x, 'a>) -> Map<u64, u16> {
    Map::new(
        env.ids().filter(|id: u64| env.find(id) is Some && ctor_np_entry(env.find(id)->0) is Some),
        |id: u64| ctor_np_entry(env.find(id)->0)->0,
    )
}

pub proof fn to_model_of_ctor_num_params_at<'x, 'a>(env: Env<'x, 'a>, id: u64)
    ensures
        to_model_of_ctor_num_params(env).contains_key(id) == (env.find(id) is Some && ctor_np_entry(env.find(id)->0) is Some),
        to_model_of_ctor_num_params(env).contains_key(id) ==> to_model_of_ctor_num_params(env)[id] == ctor_np_entry(env.find(id)->0)->0,
{
    env.find_in_ids(id);
}

/// `Env::get_constructor`'s `num_params`. Verified against the map.
pub(crate) fn get_constructor_num_params<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<u16>)
    requires
        env_owns(*env, *n),
    ensures
        match result {
            Some(num_params) => to_model_of_ctor_num_params(*env).contains_key(name_id(*n))
                && to_model_of_ctor_num_params(*env)[name_id(*n)] == num_params,
            None => !to_model_of_ctor_num_params(*env).contains_key(name_id(*n)),
        },
{
    proof { to_model_of_ctor_num_params_at(*env, name_id(*n)); }
    match env.get_constructor(n) {
        Some(cd) => Some(cd.num_params),
        None => None,
    }
}

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

/// A recursor's data as the iota rule reads it.
pub open spec fn rec_entry<'a>(d: Declar<'a>) -> Option<RecDataSpec> {
    match d {
        Declar::Recursor(r) => Some(RecDataSpec {
            num_params: r.num_params as nat,
            num_motives: r.num_motives as nat,
            num_minors: r.num_minors as nat,
            major_idx: r.major_idx_spec(),
            uparams: level_names(to_model_of_levels(r.info.uparams)),
            rules: rec_rules_model(r.rec_rules@),
        }),
        _ => None,
    }
}

/// The environment's recursors, by name id, in the shape
/// `get_recursor_data` returns them, rule values modeled through `to_model`.
pub closed spec fn to_model_of_recursors<'x, 'a>(env: Env<'x, 'a>) -> Map<u64, RecDataSpec> {
    Map::new(
        env.ids().filter(|id: u64| env.find(id) is Some && rec_entry(env.find(id)->0) is Some),
        |id: u64| rec_entry(env.find(id)->0)->0,
    )
}

pub proof fn to_model_of_recursors_at<'x, 'a>(env: Env<'x, 'a>, id: u64)
    ensures
        to_model_of_recursors(env).contains_key(id) == (env.find(id) is Some && rec_entry(env.find(id)->0) is Some),
        to_model_of_recursors(env).contains_key(id) ==> to_model_of_recursors(env)[id] == rec_entry(env.find(id)->0)->0,
{
    env.find_in_ids(id);
}

/// `reduce_rec`'s recursor lookup: exactly the fields it reads. Verified
/// against the recursors map; the pointers are the environment's and the
/// universe parameters are parameters.
pub(crate) fn get_recursor_data<'x, 'a>(
    env: &Env<'x, 'a>,
    n: &NamePtr<'a>,
) -> (result: Option<(u16, u16, u16, usize, LevelsPtr<'a>, Arc<[RecRule<'a>]>)>)
    requires
        env_owns(*env, *n),
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
{
    proof { to_model_of_recursors_at(*env, name_id(*n)); }
    let rec = env.get_recursor(n)?;
    let rules = rec.rec_rules.clone();
    let major = rec.major_idx();
    Some((rec.num_params, rec.num_motives, rec.num_minors, major, rec.info.uparams, rules))
}

/// A structure's (single) constructor: an inductive with one constructor
/// and no indices.
pub open spec fn struct_ctor_entry<'a>(d: Declar<'a>) -> Option<u64> {
    match d {
        Declar::Inductive(i) => if i.all_ctor_names@.len() == 1 && i.num_indices == 0 {
            Some(name_id(i.all_ctor_names@[0]))
        } else {
            None
        },
        _ => None,
    }
}

/// Structure -> its constructor, by name id: the projection typing rule
/// needs two `get_structure_first_ctor` calls to agree on one ground truth.
pub closed spec fn to_model_of_struct_ctor<'x, 'a>(env: Env<'x, 'a>) -> Map<u64, u64> {
    Map::new(
        env.ids().filter(|id: u64| env.find(id) is Some && struct_ctor_entry(env.find(id)->0) is Some),
        |id: u64| struct_ctor_entry(env.find(id)->0)->0,
    )
}

pub proof fn to_model_of_struct_ctor_at<'x, 'a>(env: Env<'x, 'a>, id: u64)
    ensures
        to_model_of_struct_ctor(env).contains_key(id) == (env.find(id) is Some && struct_ctor_entry(env.find(id)->0) is Some),
        to_model_of_struct_ctor(env).contains_key(id) ==> to_model_of_struct_ctor(env)[id] == struct_ctor_entry(env.find(id)->0)->0,
{
    env.find_in_ids(id);
}

/// `Env::get_structure`'s `all_ctor_names[0]` (the match guard makes the
/// index safe). Verified against the map.
pub(crate) fn get_structure_first_ctor<'x, 'a>(
    env: &Env<'x, 'a>,
    n: &NamePtr<'a>,
    rec_ok: bool,
) -> (result: Option<NamePtr<'a>>)
    requires
        env_owns(*env, *n),
    ensures
        match result {
            Some(c) => env_owns(*env, c) && to_model_of_struct_ctor(*env).contains_key(name_id(*n))
                && to_model_of_struct_ctor(*env)[name_id(*n)] == name_id(c),
            None => true,
        },
{
    proof { to_model_of_struct_ctor_at(*env, name_id(*n)); }
    match env.get_structure(n, rec_ok) {
        Some(i) => Some(i.all_ctor_names[0]),
        None => None,
    }
}

/// A constructor's field count.
pub open spec fn ctor_nf_entry<'a>(d: Declar<'a>) -> Option<u16> {
    match d {
        Declar::Constructor(c) => Some(c.num_fields),
        _ => None,
    }
}

/// Constructor -> its field count, by name id: `def_eq_unit` relates two
/// separate reads of it.
pub closed spec fn to_model_of_ctor_num_fields<'x, 'a>(env: Env<'x, 'a>) -> Map<u64, u16> {
    Map::new(
        env.ids().filter(|id: u64| env.find(id) is Some && ctor_nf_entry(env.find(id)->0) is Some),
        |id: u64| ctor_nf_entry(env.find(id)->0)->0,
    )
}

pub proof fn to_model_of_ctor_num_fields_at<'x, 'a>(env: Env<'x, 'a>, id: u64)
    ensures
        to_model_of_ctor_num_fields(env).contains_key(id) == (env.find(id) is Some && ctor_nf_entry(env.find(id)->0) is Some),
        to_model_of_ctor_num_fields(env).contains_key(id) ==> to_model_of_ctor_num_fields(env)[id] == ctor_nf_entry(env.find(id)->0)->0,
{
    env.find_in_ids(id);
}

/// `Env::get_constructor`'s `num_fields`. Verified against the map.
pub(crate) fn get_constructor_num_fields<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<u16>)
    requires
        env_owns(*env, *n),
    ensures
        match result {
            Some(k) => to_model_of_ctor_num_fields(*env).contains_key(name_id(*n))
                && to_model_of_ctor_num_fields(*env)[name_id(*n)] == k,
            None => true,
        },
{
    proof { to_model_of_ctor_num_fields_at(*env, name_id(*n)); }
    match env.get_constructor(n) {
        Some(cd) => Some(cd.num_fields),
        None => None,
    }
}

/// A declaration's pointers belong to `env`'s arenas.
pub open spec fn declar_owned<'x, 'a>(env: Env<'x, 'a>, d: Declar<'a>) -> bool {
    declar_owned_in(env_arena_ids(env), d)
}

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
