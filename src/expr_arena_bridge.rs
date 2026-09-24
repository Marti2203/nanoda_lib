//! Bridges the real, unmodified arena-based `Expr<'a>`/`TcCtx<'t,'p>` code in
//! `util.rs`/`expr.rs` to the standalone `ExprSpec` model in
//! `expr_model.rs`, the same way `level_arena_bridge.rs` bridges
//! `level_model.rs`. Nothing in `util.rs`/`expr.rs` is modified; this works
//! entirely by registering the real types as opaque externals and giving
//! Verus hand-written, *trusted* contracts for them (`assume_specification`)
//! rather than re-verifying `TcCtx`'s arena implementation. Same trust
//! boundary as `level_arena_bridge.rs`: the axioms below assert that the
//! arena's hash-consing and cached fields behave as documented, without
//! checking `IndexSet`'s implementation or `mk_*`'s bookkeeping arithmetic.
//!
//! `Expr<'a>` is registered `external_body`, so (as with `Level<'a>`) plain
//! (non-`verus!`) helper functions do the actual pattern-matching, each with
//! its own small trusted contract. `Sort`/`Const`/`StringLit`/`NatLit` all
//! collapse to `ExprSpec::Closed` (their payload -- a `Level`, a
//! `Name`+`Levels`, a string/bignum -- is irrelevant to `inst`/`abstr`'s
//! bound-variable mechanics, matching `expr_model.rs`'s stated
//! simplification); `Pi`/`Lambda` both collapse to `ExprSpec::Bind`.
//!
//! `Local`'s free-variable identity is modeled via `expr_id`, an
//! uninterpreted injective function of the *pointer* itself (not the
//! `FVarId` field): the real `abstr_aux` compares full `ExprPtr` equality
//! (`*x == e`), which -- given hash-consing -- is a strictly finer
//! comparison than comparing `FVarId`s alone would be (two hash-consed
//! `Local` nodes could in principle share an `FVarId` while differing in
//! `binder_type`, though that shouldn't arise for well-formed terms), so
//! `expr_id` mirrors `name_id`/`level_ptr_eq`'s pointer-identity approach
//! rather than reaching into the `Local` payload.
#[cfg(verus_only)]
use crate::beta_model::{
    args_size_sum, const_expr_no_levels_canonical, depth_le_size, max_var_below, max_var_below_mono,
    nlbv_bound_implies_max_var_below, pstep, pstep_chain_valid, pstep_spine_app_star, pstep_star, pstep_star_one,
    pstep_star_refl, pstep_star_spine_reduce, pstep_star_trans, size, spine_app, spine_app_bounds, spine_app_compose,
    spine_app_concat, spine_app_decompose, spine_app_max_var_below, spine_app_nlbv, spine_app_size, spine_bind,
    spine_bind_depth, spine_bind_nlbv, spine_reduce, spine_reduce_bounds, spine_reduce_eq_subst_full, string_free,
    string_free_lits_ok, string_lit_expand_model, string_lits_ok, string_lits_ok_spine_app, subst1, subst1_depth_bound,
    subst1_max_var_below, subst_c, subst_c_eq_subst_full, subst_full_depth_bound_n, subst_full_nlbv_bound,
    subst_full_nlbv_bound_n,
};
use crate::expr::{BinderStyle, Expr, FVarId};
#[cfg(verus_only)]
use crate::expr_model::fv_absent;
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
use crate::expr_model::NatLitPayload;
use crate::expr_model::StringLitPayload;
#[cfg(verus_only)]
use crate::expr_model::{
    abstr_full, abstr_full_depth, depth, find_from_end, has_fv, mul_ge_one, mul_pred_step, nlbv, subst_expr_levels,
    subst_expr_levels_rel, subst_full, subst_full_noop,
};
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model as level_to_model;
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, to_model_of_levels};
use crate::level_arena_bridge::{verified_subst_level, verified_subst_levels};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_model::{interp, level_names, subst_env};
#[cfg(verus_only)]
use crate::name_arena_bridge::{child_ok, ptr_index, ptr_is_tc};
use crate::nat_lit_model::{biguint_is_zero, biguint_pred};
#[cfg(verus_only)]
use crate::quot_model::local_type;
#[allow(unused_imports)]
use crate::util::IterSpec;
#[allow(unused_imports)]
use crate::util::TcCtx;
use crate::util::{ExprPtr, LevelPtr, LevelsPtr, NamePtr, StringPtr};
#[allow(unused_imports)]
use vstd::prelude::*;

/// `expr.rs::get_bignum_from_expr`'s `NatLit` arm, standalone: dereference
/// and clone the arena-stored `BigUint` (real `read_bignum` returns
/// `Option<&BigUint>`; bridged as one opaque real function rather than
/// separately bridging `Option::cloned`/`Clone` for a foreign type).
#[allow(dead_code)]
pub(crate) fn read_bignum_value<'t, 'p: 't>(
    ctx: &TcCtx<'t, 'p>,
    p: crate::util::BigUintPtr<'t>,
) -> Option<num_bigint::BigUint> {
    ctx.read_bignum(p).cloned()
}


verus! {

/// TRANSPARENT, like `ExLevel`. The variants are visible to Verus, so the
/// kernel's own `match self.read_expr(p) { .. }` can be verified as written
/// and the `expr_as_*` accessors below become provable rather than assumed.
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExExpr<'a>(Expr<'a>);

/// TRANSPARENT, like `ExExpr`. Opaque, it needed two helper functions just to
/// name `Default` and `Implicit` inside `verus!`.
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExBinderStyle(BinderStyle);

/// TRANSPARENT, like `ExExpr`: the two variants are visible, so `fvar_id_eq`'s
/// contract is provable from the derived `PartialEq` rather than assumed.
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExFVarId(FVarId);

/// What an `ExprPtr` denotes in our `ExprSpec` model. Uninterpreted, same
/// trust boundary as `level_arena_bridge::to_model`.
pub uninterp spec fn to_model<'a>(ptr: ExprPtr<'a>) -> ExprSpec;

/// What a *shallow* `Expr` value (as returned by `read_expr`, before
/// following any of its child pointers) denotes.
/// The `FVarId` a `Local` node's model is keyed by. Uninterpreted, and the
/// ONE case of `to_model_of_expr` that cannot be structural: a `Local`'s
/// model is `Free(expr_id(ptr))`, keyed by the POINTER, which a function of
/// the shallow value cannot see. Everything else below is determined.
pub uninterp spec fn local_fvar_id_of<'a>(e: Expr<'a>) -> u32;

/// What a *shallow* `Expr` value (as returned by `read_expr`, before
/// following any of its child pointers) denotes.
///
/// DEFINED, not uninterpreted -- possible now that `ExExpr` is transparent.
/// Children are `to_model` of a POINTER, which stays uninterpreted, so this
/// is not recursive.
///
/// Note there is no `Closed` case: no real `Expr` variant denotes it. That
/// matters, because `expr_is_closed_leaf`'s contract mentions `Closed`, and
/// this file already records one silent unsoundness in exactly that spot
/// (see its doc comment) -- an axiom that was true when `Sort` collapsed
/// into `Closed` and became false when `Sort` got its own payload. A
/// definition makes that class of drift a verification failure instead of a
/// silent one.
pub open spec fn to_model_of_expr<'a>(e: Expr<'a>) -> ExprSpec {
    match e {
        Expr::Var { dbj_idx, .. } => ExprSpec::Var(dbj_idx as u32),
        Expr::Sort { level, .. } => ExprSpec::Sort(level_to_model(level)),
        Expr::Const { name, levels, .. } => ExprSpec::Const(
            name_id(name),
            to_model_of_levels(levels),
        ),
        Expr::App { fun, arg, .. } => ExprSpec::App(
            Box::new(to_model(fun)),
            Box::new(to_model(arg)),
        ),
        Expr::Pi { binder_type, body, .. } => ExprSpec::Bind(
            Box::new(to_model(binder_type)),
            Box::new(to_model(body)),
        ),
        Expr::Lambda { binder_type, body, .. } => ExprSpec::Bind(
            Box::new(to_model(binder_type)),
            Box::new(to_model(body)),
        ),
        Expr::Let { binder_type, val, body, .. } => ExprSpec::Let(
            Box::new(to_model(binder_type)),
            Box::new(to_model(val)),
            Box::new(to_model(body)),
        ),
        Expr::Proj { idx, structure, .. } => ExprSpec::Proj(idx, Box::new(to_model(structure))),
        Expr::NatLit { ptr, .. } => ExprSpec::NatLit(NatLitPayload(Ghost(bignum_ptr_value(ptr)))),
        Expr::StringLit { ptr, .. } => ExprSpec::StringLit(
            StringLitPayload(Ghost(string_chars(ptr))),
        ),
        Expr::Local { .. } => ExprSpec::Free(local_fvar_id_of(e)),
    }
}

// ---------------------------------------------------------------------
// ARENA STORAGE MODEL for expressions -- the same four facts proven for
// names and levels. This is the largest of the three node types: eleven
// shapes, up to three children, and leaves that reach into OTHER arenas
// (`Sort`'s level, `Const`'s name and levels, the literals' payloads).
// Those cost nothing here for the same reason `Level::Param` did: the model
// records them by opaque identity, so the recursion stays inside the
// expression storage.
//
// `Local` is the exception and is left as it is -- its denotation is
// `local_fvar_id_of`, an opaque identity that is deliberately NOT structural
// (see the module doc comment), so there is nothing to compute from storage.
// ---------------------------------------------------------------------
/// A stored expression's children live at strictly smaller indices.
pub open spec fn expr_children_below<'a>(e: Expr<'a>, i: nat) -> bool {
    match e {
        Expr::App { fun, arg, .. } => ptr_index(fun) < i && ptr_index(arg) < i,
        Expr::Pi { binder_type, body, .. } => ptr_index(binder_type) < i && ptr_index(body) < i,
        Expr::Lambda { binder_type, body, .. } => ptr_index(binder_type) < i && ptr_index(body) < i,
        Expr::Let { binder_type, val, body, .. } => ptr_index(binder_type) < i && ptr_index(val) < i
            && ptr_index(body) < i,
        Expr::Proj { structure, .. } => ptr_index(structure) < i,
        _ => true,
    }
}

pub open spec fn exprs_arena_wf<'a>(es: Seq<Expr<'a>>) -> bool {
    forall|i: int| 0 <= i < es.len() ==> expr_children_below(#[trigger] es[i], i as nat)
}

/// What the expression at index `i` denotes, COMPUTED from storage.
pub open spec fn expr_model_at<'a>(es: Seq<Expr<'a>>, i: nat) -> ExprSpec
    decreases i,
{
    if i >= es.len() {
        ExprSpec::Closed
    } else {
        match es[i as int] {
            Expr::Var { dbj_idx, .. } => ExprSpec::Var(dbj_idx as u32),
            Expr::Sort { level, .. } => ExprSpec::Sort(level_to_model(level)),
            Expr::Const { name, levels, .. } => ExprSpec::Const(
                name_id(name),
                to_model_of_levels(levels),
            ),
            Expr::NatLit { ptr, .. } => ExprSpec::NatLit(
                NatLitPayload(Ghost(bignum_ptr_value(ptr))),
            ),
            Expr::StringLit { ptr, .. } => ExprSpec::StringLit(
                StringLitPayload(Ghost(string_chars(ptr))),
            ),
            Expr::Local { .. } => ExprSpec::Free(local_fvar_id_of(es[i as int])),
            Expr::App { fun, arg, .. } => if ptr_index(fun) < i && ptr_index(arg) < i {
                ExprSpec::App(
                    Box::new(expr_model_at(es, ptr_index(fun))),
                    Box::new(expr_model_at(es, ptr_index(arg))),
                )
            } else {
                ExprSpec::Closed
            },
            Expr::Pi { binder_type, body, .. } => if ptr_index(binder_type) < i && ptr_index(body)
                < i {
                ExprSpec::Bind(
                    Box::new(expr_model_at(es, ptr_index(binder_type))),
                    Box::new(expr_model_at(es, ptr_index(body))),
                )
            } else {
                ExprSpec::Closed
            },
            Expr::Lambda { binder_type, body, .. } => if ptr_index(binder_type) < i && ptr_index(
                body,
            ) < i {
                ExprSpec::Bind(
                    Box::new(expr_model_at(es, ptr_index(binder_type))),
                    Box::new(expr_model_at(es, ptr_index(body))),
                )
            } else {
                ExprSpec::Closed
            },
            Expr::Let { binder_type, val, body, .. } => if ptr_index(binder_type) < i && ptr_index(
                val,
            ) < i && ptr_index(body) < i {
                ExprSpec::Let(
                    Box::new(expr_model_at(es, ptr_index(binder_type))),
                    Box::new(expr_model_at(es, ptr_index(val))),
                    Box::new(expr_model_at(es, ptr_index(body))),
                )
            } else {
                ExprSpec::Closed
            },
            Expr::Proj { idx, structure, .. } => if ptr_index(structure) < i {
                ExprSpec::Proj(idx, Box::new(expr_model_at(es, ptr_index(structure))))
            } else {
                ExprSpec::Closed
            },
        }
    }
}

/// Under acyclicity the well-foundedness guards are never taken, so the
/// computed denotation agrees with the structural reading of the node. Stated
/// for the compound shapes, which are the ones carrying a guard.
pub proof fn expr_model_at_unfold<'a>(es: Seq<Expr<'a>>, i: nat)
    requires
        exprs_arena_wf(es),
        i < es.len(),
    ensures
        ({
            let e = es[i as int];
            &&& (e matches Expr::App { fun, arg, .. } ==> expr_model_at(es, i) == ExprSpec::App(
                Box::new(expr_model_at(es, ptr_index(fun))),
                Box::new(expr_model_at(es, ptr_index(arg))),
            ))
            &&& (e matches Expr::Pi { binder_type, body, .. } ==> expr_model_at(es, i)
                == ExprSpec::Bind(
                Box::new(expr_model_at(es, ptr_index(binder_type))),
                Box::new(expr_model_at(es, ptr_index(body))),
            ))
            &&& (e matches Expr::Lambda { binder_type, body, .. } ==> expr_model_at(es, i)
                == ExprSpec::Bind(
                Box::new(expr_model_at(es, ptr_index(binder_type))),
                Box::new(expr_model_at(es, ptr_index(body))),
            ))
            &&& (e matches Expr::Proj { idx, structure, .. } ==> expr_model_at(es, i)
                == ExprSpec::Proj(idx, Box::new(expr_model_at(es, ptr_index(structure)))))
        }),
{
    assert(expr_children_below(es[i as int], i));
}

/// Non-degeneracy: `[Var 0, App(p0, p0)]` must denote `App(Var 0, Var 0)`, so
/// the definitions above cannot be collapsing everything to `Closed`.
pub proof fn expr_model_at_computes_nesting<'a>(p0: ExprPtr<'a>, h: u64)
    requires
        ptr_index(p0) == 0,
    ensures
        ({
            let es = seq![
                Expr::Var { hash: h, dbj_idx: 0 },
                Expr::App { hash: h, fun: p0, arg: p0, num_loose_bvars: 1, has_fvars: false },
            ];
            &&& exprs_arena_wf(es)
            &&& expr_model_at(es, 1) == ExprSpec::App(
                Box::new(ExprSpec::Var(0)),
                Box::new(ExprSpec::Var(0)),
            )
        }),
{
    let es: Seq<Expr<'a>> = seq![
        Expr::Var { hash: h, dbj_idx: 0 },
        Expr::App { hash: h, fun: p0, arg: p0, num_loose_bvars: 1, has_fvars: false },
    ];
    assert(es.len() == 2);
    assert(es[0] == Expr::<'a>::Var { hash: h, dbj_idx: 0 });
    assert forall|i: int| 0 <= i < es.len() implies expr_children_below(
        #[trigger] es[i],
        i as nat,
    ) by {
        if i == 0 {
        } else {
            assert(ptr_index(p0) == 0);
        }
    }
    assert(expr_model_at(es, 0) == ExprSpec::Var(0));
}

/// Two-tier denotation for expressions -- the shape the READERS need, since
/// `read_expr` selects a tier by dag marker and indexes into it.
pub open spec fn expr_model_at2<'a>(
    ef: Seq<Expr<'a>>,
    tc: Seq<Expr<'a>>,
    is_tc: bool,
    i: nat,
) -> ExprSpec
    decreases
            if is_tc {
                1int
            } else {
                0int
            },
            i,
{
    let store = if is_tc {
        tc
    } else {
        ef
    };
    if i >= store.len() {
        ExprSpec::Closed
    } else {
        match store[i as int] {
            Expr::Var { dbj_idx, .. } => ExprSpec::Var(dbj_idx as u32),
            Expr::Sort { level, .. } => ExprSpec::Sort(level_to_model(level)),
            Expr::Const { name, levels, .. } => ExprSpec::Const(
                name_id(name),
                to_model_of_levels(levels),
            ),
            Expr::NatLit { ptr, .. } => ExprSpec::NatLit(
                NatLitPayload(Ghost(bignum_ptr_value(ptr))),
            ),
            Expr::StringLit { ptr, .. } => ExprSpec::StringLit(
                StringLitPayload(Ghost(string_chars(ptr))),
            ),
            Expr::Local { .. } => ExprSpec::Free(local_fvar_id_of(store[i as int])),
            Expr::App { fun, arg, .. } => if child_ok(fun, is_tc, i) && child_ok(arg, is_tc, i) {
                ExprSpec::App(
                    Box::new(expr_model_at2(ef, tc, ptr_is_tc(fun), ptr_index(fun))),
                    Box::new(expr_model_at2(ef, tc, ptr_is_tc(arg), ptr_index(arg))),
                )
            } else {
                ExprSpec::Closed
            },
            Expr::Pi { binder_type, body, .. }
            | Expr::Lambda { binder_type, body, .. } => if child_ok(binder_type, is_tc, i)
                && child_ok(body, is_tc, i) {
                ExprSpec::Bind(
                    Box::new(
                        expr_model_at2(ef, tc, ptr_is_tc(binder_type), ptr_index(binder_type)),
                    ),
                    Box::new(expr_model_at2(ef, tc, ptr_is_tc(body), ptr_index(body))),
                )
            } else {
                ExprSpec::Closed
            },
            Expr::Let { binder_type, val, body, .. } => if child_ok(binder_type, is_tc, i)
                && child_ok(val, is_tc, i) && child_ok(body, is_tc, i) {
                ExprSpec::Let(
                    Box::new(
                        expr_model_at2(ef, tc, ptr_is_tc(binder_type), ptr_index(binder_type)),
                    ),
                    Box::new(expr_model_at2(ef, tc, ptr_is_tc(val), ptr_index(val))),
                    Box::new(expr_model_at2(ef, tc, ptr_is_tc(body), ptr_index(body))),
                )
            } else {
                ExprSpec::Closed
            },
            Expr::Proj { idx, structure, .. } => if child_ok(structure, is_tc, i) {
                ExprSpec::Proj(
                    idx,
                    Box::new(expr_model_at2(ef, tc, ptr_is_tc(structure), ptr_index(structure))),
                )
            } else {
                ExprSpec::Closed
            },
        }
    }
}

/// Appending to the local tier never changes an export-file pointer's
/// denotation.
pub proof fn expr_model_at2_append_tc<'a>(ef: Seq<Expr<'a>>, tc: Seq<Expr<'a>>, e: Expr<'a>, i: nat)
    ensures
        expr_model_at2(ef, tc.push(e), false, i) == expr_model_at2(ef, tc, false, i),
    decreases i,
{
    if i < ef.len() {
        match ef[i as int] {
            Expr::App { fun, arg, .. } => {
                if child_ok(fun, false, i) {
                    expr_model_at2_append_tc(ef, tc, e, ptr_index(fun));
                }
                if child_ok(arg, false, i) {
                    expr_model_at2_append_tc(ef, tc, e, ptr_index(arg));
                }
            },
            Expr::Pi { binder_type, body, .. } | Expr::Lambda { binder_type, body, .. } => {
                if child_ok(binder_type, false, i) {
                    expr_model_at2_append_tc(ef, tc, e, ptr_index(binder_type));
                }
                if child_ok(body, false, i) {
                    expr_model_at2_append_tc(ef, tc, e, ptr_index(body));
                }
            },
            Expr::Let { binder_type, val, body, .. } => {
                if child_ok(binder_type, false, i) {
                    expr_model_at2_append_tc(ef, tc, e, ptr_index(binder_type));
                }
                if child_ok(val, false, i) {
                    expr_model_at2_append_tc(ef, tc, e, ptr_index(val));
                }
                if child_ok(body, false, i) {
                    expr_model_at2_append_tc(ef, tc, e, ptr_index(body));
                }
            },
            Expr::Proj { structure, .. } => {
                if child_ok(structure, false, i) {
                    expr_model_at2_append_tc(ef, tc, e, ptr_index(structure));
                }
            },
            _ => {},
        }
    }
}

/// MONOTONICITY: allocating never changes what an existing pointer denotes.
pub proof fn expr_model_at_append<'a>(es: Seq<Expr<'a>>, e: Expr<'a>, i: nat)
    requires
        i < es.len(),
    ensures
        expr_model_at(es.push(e), i) == expr_model_at(es, i),
    decreases i,
{
    match es[i as int] {
        Expr::App { fun, arg, .. } => {
            if ptr_index(fun) < i {
                expr_model_at_append(es, e, ptr_index(fun));
            }
            if ptr_index(arg) < i {
                expr_model_at_append(es, e, ptr_index(arg));
            }
        },
        Expr::Pi { binder_type, body, .. } | Expr::Lambda { binder_type, body, .. } => {
            if ptr_index(binder_type) < i {
                expr_model_at_append(es, e, ptr_index(binder_type));
            }
            if ptr_index(body) < i {
                expr_model_at_append(es, e, ptr_index(body));
            }
        },
        Expr::Let { binder_type, val, body, .. } => {
            if ptr_index(binder_type) < i {
                expr_model_at_append(es, e, ptr_index(binder_type));
            }
            if ptr_index(val) < i {
                expr_model_at_append(es, e, ptr_index(val));
            }
            if ptr_index(body) < i {
                expr_model_at_append(es, e, ptr_index(body));
            }
        },
        Expr::Proj { structure, .. } => {
            if ptr_index(structure) < i {
                expr_model_at_append(es, e, ptr_index(structure));
            }
        },
        _ => {},
    }
    assert(es.push(e)[i as int] == es[i as int]);
}

/// A `Local` pointer's free-variable identity, standing in for genuine
/// `ExprPtr` identity (see the module doc comment).
pub open spec fn expr_id<'a>(ptr: ExprPtr<'a>) -> u32 {
    ptr.raw
}

// ARENA-IDENTITY STAGE 2: false across arenas; see `name_id_injective`.
#[verifier::external_body]
pub proof fn expr_id_injective<'a>(a: ExprPtr<'a>, b: ExprPtr<'a>)
    ensures
        (a == b) <==> (expr_id(a) == expr_id(b)),
{
}

/// Was an `assume_specification`; `Ptr`'s own `PartialEq` is specified now
/// (`util_model.rs`), so the body proves the contract.
#[allow(dead_code)]
pub(crate) fn expr_ptr_eq<'t>(a: ExprPtr<'t>, b: ExprPtr<'t>) -> (result: bool)
    ensures
        result == (a == b),
{
    a == b
}

// ---------------------------------------------------------------------
// The de Bruijn-LEVEL abstraction's model support.
//
// `abstr_aux_levels` branches on a free variable's `DbjLevel` SERIAL, and the
// model has erased it: `to_model(local) == ExprSpec::Free(expr_id(ptr))` carries
// an opaque pointer identity, not the serial.
//
// `FVarId` is transparent, so the FVarId-keyed version below is a DEFINITION.
// The ID-keyed one cannot be: tying it to the node means inverting `expr_id`,
// which is injective (`expr_id_injective`) but not invertible in spec without a
// `choose` over a lifetime-parameterised type. So `dbj_serial` is uninterpreted
// and keyed on `read_expr`, exactly as the `Const`/`Local`/`NatLit`/`StringLit`
// payload clauses are -- that keying is what made those provable rather than
// assumed, and it does the same job here.
// ---------------------------------------------------------------------
/// The `DbjLevel` serial an `FVarId` carries, `None` for a `Unique` one.
/// DEFINED -- `ExFVarId` is transparent.
pub open spec fn fvar_dbj_serial(id: FVarId) -> Option<u16> {
    match id {
        FVarId::DbjLevel(s) => Some(s),
        FVarId::Unique(_) => None,
    }
}

/// The same, keyed by the id a `Free` node carries in the model. Uninterpreted;
/// `read_expr` ties it to the node.
pub uninterp spec fn dbj_serial(id: u32) -> Option<u16>;

/// The memo caches are sound: every entry maps its key to a pointer denoting
/// exactly what the key's function computes. `subst_aux`'s `return cached`
/// branch is correct precisely when this holds, and its `insert` branch is what
/// preserves it -- so this is a genuine invariant to be CHECKED, not a fact to
/// be assumed about the cache.
pub open spec fn subst_cache_sound<'t, 'p>(ctx: TcCtx<'t, 'p>) -> bool {
    forall|k: (ExprPtr<'t>, LevelsPtr<'t>, LevelsPtr<'t>)| #[trigger]
        ctx.expr_cache.subst_cache@.contains_key(k) ==> to_model(ctx.expr_cache.subst_cache@[k])
            == subst_expr_levels(
            to_model(k.0),
            crate::level_model::level_names(to_model_of_levels(k.1)),
            to_model_of_levels(k.2),
        )
}

/// Same invariant for the OUTER level-substitution cache. `subst_expr_levels`
/// keys this one and clears `subst_cache` beneath it, so the two are
/// independent: the inner one is scratch for a single call, this one persists.
pub open spec fn dsubst_cache_sound<'t, 'p>(ctx: TcCtx<'t, 'p>) -> bool {
    forall|k: (ExprPtr<'t>, LevelsPtr<'t>, LevelsPtr<'t>)| #[trigger]
        ctx.expr_cache.dsubst_cache@.contains_key(k) ==> to_model(ctx.expr_cache.dsubst_cache@[k])
            == subst_expr_levels(
            to_model(k.0),
            crate::level_model::level_names(to_model_of_levels(k.1)),
            to_model_of_levels(k.2),
        )
}

/// The instantiation cache. Unlike the level caches, this one is keyed by
/// `(expr, offset)` only -- the substitution list is NOT part of the key,
/// because `inst` clears the cache on every call. So soundness is relative to
/// the `substs` in flight, and the reset is what makes that safe.
pub open spec fn inst_cache_sound<'t, 'p>(ctx: TcCtx<'t, 'p>, substs: Seq<ExprPtr<'t>>) -> bool {
    forall|k: (ExprPtr<'t>, u16)| #[trigger]
        ctx.expr_cache.inst_cache@.contains_key(k) ==> to_model(ctx.expr_cache.inst_cache@[k])
            == subst_full(to_model(k.0), ptr_models(substs), k.1 as nat)
}

/// The de Bruijn-LEVEL abstraction's cache. Keyed by the full triple, unlike the
/// other two: `abstr_levels` resets it per call the way `abstr` does, but both
/// `start_pos` and `num_open_binders` vary WITHIN a single traversal, so neither
/// can be left out of the key.
pub open spec fn abstr_levels_cache_sound<'t, 'p>(ctx: TcCtx<'t, 'p>) -> bool {
    forall|k: (ExprPtr<'t>, u16, u16)| #[trigger]
        ctx.expr_cache.abstr_cache_levels@.contains_key(k) ==> to_model(
            ctx.expr_cache.abstr_cache_levels@[k],
        ) == crate::expr_model::abstr_levels_full(to_model(k.0), k.1, k.2)
            && crate::expr_model::levels_fit(to_model(k.0), k.2)
}

/// The abstraction cache. Keyed `(expr, offset)` like the instantiation one and
/// for the same reason: `abstr` clears it per call, so the `locals` list need
/// not be part of the key and soundness is relative to the list in flight.
pub open spec fn abstr_cache_sound<'t, 'p>(ctx: TcCtx<'t, 'p>, locals: Seq<ExprPtr<'t>>) -> bool {
    forall|k: (ExprPtr<'t>, u16)| #[trigger]
        ctx.expr_cache.abstr_cache@.contains_key(k) ==> to_model(ctx.expr_cache.abstr_cache@[k])
            == abstr_full(to_model(k.0), local_ids(locals), k.1 as nat)
}

/// The `expr_id`s of a list of locals -- `abstr_full`'s own `Seq<u32>` argument.
/// Named rather than written inline so it can be a quantifier trigger.
pub open spec fn local_ids<'t>(locals: Seq<ExprPtr<'t>>) -> Seq<u32> {
    Seq::new(locals.len(), |i: int| expr_id(locals[i]))
}

/// THE ARENA'S CACHED-FIELD INVARIANT.
///
/// Five of `Expr`'s shapes carry precomputed `num_loose_bvars` and `has_fvars`
/// alongside their children, and `to_model_of_expr` deliberately IGNORES them
/// -- a node's denotation is built from its children, so the cached values are
/// not part of what it means. Their correctness is therefore a property of the
/// arena, maintained by whoever allocates, and it cannot be derived from the
/// denotation.
///
/// It is stated ONCE here, at the read boundary, rather than separately on
/// each accessor that happens to read a cached field. That is what lets
/// `TcCtx::num_loose_bvars` and `TcCtx::has_fvars` be PROVEN rather than
/// assumed -- and it is available to anything else that matches on a node,
/// which the per-accessor form was not.
///
/// The leaf shapes need no clause -- their zeros follow from `nlbv`'s own
/// definition, so the kernel computes rather than caches them.
///
/// `Var` needs one, but not about a cached field: the kernel computes
/// `dbj_idx + 1` in `u16`, which overflows at `u16::MAX`. The original wraps
/// to 0 there and silently reports a closed term as having no loose bound
/// variables. Saying the arena never stores such a node keeps the kernel's
/// arithmetic as written; the alternative was a guard, which would be a
/// behaviour change on a path no real term reaches (a de Bruijn index of
/// 65535 means 65535 enclosing binders).
pub open spec fn node_cache_ok<'t>(e: Expr<'t>) -> bool {
    match e {
        Expr::App { num_loose_bvars, has_fvars, .. } => num_loose_bvars as nat == nlbv(
            to_model_of_expr(e),
        ) && has_fvars == has_fv(to_model_of_expr(e)),
        Expr::Pi { num_loose_bvars, has_fvars, .. } => num_loose_bvars as nat == nlbv(
            to_model_of_expr(e),
        ) && has_fvars == has_fv(to_model_of_expr(e)),
        Expr::Lambda { num_loose_bvars, has_fvars, .. } => num_loose_bvars as nat == nlbv(
            to_model_of_expr(e),
        ) && has_fvars == has_fv(to_model_of_expr(e)),
        Expr::Let { num_loose_bvars, has_fvars, .. } => num_loose_bvars as nat == nlbv(
            to_model_of_expr(e),
        ) && has_fvars == has_fv(to_model_of_expr(e)),
        Expr::Proj { num_loose_bvars, has_fvars, .. } => num_loose_bvars as nat == nlbv(
            to_model_of_expr(e),
        ) && has_fvars == has_fv(to_model_of_expr(e)),
        Expr::Var { dbj_idx, .. } => dbj_idx < u16::MAX,
        _ => true,
    }
}


pub assume_specification<'t, 'p>[ TcCtx::<'t, 'p>::read_expr ](
    ctx: &TcCtx<'t, 'p>,
    ptr: ExprPtr<'t>,
) -> (result: Expr<'t>) where 'p: 't
    ensures
        to_model_of_expr(result) == to_model(ptr),
        node_cache_ok(result),
        // `const_name_of`/`const_levels_of` are uninterpreted, so until now the
        // ONLY way to learn what they are was `expr_as_const`'s own axiom --
        // which is keyed on a caller-supplied `(ptr, e)` pair and silently
        // assumes the caller passed a pair that actually corresponds. Keying
        // the same fact on `read_expr` instead removes that unchecked side
        // condition: `read_expr` reads the node the pointer names, so there is
        // no pair to get wrong. This is what lets the kernel's own
        // `unfold_const_apps` match on `Const { .. }` directly.
        result matches Expr::Const { name, levels, .. } ==> const_name_of(ptr) == name
            && const_levels_of(ptr) == levels,
        result matches Expr::Local { id, binder_type, .. } ==> local_id_of(ptr) == id
            && local_binder_type_of(ptr) == binder_type,
        result matches Expr::NatLit { ptr: np, .. } ==> nat_lit_ptr_of(ptr) == np,
        result matches Expr::StringLit { ptr: sp, .. } ==> string_lit_ptr_of(ptr) == sp,
        // The last of `expr_is_local`'s claims, re-keyed here for the same
        // reason as the others: keyed on `read_expr` there is no `(ptr, e)`
        // pair to get wrong. This is what lets the kernel's `abstr_aux` learn
        // anything at its `Local` arm.
        result matches Expr::Local { .. } ==> to_model(ptr) == ExprSpec::Free(expr_id(ptr)),
        // The de Bruijn-LEVEL serial, keyed here for the same reason as the
        // payload clauses above: on `read_expr` there is no `(ptr, e)` pair to
        // get wrong.
        result matches Expr::Local { id, .. } ==> dbj_serial(expr_id(ptr)) == fvar_dbj_serial(id),
;

// Contradiction detector, run and removed: a `proof fn` taking `ptr` and `e`,
// assuming exactly the six clauses above (`to_model_of_expr(e) ==
// to_model(ptr)` together with the `Const`, `Local`, `NatLit` and `StringLit`
// payload correspondences, and the `dbj_serial` one) and claiming
// `ensures false`, FAILS to verify.
// That is the result wanted -- had it verified, the conjuncts would have been
// inconsistent with the rest of the arena model and every proof downstream of
// them worthless. Non-degeneracy is witnessed on the other side by the
// functions that consume them: `TcCtx::try_const_info` and
// `TcCtx::unfold_const_apps` in `expr.rs`, and `expr_as_local`/
// `expr_as_nat_lit`/`expr_as_string_lit` below, none of which can state their
// contract at all without the matching clause.
#[allow(dead_code)]
pub fn expr_as_var(e: &Expr) -> (result: Option<u16>)
    ensures
        match result {
            Some(i) => to_model_of_expr(*e) == ExprSpec::Var(i as u32),
            None => !matches!(to_model_of_expr(*e), ExprSpec::Var(_)),
        },
{
    match e {
        Expr::Var { dbj_idx, .. } => Some(*dbj_idx),
        _ => None,
    }
}

/// Was an `assume_specification` over a `(ptr, e)` pair -- the last one of that
/// shape. Reads the node itself now, so both halves are proven.
pub fn expr_is_local<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, ptr: ExprPtr<'t>) -> (result: bool)
    ensures
        result ==> to_model(ptr) == ExprSpec::Free(expr_id(ptr)),
        !result ==> !matches!(to_model(ptr), ExprSpec::Free(_)),
{
    matches!(ctx.read_expr(ptr), Expr::Local { .. })
}

#[allow(dead_code)]
pub fn expr_is_bind_shape<'t>(e: &Expr<'t>) -> (result: bool)
    ensures
        result == matches!(to_model_of_expr(*e), ExprSpec::Bind(_, _)),
{
    matches!(e, Expr::Pi { .. } | Expr::Lambda { .. })
}

#[allow(dead_code)]
pub fn expr_is_const_shape<'t>(e: &Expr<'t>) -> (result: bool)
    ensures
        result == matches!(to_model_of_expr(*e), ExprSpec::Const(_, _)),
{
    matches!(e, Expr::Const { .. })
}

/// No real expression denotes `ExprSpec::Closed`. Every `Expr` variant maps
/// to a variant carrying its own content; `Closed` survives in `ExprSpec`
/// only as the model's payload-free leaf, which the arena never builds.
/// A one-line consequence of `to_model_of_expr`'s definition -- and the fact
/// the old `expr_is_closed_leaf` axiom got wrong in the other direction back
/// when `Sort` still collapsed into `Closed`.
pub proof fn to_model_of_expr_never_closed<'a>(e: Expr<'a>)
    ensures
        to_model_of_expr(e) != ExprSpec::Closed,
{
}

/// PROVEN, and restated. The old contract mixed a shallow VALUE with three
/// POINTER flags and never required the two to correspond; it was also
/// unprovable, because the flags were forward-only and nothing could derive
/// `is_const_shape(ptr)` from a `Const`-shaped model. Both halves are fixed:
/// `to_model_of_expr` is a definition, and the flags are now defined AS the
/// model's shape, so the contract can be stated where the function actually
/// looks -- at the value -- and discharged from those definitions.
#[allow(dead_code)]
pub fn expr_is_closed_leaf<'t>(_ptr: ExprPtr<'t>, e: &Expr<'t>) -> (result: bool)
    ensures
        result
            == matches!(to_model_of_expr(*e),
        ExprSpec::Closed | ExprSpec::Sort(_) | ExprSpec::Const(_, _)
        | ExprSpec::NatLit(_) | ExprSpec::StringLit(_)),
{
    matches!(e, Expr::Sort { .. } | Expr::Const { .. } | Expr::StringLit { .. } | Expr::NatLit { .. })
}

#[allow(dead_code)]
pub fn expr_as_app<'t>(e: &Expr<'t>) -> (result: Option<(ExprPtr<'t>, ExprPtr<'t>)>)
    ensures
        match result {
            Some((f, a)) => to_model_of_expr(*e) == ExprSpec::App(
                Box::new(to_model(f)),
                Box::new(to_model(a)),
            ),
            None => !matches!(to_model_of_expr(*e), ExprSpec::App(_, _)),
        },
{
    match e {
        Expr::App { fun, arg, .. } => Some((*fun, *arg)),
        _ => None,
    }
}

/// `Const`'s name/levels, keyed by the pointer (like `expr_id`) --
/// `const_name_of`/`const_levels_of` are a separate side channel from
/// `to_model`, carrying the real `NamePtr`/`LevelsPtr` that `to_model`'s
/// `ExprSpec::Const(u64, Seq<LevelSpec>)` payload is derived from.
/// `const_id` is NOT a fresh axiomatized identity -- it's DERIVED from
/// `name_id` (the pre-existing NAME-identity bridge in
/// `level_arena_bridge.rs`), so "same name implies same id" falls out of
/// `name_id_injective` automatically rather than needing its own axiom.
/// `const_levels_vec` is the analogous Vec-shaped side channel for the
/// levels payload, connected to `to_model_of_levels` by
/// `const_levels_vec_model` below. `is_const_shape_model` is the trusted
/// fact that a `Const`-shaped pointer's `to_model` is exactly
/// `ExprSpec::Const(const_id(ptr), const_levels_vec(ptr))`.
/// DEFINED, not uninterpreted: the flag IS the model's shape. Leaving it
/// opaque made it forward-only (`is_const_shape(ptr) ==> to_model(ptr) ==
/// Const(..)`, no converse), which is what stopped `expr_is_closed_leaf`
/// being provable -- nothing could derive the flag from a `Const`-shaped
/// model. The side channels `const_id`/`const_levels_vec` stay
/// uninterpreted; `is_const_shape_model` still ties them to the payload.
pub open spec fn is_const_shape<'a>(ptr: ExprPtr<'a>) -> bool {
    matches!(to_model(ptr), ExprSpec::Const(_, _))
}

pub uninterp spec fn const_name_of<'a>(ptr: ExprPtr<'a>) -> NamePtr<'a>;

pub uninterp spec fn const_levels_of<'a>(ptr: ExprPtr<'a>) -> LevelsPtr<'a>;

pub open spec fn const_id<'a>(ptr: ExprPtr<'a>) -> u64 {
    name_id(const_name_of(ptr))
}

/// (Delta-lift L1: no longer an uninterpreted Vec side channel -- `ExprSpec::Const`
/// carries a `Seq<LevelSpec>` now, so this is simply the level bridge itself.)
pub open spec fn const_levels_vec<'a>(ptr: ExprPtr<'a>) -> Seq<LevelSpec> {
    to_model_of_levels(const_levels_of(ptr))
}

/// Now definitional (kept so the ~50 existing call sites read unchanged).
pub proof fn const_levels_vec_model<'a>(ptr: ExprPtr<'a>)
    ensures
        const_levels_vec(ptr) =~= to_model_of_levels(const_levels_of(ptr)),
{
}

/// The trust boundary connecting `is_const_shape` to `to_model`: stated
/// as a standalone callable lemma (rather than folded into
/// `expr_as_const`'s own postcondition) so it's usable anywhere
/// `is_const_shape(ptr)` is already known, not just at `expr_as_const`'s
/// own call sites -- e.g. `expr_is_closed_leaf`'s `is_const_shape(ptr)`
/// disjunct needs exactly this to relate its own result back to
/// `to_model(ptr)`'s actual shape.
#[verifier::external_body]
pub proof fn is_const_shape_model<'a>(ptr: ExprPtr<'a>)
    requires
        is_const_shape(ptr),
    ensures
        to_model(ptr) == ExprSpec::Const(const_id(ptr), const_levels_vec(ptr)),
{
}

/// `Local`'s payload, same trust-boundary shape as `Const`'s
/// `is_const_shape`/`const_name_of`/`const_levels_of`: `local_id_of` is the
/// `FVarId` a `Local`-shaped pointer carries (deliberately separate from
/// `expr_id`, which models pointer identity, not the `FVarId` field value
/// -- see the module doc comment), and `local_binder_type_of` is its
/// `binder_type: ExprPtr`.
pub open spec fn is_local_shape<'a>(ptr: ExprPtr<'a>) -> bool {
    matches!(to_model(ptr), ExprSpec::Free(_))
}

pub uninterp spec fn local_id_of<'a>(ptr: ExprPtr<'a>) -> FVarId;

pub uninterp spec fn local_binder_type_of<'a>(ptr: ExprPtr<'a>) -> ExprPtr<'a>;

/// The arena's local context, viewed at the MODEL level: the (total,
/// ambient) map from a `Local`-shaped node's model identity
/// (`expr_id`, i.e. the payload of its `ExprSpec::Free` model) to the
/// MODEL of its recorded binder type. Same "pure function of the one
/// ambient arena" convention as `to_model` itself -- and the same
/// disclosed-trust character: `arena_lctx_local` below is the one
/// axiom connecting it to the real `local_binder_type_of` field, so
/// the model-level typing relation (`types_to`, `delta_bound_model.rs`)
/// can give `Free` leaves a type without reaching back into ptr-land.
pub uninterp spec fn arena_lctx() -> Map<u32, ExprSpec>;

#[verifier::external_body]
pub proof fn arena_lctx_local<'a>(ptr: ExprPtr<'a>)
    requires
        is_local_shape(ptr),
    ensures
        arena_lctx().contains_key(expr_id(ptr)),
        arena_lctx()[expr_id(ptr)] == to_model(local_binder_type_of(ptr)),
{
}

/// Read-side twin of `is_const_shape_model` for `Local`s: a bare
/// `is_local_shape` fact pins the model to `Free(expr_id(...))` --
/// the same content `expr_is_local`'s `assume_specification` already
/// asserts at its own call sites, just callable from the shape flag
/// alone (needed by `types_to` producers that hold `is_local_shape`
/// from an earlier accessor rather than a fresh `expr_is_local` call).
#[verifier::external_body]
pub proof fn is_local_shape_model<'a>(ptr: ExprPtr<'a>)
    requires
        is_local_shape(ptr),
    ensures
        to_model(ptr) == ExprSpec::Free(expr_id(ptr)),
{
}

/// `env_global_cap`'s counterpart for LOCALS instead of declarations:
/// "there's a real maximum depth some Local's stored `binder_type` can
/// reach, even though this model doesn't compute it" -- same "name the
/// max, don't claim a number" pattern `env_global_cap` uses (a caller
/// who needs a CONCRETE bound states `local_type_cap() <= some_value` as
/// their own hypothesis, same as `env_global_cap(*env) <= d` elsewhere).
/// `mk_dbj_level`'s own bridge (below) never tracked a bound on `binder_
/// type` at all -- capturing "how deep can a caller-supplied binder_type
/// ever be" by touching every existing `mk_dbj_level` call site across
/// this whole project would be enormously invasive; this sidesteps that
/// by asserting a single, UNCONDITIONAL global maximum exists instead,
/// closing the "Local branch genuinely has no derivable bound" gap
/// `verified_infer`'s dispatcher has carried since `Local` was first
/// bridged. Deliberately UNPARAMETERIZED by `Env`/`TcCtx` (unlike `env_
/// global_cap`) -- locals are per-execution-context, not per-`Env`, and
/// this whole arc's convention is already "one flat numeric constant
/// bound, established via a hypothesis" (`60000`) rather than tracking
/// separate caps per context.
pub uninterp spec fn local_type_cap() -> nat;

/// Deliberately omits `max_var_below`/`size` (unlike `env_global_wf`) --
/// `depth` is needed for `infer`'s own depth-boundedness, and an
/// UNCONDITIONAL axiom that includes `size` has been shown to blow up
/// full-crate check time 50x+ even when unused (see `feedback_verus_
/// size_axiom_blowup.md`). `nlbv == 0` IS included (unlike `max_var_
/// below`/`size`) -- a bisection identical in spirit to `env_global_wf`'s
/// own confirmed `nlbv` alone stays cheap; needed for `verified_infer`'s
/// `Local` branch to contribute to the dispatcher's own closedness
/// guarantee (`nlbv(to_model(r)) <= 0`), itself needed so a FUTURE `Proj`
/// composition can call `verified_infer` on `structure` directly and get
/// a closed `structure_ty` back, rather than taking it as an external
/// parameter forever.
#[verifier::external_body]
pub proof fn local_type_wf<'a>(ptr: ExprPtr<'a>)
    ensures
        is_local_shape(ptr) ==> {
            &&& depth(to_model(local_binder_type_of(ptr))) <= local_type_cap()
            &&& nlbv(to_model(local_binder_type_of(ptr))) == 0
        },
{
}

/// Was an `assume_specification`. `ExFVarId` is transparent now, so comparing
/// the variants explicitly proves what the derived `PartialEq` only asserted:
/// making the type transparent is not by itself enough, because `==` on it is
/// still an unspecified external call -- the match is what discharges it.
#[allow(dead_code)]
pub(crate) fn fvar_id_eq(a: FVarId, b: FVarId) -> (result: bool)
    ensures
        result == (a == b),
{
    match (a, b) {
        (FVarId::DbjLevel(x), FVarId::DbjLevel(y)) => x == y,
        (FVarId::Unique(x), FVarId::Unique(y)) => x == y,
        _ => false,
    }
}

/// Was an `assume_specification` over a `(ptr, e)` pair whose correspondence
/// nothing checked; reads the node itself now, so the same contract is proven.
pub fn expr_as_local<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, ptr: ExprPtr<'t>) -> (result: Option<
    (FVarId, ExprPtr<'t>),
>)
    ensures
        match result {
            Some((id, t)) => is_local_shape(ptr) && local_id_of(ptr) == id && local_binder_type_of(
                ptr,
            ) == t,
            None => !is_local_shape(ptr),
        },
{
    match ctx.read_expr(ptr) {
        Expr::Local { id, binder_type, .. } => Some((id, binder_type)),
        _ => None,
    }
}

/// A freshly-constructed `Const` node is `is_const_shape` with exactly the
/// given name/levels -- the construction-side mirror of `expr_as_const`'s
/// read-side contract above (same three facts), letting `is_const_shape_
/// model`/`const_levels_vec_model` derive `to_model(result)` the same way
/// for either a freshly-built or a pre-existing `Const` pointer.
/// Construction-side mirror for `Local`, same pattern as `mk_const` above:
/// `mk_dbj_level` (`util.rs:612-623`, "open a binder with a fresh free
/// variable") always produces an `is_local_shape` node carrying exactly
/// the given `binder_type`, and -- since the counter frame landed -- the
/// SERIAL it allocates and what it does to the counter. Those last two are
/// what let a caller line a list of locals up with
/// `abstr_levels_full_eq_abstr_full`, and what makes `mk`/`replace` cancel.
/// Also states the link to the OLDER, pre-existing `expr_is_local`/
/// `expr_id` free-variable bridge (`to_model(result) ==
/// ExprSpec::Free(expr_id(result))`) -- `is_local_shape`/`expr_is_local`
/// are two independently-added notions of "this pointer denotes a Local"
/// (the latter predates this session, built for `inst`/`abstr`'s bound-
/// variable mechanics) that were never explicitly connected; stating it
/// here, at the one place that actually constructs a fresh Local, is
/// enough for what `verified_def_eq_binder_step`'s depth bookkeeping
/// needs (`depth(ExprSpec::Free(_)) == 0`) without a separate linking
/// lemma between the two notions in general.
// STILL ASSUMED, but no longer claim-poor. The body is
//
//     let level = self.dbj_level_counter;
//     self.dbj_level_counter += 1;
//
// and `dbj_level_counter` is a `u16`, so the increment needs
// `dbj_level_counter < u16::MAX`. That obligation is unavoidable -- it does not
// depend on what the contract claims -- so it appears below as a `requires`.
//
// An earlier attempt backed out here, on the grounds that the `requires` would
// cascade a ceiling through every caller. It does not, and the reason is worth
// recording: every call site sits in a SHADOW-route function that already has a
// decline path (`None`, or `false` under a `result ==>` postcondition). So each
// one discharges the precondition locally with a runtime check --
//
//     if get_dbj_level_counter(ctx) == u16::MAX { return None; }
//
// -- and nothing propagates. At 65536 nested open binders the shadow declines
// to certify instead of wrapping; the kernel still decides. Reach for a local
// decline before a ceiling cascade.
//
// The overflow itself is real and unchecked in the KERNEL's own call sites
// (`tc.rs`), like `abstr_aux`'s offset and `fvar_to_bvar`'s subtraction. Not
// reachable with real Lean terms; not checked there either.
//
// It states the SERIAL (`dbj_serial(expr_id(result)) == Some(old counter)`)
// and the counter's increment, which is what relates abstraction by level
// (`abstr_levels`) to abstraction by identity (`abstr_full`).
pub assume_specification<'t, 'p>[ TcCtx::<'t, 'p>::mk_dbj_level ](
    ctx: &mut TcCtx<'t, 'p>,
    binder_name: NamePtr<'t>,
    binder_style: BinderStyle,
    binder_type: ExprPtr<'t>,
) -> (result: ExprPtr<'t>) where 'p: 't
    requires
        old(ctx).dbj_level_counter < u16::MAX,
        // a local's type is closed: `local_type_wf` states it of EVERY local,
        // so creating one has to establish it
        nlbv(to_model(binder_type)) == 0,
    ensures
        is_local_shape(result),
        local_binder_type_of(result) == binder_type,
        to_model(result) == ExprSpec::Free(expr_id(result)),
        dbj_serial(expr_id(result)) == Some(old(ctx).dbj_level_counter),
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter + 1,
        final(ctx).expr_cache == old(ctx).expr_cache,
;

/// Was a claim-free `assume_specification` -- `TcCtx` was `external_body`, so
/// a wrapper round a field read could not even say which field. Transparent, it
/// says so and proves it.
#[allow(dead_code)]
pub(crate) fn get_dbj_level_counter<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>) -> (result: u16)
    ensures
        result == ctx.dbj_level_counter,
{
    ctx.dbj_level_counter
}

/// Was claim-free. It now says what it does to the counter, which is the other
/// half of the de Bruijn frame: `mk_dbj_level` raises it, this lowers it, and
/// without both facts nothing can show a shadow route leaves it where it found
/// it.
///
/// Still assumed rather than verified. Its body is three lines, but they are
/// awkward ones: a `debug_assert_eq!` (same `AssertKind` wall as `assert_eq!`),
/// a `panic!` arm that formats via `debug_print`, and the decrement itself.
pub assume_specification<'t, 'p>[ TcCtx::<'t, 'p>::replace_dbj_level ](
    ctx: &mut TcCtx<'t, 'p>,
    e: ExprPtr<'t>,
) -> (result: ()) where 'p: 't
    requires
        old(ctx).dbj_level_counter > 0,
    ensures
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter - 1,
        final(ctx).expr_cache == old(ctx).expr_cache,
;


/// `expr.rs::bool_to_expr`'s result identity: `Const(bool_true_id, [])`
/// or `Const(bool_false_id, [])`, whichever `b` selects -- `bool_true_id`/
/// `bool_false_id` are uninterpreted NAME ids (same "just an identity,
/// not the name's content" convention `const_id`/`name_id` already use)
/// standing in for `export_file.name_cache.bool_true()`/`bool_false`'s
/// real, per-export-file `NamePtr`s. A model-level simplification (this
/// doesn't distinguish between different `ctx`/`export_file` instances
/// possibly caching different pointers for "the" `Bool.true`/`Bool.false`
/// constant), consistent with how every other `name_id`-keyed fact in
/// this codebase already treats identity globally rather than per-`ctx`.
/// `None` covers the real function's only failure mode (the name isn't
/// present in this export file's cache at all).
pub uninterp spec fn bool_true_id() -> u64;

pub uninterp spec fn bool_false_id() -> u64;

/// `expr.rs::TcCtx::c_bool_true`'s result identity, same "`Const(name_
/// cache.bool_true, [])`" shape as `bool_to_expr`'s `true` branch --
/// `c_bool_true`/`c_bool_false` construct the SAME `Bool.true`/`Bool.
/// false` constant `bool_to_expr` does, just without needing a `bool` to
/// select which one.

/// `expr.rs::is_nat_zero`/`pred_of_nat_succ`'s identity facts, same
/// "uninterpreted name id" convention as `bool_true_id`/`bool_false_id`
/// above -- `nat_zero_id`/`nat_succ_id` stand in for `export_file.
/// name_cache.nat_zero()`/`nat_succ`'s real per-export-file `NamePtr`s.
/// `is_nat_zero` accepts EITHER representation of zero (a real `NatLit`
/// with value 0, or the `Const Nat.zero []` node); `pred_of_nat_succ`
/// mirrors this for the predecessor: either peel `Nat.succ`off an `App`,
/// or decrement a nonzero `NatLit` in place (`biguint_pred`, previous
/// commit).
/// Arena-global identity of the quotient primitives (0 `Quot.lift`,
/// 1 `Quot.ind`, 2 `Quot.mk`), tied to the real name cache by the
/// `quot_kind_code` specification below -- same convention as
/// `nat_bin_op_of`.
pub uninterp spec fn quot_kind_of(id: u64) -> Option<u8>;

pub uninterp spec fn nat_zero_id() -> u64;

pub uninterp spec fn nat_succ_id() -> u64;




/// NAT-LITERAL FOLDING (rec-iota P3, 2026-09-04): the kernel's `nat_
/// extension` dispatch (`tc.rs::try_reduce_nat`) keyed by name id, as an
/// ARENA-GLOBAL uninterpreted op code -- same "one declaration per name
/// id per export" trust as `nat_zero_id` above.
/// Op codes: 0 add, 1 sub, 2 mul, 3 div, 4 mod, 5 pow, 6 gcd, 7 beq,
/// 8 ble (`land`/`lor`/`xor`/`shl`/`shr` are NOT modeled: `None`).
pub uninterp spec fn nat_bin_op_of(id: u64) -> Option<u8>;

/// RECURSOR DATA: what `pstep`'s recursor-iota rule needs about a
/// recursor, read from `EnvSpec::recs`. Rules are keyed by constructor id; `nfields` is the
/// constructor's telescope size without the inductive's parameters
/// (`RecRule::ctor_telescope_size_wo_params`); `rhs` is the rule's value
/// (a closed lambda term over params/motives/minors/fields), instantiated
/// at the recursor's universe parameters `uparams`.
pub ghost struct RecRuleSpec {
    pub ctor_id: u64,
    pub nfields: nat,
    pub rhs: ExprSpec,
}

pub ghost struct RecDataSpec {
    pub num_params: nat,
    pub num_motives: nat,
    pub num_minors: nat,
    pub major_idx: nat,
    pub uparams: Seq<u64>,
    pub rules: Seq<RecRuleSpec>,
}

/// The model of an environment: its definitions (the delta rule's
/// unfoldings) and the per-name tables the reduction and typing rules key
/// on. Every table belongs to ONE environment -- a name can mean different
/// things in two environments (a nested inductive's temporary environment
/// re-declares its recursor), so no table is global.
pub ghost struct EnvSpec {
    pub defs: Map<u64, (Seq<u64>, ExprSpec)>,
    pub recs: Map<u64, RecDataSpec>,
    pub ctor_np: Map<u64, u16>,
    pub struct_ctor: Map<u64, u64>,
    pub ctor_nf: Map<u64, u16>,
}

impl EnvSpec {
    /// No definitions and no tables: the delta-free, iota-free fragment.
    pub open spec fn empty() -> EnvSpec {
        EnvSpec {
            defs: Map::empty(),
            recs: Map::empty(),
            ctor_np: Map::empty(),
            struct_ctor: Map::empty(),
            ctor_nf: Map::empty(),
        }
    }

    pub open spec fn spec_index(self, id: u64) -> (Seq<u64>, ExprSpec) {
        self.defs[id]
    }

    pub open spec fn contains_key(self, id: u64) -> bool {
        self.defs.contains_key(id)
    }

    pub open spec fn rec_data(self, id: u64) -> Option<RecDataSpec> {
        if self.recs.contains_key(id) { Some(self.recs[id]) } else { None }
    }

    pub open spec fn ctor_num_params(self, id: u64) -> Option<u16> {
        if self.ctor_np.contains_key(id) { Some(self.ctor_np[id]) } else { None }
    }

    pub open spec fn struct_ctor(self, id: u64) -> Option<u64> {
        if self.struct_ctor.contains_key(id) { Some(self.struct_ctor[id]) } else { None }
    }

    pub open spec fn ctor_num_fields(self, id: u64) -> Option<u16> {
        if self.ctor_nf.contains_key(id) { Some(self.ctor_nf[id]) } else { None }
    }

    /// `self`'s definitions and tables all appear, unchanged, in `other`:
    /// every reduction under `self` is one under `other`.
    pub open spec fn sub(self, other: EnvSpec) -> bool {
        &&& forall|k: u64| #[trigger]
            self.defs.contains_key(k) ==> other.defs.contains_key(k) && self.defs[k] == other.defs[k]
        &&& forall|k: u64| #[trigger]
            self.recs.contains_key(k) ==> other.recs.contains_key(k) && self.recs[k] == other.recs[k]
        &&& forall|k: u64| #[trigger]
            self.ctor_np.contains_key(k) ==> other.ctor_np.contains_key(k) && self.ctor_np[k] == other.ctor_np[k]
    }
}


/// `e` is SOME representation of `Nat` zero -- reused by `verified_def_
/// eq_nat` (`tc_model.rs`) so it doesn't have to restate this disjunction
/// itself.
pub open spec fn nat_repr_is_zero<'a>(e: ExprPtr<'a>) -> bool {
    (is_nat_lit_shape(e) && nat_lit_value(e) == 0) || (is_const_shape(e) && const_id(e)
        == nat_zero_id() && const_levels_vec(e).len() == 0)
}

/// Exec size computation over the real arena, mirroring the model
/// `size` exactly -- THE opening piece of the chain-carrying
/// producer-claim surface: producers that materialize their reduction
/// intermediates can size-GATE each one with this (returning `None`
/// above 60000, the ceiling headroom the strip/confluence/binder-intro
/// lemmas need), which is what lets their ensures carry explicit chains
/// with dischargeable per-element bounds. `None` covers fuel
/// exhaustion, the gate, and unmodeled shapes -- honest incompleteness,
/// never a wrong size.
pub fn verified_size<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, e: ExprPtr<'t>, fuel: u32) -> (result: Option<
    u32,
>)
    ensures
        match result {
            Some(n) => n as nat == size(to_model(e)) && n <= 60000,
            None => true,
        },
    decreases fuel,
{
    if fuel == 0 {
        return None;
    }
    let el = ctx.read_expr(e);
    if let Some((f, a)) = expr_as_app(&el) {
        let nf = match verified_size(ctx, f, fuel - 1) {
            Some(v) => v,
            None => return None,
        };
        let na = match verified_size(ctx, a, fuel - 1) {
            Some(v) => v,
            None => return None,
        };
        let total: u64 = 1u64 + nf as u64 + na as u64;
        if total > 60000 {
            return None;
        }
        assert(size(to_model(e)) == 1 + size(to_model(f)) + size(to_model(a)));
        return Some(total as u32);
    }
    if let Some((_, _, ty, body)) = expr_as_pi(&el) {
        let nt = match verified_size(ctx, ty, fuel - 1) {
            Some(v) => v,
            None => return None,
        };
        let nb = match verified_size(ctx, body, fuel - 1) {
            Some(v) => v,
            None => return None,
        };
        let total: u64 = 1u64 + nt as u64 + nb as u64;
        if total > 60000 {
            return None;
        }
        assert(size(to_model(e)) == 1 + size(to_model(ty)) + size(to_model(body)));
        return Some(total as u32);
    }
    if let Some((_, _, ty, body)) = expr_as_lambda(&el) {
        let nt = match verified_size(ctx, ty, fuel - 1) {
            Some(v) => v,
            None => return None,
        };
        let nb = match verified_size(ctx, body, fuel - 1) {
            Some(v) => v,
            None => return None,
        };
        let total: u64 = 1u64 + nt as u64 + nb as u64;
        if total > 60000 {
            return None;
        }
        assert(size(to_model(e)) == 1 + size(to_model(ty)) + size(to_model(body)));
        return Some(total as u32);
    }
    if let Some((_, ty, v, body, _)) = expr_as_let(&el) {
        let nt = match verified_size(ctx, ty, fuel - 1) {
            Some(v2) => v2,
            None => return None,
        };
        let nv = match verified_size(ctx, v, fuel - 1) {
            Some(v2) => v2,
            None => return None,
        };
        let nb = match verified_size(ctx, body, fuel - 1) {
            Some(v2) => v2,
            None => return None,
        };
        let total: u64 = 1u64 + nt as u64 + nv as u64 + nb as u64;
        if total > 60000 {
            return None;
        }
        assert(size(to_model(e)) == 1 + size(to_model(ty)) + size(to_model(v)) + size(
            to_model(body),
        ));
        return Some(total as u32);
    }
    if let Some((_, _, st)) = expr_as_proj(&el) {
        let ns = match verified_size(ctx, st, fuel - 1) {
            Some(v) => v,
            None => return None,
        };
        let total: u64 = 1u64 + ns as u64;
        if total > 60000 {
            return None;
        }
        assert(size(to_model(e)) == 1 + size(to_model(st)));
        return Some(total as u32);
    }
    if expr_as_var(&el).is_some() {
        assert(size(to_model(e)) == 1);
        return Some(1);
    }
    if expr_as_sort(&el).is_some() {
        assert(size(to_model(e)) == 1);
        return Some(1);
    }
    if expr_is_const_shape(&el) {
        proof {
            is_const_shape_model(e);
        }
        assert(size(to_model(e)) == 1);
        return Some(1);
    }
    if expr_as_local(ctx, e).is_some() {
        proof {
            is_local_shape_model(e);
        }
        assert(size(to_model(e)) == 1);
        return Some(1);
    }
    if expr_as_nat_lit(ctx, e).is_some() {
        proof {
            is_nat_lit_shape_model(e);
        }
        assert(size(to_model(e)) == 1);
        return Some(1);
    }
    if expr_as_string_lit(ctx, e) {
        proof {
            is_string_lit_shape_model(e);
        }
        assert(size(to_model(e)) == 1);
        return Some(1);
    }
    None
}

/// Freshness walker for the binder fresh-instance rule: `Some(true)`
/// certifies `fv_absent(to_model(e), expr_id(local))` by POINTER
/// comparison at every `Local` node (`expr_id` is injective on pointers,
/// `expr_id_injective`). Sound regardless of `FVarId` reuse, since the
/// model keys free variables by pointer identity.
pub fn verified_fv_absent<'t, 'p: 't>(
    ctx: &TcCtx<'t, 'p>,
    e: ExprPtr<'t>,
    local: ExprPtr<'t>,
    fuel: u32,
) -> (result: Option<bool>)
    ensures
        match result {
            Some(true) => fv_absent(to_model(e), expr_id(local)),
            _ => true,
        },
    decreases fuel,
{
    if fuel == 0 {
        return None;
    }
    let el = ctx.read_expr(e);
    if let Some((f, a)) = expr_as_app(&el) {
        if verified_fv_absent(ctx, f, local, fuel - 1) != Some(true) {
            return None;
        }
        if verified_fv_absent(ctx, a, local, fuel - 1) != Some(true) {
            return None;
        }
        return Some(true);
    }
    if let Some((_, _, ty, body)) = expr_as_pi(&el) {
        if verified_fv_absent(ctx, ty, local, fuel - 1) != Some(true) {
            return None;
        }
        if verified_fv_absent(ctx, body, local, fuel - 1) != Some(true) {
            return None;
        }
        return Some(true);
    }
    if let Some((_, _, ty, body)) = expr_as_lambda(&el) {
        if verified_fv_absent(ctx, ty, local, fuel - 1) != Some(true) {
            return None;
        }
        if verified_fv_absent(ctx, body, local, fuel - 1) != Some(true) {
            return None;
        }
        return Some(true);
    }
    if let Some((_, ty, v, body, _)) = expr_as_let(&el) {
        if verified_fv_absent(ctx, ty, local, fuel - 1) != Some(true) {
            return None;
        }
        if verified_fv_absent(ctx, v, local, fuel - 1) != Some(true) {
            return None;
        }
        if verified_fv_absent(ctx, body, local, fuel - 1) != Some(true) {
            return None;
        }
        return Some(true);
    }
    if let Some((_, _, st)) = expr_as_proj(&el) {
        if verified_fv_absent(ctx, st, local, fuel - 1) != Some(true) {
            return None;
        }
        return Some(true);
    }
    if expr_as_var(&el).is_some() {
        return Some(true);
    }
    if expr_as_sort(&el).is_some() {
        return Some(true);
    }
    if expr_is_const_shape(&el) {
        proof {
            is_const_shape_model(e);
        }
        return Some(true);
    }
    if expr_as_local(ctx, e).is_some() {
        proof {
            is_local_shape_model(e);
        }
        if expr_ptr_eq(e, local) {
            return None;
        }
        proof {
            expr_id_injective(e, local);
        }
        return Some(true);
    }
    if expr_as_nat_lit(ctx, e).is_some() {
        proof {
            is_nat_lit_shape_model(e);
        }
        return Some(true);
    }
    if expr_as_string_lit(ctx, e) {
        proof {
            is_string_lit_shape_model(e);
        }
        return Some(true);
    }
    None
}




/// `Some(true)` certifies the term contains no string literal
/// (`string_free`), by the same walk as `verified_fv_absent`.
pub fn verified_string_free<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, e: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    ensures
        result == Some(true) ==> crate::beta_model::string_free(to_model(e)),
    decreases fuel,
{
    if fuel == 0 {
        return None;
    }
    let el = ctx.read_expr(e);
    if let Some((f, a)) = expr_as_app(&el) {
        if verified_string_free(ctx, f, fuel - 1) != Some(true) {
            return None;
        }
        if verified_string_free(ctx, a, fuel - 1) != Some(true) {
            return None;
        }
        return Some(true);
    }
    if let Some((_, _, ty, body)) = expr_as_pi(&el) {
        if verified_string_free(ctx, ty, fuel - 1) != Some(true) {
            return None;
        }
        if verified_string_free(ctx, body, fuel - 1) != Some(true) {
            return None;
        }
        return Some(true);
    }
    if let Some((_, _, ty, body)) = expr_as_lambda(&el) {
        if verified_string_free(ctx, ty, fuel - 1) != Some(true) {
            return None;
        }
        if verified_string_free(ctx, body, fuel - 1) != Some(true) {
            return None;
        }
        return Some(true);
    }
    if let Some((_, ty, v, body, _)) = expr_as_let(&el) {
        if verified_string_free(ctx, ty, fuel - 1) != Some(true) {
            return None;
        }
        if verified_string_free(ctx, v, fuel - 1) != Some(true) {
            return None;
        }
        if verified_string_free(ctx, body, fuel - 1) != Some(true) {
            return None;
        }
        return Some(true);
    }
    if let Some((_, _, st)) = expr_as_proj(&el) {
        if verified_string_free(ctx, st, fuel - 1) != Some(true) {
            return None;
        }
        return Some(true);
    }
    if expr_as_var(&el).is_some() || expr_as_sort(&el).is_some() {
        return Some(true);
    }
    if expr_is_const_shape(&el) {
        proof {
            is_const_shape_model(e);
        }
        return Some(true);
    }
    if expr_as_local(ctx, e).is_some() {
        proof {
            is_local_shape_model(e);
        }
        return Some(true);
    }
    if expr_as_nat_lit(ctx, e).is_some() {
        proof {
            is_nat_lit_shape_model(e);
        }
        return Some(true);
    }
    None
}

/// `p` is `e`'s `Nat` predecessor, under EITHER representation -- ditto.
pub open spec fn nat_repr_pred<'a>(e: ExprPtr<'a>, p: ExprPtr<'a>) -> bool {
    (exists|fun: ExprPtr<'a>|
        to_model(e) == ExprSpec::App(Box::new(to_model(fun)), Box::new(to_model(p)))
            && is_const_shape(fun) && const_id(fun) == nat_succ_id() && const_levels_vec(fun).len()
            == 0) || (is_nat_lit_shape(e)
        && nat_lit_value(e) > 0 && is_nat_lit_shape(p) && nat_lit_value(p) == (nat_lit_value(e)
        - 1) as nat)
}

/// Real-arena counterpart to `expr.rs::TcCtx::nat_lit_to_constructor`
/// (`expr.rs:523-533`): turn a bignum into the constructor it denotes --
/// `Nat.zero` when it's `0`, `Nat.succ (bignum - 1)` otherwise. Every
/// piece composed here was already trusted for a DIFFERENT reason:
/// `biguint_is_zero`/`biguint_pred` (already used by `pred_of_nat_succ`'s
/// own `NatLit` case), `mk_nat_lit_quick` (already used by every `do_nat_
/// bin` bridge to construct ITS OWN result), `c_nat_zero`/`c_nat_succ`
/// (mirroring `c_bool_true`'s exact pattern, now also pinning `const_
/// levels_vec(e)@.len() == 0` -- needed below, true of the real
/// monomorphic constants regardless) -- this is the first time all four
/// compose together. `depth <= 1` follows from `Nat.succ`'s own `Const`-
/// shape (depth 0) applied to a freshly-built `NatLit` (depth 0, same as
/// every other bound-variable-inert leaf) -- `App(Const, NatLit)` is depth
/// exactly 1, matching every other "small, closed, shallow" construction
/// in this arc.
///
/// The `pstep` conjunct is the genuinely NEW part (previous version only
/// stated structural bounds, saying nothing about what this constructs
/// relative to the bignum it started from): the result is EXACTLY what
/// `beta_model::pstep`'s `NatLit`-unfolding rule says `NatLit(bignum_ptr_
/// value(n))` reduces to, bridged from the opaque `const_expr_no_levels`
/// stand-in (see its own doc comment) to the REAL `Const` this function
/// actually builds via `const_expr_no_levels_canonical`.
pub fn verified_nat_lit_to_constructor<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    n: crate::util::BigUintPtr<'t>,
) -> (result: Option<ExprPtr<'t>>)
    ensures
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        match result {
            Some(r) => nlbv(to_model(r)) <= 0 && max_var_below(to_model(r), 0) && depth(to_model(r))
                <= 1 && pstep(
                crate::expr_arena_bridge::EnvSpec::empty(),
                ExprSpec::NatLit(NatLitPayload(Ghost(bignum_ptr_value(n)))),
                to_model(r),
            ),
            None => true,
        },
{
    let val = match read_bignum_value(ctx, n) {
        Some(v) => v,
        None => return None,
    };
    if biguint_is_zero(&val) {
        let result = match ctx.c_nat_zero() {
            Some(v) => v,
            None => return None,
        };
        proof {
            is_const_shape_model(result);
            assert(bignum_ptr_value(n) == 0);
            const_expr_no_levels_canonical(to_model(result), nat_zero_id());
            assert(pstep(
                crate::expr_arena_bridge::EnvSpec::empty(),
                ExprSpec::NatLit(NatLitPayload(Ghost(bignum_ptr_value(n)))),
                to_model(result),
            ));
        }
        Some(result)
    } else {
        let pred_val = biguint_pred(val);
        let pred = match ctx.mk_nat_lit_quick(pred_val) {
            Some(v) => v,
            None => return None,
        };
        let succ_c = match ctx.c_nat_succ() {
            Some(v) => v,
            None => return None,
        };
        proof {
            is_const_shape_model(succ_c);
            is_nat_lit_shape_model(pred);
            assert(bignum_ptr_value(n) > 0);
            assert(nat_lit_value(pred) == (bignum_ptr_value(n) - 1) as nat);
            const_expr_no_levels_canonical(to_model(succ_c), nat_succ_id());
        }
        let result = ctx.mk_app(succ_c, pred);
        proof {
            assert(to_model(result) == ExprSpec::App(
                Box::new(to_model(succ_c)),
                Box::new(to_model(pred)),
            ));
            assert(depth(to_model(succ_c)) == 0);
            assert(depth(to_model(pred)) == 0);
            assert(nlbv(to_model(succ_c)) == 0);
            assert(nlbv(to_model(pred)) == 0);
            assert(max_var_below(to_model(succ_c), 0));
            assert(max_var_below(to_model(pred), 0));
            assert(pstep(
                crate::expr_arena_bridge::EnvSpec::empty(),
                ExprSpec::NatLit(NatLitPayload(Ghost(bignum_ptr_value(n)))),
                to_model(result),
            ));
        }
        Some(result)
    }
}

/// `expr.rs::nat_type`/`string_type`'s result identity: `Const(nat_type_id,
/// [])`/`Const(string_type_id, [])` -- same "uninterpreted name id"
/// convention as `bool_true_id`/`nat_zero_id` above, standing in for
/// `export_file.name_cache.nat()`/`string`'s real per-export-file `NamePtr`s.
/// `None` covers the real function's only failure mode (the name isn't
/// present in this export file's cache). Deliberately does NOT model the
/// real callers' `assert!(config.nat_extension)`/`assert!(config.string_
/// extension)` guards -- a real, correctly-loaded kernel environment has
/// these set consistently with which literal shapes it actually contains,
/// same "don't model environment-level config" convention as everywhere
/// else in this arc.
pub uninterp spec fn nat_type_id() -> u64;

pub uninterp spec fn string_type_id() -> u64;

/// `NatLit`'s bignum payload, same trust-boundary shape as `Const`'s
/// `const_id`/`const_levels_vec`: `is_nat_lit_shape` marks a `NatLit`-
/// shaped pointer (bound-variable-inert, collapses to `ExprSpec::Closed`
/// like every other closed leaf), `bignum_ptr_value` is the uninterpreted
/// value a `BigUintPtr` denotes (mirrors `nat_lit_model.rs`'s `to_nat`,
/// but keyed by the ARENA pointer rather than a `BigUint` value directly,
/// exactly the same "pointer identity, not structural content" pattern
/// `name_id`/`expr_id` already use), and `nat_lit_value` composes the two
/// so callers can talk about "the nat this `ExprPtr` denotes" in one step.
pub open spec fn is_nat_lit_shape<'a>(ptr: ExprPtr<'a>) -> bool {
    matches!(to_model(ptr), ExprSpec::NatLit(_))
}

pub uninterp spec fn nat_lit_ptr_of<'a>(ptr: ExprPtr<'a>) -> crate::util::BigUintPtr<'a>;

pub uninterp spec fn bignum_ptr_value<'a>(p: crate::util::BigUintPtr<'a>) -> nat;

pub open spec fn nat_lit_value<'a>(ptr: ExprPtr<'a>) -> nat {
    bignum_ptr_value(nat_lit_ptr_of(ptr))
}

#[verifier::external_body]
pub proof fn is_nat_lit_shape_model<'a>(ptr: ExprPtr<'a>)
    requires
        is_nat_lit_shape(ptr),
    ensures
        to_model(ptr) == ExprSpec::NatLit(NatLitPayload(Ghost(nat_lit_value(ptr)))),
{
}

/// Same change as `expr_as_local`: proven from `read_expr` rather than assumed.
pub fn expr_as_nat_lit<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, ptr: ExprPtr<'t>) -> (result: Option<
    crate::util::BigUintPtr<'t>,
>)
    ensures
        match result {
            Some(p) => is_nat_lit_shape(ptr) && nat_lit_ptr_of(ptr) == p,
            None => !is_nat_lit_shape(ptr),
        },
{
    match ctx.read_expr(ptr) {
        Expr::NatLit { ptr: np, .. } => Some(np),
        _ => None,
    }
}

/// `StringLit`'s shape flag, now WITH a value accessor (`string_lit_ptr_
/// of`, mirroring `NatLit`'s `nat_lit_ptr_of` exactly): `is_string_lit_
/// shape` marks a `StringLit`-shaped pointer (bound-variable-inert), and
/// `string_lit_ptr_of` is the `StringPtr` it wraps -- same "pointer
/// identity, not structural content" pattern `nat_lit_ptr_of`/`name_id`/
/// `expr_id` already use. `expr_as_string_lit`'s own doc comment
/// previously noted this accessor didn't exist yet; it's needed now that
/// `ExprSpec::StringLit` carries real content (its length) instead of
/// collapsing into `Closed`.
pub open spec fn is_string_lit_shape<'a>(ptr: ExprPtr<'a>) -> bool {
    matches!(to_model(ptr), ExprSpec::StringLit(_))
}

pub uninterp spec fn string_lit_ptr_of<'a>(ptr: ExprPtr<'a>) -> StringPtr<'a>;

/// Same change as `expr_as_local`: proven from `read_expr` rather than assumed.
pub fn expr_as_string_lit<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, ptr: ExprPtr<'t>) -> (result: bool)
    ensures
        result == is_string_lit_shape(ptr),
{
    matches!(ctx.read_expr(ptr), Expr::StringLit { .. })
}

#[verifier::external_body]
pub proof fn is_string_lit_shape_model<'a>(ptr: ExprPtr<'a>)
    requires
        is_string_lit_shape(ptr),
    ensures
        to_model(ptr) == ExprSpec::StringLit(
            StringLitPayload(Ghost(string_chars(string_lit_ptr_of(ptr)))),
        ),
{
}

/// A string's character count -- an uninterpreted quantity (this arc
/// never models string CONTENT, only, here, its LENGTH) needed to state
/// `str_lit_to_constructor`'s real depth growth honestly: the real
/// function (`expr.rs:550-584`) builds one `List.cons (Char.ofNat _)`
/// `App` layer PER CHARACTER, so the result's depth genuinely scales
/// with the string's length -- a FIXED numeric cap here would be
/// unsound for a long enough string, not just imprecise (the standing
/// "no arbitrary caps when a real bound is derivable" rule applies
/// directly). Callers instead take `string_len(s)` bounded by an
/// explicit parameter, the same "caller-supplied sufficient bound"
/// pattern used throughout this whole arc.
/// The character codes of a stored string.
pub uninterp spec fn string_chars<'a>(s: StringPtr<'a>) -> Seq<nat>;

pub open spec fn string_len<'a>(s: StringPtr<'a>) -> nat {
    string_chars(s).len()
}

/// `expr.rs::str_lit_to_constructor`'s real construction, counted by
/// hand: `List.nil`'s own wrapper is depth 1; each character adds
/// `App(App(List.cons, App(Char.ofNat, NatLit)), rest)` -- `NatLit`
/// collapses to `ExprSpec::Closed` (depth 0, `is_nat_lit_shape_model`),
/// so `App(Char.ofNat, NatLit)` is depth 1, `App(List.cons_partial, ..)`
/// is depth 2, and wrapping the PREVIOUS `rest` costs exactly one more
/// level once `rest`'s own depth reaches 2 (true from the first
/// character on) -- so after `string_len(s)` characters the depth is
/// `string_len(s) + 2`, plus one final `App` for the `String.ofList`
/// wrapper: `string_len(s) + 3`. Every subterm is `Const`/`Closed`/`App`
/// of those -- no `Var`/`Free` anywhere -- so `nlbv`/`max_var_below`
/// hold unconditionally (bound `0` suffices for `max_var_below`,
/// weakened to whatever the caller needs via `max_var_below_mono`).
pub assume_specification<'t, 'p>[ TcCtx::<'t, 'p>::str_lit_to_constructor ](
    ctx: &mut TcCtx<'t, 'p>,
    s: StringPtr<'t>,
) -> (result: Option<ExprPtr<'t>>) where 'p: 't
    ensures
        final(ctx).expr_cache.dsubst_cache == old(ctx).expr_cache.dsubst_cache,
        match result {
            Some(r) => {
                &&& nlbv(to_model(r)) <= 0
                &&& max_var_below(to_model(r), 0)
                &&& depth(to_model(r)) <= string_len(s) + 3
                &&& to_model(r) == string_lit_expand_model(string_chars(s))
            },
            None => true,
        },
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
;

pub assume_specification<'t, 'p>[ read_bignum_value ](
    ctx: &TcCtx<'t, 'p>,
    p: crate::util::BigUintPtr<'t>,
) -> (result: Option<num_bigint::BigUint>) where 'p: 't
    ensures
        match result {
            Some(v) => crate::nat_lit_model::to_nat(v) == bignum_ptr_value(p),
            None => true,
        },
;

/// `Sort`'s level, read directly off the shallow value -- simpler than
/// `Const`'s `is_const_shape`/`const_name_of` indirection since `Sort`'s
/// payload (one `LevelPtr`) needs no `const_id`-style derivation or
/// `Vec`-vs-`Seq` bridging, so its contract can state `to_model_of_expr`
/// directly, the same way `expr_as_var` does. Needed now that `Sort`
/// carries its own `ExprSpec::Sort(LevelSpec)` payload (Phase 2a) rather
/// than collapsing into `Closed` -- until this was added,
/// `expr_is_closed_leaf`'s axiom below (which real `Expr::Sort` values DO
/// satisfy, since the real function pattern-matches `Sort`/`Const`/
/// `StringLit`/`NatLit` together) FORCED `to_model_of_expr` to be
/// `ExprSpec::Closed` for every real `Sort` node -- an actively false,
/// silently unsound axiom once `Sort` became a distinct variant, not just
/// an underspecified one (nothing previously exercised it against a
/// genuine `Sort` node to surface the inconsistency).
#[allow(dead_code)]
pub fn expr_as_sort<'t>(e: &Expr<'t>) -> (result: Option<LevelPtr<'t>>)
    ensures
        match result {
            Some(level) => to_model_of_expr(*e) == ExprSpec::Sort(level_to_model(level)),
            None => !matches!(to_model_of_expr(*e), ExprSpec::Sort(_)),
        },
{
    match e {
        Expr::Sort { level, .. } => Some(*level),
        _ => None,
    }
}

#[allow(dead_code)]
pub fn expr_as_pi<'t>(e: &Expr<'t>) -> (result: Option<
    (NamePtr<'t>, BinderStyle, ExprPtr<'t>, ExprPtr<'t>),
>)
    ensures
        match result {
            Some((_, _, ty, body)) => to_model_of_expr(*e) == ExprSpec::Bind(
                Box::new(to_model(ty)),
                Box::new(to_model(body)),
            ),
            None => true,
        },
{
    match e {
        Expr::Pi { binder_name, binder_style, binder_type, body, .. } => Some(
            (*binder_name, *binder_style, *binder_type, *body),
        ),
        _ => None,
    }
}

#[allow(dead_code)]
pub fn expr_as_lambda<'t>(e: &Expr<'t>) -> (result: Option<
    (NamePtr<'t>, BinderStyle, ExprPtr<'t>, ExprPtr<'t>),
>)
    ensures
        match result {
            Some((_, _, ty, body)) => to_model_of_expr(*e) == ExprSpec::Bind(
                Box::new(to_model(ty)),
                Box::new(to_model(body)),
            ),
            None => true,
        },
{
    match e {
        Expr::Lambda { binder_name, binder_style, binder_type, body, .. } => Some(
            (*binder_name, *binder_style, *binder_type, *body),
        ),
        _ => None,
    }
}

#[allow(dead_code)]
pub fn expr_as_let<'t>(e: &Expr<'t>) -> (result: Option<
    (NamePtr<'t>, ExprPtr<'t>, ExprPtr<'t>, ExprPtr<'t>, bool),
>)
    ensures
        match result {
            Some((_, ty, v, body, _)) => to_model_of_expr(*e) == ExprSpec::Let(
                Box::new(to_model(ty)),
                Box::new(to_model(v)),
                Box::new(to_model(body)),
            ),
            None => !matches!(to_model_of_expr(*e), ExprSpec::Let(_, _, _)),
        },
{
    match e {
        Expr::Let { binder_name, binder_type, val, body, nondep, .. } => Some(
            (*binder_name, *binder_type, *val, *body, *nondep),
        ),
        _ => None,
    }
}

#[allow(dead_code)]
pub fn expr_as_proj<'t>(e: &Expr<'t>) -> (result: Option<(NamePtr<'t>, usize, ExprPtr<'t>)>)
    ensures
        match result {
            Some((_, idx, s)) => to_model_of_expr(*e) == ExprSpec::Proj(idx, Box::new(to_model(s))),
            None => !matches!(to_model_of_expr(*e), ExprSpec::Proj(_, _)),
        },
{
    match e {
        Expr::Proj { ty_name, idx, structure, .. } => Some((*ty_name, *idx, *structure)),
        _ => None,
    }
}

/// THE storage primitive for bignums: allocation returns a pointer denoting
/// exactly the value handed in. Hash-consing may return an existing pointer
/// rather than appending, but either way the stored value IS `n`.
///
/// This replaces `mk_nat_lit_quick`'s own axiom. The assumption is the same
/// size but sits in a better place: a fact about what STORAGE holds, rather
/// than about what one convenience constructor returns -- and with it both
/// `mk_nat_lit` and `mk_nat_lit_quick` are proved rather than assumed.
pub assume_specification<'t, 'p>[ TcCtx::<'t, 'p>::alloc_bignum ](
    ctx: &mut TcCtx<'t, 'p>,
    n: num_bigint::BigUint,
) -> (result: Option<crate::util::BigUintPtr<'t>>) where 'p: 't
    ensures
        match result {
            Some(p) => bignum_ptr_value(p) == crate::nat_lit_model::to_nat(n),
            None => true,
        },
        final(ctx).expr_cache == old(ctx).expr_cache,
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
;

/// THE storage primitive for expressions: allocation returns a pointer
/// denoting exactly the node handed in. Hash-consing may return an existing
/// pointer rather than appending, but either way the stored node IS `e`, and
/// children keep their denotations by `expr_model_at_append` (proven above).
///
/// The `mk_*` contracts are DERIVED from this rather than assumed separately.
pub assume_specification<'t, 'p>[ TcCtx::<'t, 'p>::alloc_expr ](
    ctx: &mut TcCtx<'t, 'p>,
    e: Expr<'t>,
) -> (result: ExprPtr<'t>) where 'p: 't
    requires
        // what `read_expr` promises of every stored node has to hold of what
        // is stored: the cached flags are right, and a local's type is closed
        // (`local_type_wf`)
        node_cache_ok(e),
        e matches Expr::Local { binder_type, .. } ==> nlbv(to_model(binder_type)) == 0,
    ensures
        to_model(result) == to_model_of_expr(e),
        // The same clause `read_expr` carries, on the write side. `const_name_of`
        // and `const_levels_of` are uninterpreted, so `to_model(result)` alone
        // cannot say what they are -- which is why `mk_const` was the one
        // constructor of fifteen still needing its own axiom while the other
        // twelve derived from this one. With this, it derives too.
        e matches Expr::Const { name, levels, .. } ==> const_name_of(result) == name
            && const_levels_of(result) == levels,
        // Same, for the literal's payload pointer: `nat_lit_ptr_of` is a
        // separate uninterpreted projection from the one the denotation
        // carries, so `to_model(result)` alone does not pin it.
        e matches Expr::NatLit { ptr, .. } ==> nat_lit_ptr_of(result) == ptr,
        // FRAME. Allocation touches the dag, never the memo caches. Without
        // this, every constructor call inside a cache-wrapped function havocs
        // the cache and its soundness invariant cannot survive the body.
        final(ctx).expr_cache == old(ctx).expr_cache,
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
;

// HOW THESE NINE GET RETIRED (piloted 2026-09-17, not landed).
//
// Every `mk_*` body is two lines: compute a hash, call `alloc_expr`. So ONE
// storage primitive
//
//     assume_specification [TcCtx::alloc_expr](ctx, e) -> (result: ExprPtr)
//         ensures to_model(result) == to_model_of_expr(e);
//
// derives all nine denotation contracts, once the bodies are inside
// `verus!`. That primitive is justified by the facts proven above:
// hash-consing may return an existing pointer rather than appending, but
// either way the stored node IS `e`, and children keep their denotations by
// `expr_model_at_append`.
//
// What stops the bodies moving in is `hash64!`, not the denotation
// reasoning. Piloted on `mk_var`: registering `rustc_hash::FxHasher` as an
// external type clears the hasher, and then `Hash::hash` wants an
// `assume_specification` per primitive type hashed (u16, u64, the `Ptr`
// types) and the `*_HASH` consts need to be visible inside `verus!`.
// Estimated 8-12 further claim-free additions, all about hashing, which no
// model function reads.
//
// Net once done: these 9, plus the level and name constructors -- roughly 25
// denotation claims -- collapse to 3 storage primitives, and that many kernel
// functions move inside `verus!`.
/// Adapter over the kernel's own `TcCtx::inst`, which is verified in place now
/// (`expr.rs`). This was a 110-line reimplementation with its own fuel
/// parameter; what is left is the `Option` shape its twenty-four call sites
/// expect.
///
/// `offset == 0` is now required rather than supported. Every call site passes
/// a literal `0` -- the general-offset entry point was only ever exercised by
/// the mirror's own recursion, and the kernel has no such entry point at all
/// (`inst` fixes the offset at 0 and `inst_aux` is private to `expr.rs`).
///
/// The `substs` length check takes the place of a precondition the call sites
/// could not establish, using the same `None` escape the mirror used for fuel
/// exhaustion.
pub fn verified_inst<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    e: ExprPtr<'t>,
    substs: &[ExprPtr<'t>],
    offset: u16,
    fuel: u32,
) -> (result: Option<ExprPtr<'t>>)
    requires
        offset == 0,
        offset as nat + depth(to_model(e)) <= 60000,
    ensures
        (match result {
            Some(r) => to_model(r) == subst_full(
                to_model(e),
                Seq::new(substs@.len(), |i: int| to_model(substs@[i])),
                offset as nat,
            ),
            None => true,
        }),
        // Frame on the de Bruijn counter. Nothing in the shadow route said what
        // it does to this, which is what blocked both halves of the dbj-level
        // arc; `inst` resets a cache and touches no locals, so it says so.
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
{
    let _ = fuel;
    if substs.len() >= 60000 {
        return None;
    }
    let r = ctx.inst(e, substs);
    proof {
        assert(Seq::new(substs@.len(), |i: int| to_model(substs@[i])) =~= ptr_models(substs@));
    }
    Some(r)
}

/// Closed-form model of `TcCtx::abstr_pi_telescope`'s (`expr.rs:670-676`)
/// own recursion: peels `binder_ids`/`binder_tys` from the END (matching
/// the real function's `while let [tl @ .., binder] = binders`), each
/// step wrapping the accumulated body in ONE `abstr_pi`-shaped `Bind`
/// (`abstr_pi`'s own axiom, `quot_model.rs`) before recursing on the
/// shorter prefix -- so the OUTERMOST `Pi` in the result binds
/// `binder_ids[0]`/`binder_tys[0]`, matching `[a, b, c], e ~> Pi(a, Pi(b,
/// Pi(c, e)))` exactly as the doc comment there describes.
pub open spec fn abstr_pi_telescope_model(
    binder_ids: Seq<u32>,
    binder_tys: Seq<ExprSpec>,
    e: ExprSpec,
) -> ExprSpec
    decreases binder_ids.len(),
{
    if binder_ids.len() == 0 {
        e
    } else {
        let last_id = binder_ids.last();
        let last_ty = binder_tys.last();
        let rest_ids = binder_ids.drop_last();
        let rest_tys = binder_tys.drop_last();
        abstr_pi_telescope_model(
            rest_ids,
            rest_tys,
            ExprSpec::Bind(Box::new(last_ty), Box::new(abstr_full(e, seq![last_id], 0))),
        )
    }
}

/// Real-arena mirror of `TcCtx::abstr_pi_telescope` (`expr.rs:670-676`),
/// needed by `mk_motive_dep` (`inductive.rs:1058-1071`) to abstract a
/// motive's own index binders into a `Pi`-telescope. Each `binders[i]`
/// must be `Free`-shaped (an already-created `Local`, same precondition
/// `abstr_pi` itself already carries) for its own `abstr_pi` step to
/// apply.
pub fn verified_abstr_pi_telescope<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    binders: &[ExprPtr<'t>],
    e: ExprPtr<'t>,
) -> (result: ExprPtr<'t>)
    requires
        (forall|i: int|
            #![trigger binders@[i]]
            0 <= i < binders@.len() ==> {
                let m = to_model(binders@[i]);
                matches!(m, ExprSpec::Free(_))
            }),
        // Each step consumes one binder and wraps the result in a `Bind` whose
        // DOMAIN is that binder's type, so the depth grows by `1 + the type's
        // depth` per step -- not by one. `local_type_cap` bounds the latter,
        // and the caller supplies its concrete value, which is the convention
        // that cap is documented with.
        binders@.len() * (1 + local_type_cap()) + depth(to_model(e)) <= 60000,
    ensures
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        // Exported so a CHAIN of telescopes can be bounded by its callers: each
        // step adds one `Bind` whose domain is a binder's type.
        depth(to_model(result)) <= depth(to_model(e)) + binders@.len() * (1 + local_type_cap()),
        to_model(result) == abstr_pi_telescope_model(
            Seq::new(binders@.len(), |i: int| expr_id(binders@[i])),
            Seq::new(binders@.len(), |i: int| local_type(binders@[i])),
            to_model(e),
        ),
    decreases binders.len(),
{
    if binders.len() == 0 {
        assert(Seq::new(binders@.len(), |i: int| expr_id(binders@[i])).len() == 0);
        return e;
    }
    let last = binders[binders.len() - 1];
    let rest = &binders[0..binders.len() - 1];
    assert(rest@ =~= binders@.subrange(0, binders@.len() as int - 1));
    proof {
        local_type_wf(last);
        mul_ge_one(binders@.len(), (1 + local_type_cap()) as nat);
        assert(depth(to_model(e)) + 1 + local_type_cap() <= 60000);
    }
    let e2 = ctx.abstr_pi(last, e);
    proof {
        abstr_full_depth(to_model(e), seq![expr_id(last)], 0);
        assert(depth(to_model(e2)) <= 1 + local_type_cap() + depth(to_model(e)));
        mul_pred_step(binders@.len(), (1 + local_type_cap()) as nat);
    }
    let result = verified_abstr_pi_telescope(ctx, rest, e2);
    proof {
        let ids = Seq::new(binders@.len(), |i: int| expr_id(binders@[i]));
        let tys = Seq::new(binders@.len(), |i: int| local_type(binders@[i]));
        let rest_ids = Seq::new(rest@.len(), |i: int| expr_id(rest@[i]));
        let rest_tys = Seq::new(rest@.len(), |i: int| local_type(rest@[i]));
        assert(ids.drop_last() =~= rest_ids);
        assert(tys.drop_last() =~= rest_tys);
        assert(ids.last() == expr_id(last));
        assert(tys.last() == local_type(last));
    }
    result
}

/// Real-arena mirror of `TcCtx::abstr_lambda_telescope` (`expr.rs:658-
/// 664`): peels `binders` from the end via `apply_lambda`, needed by
/// `handle_rec_ctor_args_rec_rule`/`mk_rec_rule1` (`inductive.rs:1201-
/// 1250`). Reuses `abstr_pi_telescope_model` UNCHANGED as its closed-form
/// model, not a separate `abstr_lambda_telescope_model` -- `apply_lambda`'s
/// own `ensures` is IDENTICAL in shape to `abstr_pi`'s (both produce
/// `ExprSpec::Bind`, the model never distinguishes `Pi` from `Lambda`),
/// so the two telescope functions' closed forms are the SAME spec fn,
/// just reached via a different real constructor underneath (invisible
/// to the model either way).
pub fn verified_abstr_lambda_telescope<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    binders: &[ExprPtr<'t>],
    e: ExprPtr<'t>,
) -> (result: ExprPtr<'t>)
    requires
        (forall|i: int|
            #![trigger binders@[i]]
            0 <= i < binders@.len() ==> {
                let m = to_model(binders@[i]);
                matches!(m, ExprSpec::Free(_))
            }),
        // Each step consumes one binder and wraps the result in a `Bind` whose
        // DOMAIN is that binder's type, so the depth grows by `1 + the type's
        // depth` per step -- not by one. `local_type_cap` bounds the latter,
        // and the caller supplies its concrete value, which is the convention
        // that cap is documented with.
        binders@.len() * (1 + local_type_cap()) + depth(to_model(e)) <= 60000,
    ensures
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        // Exported so a CHAIN of telescopes can be bounded by its callers: each
        // step adds one `Bind` whose domain is a binder's type.
        depth(to_model(result)) <= depth(to_model(e)) + binders@.len() * (1 + local_type_cap()),
        to_model(result) == abstr_pi_telescope_model(
            Seq::new(binders@.len(), |i: int| expr_id(binders@[i])),
            Seq::new(binders@.len(), |i: int| local_type(binders@[i])),
            to_model(e),
        ),
    decreases binders.len(),
{
    if binders.len() == 0 {
        assert(Seq::new(binders@.len(), |i: int| expr_id(binders@[i])).len() == 0);
        return e;
    }
    let last = binders[binders.len() - 1];
    let rest = &binders[0..binders.len() - 1];
    assert(rest@ =~= binders@.subrange(0, binders@.len() as int - 1));
    proof {
        local_type_wf(last);
        mul_ge_one(binders@.len(), (1 + local_type_cap()) as nat);
        assert(depth(to_model(e)) + 1 + local_type_cap() <= 60000);
    }
    let e2 = ctx.apply_lambda(last, e);
    proof {
        abstr_full_depth(to_model(e), seq![expr_id(last)], 0);
        assert(depth(to_model(e2)) <= 1 + local_type_cap() + depth(to_model(e)));
        mul_pred_step(binders@.len(), (1 + local_type_cap()) as nat);
    }
    let result = verified_abstr_lambda_telescope(ctx, rest, e2);
    proof {
        let ids = Seq::new(binders@.len(), |i: int| expr_id(binders@[i]));
        let tys = Seq::new(binders@.len(), |i: int| local_type(binders@[i]));
        let rest_ids = Seq::new(rest@.len(), |i: int| expr_id(rest@[i]));
        let rest_tys = Seq::new(rest@.len(), |i: int| local_type(rest@[i]));
        assert(ids.drop_last() =~= rest_ids);
        assert(tys.drop_last() =~= rest_tys);
        assert(ids.last() == expr_id(last));
        assert(tys.last() == local_type(last));
    }
    result
}

/// Real-arena counterpart to real `TcCtx::subst_aux`/`subst_expr_levels`
/// (`expr.rs:333-391`): substitutes universe-level PARAMETERS (not de
/// Bruijn indices) throughout an expression -- the building block
/// `unfold_def`'s real delta-reduction step needs, since unfolding
/// `foo.{u,v}` means substituting `foo`'s definition body's own level
/// parameters by `u,v` before use. Mirrors `expr_model::subst_expr_levels_
/// model`'s structure (`Sort`/`Const` route through `verified_subst_level`/
/// `verified_subst_levels`, everything else recurses structurally), proven
/// against `subst_expr_levels_rel` the same way that model function is.
/// Like `subst_aux`'s own comment, this is only ever meant to be called on
/// expressions freshly pulled from the environment (no `Local`s) --
/// `expr_is_local` is treated as a no-op here purely for totality, mirroring
/// `subst_expr_levels_model`'s `Free` case, not because it's expected to
/// fire.
pub fn verified_subst_expr_levels<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    e: ExprPtr<'t>,
    ks: LevelsPtr<'t>,
    vs: LevelsPtr<'t>,
    fuel: u32,
) -> (result: Option<ExprPtr<'t>>)
    requires
        to_model_of_levels(ks).len() == to_model_of_levels(vs).len(),
        forall|j: int|
            0 <= j < to_model_of_levels(ks).len() ==> #[trigger] to_model_of_levels(ks)[j] is Param,
    ensures
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        match result {
            Some(r) => subst_expr_levels_rel(
                to_model(e),
                level_names(to_model_of_levels(ks)),
                to_model_of_levels(vs),
                to_model(r),
            )
            // SYNTACTIC pin (delta-lift L2): the real result IS the spec function's output.
             && to_model(r) == subst_expr_levels(
                to_model(e),
                level_names(to_model_of_levels(ks)),
                to_model_of_levels(vs),
            ),
            None => true,
        },
    decreases fuel,
{
    if fuel == 0 {
        return None;
    }
    let fuel1 = fuel - 1;
    let el = ctx.read_expr(e);
    if let Some(dbj_idx) = expr_as_var(&el) {
        assert(to_model(e) == ExprSpec::Var(dbj_idx as u32));
        return Some(e);
    }
    if expr_is_local(ctx, e) {
        assert(to_model(e) == ExprSpec::Free(expr_id(e)));
        return Some(e);
    }
    if let Some(level) = expr_as_sort(&el) {
        assert(to_model(e) == ExprSpec::Sort(level_to_model(level)));
        return match verified_subst_level(ctx, level, ks, vs, fuel1) {
            Some(new_level) => {
                let result = ctx.mk_sort(new_level);
                assert(to_model(result) == ExprSpec::Sort(level_to_model(new_level)));
                assert(to_model(result) == subst_expr_levels(
                    to_model(e),
                    level_names(to_model_of_levels(ks)),
                    to_model_of_levels(vs),
                ));
                Some(result)
            },
            None => None,
        };
    }
    if let Expr::Const { name, levels, .. } = el {
        assert(is_const_shape(e) && const_name_of(e) == name && const_levels_of(e) == levels);
        proof {
            is_const_shape_model(e);
            const_levels_vec_model(e);
        }
        assert(to_model(e) == ExprSpec::Const(const_id(e), const_levels_vec(e)));
        assert(const_levels_vec(e) =~= to_model_of_levels(levels));
        return match verified_subst_levels(ctx, levels, ks, vs, fuel1) {
            Some(new_levels) => {
                let result = ctx.mk_const(name, new_levels);
                assert(is_const_shape(result) && const_name_of(result) == name && const_levels_of(
                    result,
                ) == new_levels);
                proof {
                    is_const_shape_model(result);
                    const_levels_vec_model(result);
                }
                assert(to_model(result) == ExprSpec::Const(
                    const_id(result),
                    const_levels_vec(result),
                ));
                assert(const_levels_vec(result) =~= to_model_of_levels(new_levels));
                assert(const_id(result) == const_id(e));
                assert(to_model_of_levels(new_levels).len() == to_model_of_levels(levels).len());
                assert forall|j: int, rho: Map<nat, nat>|
                    0 <= j < to_model_of_levels(levels).len() implies #[trigger] interp(
                    to_model_of_levels(new_levels)[j],
                    rho,
                ) == interp(
                    to_model_of_levels(levels)[j],
                    subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs)),
                ) by {}
                assert(const_levels_vec(result).len() == const_levels_vec(e).len());
                assert forall|j: int, rho: Map<nat, nat>|
                    0 <= j < const_levels_vec(e).len() implies #[trigger] interp(
                    const_levels_vec(result)[j],
                    rho,
                ) == interp(
                    const_levels_vec(e)[j],
                    subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs)),
                ) by {}
                // Syntactic pin: the Seq extensional equality from the level
                // bridge lifts to the Const node.
                assert(to_model_of_levels(new_levels) =~= crate::level_model::subst_levels_spec(
                    to_model_of_levels(levels),
                    level_names(to_model_of_levels(ks)),
                    to_model_of_levels(vs),
                ));
                assert(to_model(result) == ExprSpec::Const(
                    const_id(e),
                    crate::level_model::subst_levels_spec(
                        const_levels_vec(e),
                        level_names(to_model_of_levels(ks)),
                        to_model_of_levels(vs),
                    ),
                ));
                assert(to_model(result) == subst_expr_levels(
                    to_model(e),
                    level_names(to_model_of_levels(ks)),
                    to_model_of_levels(vs),
                ));
                Some(result)
            },
            None => None,
        };
    }
    if let Some(_p) = expr_as_nat_lit(ctx, e) {
        assert(is_nat_lit_shape(e));
        proof {
            is_nat_lit_shape_model(e);
        }
        assert(to_model(e) == ExprSpec::NatLit(NatLitPayload(Ghost(nat_lit_value(e)))));
        return Some(e);
    }
    if expr_as_string_lit(ctx, e) {
        assert(is_string_lit_shape(e));
        proof {
            is_string_lit_shape_model(e);
        }
        assert(to_model(e) == ExprSpec::StringLit(
            StringLitPayload(Ghost(string_chars(string_lit_ptr_of(e)))),
        ));
        return Some(e);
    }
    if expr_is_closed_leaf(e, &el) {
        assert(to_model(e) == ExprSpec::Closed);
        return Some(e);
    }
    if let Some((fun, arg)) = expr_as_app(&el) {
        assert(to_model(e) == ExprSpec::App(Box::new(to_model(fun)), Box::new(to_model(arg))));
        return match (
            verified_subst_expr_levels(ctx, fun, ks, vs, fuel1),
            verified_subst_expr_levels(ctx, arg, ks, vs, fuel1),
        ) {
            (Some(sf), Some(sa)) => Some(ctx.mk_app(sf, sa)),
            _ => None,
        };
    }
    if let Some((binder_name, binder_style, binder_type, body)) = expr_as_pi(&el) {
        assert(to_model(e) == ExprSpec::Bind(
            Box::new(to_model(binder_type)),
            Box::new(to_model(body)),
        ));
        return match (
            verified_subst_expr_levels(ctx, binder_type, ks, vs, fuel1),
            verified_subst_expr_levels(ctx, body, ks, vs, fuel1),
        ) {
            (Some(st), Some(sb)) => Some(ctx.mk_pi(binder_name, binder_style, st, sb)),
            _ => None,
        };
    }
    if let Some((binder_name, binder_style, binder_type, body)) = expr_as_lambda(&el) {
        assert(to_model(e) == ExprSpec::Bind(
            Box::new(to_model(binder_type)),
            Box::new(to_model(body)),
        ));
        return match (
            verified_subst_expr_levels(ctx, binder_type, ks, vs, fuel1),
            verified_subst_expr_levels(ctx, body, ks, vs, fuel1),
        ) {
            (Some(st), Some(sb)) => Some(ctx.mk_lambda(binder_name, binder_style, st, sb)),
            _ => None,
        };
    }
    if let Some((binder_name, binder_type, val, body, nondep)) = expr_as_let(&el) {
        assert(to_model(e) == ExprSpec::Let(
            Box::new(to_model(binder_type)),
            Box::new(to_model(val)),
            Box::new(to_model(body)),
        ));
        return match (
            verified_subst_expr_levels(ctx, binder_type, ks, vs, fuel1),
            verified_subst_expr_levels(ctx, val, ks, vs, fuel1),
        ) {
            (Some(st), Some(sv)) => match verified_subst_expr_levels(ctx, body, ks, vs, fuel1) {
                Some(sb) => Some(ctx.mk_let(binder_name, st, sv, sb, nondep)),
                None => None,
            },
            _ => None,
        };
    }
    if let Some((ty_name, idx, structure)) = expr_as_proj(&el) {
        assert(to_model(e) == ExprSpec::Proj(idx, Box::new(to_model(structure))));
        return match verified_subst_expr_levels(ctx, structure, ks, vs, fuel1) {
            Some(ss) => Some(ctx.mk_proj(ty_name, idx, ss)),
            None => None,
        };
    }
    None
}

// -----------------------------------------------------------------------
// Bridging `tc.rs`'s real beta-reduction step (`whnf_no_unfolding_aux`'s
// `Lambda { .. } if !args.is_empty()` case) to `beta_model.rs`'s
// telescopic-reduction confluence machinery (`spine_bind`/`spine_app`/
// `spine_reduce`/`spine_reduce_eq_subst_full`). `verified_inst` above
// already gives `inst`'s correctness relative to `subst_full`; what's new
// here is bridging the SURROUNDING peel/reapply logic (`unfold_apps`,
// counting how many lambdas to peel, `foldl_apps`) so the real code's
// FULL beta step -- not just its `inst` sub-call -- is provably related
// to the model.
// -----------------------------------------------------------------------
/// A slice-shaped call into the kernel's own `TcCtx::foldl_apps`, which is
/// now verified in place (`expr.rs`). This used to be a mirror: the loop
/// reformulated as a recursion, because a real exec loop could not carry the
/// proof obligation across iterations. It can now -- the obstacle was a Verus
/// bug in `for` over a generic iterator, since fixed -- so the recursion and
/// its `spine_app_compose` bridge are gone and this is only an adapter.
///
/// What it adapts is the argument shape: callers hold a `&[ExprPtr]`, the
/// kernel takes an `Iterator`. The two asserts are the two extensionality
/// steps that bridge them -- `iter().copied()`'s `remaining()` to the slice
/// view, and `ptr_models` to the `Seq::new` spelling the callers use.
pub fn verified_foldl_apps<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    fun: ExprPtr<'t>,
    args: &[ExprPtr<'t>],
) -> (result: ExprPtr<'t>)
    ensures
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        to_model(result) == spine_app(
            to_model(fun),
            Seq::new(args@.len(), |i: int| to_model(args@[i])),
        ),
{
    let it = args.iter().copied();
    proof {
        assert(it.remaining() =~= args@);
    }
    let r = ctx.foldl_apps(fun, it);
    proof {
        assert(Seq::new(args@.len(), |i: int| to_model(args@[i])) =~= ptr_models(args@));
    }
    r
}

/// Real-arena counterpart to `spine_app`'s inverse: `TcCtx::unfold_apps`'s
/// actual loop (`from f a_0 .. a_N, return (f, [a_0, .. a_N])`),
/// reformulated recursively -- peels one `App` at a time descending into
/// `fun`, appending `arg` to the tail on the way back up, which lands
/// args in the SAME `[a_0, .. a_N]` order the real loop produces only
/// after its own explicit `args.reverse()`. `ExprPtr` is opaque (no
/// structural `decreases`), so this needs fuel, like `verified_inst`.
// `<[T]>::reverse` used to be assumed here. It is in vstd now (the spec is
// general, not nanoda-specific, so that is where it belongs) and this crate
// picks it up from there.
// `foldl_apps` -- the dual of `unfold_apps` -- was attempted and backed out
// (2026-09-17). Its contract and invariant are straightforward:
//
//     ensures to_model(result) == spine_app(to_model(fun0), ptr_models(args.remaining()))
//     invariant to_model(fun) == spine_app(to_model(fun0),
//                                          ptr_models(it.seq().take(it.index())))
//
// and the step needs only `spine_app_compose_last` plus a push-commutes
// lemma. What did not come through is the `for`-loop wrapper's own facts:
// neither the entry invariant (`take(0)` empty) nor the tie between
// `it.seq()` and `args.remaining()` discharged, and `it` is out of scope
// after the loop so the exit cannot be bridged by hand.
//
// This is the same wall as the `copied()` loop upstream: writing the
// invariant is easy, getting the wrapper to hand over its relationship to
// the original iterator is not. `unfold_apps` avoided it by using a bare
// `loop` rather than a `for`.
/// The models of a sequence of expression pointers.
pub open spec fn ptr_models<'a>(s: Seq<ExprPtr<'a>>) -> Seq<ExprSpec> {
    Seq::new(s.len(), |i: int| to_model(s[i]))
}

/// Taking models commutes with pushing.
pub proof fn ptr_models_push<'a>(s: Seq<ExprPtr<'a>>, x: ExprPtr<'a>)
    ensures
        ptr_models(s.push(x)) =~= ptr_models(s).push(to_model(x)),
{
    assert forall|i: int| 0 <= i < s.len() + 1 implies #[trigger] ptr_models(s.push(x))[i]
        == ptr_models(s).push(to_model(x))[i] by {
        if i < s.len() {
            assert(s.push(x)[i] == s[i]);
        }
    }
}

/// Taking models distributes over concatenation.
pub proof fn ptr_models_add<'a>(a: Seq<ExprPtr<'a>>, b: Seq<ExprPtr<'a>>)
    ensures
        ptr_models(a + b) =~= ptr_models(a) + ptr_models(b),
{
    assert forall|i: int| 0 <= i < (a + b).len() implies #[trigger] ptr_models(a + b)[i] == (
    ptr_models(a) + ptr_models(b))[i] by {
        if i < a.len() {
            assert((a + b)[i] == a[i]);
        } else {
            assert((a + b)[i] == b[i - a.len()]);
        }
    }
}

/// Taking models commutes with reversing.
pub proof fn ptr_models_reverse<'a>(s: Seq<ExprPtr<'a>>)
    ensures
        ptr_models(s.reverse()) =~= ptr_models(s).reverse(),
{
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] ptr_models(s.reverse())[i]
        == ptr_models(s).reverse()[i] by {
        assert(s.reverse()[i] == s[s.len() - 1 - i]);
    }
}

/// Real-arena counterpart to `spine_bind`: mirrors
/// `whnf_no_unfolding_aux`'s peeling `while let (Lambda { body, .. },
/// [_arg, _rest @ ..]) = (read_expr(e), &args[n_args..]) { n_args += 1;
/// e = body; }` loop, again reformulated recursively for the same fuel
/// reason `verified_inst` needs it. Peels exactly `min(nested-Lambda-
/// depth of e, args_len)` binders -- the loop stops the instant EITHER
/// condition fails, matching `spine_bind`'s own "peel until `n` or until
/// not `Bind`-shaped" behavior exactly.
pub fn verified_peel_lambdas<'t, 'p: 't>(
    ctx: &TcCtx<'t, 'p>,
    e: ExprPtr<'t>,
    args_len: usize,
    fuel: u32,
) -> (result: Option<(ExprPtr<'t>, usize)>)
    ensures
        match result {
            Some((body, n)) => n <= args_len && spine_bind(to_model(e), n as nat) == Some(
                to_model(body),
            ),
            None => true,
        },
    decreases fuel,
{
    if fuel == 0 {
        return None;
    }
    if args_len == 0 {
        assert(spine_bind(to_model(e), 0) == Some(to_model(e)));
        return Some((e, 0));
    }
    let fuel1 = fuel - 1;
    let el = ctx.read_expr(e);
    if let Some((_, _, ty, body)) = expr_as_lambda(&el) {
        assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(ty)), Box::new(to_model(body))));
        match verified_peel_lambdas(ctx, body, args_len - 1, fuel1) {
            Some((b2, n2)) => {
                assert(spine_bind(to_model(e), (n2 + 1) as nat) == spine_bind(
                    to_model(body),
                    n2 as nat,
                ));
                Some((b2, n2 + 1))
            },
            None => None,
        }
    } else {
        Some((e, 0))
    }
}

/// The capstone: bridges `tc.rs`'s `whnf_no_unfolding_aux`'s
/// `Lambda { .. } if !args.is_empty()` branch -- the real kernel's
/// actual beta-reduction step (peel as many binders as there are
/// available args via `verified_peel_lambdas`, substitute all of them
/// at once via `verified_inst`, reapply any leftover args via
/// `verified_foldl_apps`) -- to `spine_reduce`, connecting REAL,
/// EXECUTABLE code to the model's telescopic-substitution/confluence
/// machinery for the first time in this codebase.
///
/// Requires `e_fun` and every arg to be CLOSED (`nlbv <= 0`, no escaping
/// loose references at all) -- the discipline real top-level `whnf`
/// calls maintain (anything bound further out is a `Local`, never a raw
/// escaping `Var`; see `spine_reduce`'s own doc comment in
/// `beta_model.rs`). This is what lets `spine_bind_nlbv` guarantee the
/// peeled body satisfies `spine_reduce_eq_subst_full`'s precondition for
/// WHATEVER peel count `n` the real code data-dependently computes,
/// without needing to know `n` in advance.
pub fn verified_whnf_beta_step<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    e_fun: ExprPtr<'t>,
    args: &[ExprPtr<'t>],
    fuel: u32,
    Ghost(bound): Ghost<nat>,
) -> (result: Option<ExprPtr<'t>>)
    requires
        args.len() > 0,
        nlbv(to_model(e_fun)) <= 0,
        forall|i: int|
            0 <= i < args@.len() ==> nlbv(to_model(args@[i])) <= 0 && max_var_below(
                to_model(args@[i]),
                bound,
            ),
        depth(to_model(e_fun)) <= 60000,
        bound + 10 <= 0xFFFF_0000,
    ensures
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        match result {
            Some(r) => exists|n: nat|
                #![trigger spine_bind(to_model(e_fun), n)]
                n <= args.len() && spine_bind(to_model(e_fun), n) is Some && to_model(r)
                    == spine_app(
                    spine_reduce(to_model(e_fun), Seq::new(n, |i: int| to_model(args@[i]))),
                    Seq::new((args@.len() - n) as nat, |i: int| to_model(args@[n as int + i])),
                ) && pstep_star(
                    crate::expr_arena_bridge::EnvSpec::empty(),
                    spine_app(to_model(e_fun), Seq::new(args@.len(), |i: int| to_model(args@[i]))),
                    to_model(r),
                ),
            None => true,
        },
{
    match verified_peel_lambdas(ctx, e_fun, args.len(), fuel) {
        Some((peeled, n)) => {
            proof {
                spine_bind_nlbv(to_model(e_fun), n as nat, to_model(peeled), 0);
                spine_bind_depth(to_model(e_fun), n as nat, to_model(peeled));
            }
            let consumed = &args[0..n];
            let remaining = &args[n..args.len()];
            match verified_inst(ctx, peeled, consumed, 0, fuel) {
                Some(inst_result) => {
                    proof {
                        assert forall|i: int| 0 <= i < consumed@.len() implies nlbv(
                            to_model(consumed@[i]),
                        ) <= 0 && max_var_below(to_model(consumed@[i]), bound) by {
                            assert(consumed@[i] == args@[i]);
                        }
                        let consumed_model = Seq::new(
                            consumed@.len(),
                            |i: int| to_model(consumed@[i]),
                        );
                        spine_reduce_eq_subst_full(
                            to_model(e_fun),
                            consumed_model,
                            to_model(peeled),
                            bound,
                        );
                        assert(spine_reduce(to_model(e_fun), consumed_model) == subst_full(
                            to_model(peeled),
                            consumed_model,
                            0,
                        ));
                        assert(to_model(inst_result) == subst_full(
                            to_model(peeled),
                            consumed_model,
                            0,
                        ));
                    }
                    let result = verified_foldl_apps(ctx, inst_result, remaining);
                    proof {
                        assert(remaining@ =~= args@.subrange(n as int, args@.len() as int));
                        assert(Seq::new(remaining@.len(), |i: int| to_model(remaining@[i]))
                            =~= Seq::new(
                            (args@.len() - n) as nat,
                            |i: int| to_model(args@[n as int + i]),
                        ));
                        assert(Seq::new(consumed@.len(), |i: int| to_model(consumed@[i]))
                            =~= Seq::new(n as nat, |i: int| to_model(args@[i])));
                        assert(to_model(result) == spine_app(
                            to_model(inst_result),
                            Seq::new(remaining@.len(), |i: int| to_model(remaining@[i])),
                        ));
                        assert(to_model(result) == spine_app(
                            spine_reduce(
                                to_model(e_fun),
                                Seq::new(n as nat, |i: int| to_model(args@[i])),
                            ),
                            Seq::new(
                                (args@.len() - n) as nat,
                                |i: int| to_model(args@[n as int + i]),
                            ),
                        ));
                        assert(spine_bind(to_model(e_fun), n as nat) == Some(to_model(peeled)));

                        let consumed_model = Seq::new(n as nat, |i: int| to_model(args@[i]));
                        let remaining_model = Seq::new(
                            (args@.len() - n) as nat,
                            |i: int| to_model(args@[n as int + i]),
                        );
                        let full_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
                        assert(consumed_model + remaining_model =~= full_model);

                        pstep_star_spine_reduce(
                            crate::expr_arena_bridge::EnvSpec::empty(),
                            to_model(e_fun),
                            consumed_model,
                        );
                        assert(pstep_star(
                            crate::expr_arena_bridge::EnvSpec::empty(),
                            spine_app(to_model(e_fun), consumed_model),
                            spine_reduce(to_model(e_fun), consumed_model),
                        ));

                        pstep_spine_app_star(
                            crate::expr_arena_bridge::EnvSpec::empty(),
                            spine_app(to_model(e_fun), consumed_model),
                            spine_reduce(to_model(e_fun), consumed_model),
                            remaining_model,
                        );
                        assert(pstep_star(
                            crate::expr_arena_bridge::EnvSpec::empty(),
                            spine_app(spine_app(to_model(e_fun), consumed_model), remaining_model),
                            spine_app(
                                spine_reduce(to_model(e_fun), consumed_model),
                                remaining_model,
                            ),
                        ));

                        spine_app_concat(to_model(e_fun), consumed_model, remaining_model);
                        assert(spine_app(to_model(e_fun), full_model) == spine_app(
                            spine_app(to_model(e_fun), consumed_model),
                            remaining_model,
                        ));

                        assert(pstep_star(
                            crate::expr_arena_bridge::EnvSpec::empty(),
                            spine_app(to_model(e_fun), full_model),
                            to_model(result),
                        ));
                    }
                    Some(result)
                },
                None => None,
            }
        },
        None => None,
    }
}

/// Bridges `tc.rs`'s `whnf_no_unfolding_aux`'s `Let { val, body, .. }`
/// branch -- the real kernel's actual ZETA-reduction step: `inst(body,
/// [val])` (a single substitution -- `Let`'s type annotation `t` is
/// simply irrelevant and discarded, matching `pstep`'s own zeta rule),
/// then reapply any args the `Let`-headed spine was carrying. Much
/// simpler than `verified_whnf_beta_step`: no binder-peeling loop (a
/// `Let` never has "more than one" to peel -- it's a single substitution
/// every time), so this is a direct `verified_inst` call at a
/// one-element substs list, matching `subst1` exactly.
///
/// Only possible after `pstep`'s `Let` case was extended with an actual
/// zeta rule (see `beta_model.rs`'s `pstep` doc comment): without it,
/// `pstep(Let(t,v,b), subst1(b,v))` was simply false in the model, so
/// this bridge (and the `pstep_star` conclusion in particular) could not
/// have been stated, let alone proven.
pub fn verified_whnf_zeta_step<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    e_fun: ExprPtr<'t>,
    val: ExprPtr<'t>,
    body: ExprPtr<'t>,
    args: &[ExprPtr<'t>],
    fuel: u32,
    Ghost(bound): Ghost<nat>,
) -> (result: Option<ExprPtr<'t>>)
    requires
        exists|t_model: ExprSpec|
            to_model(e_fun) == ExprSpec::Let(
                Box::new(t_model),
                Box::new(to_model(val)),
                Box::new(to_model(body)),
            ),
        nlbv(to_model(body)) <= 1,
        nlbv(to_model(val)) <= 0,
        max_var_below(to_model(val), bound),
        forall|i: int|
            0 <= i < args@.len() ==> nlbv(to_model(args@[i])) <= 0 && max_var_below(
                to_model(args@[i]),
                bound,
            ),
        depth(to_model(body)) <= 60000,
        bound + 10 <= 0xFFFF_0000,
    ensures
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        match result {
            Some(r) => to_model(r) == spine_app(
                subst1(to_model(body), to_model(val)),
                Seq::new(args@.len(), |i: int| to_model(args@[i])),
            ) && pstep_star(
                crate::expr_arena_bridge::EnvSpec::empty(),
                spine_app(to_model(e_fun), Seq::new(args@.len(), |i: int| to_model(args@[i]))),
                to_model(r),
            ),
            None => true,
        },
{
    let substs_arr = [val];
    match verified_inst(ctx, body, &substs_arr, 0, fuel) {
        Some(inst_result) => {
            proof {
                assert(substs_arr@ =~= seq![val]);
                assert(Seq::new(substs_arr@.len(), |i: int| to_model(substs_arr@[i])) =~= seq![
                    to_model(val),
                ]);
                assert(to_model(inst_result) == subst_full(to_model(body), seq![to_model(val)], 0));

                assert(subst1(to_model(body), to_model(val)) == subst_c(
                    to_model(body),
                    to_model(val),
                    0,
                ));
                subst_c_eq_subst_full(to_model(body), to_model(val), 0, bound);
                assert(subst_c(to_model(body), to_model(val), 0) == subst_full(
                    to_model(body),
                    seq![to_model(val)],
                    0,
                ));
                assert(to_model(inst_result) == subst1(to_model(body), to_model(val)));
            }
            let result = verified_foldl_apps(ctx, inst_result, args);
            proof {
                let args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
                assert(to_model(result) == spine_app(to_model(inst_result), args_model));
                assert(to_model(result) == spine_app(
                    subst1(to_model(body), to_model(val)),
                    args_model,
                ));

                assert(pstep(
                    crate::expr_arena_bridge::EnvSpec::empty(),
                    to_model(e_fun),
                    subst1(to_model(body), to_model(val)),
                )) by {
                    assert(pstep(
                        crate::expr_arena_bridge::EnvSpec::empty(),
                        to_model(body),
                        to_model(body),
                    ));
                    assert(pstep(
                        crate::expr_arena_bridge::EnvSpec::empty(),
                        to_model(val),
                        to_model(val),
                    ));
                }
                pstep_star_one(
                    crate::expr_arena_bridge::EnvSpec::empty(),
                    to_model(e_fun),
                    subst1(to_model(body), to_model(val)),
                );
                pstep_spine_app_star(
                    crate::expr_arena_bridge::EnvSpec::empty(),
                    to_model(e_fun),
                    subst1(to_model(body), to_model(val)),
                    args_model,
                );
                assert(pstep_star(
                    crate::expr_arena_bridge::EnvSpec::empty(),
                    spine_app(to_model(e_fun), args_model),
                    spine_app(subst1(to_model(body), to_model(val)), args_model),
                ));
                assert(pstep_star(
                    crate::expr_arena_bridge::EnvSpec::empty(),
                    spine_app(to_model(e_fun), args_model),
                    to_model(result),
                ));
            }
            Some(result)
        },
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs`'s `whnf_no_unfolding_aux`, ONE pass
/// through its match (not chasing its own further recursive call on the
/// result -- matching this file's existing precedent of `verified_
/// whnf_beta_step`/`verified_whnf_zeta_step` each modeling one telescoped
/// step rather than a full fixpoint): peel the applied spine via `verified_
/// unfold_apps`, then dispatch on the (real) head shape exactly like the
/// real match does -- `Lambda` with args reuses `verified_whnf_beta_step`,
/// `Let` reuses `verified_whnf_zeta_step`, and every other shape (`Pi`,
/// `Local`, `NatLit`, `StringLit`, a no-arg `Lambda`, and -- honestly NOT
/// yet modeled -- `Proj`/`Sort`'s `simplify` call/`Const`'s `reduce_quot`/
/// `reduce_rec`) falls through to the identity `pstep_star` step, which is
/// always sound (if incomplete) regardless of shape.
///
/// `spine_app_decompose` (`beta_model.rs`) is what makes this possible at
/// all: `verified_whnf_beta_step`/`verified_whnf_zeta_step` both require
/// `nlbv`/`max_var_below`/`depth` facts about `e_fun`/`args`
/// *individually*, but this function's own precondition only gives those
/// facts about the WHOLE spine `e` -- `spine_app_decompose` is the
/// converse of `spine_app`'s own construction, carrying the whole-spine
/// facts down to the peeled head and each argument.
///
/// Also proves a growth bound on the result (`max_var_below`/`depth`
/// grow by at most a computable amount from the input's own `d`), via
/// `spine_reduce_bounds`/`spine_app_bounds` (`beta_model.rs`) at the beta
/// case -- the WITHIN-one-call half of what a fixpoint composing several
/// calls needs. `args.len()` is bounded by `d` itself (`spine_app_
/// decompose`'s own `args.len() <= depth(spine_app(...))` fact -- a real
/// structural truth, not a chosen restriction: an App-spine with `n`
/// arguments genuinely has depth at least `n`), so NO separate cap on how
/// many arguments one redex may apply is imposed -- the cost of that
/// generality is that the growth formula below is CUBIC in `d` (`spine_
/// reduce_bounds`'s quadratic-in-`args.len()` growth, itself scaled by
/// `args.len() <= d` once more), so `d` itself must stay modest (low
/// thousands, not tens of thousands) for the arithmetic to fit in
/// `0xFFFF_0000` -- a real, motivated numeric consequence of proving the
/// fully general (any `args.len()`) statement, not an arbitrary choice.
pub fn verified_whnf_no_unfolding_step<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    e: ExprPtr<'t>,
    fuel: u32,
    Ghost(bound): Ghost<nat>,
    Ghost(d): Ghost<nat>,
) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        d <= 60000,
        bound + d * d * d + d * d + d + 10 <= 0xFFFF_0000,
    ensures
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        match result {
            Some(r) => pstep_star(
                crate::expr_arena_bridge::EnvSpec::empty(),
                to_model(e),
                to_model(r),
            ) && nlbv(to_model(r)) <= 0 && max_var_below(to_model(r), bound + d * d * d + d * d)
                && depth(to_model(r)) <= d * d + 4 * d,
            None => true,
        },
{
    {
        let (e_fun, args) = ctx.unfold_apps(e);
        {
            let ghost args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
            proof {
                assert(to_model(e) == spine_app(to_model(e_fun), args_model));
                spine_app_decompose(to_model(e_fun), args_model, bound);
                assert forall|i: int| 0 <= i < args@.len() implies nlbv(to_model(args@[i])) <= 0
                    && max_var_below(to_model(args@[i]), bound) && depth(to_model(args@[i]))
                    <= d by {
                    assert(args_model[i] == to_model(args@[i]));
                }
                assert(args_model.len() <= depth(spine_app(to_model(e_fun), args_model)));
                assert(depth(spine_app(to_model(e_fun), args_model)) == depth(to_model(e)));
                assert(args_model.len() <= d);
            }
            let e_fun_el = ctx.read_expr(e_fun);
            if args.len() > 0 {
                if let Some(_) = expr_as_lambda(&e_fun_el) {
                    return match verified_whnf_beta_step(ctx, e_fun, &args, fuel, Ghost(bound)) {
                        Some(r) => {
                            proof {
                                assert(to_model(e) == spine_app(to_model(e_fun), args_model));
                                spine_app_decompose(to_model(e_fun), args_model, bound);
                                assert(args_model.len() <= depth(
                                    spine_app(to_model(e_fun), args_model),
                                ));
                                assert(depth(spine_app(to_model(e_fun), args_model)) == depth(
                                    to_model(e),
                                ));
                                assert(args_model.len() <= d);
                                assert(nlbv(to_model(e_fun)) <= 0);
                                assert(depth(to_model(e_fun)) <= d);
                                let ghost n = choose|n: nat|
                                    #![trigger spine_bind(to_model(e_fun), n)]
                                    n <= args.len() && spine_bind(to_model(e_fun), n) is Some
                                        && to_model(r) == spine_app(
                                        spine_reduce(
                                            to_model(e_fun),
                                            Seq::new(n, |i: int| to_model(args@[i])),
                                        ),
                                        Seq::new(
                                            (args@.len() - n) as nat,
                                            |i: int| to_model(args@[n as int + i]),
                                        ),
                                    );
                                assert(n <= args_model.len());
                                let ghost prefix = args_model.subrange(0, n as int);
                                let ghost suffix = args_model.subrange(
                                    n as int,
                                    args_model.len() as int,
                                );
                                assert(prefix.len() == n);
                                assert(suffix.len() == args_model.len() - n);
                                assert(prefix =~= Seq::new(n, |i: int| to_model(args@[i])));
                                assert(suffix =~= Seq::new(
                                    (args@.len() - n) as nat,
                                    |i: int| to_model(args@[n as int + i]),
                                ));
                                assert(to_model(r) == spine_app(
                                    spine_reduce(to_model(e_fun), prefix),
                                    suffix,
                                ));
                                assert forall|i: int| 0 <= i < prefix.len() implies nlbv(prefix[i])
                                    <= 0 && max_var_below(prefix[i], bound) && depth(prefix[i])
                                    <= d by {
                                    assert(prefix[i] == args_model[i]);
                                }
                                assert forall|i: int| 0 <= i < suffix.len() implies nlbv(suffix[i])
                                    <= 0 && max_var_below(suffix[i], bound) && depth(suffix[i])
                                    <= d by {
                                    assert(suffix[i] == args_model[n as int + i]);
                                }
                                assert(prefix.len() <= d) by (nonlinear_arith)
                                    requires
                                        prefix.len() == n,
                                        n <= args_model.len(),
                                        args_model.len() <= d,
                                {}
                                assert(suffix.len() <= d) by (nonlinear_arith)
                                    requires
                                        suffix.len() == args_model.len() - n,
                                        n <= args_model.len(),
                                        args_model.len() <= d,
                                {}
                                assert(bound + prefix.len() * d + prefix.len() * prefix.len() * d
                                    + prefix.len() + 1 <= 0xFFFF_0000) by (nonlinear_arith)
                                    requires
                                        prefix.len() <= d,
                                        bound + d * d * d + d * d + d + 10 <= 0xFFFF_0000,
                                {}
                                spine_reduce_bounds(to_model(e_fun), prefix, bound, d, d);
                                let ghost sr_bound = (bound + prefix.len() * d + prefix.len()
                                    * prefix.len() * d) as nat;
                                let ghost sr_depth = (d + d * (prefix.len() + 1)) as nat;
                                assert(max_var_below(
                                    spine_reduce(to_model(e_fun), prefix),
                                    sr_bound,
                                ));
                                assert(depth(spine_reduce(to_model(e_fun), prefix)) <= sr_depth);
                                assert(bound <= sr_bound) by (nonlinear_arith)
                                    requires
                                        sr_bound == bound + prefix.len() * d + prefix.len()
                                            * prefix.len() * d,
                                {}
                                assert forall|i: int| 0 <= i < suffix.len() implies max_var_below(
                                    suffix[i],
                                    sr_bound,
                                ) by {
                                    max_var_below_mono(suffix[i], bound, sr_bound);
                                }
                                spine_app_bounds(
                                    spine_reduce(to_model(e_fun), prefix),
                                    suffix,
                                    sr_bound,
                                    sr_depth,
                                    d,
                                );
                                assert(sr_bound <= bound + d * d * d + d * d) by (nonlinear_arith)
                                    requires
                                        prefix.len() <= d,
                                        sr_bound == bound + prefix.len() * d + prefix.len()
                                            * prefix.len() * d,
                                {}
                                max_var_below_mono(
                                    to_model(r),
                                    sr_bound,
                                    bound + d * d * d + d * d,
                                );
                                assert(sr_depth + d + suffix.len() <= d * d + 4 * d)
                                    by (nonlinear_arith)
                                    requires
                                        prefix.len() <= d,
                                        suffix.len() <= d,
                                        sr_depth == d + d * (prefix.len() + 1),
                                {}
                                assert(spine_bind(to_model(e_fun), n) is Some);
                                let ghost peeled_model = spine_bind(to_model(e_fun), n)->0;
                                assert(spine_bind(to_model(e_fun), n) == Some(peeled_model));
                                assert(nlbv(to_model(e_fun)) <= 0);
                                spine_bind_nlbv(to_model(e_fun), n, peeled_model, 0);
                                assert(nlbv(peeled_model) <= n);
                                subst_full_nlbv_bound_n(peeled_model, prefix, 0);
                                spine_reduce_eq_subst_full(
                                    to_model(e_fun),
                                    prefix,
                                    peeled_model,
                                    bound,
                                );
                                assert(spine_reduce(to_model(e_fun), prefix) == subst_full(
                                    peeled_model,
                                    prefix,
                                    0,
                                ));
                                assert(nlbv(spine_reduce(to_model(e_fun), prefix)) <= 0);
                                spine_app_nlbv(spine_reduce(to_model(e_fun), prefix), suffix);
                                assert(nlbv(to_model(r)) <= 0);
                            }
                            Some(r)
                        },
                        None => None,
                    };
                }
            }
            if let Some((_, _ty, val, body, _)) = expr_as_let(&e_fun_el) {
                assert(to_model(e_fun) == ExprSpec::Let(
                    Box::new(to_model(_ty)),
                    Box::new(to_model(val)),
                    Box::new(to_model(body)),
                ));
                return match verified_whnf_zeta_step(
                    ctx,
                    e_fun,
                    val,
                    body,
                    &args,
                    fuel,
                    Ghost(bound),
                ) {
                    Some(r) => {
                        proof {
                            assert(max_var_below(to_model(e_fun), bound));
                            assert(max_var_below(to_model(body), bound));
                            assert(max_var_below(to_model(val), bound));
                            assert(depth(to_model(body)) < depth(to_model(e_fun)));
                            assert(depth(to_model(body)) < d);
                            assert(nlbv(to_model(body)) <= 1);
                            assert(nlbv(to_model(val)) <= 0);
                            subst1_max_var_below(bound, to_model(body), to_model(val));
                            subst1_depth_bound(to_model(body), to_model(val));
                            let ghost new_bound = (bound + 1 + depth(to_model(body))) as nat;
                            let ghost new_hd = (depth(to_model(body)) + depth(
                                to_model(val),
                            )) as nat;
                            assert(max_var_below(subst1(to_model(body), to_model(val)), new_bound));
                            assert(depth(subst1(to_model(body), to_model(val))) <= new_hd);
                            assert(new_bound <= bound + d);
                            assert(new_hd <= 2 * d);
                            assert(to_model(e) == spine_app(to_model(e_fun), args_model));
                            spine_app_decompose(to_model(e_fun), args_model, bound);
                            assert(args_model.len() <= depth(
                                spine_app(to_model(e_fun), args_model),
                            ));
                            assert(depth(spine_app(to_model(e_fun), args_model)) == depth(
                                to_model(e),
                            ));
                            assert(args_model.len() <= d);
                            assert forall|i: int| 0 <= i < args_model.len() implies max_var_below(
                                args_model[i],
                                new_bound,
                            ) && depth(args_model[i]) <= d by {
                                max_var_below_mono(args_model[i], bound, new_bound);
                            }
                            spine_app_bounds(
                                subst1(to_model(body), to_model(val)),
                                args_model,
                                new_bound,
                                new_hd,
                                d,
                            );
                            assert(to_model(r) == spine_app(
                                subst1(to_model(body), to_model(val)),
                                args_model,
                            ));
                            assert(new_bound <= bound + d * d * d + d * d) by (nonlinear_arith)
                                requires
                                    new_bound <= bound + d,
                            {}
                            assert(new_hd + d + args_model.len() <= d * d + 4 * d)
                                by (nonlinear_arith)
                                requires
                                    new_hd <= 2 * d,
                                    args_model.len() <= d,
                            {}
                            max_var_below_mono(to_model(r), new_bound, bound + d * d * d + d * d);
                            subst_c_eq_subst_full(to_model(body), to_model(val), 0, bound);
                            assert(subst1(to_model(body), to_model(val)) == subst_c(
                                to_model(body),
                                to_model(val),
                                0,
                            ));
                            subst_full_nlbv_bound(to_model(body), to_model(val), 0);
                            assert(nlbv(subst_full(to_model(body), seq![to_model(val)], 0)) <= 0);
                            assert(nlbv(subst1(to_model(body), to_model(val))) <= 0);
                            spine_app_nlbv(subst1(to_model(body), to_model(val)), args_model);
                            assert(nlbv(to_model(r)) <= 0);
                        }
                        Some(r)
                    },
                    None => None,
                };
            }
            proof {
                pstep_star_refl(crate::expr_arena_bridge::EnvSpec::empty(), to_model(e));
                max_var_below_mono(to_model(e), bound, bound + d * d * d + d * d);
            }
            Some(e)
        }
    }
}

/// PLAIN (gate-free) beta/zeta step (2026-09-08): the same two primitives
/// as `verified_whnf_no_unfolding_step`, but the contract keeps only the
/// reduction claim and closedness -- no growth-bound bookkeeping, hence no
/// cubic ceiling on the input. Lets the measured whnf keep reducing terms
/// above its 1500 size gate (well-founded-recursion unfoldings, large
/// decidability instances), which was the largest remaining def_eq wall.
pub fn verified_whnf_no_unfolding_step_plain<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    e: ExprPtr<'t>,
    fuel: u32,
) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        depth(to_model(e)) <= 60000,
    ensures
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        match result {
            Some(r) => pstep_star(
                crate::expr_arena_bridge::EnvSpec::empty(),
                to_model(e),
                to_model(r),
            ) && nlbv(to_model(r)) <= 0,
            None => true,
        },
{
    let ghost bound: nat = 60000;
    proof {
        nlbv_bound_implies_max_var_below(to_model(e), 0);
        max_var_below_mono(to_model(e), (depth(to_model(e)) + 0) as nat, bound);
    }
    {
        let (e_fun, args) = ctx.unfold_apps(e);
        {
            let ghost args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
            proof {
                assert(to_model(e) == spine_app(to_model(e_fun), args_model));
                spine_app_decompose(to_model(e_fun), args_model, bound);
                assert forall|i: int| 0 <= i < args@.len() implies nlbv(to_model(args@[i])) <= 0
                    && max_var_below(to_model(args@[i]), bound) by {
                    assert(args_model[i] == to_model(args@[i]));
                }
            }
            let e_fun_el = ctx.read_expr(e_fun);
            if args.len() > 0 {
                if let Some(_) = expr_as_lambda(&e_fun_el) {
                    return match verified_whnf_beta_step(ctx, e_fun, &args, fuel, Ghost(bound)) {
                        Some(r) => {
                            proof {
                                assert(to_model(e) == spine_app(to_model(e_fun), args_model));
                                assert(nlbv(to_model(e_fun)) <= 0);
                                let ghost n = choose|n: nat|
                                    #![trigger spine_bind(to_model(e_fun), n)]
                                    n <= args.len() && spine_bind(to_model(e_fun), n) is Some
                                        && to_model(r) == spine_app(
                                        spine_reduce(
                                            to_model(e_fun),
                                            Seq::new(n, |i: int| to_model(args@[i])),
                                        ),
                                        Seq::new(
                                            (args@.len() - n) as nat,
                                            |i: int| to_model(args@[n as int + i]),
                                        ),
                                    );
                                assert(n <= args_model.len());
                                let ghost prefix = args_model.subrange(0, n as int);
                                let ghost suffix = args_model.subrange(
                                    n as int,
                                    args_model.len() as int,
                                );
                                assert(prefix =~= Seq::new(n, |i: int| to_model(args@[i])));
                                assert(suffix =~= Seq::new(
                                    (args@.len() - n) as nat,
                                    |i: int| to_model(args@[n as int + i]),
                                ));
                                assert(to_model(r) == spine_app(
                                    spine_reduce(to_model(e_fun), prefix),
                                    suffix,
                                ));
                                assert forall|i: int| 0 <= i < prefix.len() implies nlbv(prefix[i])
                                    <= 0 && max_var_below(prefix[i], bound) by {
                                    assert(prefix[i] == args_model[i]);
                                }
                                assert forall|i: int| 0 <= i < suffix.len() implies nlbv(suffix[i])
                                    <= 0 by {
                                    assert(suffix[i] == args_model[n as int + i]);
                                }
                                assert(spine_bind(to_model(e_fun), n) is Some);
                                let ghost peeled_model = spine_bind(to_model(e_fun), n)->0;
                                assert(spine_bind(to_model(e_fun), n) == Some(peeled_model));
                                spine_bind_nlbv(to_model(e_fun), n, peeled_model, 0);
                                assert(nlbv(peeled_model) <= n);
                                subst_full_nlbv_bound_n(peeled_model, prefix, 0);
                                spine_reduce_eq_subst_full(
                                    to_model(e_fun),
                                    prefix,
                                    peeled_model,
                                    bound,
                                );
                                assert(spine_reduce(to_model(e_fun), prefix) == subst_full(
                                    peeled_model,
                                    prefix,
                                    0,
                                ));
                                assert(nlbv(spine_reduce(to_model(e_fun), prefix)) <= 0);
                                spine_app_nlbv(spine_reduce(to_model(e_fun), prefix), suffix);
                                assert(nlbv(to_model(r)) <= 0);
                            }
                            Some(r)
                        },
                        None => None,
                    };
                }
            }
            if let Some((_, _ty, val, body, _)) = expr_as_let(&e_fun_el) {
                assert(to_model(e_fun) == ExprSpec::Let(
                    Box::new(to_model(_ty)),
                    Box::new(to_model(val)),
                    Box::new(to_model(body)),
                ));
                proof {
                    assert(nlbv(to_model(val)) <= 0);
                    assert(nlbv(to_model(body)) <= 1);
                    assert(depth(to_model(body)) < depth(to_model(e_fun)));
                    assert(max_var_below(to_model(val), bound));
                }
                return match verified_whnf_zeta_step(
                    ctx,
                    e_fun,
                    val,
                    body,
                    &args,
                    fuel,
                    Ghost(bound),
                ) {
                    Some(r) => {
                        proof {
                            assert(to_model(e) == spine_app(to_model(e_fun), args_model));
                            assert(to_model(r) == spine_app(
                                subst1(to_model(body), to_model(val)),
                                args_model,
                            ));
                            subst_c_eq_subst_full(to_model(body), to_model(val), 0, bound);
                            assert(subst1(to_model(body), to_model(val)) == subst_c(
                                to_model(body),
                                to_model(val),
                                0,
                            ));
                            subst_full_nlbv_bound(to_model(body), to_model(val), 0);
                            assert(nlbv(subst_full(to_model(body), seq![to_model(val)], 0)) <= 0);
                            assert(nlbv(subst1(to_model(body), to_model(val))) <= 0);
                            spine_app_nlbv(subst1(to_model(body), to_model(val)), args_model);
                            assert(nlbv(to_model(r)) <= 0);
                        }
                        Some(r)
                    },
                    None => None,
                };
            }
            proof {
                pstep_star_refl(crate::expr_arena_bridge::EnvSpec::empty(), to_model(e));
            }
            Some(e)
        }
    }
}

} // verus!
