//! Exploratory Verus model addressing a duplication risk found while
//! auditing `parser.rs`: it has its own independent implementation of the
//! `num_loose_bvars`/`has_fvars` cache-combining formulas for
//! `App`/`Lambda`/`Pi`/`Let`/`Proj` (in `go1`, computed inline before each
//! `self.dag.exprs.insert_full(...)` call), rather than calling
//! `TcCtx::mk_app`/`mk_pi`/`mk_lambda`/`mk_let`/`mk_proj` (`util.rs`) the
//! way the rest of the type checker does. That's exactly the kind of place
//! a future edit to one side and not the other could silently corrupt the
//! cached fields `inst_aux`/`abstr_aux`'s short-circuits (and
//! `expr_arena_bridge.rs`'s trust axioms) depend on, for every expression
//! loaded from an export file.
//!
//! Manual line-by-line audit found the two formulas identical today:
//!   - `App`: `parser.rs:670-671` vs. `util.rs:525-526`
//!   - `Lambda`: `parser.rs:689-690` vs. `util.rs:538-539`
//!   - `Pi`: `parser.rs:709-710` vs. `util.rs:551-552`
//!   - `Let`: `parser.rs:730-733` vs. `util.rs:565-568`
//!   - `Proj`: `parser.rs:752-753` vs. `util.rs:574-575` (see `mk_proj`)
//!
//! This file proves the *formula itself* -- transcribed from those exact
//! locations -- correctly implements `expr_model.rs`'s `nlbv`/`has_fv`
//! (which `expr_arena_bridge.rs` already establishes is what `mk_app`/etc.
//! compute). It does not touch `parser.rs` or `util.rs`: unlike
//! `util_model.rs`'s `Ptr::raw()` accessor, there was no way to attach a
//! `assume_specification` directly to `go1`'s private inline logic without
//! a much larger refactor, so what's checked here is conditional on the
//! transcription above staying accurate -- a real, if weaker, guarantee
//! than a wired-in proof: it still catches a *formula* bug (get the
//! combining logic itself wrong), just not a copy-paste drift where the
//! transcription and the real source silently diverge without this file
//! being updated to match.

use vstd::prelude::*;
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[cfg(verus_only)]
use crate::expr_model::{nlbv, has_fv};

verus! {

/// `App`'s combining formula (`nb_fun.max(nb_arg)`, `fv_fun || fv_arg`),
/// given children whose cached `u16`/`bool` values already correctly
/// represent `nlbv`/`has_fv` (as `TcCtx::num_loose_bvars`/`has_fvars`'s
/// trust chain in `expr_arena_bridge.rs` establishes for any real
/// `ExprPtr`), and whose `nlbv` values fit in `u16` (matching the real
/// field's type -- the combining arithmetic can't itself overflow past
/// that, since `u16::max` of two in-range values stays in range).
pub proof fn app_fields_correct(model_fun: ExprSpec, model_arg: ExprSpec, nb_fun: u16, nb_arg: u16, fv_fun: bool, fv_arg: bool)
    requires
        nb_fun as nat == nlbv(model_fun),
        nb_arg as nat == nlbv(model_arg),
        fv_fun == has_fv(model_fun),
        fv_arg == has_fv(model_arg),
        nlbv(model_fun) < 0x1_0000,
        nlbv(model_arg) < 0x1_0000,
    ensures ({
        let e = ExprSpec::App(Box::new(model_fun), Box::new(model_arg));
        &&& (if nb_fun >= nb_arg { nb_fun } else { nb_arg }) as nat == nlbv(e)
        &&& (fv_fun || fv_arg) == has_fv(e)
    })
{
}

/// `Lambda`/`Pi`'s shared combining formula (`nb_ty.max(nb_body.
/// saturating_sub(1))`, `fv_ty || fv_body`) -- both real functions
/// construct `ExprSpec::Bind` in the model (see `expr_model.rs`'s doc
/// comment on why `Lambda`/`Pi` collapse to one variant there).
pub proof fn bind_fields_correct(model_ty: ExprSpec, model_body: ExprSpec, nb_ty: u16, nb_body: u16, fv_ty: bool, fv_body: bool)
    requires
        nb_ty as nat == nlbv(model_ty),
        nb_body as nat == nlbv(model_body),
        fv_ty == has_fv(model_ty),
        fv_body == has_fv(model_body),
        nlbv(model_ty) < 0x1_0000,
        nlbv(model_body) < 0x1_0000,
    ensures ({
        let e = ExprSpec::Bind(Box::new(model_ty), Box::new(model_body));
        let bb: u16 = if nb_body == 0 { 0 } else { (nb_body - 1) as u16 };
        &&& (if nb_ty >= bb { nb_ty } else { bb }) as nat == nlbv(e)
        &&& (fv_ty || fv_body) == has_fv(e)
    })
{
}

/// `Let`'s combining formula (`nb_ty.max(nb_val.max(nb_body.
/// saturating_sub(1)))`, three-way `||`).
pub proof fn let_fields_correct(
    model_ty: ExprSpec, model_val: ExprSpec, model_body: ExprSpec,
    nb_ty: u16, nb_val: u16, nb_body: u16, fv_ty: bool, fv_val: bool, fv_body: bool,
)
    requires
        nb_ty as nat == nlbv(model_ty),
        nb_val as nat == nlbv(model_val),
        nb_body as nat == nlbv(model_body),
        fv_ty == has_fv(model_ty),
        fv_val == has_fv(model_val),
        fv_body == has_fv(model_body),
        nlbv(model_ty) < 0x1_0000,
        nlbv(model_val) < 0x1_0000,
        nlbv(model_body) < 0x1_0000,
    ensures ({
        let e = ExprSpec::Let(Box::new(model_ty), Box::new(model_val), Box::new(model_body));
        let bb: u16 = if nb_body == 0 { 0 } else { (nb_body - 1) as u16 };
        let val_bb: u16 = if nb_val >= bb { nb_val } else { bb };
        &&& (if nb_ty >= val_bb { nb_ty } else { val_bb }) as nat == nlbv(e)
        &&& (fv_ty || fv_val || fv_body) == has_fv(e)
    })
{
}

/// `Proj`'s combining formula: just passes the single child's fields
/// through unchanged.
pub proof fn proj_fields_correct(model_structure: ExprSpec, nb_structure: u16, fv_structure: bool)
    requires
        nb_structure as nat == nlbv(model_structure),
        fv_structure == has_fv(model_structure),
    ensures ({
        let e = ExprSpec::Proj(Box::new(model_structure));
        &&& nb_structure as nat == nlbv(e)
        &&& fv_structure == has_fv(e)
    })
{
}

}
