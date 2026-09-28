//! Placeholder:
//! ```ignore
//! Doc comment example
//! ```
#![allow(clippy::too_many_arguments)]
#![deny(clippy::cast_possible_truncation)]

#[allow(unused_imports)]
use vstd::prelude::*;

pub mod arena_history;
pub mod beta_model;
pub mod ctor_typing;
pub mod debug_printer;
pub mod env;
pub mod dom_adeq;
pub mod dom_adeq_base;
pub mod dom_adeq_syn;
pub mod dom_compact;
pub mod dom_con_rel;
pub mod dom_fund;
pub mod dom_model;
pub mod dom_proj;
pub mod dom_rec;
pub mod dom_rel;
pub mod dom_rel_hexp;
pub mod dom_rel_mono;
pub mod dom_rel_per;
pub mod dom_rel_stab;
pub mod dom_sem;
pub mod dom_sem_rel;
pub mod dom_sound;
pub mod dom_typing;
pub mod hyps_refuted;
pub mod dom_untyped;
pub mod e2_lift;
pub mod env_model;
pub mod confluence;
pub mod conv_cr;
pub mod conv_frag;
pub mod fclose;
pub mod env_weaken;
pub mod expr;
pub mod expr_arena_bridge;
pub mod export_sound;
pub mod export_builder;
pub mod expr_model;
pub mod injectivity;
pub mod inductive;
pub mod jkernel;
pub mod rec_canon;
pub mod ti_locals;
pub mod kbind;
pub mod ti_zsize;
pub mod ti_level;
pub mod kclaims;
pub mod inductive_model;
pub mod indexmap_model;
pub mod level;
pub mod level_arena_bridge;
pub mod level_inst;
pub mod level_model;
pub mod level_typed;
pub mod metatheory;
pub mod name;
pub mod name_arena_bridge;
pub mod name_model;
pub mod nat_ext;
pub mod nat_lit_model;
pub mod parser;
pub mod proj_reg;
pub mod pretty_printer;
pub mod quot;
pub mod quot_model;
pub mod rctx;
pub mod real_gen;
pub mod reduce_fv;
pub mod regularity;
pub mod subst_algebra;
pub mod subst_model;
pub mod subst_conv;
pub mod subst_typed;
pub mod swap_model;
pub mod swap_typed;
pub mod tc;
pub mod tc_model;
pub mod ti_chain;
pub mod ti_gen;
pub mod ti_scope;
pub mod ti_sr;
pub mod ti_hred;
pub mod ti_meta;
pub mod ti_sub;
pub mod ti_subst;
pub mod ti_syntax;
pub mod ti_valid;
pub mod telescope;
#[cfg(test)]
mod tests;
pub mod unique_hasher;
pub mod util;
pub mod util_model;
pub mod weaken;

pub(crate) const STACK_SIZE: usize = 16_777_216;
