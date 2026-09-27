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
pub mod env_model;
pub mod env_weaken;
pub mod expr;
pub mod expr_arena_bridge;
pub mod export_sound;
pub mod expr_model;
pub mod inductive;
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
pub mod nat_lit_model;
pub mod parser;
pub mod proj_reg;
pub mod pretty_printer;
pub mod quot;
pub mod quot_model;
pub mod rctx;
pub mod real_gen;
pub mod reduce_fv;
pub mod replace;
pub mod regularity;
pub mod subst_model;
pub mod subst_conv;
pub mod subst_typed;
pub mod swap_model;
pub mod swap_typed;
pub mod tc;
pub mod tc_model;
pub mod telescope;
#[cfg(test)]
mod tests;
pub mod unique_hasher;
pub mod util;
pub mod util_model;
pub mod weaken;

pub(crate) const STACK_SIZE: usize = 16_777_216;
