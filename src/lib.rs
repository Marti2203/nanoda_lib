//! Placeholder:
//! ```ignore
//! Doc comment example
//! ```
#![allow(clippy::too_many_arguments)]
#![deny(clippy::cast_possible_truncation)]

#[allow(unused_imports)]
use vstd::prelude::*;

pub mod debug_printer;
pub mod delta_bound_model;
pub mod env;
pub mod env_model;
pub mod beta_model;
pub mod beta_model_z;
pub mod expr;
pub mod expr_arena_bridge;
pub mod expr_model;
pub mod inductive;
pub mod inductive_model;
pub mod level;
pub mod level_arena_bridge;
pub mod level_model;
pub mod name;
pub mod name_arena_bridge;
pub mod name_model;
pub mod nat_lit_model;
pub mod parser;
pub mod parser_model;
pub mod pretty_printer;
pub mod quot;
pub mod quot_model;
pub mod tc;
pub mod tc_model;
pub mod union_find_model;
#[cfg(test)]
mod tests;
pub mod unique_hasher;
pub mod util;
pub mod util_model;

pub(crate) const STACK_SIZE: usize = 16_777_216;
