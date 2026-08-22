//! Placeholder:
//! ```ignore
//! Doc comment example
//! ```
#![allow(clippy::too_many_arguments)]
#![deny(clippy::cast_possible_truncation)]

#[allow(unused_imports)]
use vstd::prelude::*;

pub mod debug_printer;
pub mod env;
pub mod env_model;
pub mod expr;
pub mod expr_arena_bridge;
pub mod expr_model;
pub mod inductive;
pub mod level;
pub mod level_arena_bridge;
pub mod level_model;
pub mod name;
pub mod name_model;
pub mod parser;
pub mod pretty_printer;
pub mod quot;
pub mod tc;
pub mod union_find_model;
#[cfg(test)]
mod tests;
pub mod unique_hasher;
pub mod util;
pub mod util_model;

pub(crate) const STACK_SIZE: usize = 16_777_216;
