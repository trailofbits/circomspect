pub mod declarations;
pub mod errors;
pub mod type_meta;
pub mod value_meta;
pub mod variable_meta;

mod expression_impl;
mod ir;
mod statement_impl;
pub mod lifting;

pub use ir::*;
