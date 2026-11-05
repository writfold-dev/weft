#![forbid(unsafe_code)]

pub mod diagnostic;
pub mod document;
pub mod evaluation;
pub mod ids;
pub mod limits;
pub mod theory;
pub mod value;

pub use crate::document::*;
pub use crate::evaluation::*;
pub use crate::ids::*;
pub use crate::theory::*;
pub use diagnostic::{Code, Diagnostic, Label, Phase};
pub use limits::{LimitKind, Limits, WorkUsage};
pub use value::{IdentityValue, Natural, Scalar, ScalarType};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InvariantError {
    InvalidSpan,
    InvalidNatural,
    EmptyIdentityComponent,
    InvalidReference(&'static str),
    DuplicateName(String),
    MixedSetTypes,
    Limit(LimitKind),
}

impl std::fmt::Display for InvariantError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for InvariantError {}
