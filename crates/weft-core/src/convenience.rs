//! Trait impls the decision modules would otherwise derive. Charon translates
//! every impl in a module it starts from, derived or not, so the decision
//! modules carry no `#[derive]`; these impls live here, unreached by the
//! translation (`[package.metadata.charon] start_from` in Cargo.toml).
//! Formatting matches what `#[derive(Debug)]` printed before the move.
use crate::scope::{Comparison, Requirement};
use crate::verdict::{LogicalVerdict, RowRole, TraceRow};
use core::fmt;

impl Clone for TraceRow {
    fn clone(&self) -> Self {
        *self
    }
}
impl Copy for TraceRow {}
impl fmt::Debug for TraceRow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TraceRow")
            .field("valuation", &self.valuation)
            .field("premises_hold", &self.premises_hold)
            .field("query", &self.query)
            .finish()
    }
}

macro_rules! fieldless {
    ($ty:ident { $($variant:ident),+ }) => {
        impl Clone for $ty {
            fn clone(&self) -> Self {
                *self
            }
        }
        impl Copy for $ty {}
        impl PartialEq for $ty {
            fn eq(&self, other: &Self) -> bool {
                matches!((self, other), $((Self::$variant, Self::$variant))|+)
            }
        }
        impl Eq for $ty {}
        impl fmt::Debug for $ty {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(match self {
                    $(Self::$variant => stringify!($variant),)+
                })
            }
        }
    };
}

fieldless!(LogicalVerdict {
    Entailed,
    Refuted,
    Undetermined,
    InconsistentPremises
});
fieldless!(RowRole {
    Supporting,
    Refuting,
    Excluded
});
fieldless!(Requirement { Equal, Unequal });

impl Clone for Comparison {
    fn clone(&self) -> Self {
        Self {
            requirement: self.requirement,
            recorded: self.recorded.clone(),
            required: self.required.clone(),
        }
    }
}
impl fmt::Debug for Comparison {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Comparison")
            .field("requirement", &self.requirement)
            .field("recorded", &self.recorded)
            .field("required", &self.required)
            .finish()
    }
}
