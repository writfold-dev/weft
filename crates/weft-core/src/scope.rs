//! The decision behind `weft reuse`: a prior report's recorded scope is
//! reusable only if every comparison is satisfied, byte for byte. The wire
//! layer builds one comparison per scope field (source digest, profile,
//! report kind, each evaluation bound) and names a difference for every
//! position returned by [`refusals`]. Proved in `proofs/Kernel/Scope.lean`.
use alloc::vec::Vec;

/// How a recorded value must relate to the required one.
pub enum Requirement {
    /// Byte-identical (source digest, profile, bounds).
    Equal,
    /// Anything but the required bytes (a diagnostics-only report kind).
    Unequal,
}

pub struct Comparison {
    pub requirement: Requirement,
    pub recorded: Vec<u8>,
    pub required: Vec<u8>,
}

/// Byte-exact equality, length included.
pub fn same_bytes(left: &[u8], right: &[u8]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut i = 0;
    while i < left.len() {
        if left[i] != right[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// Whether one comparison holds.
pub fn satisfied(comparison: &Comparison) -> bool {
    // Deref coercion, not `as_slice()` (an axiom in the Aeneas library).
    let equal = same_bytes(&comparison.recorded, &comparison.required);
    match comparison.requirement {
        Requirement::Equal => equal,
        Requirement::Unequal => !equal,
    }
}

/// The positions of every unsatisfied comparison, ascending. Reuse is
/// admitted only when this is empty.
pub fn refusals(comparisons: &[Comparison]) -> Vec<usize> {
    let mut refused = Vec::new();
    let mut i = 0;
    while i < comparisons.len() {
        if !satisfied(&comparisons[i]) {
            refused.push(i);
        }
        i += 1;
    }
    refused
}
