//! Finite set algebra over value identities (`usize`): the decision half of
//! `weft_domain`'s set operations. The domain owns typing, budget charging
//! and origin bookkeeping; every membership and order decision is made here.
//!
//! Results keep deterministic first-occurrence order: normalization and union
//! keep the first occurrence of each value (left before right); intersection
//! and difference keep qualifying left order. Proved in `proofs/Kernel/Sets.lean`.
use alloc::vec::Vec;

/// The first position holding `value`, if any.
pub fn position_of(values: &[usize], value: usize) -> Option<usize> {
    let mut i = 0;
    while i < values.len() {
        if values[i] == value {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Membership.
pub fn contains(values: &[usize], value: usize) -> bool {
    position_of(values, value).is_some()
}

/// Appends each value of `raw`, in order, that `members` does not yet hold.
pub fn extend_unique(members: Vec<usize>, raw: &[usize]) -> Vec<usize> {
    let mut extended = members;
    let mut i = 0;
    while i < raw.len() {
        // `&extended` (Deref), not `as_slice()`: Aeneas models `Vec::deref`
        // but translates `Vec::as_slice` to an axiom.
        if !contains(&extended, raw[i]) {
            extended.push(raw[i]);
        }
        i += 1;
    }
    extended
}

/// Normalization: the distinct values of `raw` in first-occurrence order.
pub fn normalize(raw: &[usize]) -> Vec<usize> {
    extend_unique(Vec::new(), raw)
}

/// Union: the left operand's values, then the right's unseen values.
pub fn union(left: &[usize], right: &[usize]) -> Vec<usize> {
    extend_unique(normalize(left), right)
}

/// The left values whose membership in `right` equals `present`, in left order.
fn select(left: &[usize], right: &[usize], present: bool) -> Vec<usize> {
    let mut kept = Vec::new();
    let mut i = 0;
    while i < left.len() {
        if contains(right, left[i]) == present {
            kept.push(left[i]);
        }
        i += 1;
    }
    kept
}

/// Intersection: the left values also in `right`, in left order.
pub fn intersection(left: &[usize], right: &[usize]) -> Vec<usize> {
    select(left, right, true)
}

/// Left difference: the left values not in `right`, in left order.
pub fn difference(left: &[usize], right: &[usize]) -> Vec<usize> {
    select(left, right, false)
}

/// Inclusive subset: `None` when every left value is in `right`, otherwise
/// the first left position whose value is not (the counterexample).
pub fn subset(left: &[usize], right: &[usize]) -> Option<usize> {
    let mut i = 0;
    while i < left.len() {
        if !contains(right, left[i]) {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Extensional equality: each side is a subset of the other.
pub fn same_members(left: &[usize], right: &[usize]) -> bool {
    subset(left, right).is_none() && subset(right, left).is_none()
}
