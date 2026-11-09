#![forbid(unsafe_code)]
//! Behavioral examples; the guarantees themselves are the Lean theorems in
//! proofs/Kernel/ over the translation of this crate.

use weft_core::scope::{Comparison, Requirement, refusals, same_bytes};
use weft_core::sets::{
    contains, difference, intersection, normalize, position_of, same_members, subset, union,
};
use weft_core::verdict::{LogicalVerdict, TraceRow, classify};

#[test]
fn set_algebra_keeps_first_occurrence_order() {
    assert_eq!(normalize(&[3, 1, 3, 2, 1]), [3, 1, 2]);
    assert_eq!(union(&[3, 1], &[2, 1, 4]), [3, 1, 2, 4]);
    assert_eq!(intersection(&[3, 1, 2], &[2, 3]), [3, 2]);
    assert_eq!(difference(&[3, 1, 2], &[2, 3]), [1]);
    assert_eq!(position_of(&[5, 6, 6], 6), Some(1));
    assert!(contains(&[5, 6], 6) && !contains(&[], 6));
    assert_eq!(subset(&[1, 2], &[2, 1, 3]), None);
    assert_eq!(subset(&[1, 4, 5], &[1]), Some(1));
    assert!(same_members(&[1, 2], &[2, 1]) && !same_members(&[1], &[1, 2]));
}

fn rows(cells: &[(bool, bool)]) -> Vec<TraceRow> {
    cells
        .iter()
        .zip(0_u64..)
        .map(|(&(premises_hold, query), valuation)| TraceRow {
            valuation,
            premises_hold,
            query,
        })
        .collect()
}

#[test]
fn classification_follows_both_polarities() {
    use LogicalVerdict::{Entailed, InconsistentPremises, Refuted, Undetermined};
    assert_eq!(classify(&rows(&[(true, true), (false, false)])), Entailed);
    assert_eq!(classify(&rows(&[(true, false), (false, true)])), Refuted);
    assert_eq!(
        classify(&rows(&[(true, true), (true, false)])),
        Undetermined
    );
    assert_eq!(classify(&rows(&[(false, true)])), InconsistentPremises);
    assert_eq!(classify(&[]), InconsistentPremises);
    assert_eq!(format!("{Entailed:?}"), "Entailed");
}

#[test]
fn reuse_refuses_every_unsatisfied_comparison() {
    let compare = |requirement, recorded: &str, required: &str| Comparison {
        requirement,
        recorded: recorded.as_bytes().to_vec(),
        required: required.as_bytes().to_vec(),
    };
    assert!(
        same_bytes(b"abc", b"abc") && !same_bytes(b"abc", b"ab") && !same_bytes(b"abd", b"abc")
    );
    let comparisons = [
        compare(Requirement::Equal, "abc", "abc"),
        compare(Requirement::Equal, "abc", "abd"),
        compare(Requirement::Unequal, "assessment", "diagnostics"),
        compare(Requirement::Unequal, "diagnostics", "diagnostics"),
    ];
    assert_eq!(refusals(&comparisons), [1, 3]);
    assert!(refusals(&comparisons[..1]).is_empty());
}
