//! Classification of one complete finite trace. Each row records whether the
//! check's premises hold under one valuation and the query's value there; the
//! verdict is the calculus's `verdictOf` over the two polarity flags
//! (`formal/Weft/Logic/Classification.lean`). Proved in
//! `proofs/Kernel/Verdict.lean`.
//!
//! That the rows are exactly every valuation of the active atoms is the
//! evaluator's (`weft_kernel`) obligation, exercised by tests and the
//! Lean/Rust differential, not by these theorems.

/// One evaluated valuation.
pub struct TraceRow {
    pub valuation: u64,
    pub premises_hold: bool,
    pub query: bool,
}

/// What one row contributes: a model of the premises where the query holds,
/// one where it fails, or nothing (the premises fail there).
pub enum RowRole {
    Supporting,
    Refuting,
    Excluded,
}

pub enum LogicalVerdict {
    Entailed,
    Refuted,
    Undetermined,
    InconsistentPremises,
}

/// The role of one row.
pub fn role(row: &TraceRow) -> RowRole {
    if !row.premises_hold {
        RowRole::Excluded
    } else if row.query {
        RowRole::Supporting
    } else {
        RowRole::Refuting
    }
}

/// The calculus's `verdictOf`: positive and negative polarity flags.
pub fn verdict_of(supporting: bool, refuting: bool) -> LogicalVerdict {
    if supporting {
        if refuting {
            LogicalVerdict::Undetermined
        } else {
            LogicalVerdict::Entailed
        }
    } else if refuting {
        LogicalVerdict::Refuted
    } else {
        LogicalVerdict::InconsistentPremises
    }
}

/// Classifies a complete trace.
pub fn classify(rows: &[TraceRow]) -> LogicalVerdict {
    let mut supporting = false;
    let mut refuting = false;
    let mut i = 0;
    while i < rows.len() {
        match role(&rows[i]) {
            RowRole::Supporting => supporting = true,
            RowRole::Refuting => refuting = true,
            RowRole::Excluded => {}
        }
        i += 1;
    }
    verdict_of(supporting, refuting)
}
