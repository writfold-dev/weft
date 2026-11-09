#![forbid(unsafe_code)]

mod preflight;
mod replay;
mod trace;
use replay::Replay;

use weft_domain::{
    Assessment, CheckOutcome, CheckState, Code, Compilation, CompleteEvaluation, Conclusion,
    Diagnostic, Limits, Model, NodeValue, Phase, PreparedCheck, RowRole, Theory, TraceRow,
};

/// Classifies each check independently over its exact preceding premises and active atoms.
pub fn assess(compilation: &Compilation, limits: &Limits) -> Result<Assessment, Diagnostic> {
    let mut checks = reserve(compilation.checks.len())?;
    for check in &compilation.checks {
        let conclusion = match &check.state {
            CheckState::Blocked(_) => Conclusion::Blocked,
            CheckState::Ready(prepared) => match preflight::preflight(prepared, limits) {
                Ok(count) => Conclusion::Complete(enumerate(&compilation.theory, prepared, count)?),
                Err(failure) => Conclusion::Incomplete(failure),
            },
        };
        checks.push(CheckOutcome {
            check: check.id,
            conclusion,
        });
    }
    Ok(Assessment { checks })
}

fn enumerate(
    theory: &Theory,
    check: &PreparedCheck,
    count: u64,
) -> Result<CompleteEvaluation, Diagnostic> {
    let mut replay = Replay::prepared(theory, check, count)?;
    let query = replay::position(check, check.query())?;
    let mut premises = reserve(check.premises().len())?;
    for root in check.premises() {
        premises.push(replay::position(check, *root)?);
    }
    let row_count =
        usize::try_from(count).map_err(|_| invalid("Preflight row count is not representable"))?;
    let mut rows = reserve(row_count)?;
    let premise_count = premises.len();
    let words = preflight::premise_words(row_count, premise_count)
        .ok_or_else(|| invalid("Preflight premise trace size is not representable"))?;
    let mut premise_truth_words = reserve(words)?;
    premise_truth_words.resize(words, 0);
    let mut supporting = None;
    let mut refuting = None;
    let mut premise_models = 0_u64;
    for valuation in 0..count {
        let values = replay.evaluate(valuation)?;
        let premises_hold =
            trace::record_premises(values, &premises, rows.len(), &mut premise_truth_words)?;
        let query = replay::at(values, query)?;
        rows.push(TraceRow {
            valuation,
            premises_hold,
            query,
        });
        let row = rows.last().ok_or_else(|| invalid("Missing trace row"))?;
        let model = match weft_core::verdict::role(row) {
            RowRole::Excluded => continue,
            RowRole::Supporting => &mut supporting,
            RowRole::Refuting => &mut refuting,
        };
        premise_models = premise_models
            .checked_add(1)
            .ok_or_else(|| invalid("Premise model count overflow"))?;
        if model.is_none() {
            *model = Some(capture(valuation, values)?);
        }
    }
    // The verdict is decided by the proved core over the complete trace
    // (proofs/Kernel/Verdict.lean); the captured models are its witnesses.
    let verdict = weft_core::verdict::classify(&rows);
    Ok(CompleteEvaluation {
        verdict,
        required_valuations: count,
        checked_valuations: count,
        premise_models,
        rows,
        premise_count,
        premise_truth_words,
        supporting,
        refuting,
    })
}

fn capture(valuation: u64, values: &[NodeValue]) -> Result<Model, Diagnostic> {
    let mut retained = reserve(values.len())?;
    retained.extend_from_slice(values);
    Ok(Model {
        valuation,
        values: retained,
    })
}

fn invalid(message: &'static str) -> Diagnostic {
    Diagnostic::new(Code::InvalidProgram, Phase::Evaluate, message, None)
}

fn reserve<T>(capacity: usize) -> Result<Vec<T>, Diagnostic> {
    let mut values = Vec::new();
    values.try_reserve_exact(capacity).map_err(|_| {
        Diagnostic::new(
            Code::LimitExceeded,
            Phase::Evaluate,
            "Evaluation buffer cannot be allocated",
            None,
        )
    })?;
    Ok(values)
}

#[cfg(test)]
mod tests;
