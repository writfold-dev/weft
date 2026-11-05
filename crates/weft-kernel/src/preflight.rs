use weft_domain::{IncompleteEvaluation, LimitKind, Limits, PreparedCheck, ValuationCount};

pub(crate) fn preflight(
    check: &PreparedCheck,
    limits: &Limits,
) -> Result<u64, IncompleteEvaluation> {
    cardinalities(
        check.atoms().len(),
        check.nodes().len(),
        check.premises().len(),
        limits,
    )
}

pub(crate) fn cardinalities(
    atoms: usize,
    nodes: usize,
    premises: usize,
    limits: &Limits,
) -> Result<u64, IncompleteEvaluation> {
    let count = u32::try_from(atoms)
        .ok()
        .and_then(|bits| 1_u64.checked_shl(bits));
    let required = match count {
        Some(count) => ValuationCount::Exact(count),
        None => ValuationCount::BeyondU64 { atoms },
    };
    let failure = |limit, admitted| IncompleteEvaluation {
        limit,
        required,
        admitted,
        checked_valuations: 0,
    };
    if atoms > limits.atoms {
        return Err(failure(LimitKind::Atoms, bounded(limits.atoms)));
    }
    if nodes > limits.nodes {
        return Err(failure(LimitKind::Nodes, bounded(limits.nodes)));
    }
    let count = count.ok_or_else(|| failure(LimitKind::Valuations, limits.valuations))?;
    if count > limits.valuations {
        return Err(failure(LimitKind::Valuations, limits.valuations));
    }
    let steps = nodes
        .checked_add(premises)
        .and_then(|visits| u64::try_from(visits).ok())
        .and_then(|visits| visits.checked_mul(count));
    if !matches!(steps, Some(steps) if steps <= limits.evaluation_steps) {
        return Err(failure(LimitKind::EvaluationSteps, limits.evaluation_steps));
    }
    if !matches!(usize::try_from(count), Ok(rows) if rows <= limits.trace_rows) {
        return Err(failure(LimitKind::TraceRows, bounded(limits.trace_rows)));
    }
    if usize::try_from(count)
        .ok()
        .and_then(|rows| premise_words(rows, premises))
        .is_none()
    {
        return Err(failure(LimitKind::TraceRows, bounded(limits.trace_rows)));
    }
    Ok(count)
}

pub(crate) fn premise_words(rows: usize, premises: usize) -> Option<usize> {
    let bits = rows.checked_mul(premises)?;
    let words = (bits / 64).checked_add(usize::from(bits % 64 != 0))?;
    let bytes = words.checked_mul(size_of::<u64>())?;
    isize::try_from(bytes).ok()?;
    Some(words)
}

fn bounded(value: usize) -> u64 {
    u64::try_from(value).unwrap_or(u64::MAX)
}
