use super::*;
use crate::preflight::cardinalities;

#[test]
fn every_limit_refuses_before_checking_any_valuation() -> TestResult {
    let mut f = Fixture::new()?;
    let atom = f.atom("p")?;
    let negated = f.node(FormulaOp::Not(atom))?;
    f.check(negated, &[])?;
    let compilation = f.finish()?;
    let exact = Limits {
        atoms: 1,
        nodes: 2,
        valuations: 2,
        evaluation_steps: 4,
        trace_rows: 2,
        ..Limits::default()
    };
    let full = assess(&compilation, &exact).map_err(error)?;
    assert_eq!(complete(&full, 0)?.checked_valuations, 2);
    for kind in [
        LimitKind::Atoms,
        LimitKind::Nodes,
        LimitKind::Valuations,
        LimitKind::EvaluationSteps,
        LimitKind::TraceRows,
    ] {
        let mut limited = exact.clone();
        match kind {
            LimitKind::Atoms => limited.atoms = 0,
            LimitKind::Nodes => limited.nodes = 1,
            LimitKind::Valuations => limited.valuations = 1,
            LimitKind::EvaluationSteps => limited.evaluation_steps = 3,
            LimitKind::TraceRows => limited.trace_rows = 1,
            _ => return Err("Unexpected test limit".into()),
        }
        let result = assess(&compilation, &limited).map_err(error)?;
        let failure = match &result.checks.first().ok_or("Missing outcome")?.conclusion {
            Conclusion::Incomplete(failure) => failure,
            other => return Err(format!("Expected incomplete, got {other:?}")),
        };
        assert_eq!(failure.limit, kind);
        assert_eq!(failure.required, ValuationCount::Exact(2));
        assert_eq!(failure.checked_valuations, 0);
    }
    Ok(())
}

#[test]
fn zero_budget_does_not_refute_even_a_literal() -> TestResult {
    let mut f = Fixture::new()?;
    let yes = f.node(FormulaOp::Literal(true))?;
    f.check(yes, &[])?;
    let limits = Limits {
        valuations: 0,
        ..Limits::default()
    };
    let result = assess(&f.finish()?, &limits).map_err(error)?;
    match &result.checks.first().ok_or("Missing outcome")?.conclusion {
        Conclusion::Incomplete(failure) => {
            assert_eq!(failure.required, ValuationCount::Exact(1));
            assert_eq!(failure.checked_valuations, 0);
            assert_eq!(failure.admitted, 0);
        }
        other => return Err(format!("Expected incomplete, got {other:?}")),
    }
    Ok(())
}

#[test]
fn cardinality_and_step_overflow_never_wrap() -> TestResult {
    let limits = Limits {
        atoms: usize::MAX,
        nodes: usize::MAX,
        valuations: u64::MAX,
        evaluation_steps: u64::MAX,
        trace_rows: usize::MAX,
        ..Limits::default()
    };
    for atoms in [64, 65, usize::MAX] {
        let failure = cardinalities(atoms, 1, 0, &limits)
            .err()
            .ok_or("Expected cardinality overflow")?;
        assert_eq!(failure.required, ValuationCount::BeyondU64 { atoms });
        assert_eq!(failure.limit, LimitKind::Valuations);
        assert_eq!(failure.checked_valuations, 0);
    }
    let failure = cardinalities(63, 2, 0, &limits)
        .err()
        .ok_or("Expected step overflow")?;
    assert_eq!(failure.required, ValuationCount::Exact(1_u64 << 63));
    assert_eq!(failure.limit, LimitKind::EvaluationSteps);
    assert_eq!(failure.checked_valuations, 0);
    assert_eq!(cardinalities(0, 1, 0, &limits).map_err(error)?, 1);
    Ok(())
}

#[test]
fn excessive_active_domain_is_incomplete_without_allocation() -> TestResult {
    let mut f = Fixture::new()?;
    let mut root = f.atom("p0")?;
    for index in 1..64 {
        let atom = f.atom(&format!("p{index}"))?;
        root = f.node(FormulaOp::Or(root, atom))?;
    }
    f.check(root, &[])?;
    let limits = Limits {
        atoms: 64,
        valuations: u64::MAX,
        ..Limits::default()
    };
    let result = assess(&f.finish()?, &limits).map_err(error)?;
    match &result.checks.first().ok_or("Missing outcome")?.conclusion {
        Conclusion::Incomplete(failure) => {
            assert_eq!(failure.required, ValuationCount::BeyondU64 { atoms: 64 });
            assert_eq!(failure.limit, LimitKind::Valuations);
            assert_eq!(failure.checked_valuations, 0);
        }
        other => return Err(format!("Expected incomplete, got {other:?}")),
    }
    Ok(())
}
