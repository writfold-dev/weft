use super::*;

#[test]
fn premise_truth_crosses_word_and_row_boundaries() -> TestResult {
    let mut f = Fixture::new()?;
    let p = f.atom("p")?;
    f.check(p, &vec![p; 65])?;
    let compilation = f.finish()?;
    let result = assess(&compilation, &Limits::default()).map_err(error)?;
    let evaluation = complete(&result, 0)?;
    assert_eq!(evaluation.premise_count, 65);
    assert_eq!(evaluation.premise_truth_words, vec![0, u64::MAX - 1, 3]);
    for premise in 0..65 {
        assert_eq!(evaluation.premise_holds(0, premise), Some(false));
        assert_eq!(evaluation.premise_holds(1, premise), Some(true));
    }
    assert_eq!(evaluation.premise_holds(1, 65), None);
    assert_eq!(evaluation.premise_holds(2, 0), None);
    let limits = Limits {
        evaluation_steps: 131,
        ..Limits::default()
    };
    let refused = assess(&compilation, &limits).map_err(error)?;
    match &refused.checks.first().ok_or("Missing outcome")?.conclusion {
        Conclusion::Incomplete(failure) => {
            assert_eq!(failure.limit, LimitKind::EvaluationSteps);
            assert_eq!(failure.checked_valuations, 0);
        }
        other => return Err(format!("Expected premise-visit refusal, got {other:?}")),
    }
    Ok(())
}
