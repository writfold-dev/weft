use super::*;

#[test]
fn noncontiguous_atoms_use_lean_order_and_complete_models() -> TestResult {
    let mut f = Fixture::new()?;
    let a = f.atom("a")?;
    let unrelated = f.atom("unused")?;
    let b = f.atom("b")?;
    let not_a = f.node(FormulaOp::Not(a))?;
    let query = f.node(FormulaOp::And(not_a, b))?;
    f.check(query, &[])?;
    let compilation = f.finish()?;
    let check = match &compilation.checks.first().ok_or("Missing check")?.state {
        CheckState::Ready(check) => check,
        _ => return Err("Expected prepared check".into()),
    };
    assert_eq!(
        check
            .atoms()
            .iter()
            .map(|id| id.index())
            .collect::<Vec<_>>(),
        vec![0, 2]
    );
    let result = assess(&compilation, &Limits::default()).map_err(error)?;
    let evaluation = complete(&result, 0)?;
    assert_eq!(evaluation.verdict, LogicalVerdict::Undetermined);
    assert_eq!(
        evaluation
            .rows
            .iter()
            .map(|row| (row.valuation, row.premises_hold, row.query))
            .collect::<Vec<_>>(),
        vec![
            (0, true, false),
            (1, true, true),
            (2, true, false),
            (3, true, false)
        ]
    );
    let positive = evaluation
        .supporting
        .as_ref()
        .ok_or("Missing supporting model")?;
    let negative = evaluation
        .refuting
        .as_ref()
        .ok_or("Missing refuting model")?;
    assert_eq!(positive.valuation, 1);
    assert_eq!(negative.valuation, 0);
    assert_eq!(positive.value(a), Some(false));
    assert_eq!(positive.value(b), Some(true));
    assert_eq!(positive.value(not_a), Some(true));
    assert_eq!(positive.value(query), Some(true));
    assert_eq!(positive.value(unrelated), None);
    assert_eq!(positive.values.len(), check.nodes().len());
    assert_eq!(negative.values.len(), check.nodes().len());
    Ok(())
}

#[test]
fn previous_checks_and_unreachable_atoms_do_not_change_domain() -> TestResult {
    let mut f = Fixture::new()?;
    let p = f.atom("p")?;
    f.check(p, &[])?;
    let q = f.atom("q")?;
    let either = f.node(FormulaOp::Or(p, q))?;
    f.check(either, &[])?;
    f.check(q, &[])?;
    let _unused = f.atom("later")?;
    let result = assess(&f.finish()?, &Limits::default()).map_err(error)?;
    for index in 0..3 {
        assert_eq!(
            complete(&result, index)?.verdict,
            LogicalVerdict::Undetermined
        );
    }
    assert_eq!(complete(&result, 0)?.required_valuations, 2);
    assert_eq!(complete(&result, 1)?.required_valuations, 4);
    assert_eq!(complete(&result, 2)?.required_valuations, 2);
    Ok(())
}

#[test]
fn complete_rows_include_premise_failures_without_accepting_them() -> TestResult {
    let mut f = Fixture::new()?;
    let a = f.atom("a")?;
    let b = f.atom("b")?;
    f.check(b, &[a])?;
    let result = assess(&f.finish()?, &Limits::default()).map_err(error)?;
    let evaluation = complete(&result, 0)?;
    assert_eq!(evaluation.premise_models, 2);
    assert_eq!(
        evaluation
            .rows
            .iter()
            .map(|r| (r.premises_hold, r.query))
            .collect::<Vec<_>>(),
        vec![(false, false), (false, true), (true, false), (true, true)]
    );
    assert_eq!(evaluation.supporting.as_ref().map(|m| m.valuation), Some(3));
    assert_eq!(evaluation.refuting.as_ref().map(|m| m.valuation), Some(2));
    Ok(())
}

#[test]
fn mismatched_theory_references_are_diagnostics() -> TestResult {
    let mut f = Fixture::new()?;
    let atom = f.atom("p")?;
    f.check(atom, &[])?;
    let mut compilation = f.finish()?;
    compilation.theory = TheoryBuilder::new(Limits::default()).finish();
    let diagnostic = assess(&compilation, &Limits::default())
        .err()
        .ok_or("Expected invalid reference")?;
    assert_eq!(diagnostic.code, Code::InvalidProgram);
    assert_eq!(diagnostic.phase, Phase::Evaluate);
    Ok(())
}

#[test]
fn existential_entailment_keeps_model_relative_instances() -> TestResult {
    let mut f = Fixture::new()?;
    let p = f.atom("p")?;
    let not_p = f.node(FormulaOp::Not(p))?;
    let first = f
        .builder
        .intern_value(Scalar::Boolean(false))
        .map_err(error)?;
    let second = f
        .builder
        .intern_value(Scalar::Boolean(true))
        .map_err(error)?;
    let set = f
        .builder
        .add_set(
            Some(ScalarType::Boolean),
            vec![
                SetMember {
                    value: first,
                    origin: f.origin,
                },
                SetMember {
                    value: second,
                    origin: f.origin,
                },
            ],
            f.span,
            Vec::new(),
        )
        .map_err(error)?;
    let binder = f.builder.add_binder("x".into(), f.span).map_err(error)?;
    let (_, exists) = f
        .builder
        .quantify(QuantifierKind::Exists, binder, set, vec![p, not_p], f.span)
        .map_err(error)?;
    f.check(exists, &[])?;
    f.check(p, &[])?;
    f.check(not_p, &[])?;
    let result = assess(&f.finish()?, &Limits::default()).map_err(error)?;
    let evaluation = complete(&result, 0)?;
    assert_eq!(evaluation.verdict, LogicalVerdict::Entailed);
    assert_eq!(complete(&result, 1)?.verdict, LogicalVerdict::Undetermined);
    assert_eq!(complete(&result, 2)?.verdict, LogicalVerdict::Undetermined);
    let model = evaluation
        .supporting
        .as_ref()
        .ok_or("Missing existential model")?;
    assert_eq!(model.value(p), Some(false));
    assert_eq!(model.value(not_p), Some(true));
    assert_eq!(model.value(exists), Some(true));
    Ok(())
}
