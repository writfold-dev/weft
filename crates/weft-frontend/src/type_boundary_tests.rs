use crate::{analyze, compile, types::Types};
use weft_domain::{Code, Limits, ScalarType, SourceSpan};

type TestResult = Result<(), String>;
fn source(body: &str) -> String {
    format!(
        "review r {{ context \"c\" at \"s\"; profile \"weft.symbolic/1\"; target t = proposal \"p\"; {body} }}"
    )
}

#[test]
fn nominal_types_require_exact_kind_and_realm() -> TestResult {
    let span = SourceSpan::checked("x", 0, 1).map_err(|error| format!("{error:?}"))?;
    for (left, right) in [("asset", "claim"), ("asset", "asset")] {
        let mut types = Types::default();
        let a = types.fresh(Some(ScalarType::Identity {
            kind: left.into(),
            realm: "a".into(),
        }));
        let b = types.fresh(Some(ScalarType::Identity {
            kind: right.into(),
            realm: "b".into(),
        }));
        if !matches!(types.unify(a, b, span), Err(diagnostic) if diagnostic.code == Code::TypeMismatch)
        {
            return Err("nominal types from different realms unified".into());
        }
    }
    let mut types = Types::default();
    let a = types.fresh(Some(ScalarType::Identity {
        kind: "asset".into(),
        realm: "a".into(),
    }));
    let b = types.fresh(Some(ScalarType::Identity {
        kind: "claim".into(),
        realm: "a".into(),
    }));
    if types.unify(a, b, span).is_ok() {
        return Err("different nominal kinds unified".into());
    }
    let text = types.fresh(Some(ScalarType::Text));
    if types.unify(a, text, span).is_ok() {
        return Err("text was coerced to identity".into());
    }
    Ok(())
}

#[test]
fn spread_preflight_preserves_failed_binding_as_unmaterialized() -> TestResult {
    let limits = Limits {
        members: 3,
        ..Limits::default()
    };
    let compilation = compile(
        &source("xs := {1,2}; ys := {...xs,...xs}; check q: ys == {} ;"),
        &limits,
    )
    .map_err(|analysis| format!("{:?}", analysis.diagnostics))?;
    if !compilation
        .analysis
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == Code::LimitExceeded)
    {
        return Err("raw spread exceeded member budget without refusal".into());
    }
    if compilation
        .materializations
        .sets
        .get(1)
        .and_then(|set| set.value)
        .is_some()
    {
        return Err("failed spread published a partial set".into());
    }
    Ok(())
}

#[test]
fn external_identity_is_not_a_citation_string() -> TestResult {
    let analysis = analyze(
        &source("asset a = citation \"id\"; check q: a == \"id\";"),
        &Limits::default(),
    );
    if !analysis
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == Code::UnresolvedInput)
    {
        return Err("citation string became a scalar identity".into());
    }
    Ok(())
}

#[test]
fn invalid_assumption_stays_invalid_after_duplicate_label() -> TestResult {
    let compilation = compile(
        &source("assume h: true; assume h: false; check q: true;"),
        &Limits::default(),
    )
    .map_err(|analysis| format!("{:?}", analysis.diagnostics))?;
    if !matches!(
        compilation.checks.first().map(|check| &check.state),
        Some(weft_domain::CheckState::Blocked(_))
    ) {
        return Err("invalid duplicate assumption silently disappeared".into());
    }
    Ok(())
}

#[test]
fn rejected_check_label_does_not_destroy_earlier_results() -> TestResult {
    let compilation = compile(
        &source("check a: true; check b: a == true;"),
        &Limits::default(),
    )
    .map_err(|analysis| format!("{:?}", analysis.diagnostics))?;
    if !matches!(
        compilation.checks.first().map(|check| &check.state),
        Some(weft_domain::CheckState::Ready(_))
    ) || !matches!(
        compilation.checks.get(1).map(|check| &check.state),
        Some(weft_domain::CheckState::Blocked(_))
    ) {
        return Err("rejected check-label reference escaped the blocked-check boundary".into());
    }
    Ok(())
}

#[test]
fn conservative_premise_snapshots_share_construction_budget() -> TestResult {
    let mut body = String::new();
    for index in 0..20 {
        body.push_str(&format!("assume h{index}: true;"));
    }
    for index in 0..20 {
        body.push_str(&format!("check c{index}: true;"));
    }
    let limits = Limits {
        work: 200,
        ..Limits::default()
    };
    let Err(analysis) = compile(&source(&body), &limits) else {
        return Err("quadratic premise snapshots escaped the aggregate work budget".into());
    };
    if !analysis
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == Code::LimitExceeded)
    {
        return Err("metadata budget refusal lost its limiting diagnostic".into());
    }
    Ok(())
}
