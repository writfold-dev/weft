use super::{parse, tests::review};
use crate::ast::{ExprKind, Statement};
use weft_domain::{Code, Limits, Phase, limits::MAX_SOURCE_DEPTH};

fn limited(source: &str, limits: &Limits) -> Result<(), String> {
    let errors = parse(source, limits)
        .err()
        .ok_or("expected bounded parse failure")?;
    let error = errors.first().ok_or("missing diagnostic")?;
    assert_eq!(error.code, Code::LimitExceeded);
    assert!(error.expected.is_some() && error.actual.is_some() && error.help.is_some());
    Ok(())
}

#[test]
fn intrinsic_connective_depth_is_bounded_without_recursive_syntax() -> Result<(), String> {
    let limits = Limits {
        nesting: 4,
        ..Limits::default()
    };
    for connective in [" and ", " or "] {
        let four = ["true"; 4].join(connective);
        let source = review(&format!("check q: {four};"));
        let parsed = parse(&source, &limits).map_err(|errors| format!("{errors:?}"))?;
        let Some(Statement::Check { expression, .. }) = parsed.statements.first() else {
            return Err("missing check".into());
        };
        assert_eq!(parsed.expression(*expression).ok_or("expression")?.depth, 4);
        limited(
            &review(&format!("check q: {four}{connective}true;")),
            &limits,
        )?;
    }
    Ok(())
}

#[test]
fn parentheses_and_not_use_bounded_parser_recursion() -> Result<(), String> {
    let limits = Limits {
        nesting: 4,
        ..Limits::default()
    };
    for expression in ["(((true)))", "not not not true"] {
        assert!(parse(&review(&format!("check q: {expression};")), &limits).is_ok());
    }
    for expression in ["((((true))))", "not not not not true"] {
        limited(&review(&format!("check q: {expression};")), &limits)?;
    }
    Ok(())
}

#[test]
fn huge_requested_nesting_cannot_override_architectural_cap() -> Result<(), String> {
    let limits = Limits {
        nesting: usize::MAX,
        ..Limits::default()
    };
    let expression = format!(
        "{}true{}",
        "(".repeat(MAX_SOURCE_DEPTH - 1),
        ")".repeat(MAX_SOURCE_DEPTH - 1)
    );
    assert!(parse(&review(&format!("check q: {expression};")), &limits).is_ok());
    let excessive = format!("{}true{}", "(".repeat(4096), ")".repeat(4096));
    limited(&review(&format!("check q: {excessive};")), &limits)?;
    let flat = vec!["true"; MAX_SOURCE_DEPTH].join(" and ");
    assert!(parse(&review(&format!("check q: {flat};")), &limits).is_ok());
    limited(&review(&format!("check q: {flat} and true;")), &limits)?;
    Ok(())
}

#[test]
fn nested_spreads_and_quantifiers_share_depth_limits() -> Result<(), String> {
    let limits = Limits {
        nesting: 4,
        ..Limits::default()
    };
    assert!(parse(&review("S := {...{...{...{}}}};"), &limits).is_ok());
    limited(&review("S := {...{...{...{...{}}}}};"), &limits)?;
    assert!(
        parse(
            &review("check q: forall x in {} { exists y in {} { true } };"),
            &limits
        )
        .is_ok()
    );
    limited(
        &review(
            "check q: forall a in {} { forall b in {} { forall c in {} { forall d in {} { true } } } };",
        ),
        &limits,
    )?;
    Ok(())
}

#[test]
fn ast_node_budget_counts_header_values_and_statements() -> Result<(), String> {
    let mut limits = Limits {
        nodes: 7,
        ..Limits::default()
    };
    assert!(parse(&review(""), &limits).is_ok());
    limits.nodes = 6;
    limited(&review(""), &limits)?;
    limits.nodes = 11;
    assert!(parse(&review("check q: true;"), &limits).is_ok());
    limits.nodes = 10;
    limited(&review("check q: true;"), &limits)?;
    limits.nodes = 12;
    limited(&review("S := {1,2,3,4,5,6,7,8};"), &limits)?;
    limited(&review("check q: P(a.b.c.d.e.f.g.h);"), &limits)?;
    limits.nodes = 0;
    limited(&review(""), &limits)?;
    Ok(())
}

#[test]
fn zero_nesting_refuses_expressions_and_sets_without_rejecting_empty_review() -> Result<(), String>
{
    let limits = Limits {
        nesting: 0,
        ..Limits::default()
    };
    assert!(parse(&review(""), &limits).is_ok());
    limited(&review("check q: true;"), &limits)?;
    limited(&review("S := {};"), &limits)?;
    Ok(())
}

#[test]
fn unicode_and_grouped_expression_spans_cover_exact_source_bytes() -> Result<(), String> {
    let source = review("check q: not (\"α🙂\" == \"β\");");
    let parsed = parse(&source, &Limits::default()).map_err(|errors| format!("{errors:?}"))?;
    let Some(Statement::Check {
        expression, span, ..
    }) = parsed.statements.first()
    else {
        return Err("missing check".into());
    };
    assert_eq!(
        source.get(span.start()..span.end()),
        Some("check q: not (\"α🙂\" == \"β\");")
    );
    let root = parsed.expression(*expression).ok_or("root")?;
    assert_eq!(
        source.get(root.span.start()..root.span.end()),
        Some("not (\"α🙂\" == \"β\")")
    );
    let ExprKind::Not(inner) = root.kind else {
        return Err("missing negation".into());
    };
    let grouped = parsed.expression(inner).ok_or("grouped comparison")?;
    assert_eq!(
        source.get(grouped.span.start()..grouped.span.end()),
        Some("(\"α🙂\" == \"β\")")
    );
    Ok(())
}

#[test]
fn unexpected_end_has_exact_zero_width_source_span() -> Result<(), String> {
    let source = "review r { context \"🙂\" at";
    let errors = parse(source, &Limits::default())
        .err()
        .ok_or("accepted incomplete header")?;
    let error = errors.first().ok_or("missing diagnostic")?;
    assert_eq!(error.phase, Phase::Parse);
    let span = error.primary.ok_or("missing EOF span")?;
    assert_eq!((span.start(), span.end()), (source.len(), source.len()));
    Ok(())
}
