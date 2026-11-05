use super::parse;
use crate::ast::{Comparable, ExprId, ExprKind, Parsed, SetItem, SetKind, Statement, Value};
use weft_domain::{Code, Limits, QuantifierKind};

pub(super) fn review(body: &str) -> String {
    format!(
        "review r {{ context \"c\" at \"s\"; profile \"weft.symbolic/1\"; target t = proposal \"p\"; {body} }}"
    )
}

fn check(parsed: &Parsed<'_>, index: usize) -> Result<ExprId, String> {
    match parsed.statements.get(index) {
        Some(Statement::Check { expression, .. }) => Ok(*expression),
        _ => Err("expected check statement".into()),
    }
}

#[test]
fn connective_precedence_and_association_are_structural() -> Result<(), String> {
    let source = review("check q: A() or not a.x == b.x and C() and D();");
    let parsed = parse(&source, &Limits::default()).map_err(|errors| format!("{errors:?}"))?;
    let root = parsed.expression(check(&parsed, 0)?).ok_or("root")?;
    let ExprKind::Or(left, right) = root.kind else {
        return Err("or must be outermost".into());
    };
    assert!(matches!(
        parsed.expression(left).map(|node| &node.kind),
        Some(ExprKind::Predicate { .. })
    ));
    let ExprKind::And(first, _) = parsed.expression(right).ok_or("right")?.kind else {
        return Err("and must bind tighter than or".into());
    };
    let ExprKind::And(negated, _) = parsed.expression(first).ok_or("left-associated and")?.kind
    else {
        return Err("and chain must associate left".into());
    };
    let ExprKind::Not(comparison) = parsed.expression(negated).ok_or("not")?.kind else {
        return Err("not must bind tighter than and".into());
    };
    assert!(matches!(
        parsed.expression(comparison).map(|node| &node.kind),
        Some(ExprKind::Compare { .. })
    ));
    Ok(())
}

#[test]
fn binder_brace_extent_excludes_outer_connectives() -> Result<(), String> {
    let source = review("check q: forall x in {} { exists x in S { P(x) or Q(x) } } and R();");
    let parsed = parse(&source, &Limits::default()).map_err(|errors| format!("{errors:?}"))?;
    let ExprKind::And(quantified, _) = parsed.expression(check(&parsed, 0)?).ok_or("root")?.kind
    else {
        return Err("outer and was captured by binder".into());
    };
    let ExprKind::Quantifier { kind, body, .. } =
        parsed.expression(quantified).ok_or("forall")?.kind
    else {
        return Err("missing universal".into());
    };
    assert_eq!(kind, QuantifierKind::Forall);
    let ExprKind::Quantifier {
        kind,
        body,
        ref binder,
        ..
    } = parsed.expression(body).ok_or("exists")?.kind
    else {
        return Err("missing nested existential".into());
    };
    assert_eq!(kind, QuantifierKind::Exists);
    assert_eq!(binder.text, "x");
    assert!(matches!(
        parsed.expression(body).map(|node| &node.kind),
        Some(ExprKind::Or(_, _))
    ));
    Ok(())
}

#[test]
fn nested_spreads_preserve_occurrences_and_empty_literals() -> Result<(), String> {
    let source = review("S := {1, ...{2, ...{},}, 1, ...outer.field,}; check q: S == {...S,};");
    let parsed = parse(&source, &Limits::default()).map_err(|errors| format!("{errors:?}"))?;
    let Some(Statement::Set { value, .. }) = parsed.statements.first() else {
        return Err("missing set binding".into());
    };
    let SetKind::Literal(items) = &parsed.set(*value).ok_or("set")?.kind else {
        return Err("missing literal".into());
    };
    assert_eq!(items.len(), 4);
    assert!(matches!(
        items.first(),
        Some(SetItem::Value(Value::Natural("1", _)))
    ));
    assert!(matches!(
        items.get(2),
        Some(SetItem::Value(Value::Natural("1", _)))
    ));
    let Some(SetItem::Spread(nested, _)) = items.get(1) else {
        return Err("nested spread".into());
    };
    let SetKind::Literal(inner) = &parsed.set(*nested).ok_or("nested literal")?.kind else {
        return Err("nested spread must retain literal".into());
    };
    let Some(SetItem::Spread(empty, _)) = inner.get(1) else {
        return Err("empty spread".into());
    };
    assert!(
        matches!(&parsed.set(*empty).ok_or("empty literal")?.kind, SetKind::Literal(items) if items.is_empty())
    );
    assert!(matches!(
        &parsed
            .expression(check(&parsed, 1)?)
            .ok_or("comparison")?
            .kind,
        ExprKind::Compare {
            right: Comparable::Set(_),
            ..
        }
    ));
    Ok(())
}

#[test]
fn grammar_does_not_perform_semantic_rejection() -> Result<(), String> {
    let source = review(
        "claim t = citation \"x\"; rule r = citation \"r\"; S := {1, \"mixed\"}; need future; assume h: P(1); check q: forall x in {} { unknown.field == true } by r, r; check q: Q(missing);",
    );
    let parsed = parse(&source, &Limits::default()).map_err(|errors| format!("{errors:?}"))?;
    assert_eq!(parsed.statements.len(), 7);
    Ok(())
}

#[test]
fn set_trailing_commas_do_not_leak_into_other_lists() -> Result<(), String> {
    assert!(
        parse(
            &review("S := {1,}; E := {}; check q: P(1, true) by a, b;"),
            &Limits::default()
        )
        .is_ok()
    );
    for body in [
        "check q: P(1,);",
        "check q: P(,);",
        "check q: true by r,;",
        "S := {,};",
        "S := {1,,};",
    ] {
        let errors = parse(&review(body), &Limits::default())
            .err()
            .ok_or("accepted invalid trailing comma")?;
        assert_eq!(
            errors.first().ok_or("missing diagnostic")?.code,
            Code::UnexpectedToken
        );
    }
    Ok(())
}

#[test]
fn malformed_and_excluded_forms_never_parse() -> Result<(), String> {
    let malformed = [
        "let S := {};",
        "S = {};",
        "S := {{1}};",
        "S := {...1};",
        "check q: a == b == c;",
        "check q: P(Q());",
        "check q: P({1});",
        "check q: 1 + 2 == 3;",
        "check q: name;",
        "check q: a = = b;",
        "check q: a ! = b;",
        "S : = {};",
        "S := {. . .T};",
        "check q: forall x in {1} { P(x);",
        "check q: forall x in {} {};",
        "check q: forall in {} { true };",
        "check q: exists x {} { true };",
        "assume h: true by r;",
        "check q: true",
        "check q: P(a.);",
        "check q: (1) == 1;",
        "check q: true false;",
        "check q: 1.2 == 1;",
        "run t;",
        "context \"again\" at \"s\";",
    ];
    for body in malformed {
        let source = review(body);
        let errors = parse(&source, &Limits::default())
            .err()
            .ok_or_else(|| format!("accepted {body}"))?;
        let error = errors.first().ok_or("missing diagnostic")?;
        assert!(
            error.primary.is_some()
                && error.expected.is_some()
                && error.actual.is_some()
                && error.help.is_some()
        );
    }
    Ok(())
}

#[test]
fn headers_are_ordered_and_single_review_is_enforced() {
    let malformed = [
        "review r { profile \"p\"; context \"c\" at \"s\"; target t = proposal \"p\"; }",
        "review r { context \"c\" at \"s\"; target t = proposal \"p\"; profile \"p\"; }",
        "review r { context \"c\"; profile \"p\"; target t = proposal \"p\"; }",
        "review r { context \"c\" at \"s\"; profile \"p\"; target t = citation \"p\"; }",
    ];
    for source in malformed {
        assert!(parse(source, &Limits::default()).is_err());
    }
    assert!(parse(&(review("") + &review("")), &Limits::default()).is_err());
}
