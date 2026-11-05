//! Revision-3 set-algebra surface: operator precedence, membership/subset
//! comparisons, parenthesized set expressions, non-chaining diagnostics and
//! unsupported-operator rejections.

use super::parse;
use crate::ast::{Comparable, ExprKind, SetKind, Statement};
use weft_domain::{Comparison, Limits, QuantifierKind, SetOperation};

pub(super) fn review(body: &str) -> String {
    format!(
        "review r {{ context \"c\" at \"s\"; profile \"weft.symbolic/1\"; target t = proposal \"p\"; {body} }}"
    )
}

#[test]
fn intersection_binds_tighter_than_alternation() -> Result<(), String> {
    let source = review("s := a | b & c;");
    let parsed = parse(&source, &Limits::default()).map_err(|errors| format!("{errors:?}"))?;
    let Statement::Set { value, .. } = &parsed.statements[0] else {
        return Err("expected set binding".into());
    };
    let SetKind::Binary {
        operation: SetOperation::Union,
        left,
        right,
    } = parsed.set(*value).ok_or("root")?.kind
    else {
        return Err("union must be outermost".into());
    };
    assert!(matches!(
        parsed.set(left).map(|node| &node.kind),
        Some(SetKind::Path(_))
    ));
    assert!(matches!(
        parsed.set(right).map(|node| &node.kind),
        Some(SetKind::Binary {
            operation: SetOperation::Intersection,
            ..
        })
    ));
    Ok(())
}

#[test]
fn alternation_is_left_associative() -> Result<(), String> {
    let source = review("s := a | b - c;");
    let parsed = parse(&source, &Limits::default()).map_err(|errors| format!("{errors:?}"))?;
    let Statement::Set { value, .. } = &parsed.statements[0] else {
        return Err("expected set binding".into());
    };
    let SetKind::Binary {
        operation: SetOperation::Difference,
        ..
    } = parsed.set(*value).ok_or("root")?.kind
    else {
        return Err("a | b - c must parse as (a | b) - c".into());
    };
    Ok(())
}

#[test]
fn membership_and_subset_comparisons_parse() -> Result<(), String> {
    let source = review("check q: x in (a - b) and a <= b | c;");
    let parsed = parse(&source, &Limits::default()).map_err(|errors| format!("{errors:?}"))?;
    let Statement::Check { expression, .. } = &parsed.statements[0] else {
        return Err("expected check".into());
    };
    let ExprKind::And(member, subset) = parsed.expression(*expression).ok_or("root")?.kind else {
        return Err("expected conjunction".into());
    };
    let ExprKind::Compare {
        operation: Comparison::Member,
        ref left,
        ref right,
    } = parsed.expression(member).ok_or("member")?.kind
    else {
        return Err("expected membership".into());
    };
    assert!(matches!(left, Comparable::Value(_)));
    let Comparable::Set(domain) = *right else {
        return Err("membership right operand must be a set".into());
    };
    assert!(matches!(
        parsed.set(domain).map(|node| &node.kind),
        Some(SetKind::Binary {
            operation: SetOperation::Difference,
            ..
        })
    ));
    let ExprKind::Compare {
        operation: Comparison::Subset,
        ..
    } = parsed.expression(subset).ok_or("subset")?.kind
    else {
        return Err("expected subset".into());
    };
    Ok(())
}

#[test]
fn not_binds_looser_than_membership() -> Result<(), String> {
    let source = review("check q: not x in a;");
    let parsed = parse(&source, &Limits::default()).map_err(|errors| format!("{errors:?}"))?;
    let Statement::Check { expression, .. } = &parsed.statements[0] else {
        return Err("expected check".into());
    };
    let ExprKind::Not(inner) = parsed.expression(*expression).ok_or("root")?.kind else {
        return Err("not must wrap the membership".into());
    };
    assert!(matches!(
        parsed.expression(inner).map(|node| &node.kind),
        Some(ExprKind::Compare {
            operation: Comparison::Member,
            ..
        })
    ));
    Ok(())
}

#[test]
fn parenthesized_set_groups_compose_with_comparisons() -> Result<(), String> {
    let source = review("check q: (a | b) == c;");
    let parsed = parse(&source, &Limits::default()).map_err(|errors| format!("{errors:?}"))?;
    let Statement::Check { expression, .. } = &parsed.statements[0] else {
        return Err("expected check".into());
    };
    let ExprKind::Compare {
        operation: Comparison::Equal,
        ..
    } = parsed.expression(*expression).ok_or("root")?.kind
    else {
        return Err("expected equality over a set group".into());
    };
    Ok(())
}

#[test]
fn spread_consumes_operators_to_the_item_delimiter() -> Result<(), String> {
    let source = review("s := { ...(a | b), \"extra\" };");
    let parsed = parse(&source, &Limits::default()).map_err(|errors| format!("{errors:?}"))?;
    let Statement::Set { value, .. } = &parsed.statements[0] else {
        return Err("expected set binding".into());
    };
    let SetKind::Literal(items) = &parsed.set(*value).ok_or("literal")?.kind else {
        return Err("expected literal".into());
    };
    assert_eq!(items.len(), 2);
    assert!(matches!(items[0], crate::ast::SetItem::Spread(_, _)));
    Ok(())
}

#[test]
fn comparisons_do_not_chain_across_all_operators() {
    let rejected: Vec<&str> = [
        "check q: x in a <= b;",
        "check q: a <= b == c;",
        "check q: a == b == c;",
        "check q: x in a in b;",
    ]
    .iter()
    .filter(|body| parse(&review(body), &Limits::default()).is_err())
    .copied()
    .collect();
    assert_eq!(
        rejected.len(),
        4,
        "every chained comparison must be rejected"
    );
}

#[test]
fn unsupported_operators_are_rejected() {
    for body in [
        "check q: a < b;",
        "check q: a > b;",
        "check q: a + b;",
        "check q: 1 | 2;",
        "check q: \"x\" & s;",
    ] {
        let source = review(body);
        assert!(
            parse(&source, &Limits::default()).is_err(),
            "{body} must be rejected"
        );
    }
}

#[test]
fn membership_inside_quantified_bodies_and_domains() -> Result<(), String> {
    let source = review("check q: forall x in (a - b) { x in a or not (x in b) };");
    let parsed = parse(&source, &Limits::default()).map_err(|errors| format!("{errors:?}"))?;
    let Statement::Check { expression, .. } = &parsed.statements[0] else {
        return Err("expected check".into());
    };
    let ExprKind::Quantifier {
        kind, domain, body, ..
    } = parsed.expression(*expression).ok_or("root")?.kind
    else {
        return Err("expected quantifier".into());
    };
    assert_eq!(kind, QuantifierKind::Forall);
    assert!(matches!(
        parsed.set(domain).map(|node| &node.kind),
        Some(SetKind::Binary {
            operation: SetOperation::Difference,
            ..
        })
    ));
    assert!(matches!(
        parsed.expression(body).map(|node| &node.kind),
        Some(ExprKind::Or(_, _))
    ));
    Ok(())
}
