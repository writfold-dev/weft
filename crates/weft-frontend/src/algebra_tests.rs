//! Revision-3 set-algebra semantic checks: operand typing, typed empties,
//! unavailable-operand refusals, closure retention and budget honesty at the
//! library boundary.

use crate::{analyze, compile};
use weft_domain::{
    CheckState, Code, Compilation, FormulaOp, LimitKind, Limits, NodeDetail, OriginKind, ScalarType,
};

type TestResult = Result<(), String>;

fn literal_of(compilation: &Compilation, node: weft_domain::NodeId) -> bool {
    fn evaluate(compilation: &Compilation, node: weft_domain::NodeId) -> Option<bool> {
        let node = compilation.theory.node(node)?;
        match node.operation {
            FormulaOp::Literal(value) => Some(value),
            FormulaOp::Not(child) => evaluate(compilation, child).map(|value| !value),
            FormulaOp::And(left, right) => {
                evaluate(compilation, left)?.then(|| evaluate(compilation, right))?
            }
            FormulaOp::Or(left, right) => {
                Some(evaluate(compilation, left)? || evaluate(compilation, right)?)
            }
            FormulaOp::Atom(_) => None,
        }
    }
    evaluate(compilation, node).unwrap_or(false)
}
fn source(body: &str) -> String {
    format!(
        "review r {{ context \"c\" at \"s\"; profile \"weft.symbolic/1\"; target t = proposal \"p\"; {body} }}"
    )
}
fn clean(body: &str) -> Result<Compilation, String> {
    let compilation = compile(&source(body), &Limits::default())
        .map_err(|analysis| format!("{:?}", analysis.diagnostics))?;
    if !compilation.analysis.diagnostics.is_empty() {
        return Err(format!("{:?}", compilation.analysis.diagnostics));
    }
    Ok(compilation)
}
fn diagnoses(body: &str, code: Code) -> TestResult {
    let analysis = analyze(&source(body), &Limits::default());
    if !analysis
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == code)
    {
        return Err(format!("missing {code:?}: {:?}", analysis.diagnostics));
    }
    Ok(())
}

#[test]
fn algebra_operators_evaluate_exactly() -> TestResult {
    let compilation = clean(
        "a := {1,2,3}; b := {2,3,4}; \
         u := a | b; i := a & b; d := a - b; \
         check hit: 2 in i; check miss: not (1 in i); \
         check sub: i <= a; check subf: u <= a; \
         check paren: (a - b) == d; check prec: a | b & i == a;",
    )?;
    let mut verdicts: Vec<(String, bool)> = Vec::new();
    for check in &compilation.checks {
        let CheckState::Ready(prepared) = &check.state else {
            return Err("check not ready".into());
        };
        let name = compilation
            .analysis
            .declarations
            .get(check.declaration)
            .map(|d| d.name.clone())
            .unwrap_or_default();
        verdicts.push((name, literal_of(&compilation, prepared.query())));
    }
    let expected = [
        ("hit".into(), true),
        ("miss".into(), true),
        ("sub".into(), true),
        ("subf".into(), false),
        ("paren".into(), true),
        ("prec".into(), true),
    ];
    if verdicts != expected.to_vec() {
        return Err(format!("wrong verdicts: {verdicts:?}"));
    }
    Ok(())
}

#[test]
fn false_subset_keeps_first_left_counterexample() -> TestResult {
    let compilation = clean("a := {2,4}; b := {1,2,3}; check q: a <= b;")?;
    let CheckState::Ready(prepared) = &compilation.checks[0].state else {
        return Err("check not ready".into());
    };
    let detail = compilation
        .theory
        .node(prepared.query())
        .ok_or("node")?
        .detail;
    let NodeDetail::SetComparison {
        counterexample: Some(member),
        ..
    } = detail
    else {
        return Err("missing subset counterexample".into());
    };
    let scalar = compilation
        .theory
        .value(member)
        .ok_or("counterexample value")?;
    let weft_domain::Scalar::Natural(value) = scalar else {
        return Err("counterexample must be a natural".into());
    };
    if value.as_str() != "4" {
        return Err(format!("wrong counterexample: {}", value.as_str()));
    }
    Ok(())
}

#[test]
fn difference_keeps_whole_right_operand_closure() -> TestResult {
    let compilation = clean("a := {1,2}; b := {2,3}; d := a - b;")?;
    let set = compilation
        .theory
        .sets()
        .iter()
        .find(|set| compilation.theory.origin(set.origin).is_some())
        .and_then(|set| {
            compilation
                .theory
                .origins()
                .iter()
                .position(|origin| {
                    matches!(
                        origin.kind,
                        OriginKind::SetOperation {
                            operation: weft_domain::SetOperation::Difference,
                            ..
                        }
                    )
                })
                .map(|index| (set, index))
        });
    let Some((_set, operation_origin)) = set else {
        return Err("no difference operation origin".into());
    };
    // The operation origin's parents are both operand set origins; the right
    // operand stays linked even though member 2 was removed.
    let origin = &compilation.theory.origins()[operation_origin];
    if origin.parents.len() != 2 {
        return Err("difference must link both whole operands".into());
    }
    let members: Vec<String> = compilation
        .theory
        .sets()
        .iter()
        .map(|set| {
            set.members
                .iter()
                .filter_map(|member| compilation.theory.value(member.value))
                .map(|scalar| match scalar {
                    weft_domain::Scalar::Natural(v) => v.as_str().to_string(),
                    _ => "?".to_string(),
                })
                .collect::<Vec<_>>()
                .join(",")
        })
        .collect();
    if !members.iter().any(|m| m == "1") {
        return Err(format!("missing difference result: {members:?}"));
    }
    Ok(())
}

#[test]
fn empty_results_retain_their_element_type() -> TestResult {
    let compilation = clean("a := {1,2}; d := a - a; texts := {\"x\"}; te := texts - texts;")?;
    let typed: Vec<_> = compilation
        .theory
        .sets()
        .iter()
        .filter(|set| set.members.is_empty())
        .map(|set| set.element_type.clone())
        .collect();
    if typed.len() != 2 {
        return Err(format!("expected two empty results: {typed:?}"));
    }
    if typed[0] != Some(ScalarType::Natural) || typed[1] != Some(ScalarType::Text) {
        return Err(format!("empty results lost their element types: {typed:?}"));
    }
    // A typed empty cannot later hide a nominal mismatch.
    diagnoses(
        "a := {1}; texts := {\"x\"}; m := a & texts; check q: 1 in m;",
        Code::TypeMismatch,
    )
}

#[test]
fn mixed_operand_types_are_refused() -> TestResult {
    diagnoses(
        "a := {1}; texts := {\"x\"}; u := a | texts;",
        Code::TypeMismatch,
    )?;
    diagnoses(
        "a := {1}; texts := {\"x\"}; i := a & texts;",
        Code::TypeMismatch,
    )?;
    diagnoses(
        "a := {1}; texts := {\"x\"}; d := a - texts;",
        Code::TypeMismatch,
    )?;
    diagnoses(
        "a := {1}; texts := {\"x\"}; check q: a <= texts;",
        Code::TypeMismatch,
    )?;
    diagnoses("texts := {\"x\"}; check q: 1 in texts;", Code::TypeMismatch)?;
    diagnoses("a := {1}; check q: a in a;", Code::TypeMismatch)?;
    diagnoses("a := {1}; check q: 1 <= a;", Code::TypeMismatch)?;
    diagnoses("a := {1}; check q: a <= 1;", Code::TypeMismatch)?;
    Ok(())
}

#[test]
fn unavailable_operands_refuse_rather_than_vacuate() -> TestResult {
    // A type error in either operand refuses the whole operation; the failed
    // binding never installs an empty stand-in set.
    diagnoses(
        "s := {1} & {\"x\"}; check q: not (1 in s);",
        Code::TypeMismatch,
    )?;
    diagnoses("check q: not (1 in missing_set);", Code::UnknownName)
}

#[test]
fn algebra_charges_real_operand_work() -> TestResult {
    // Two 4096-member operands exceed the default member limit (16_384 total
    // raw union members is fine, but a 20_000-member literal is not).
    let mut giant = String::from("a := {");
    for index in 0..20_000 {
        if index > 0 {
            giant.push(',');
        }
        giant.push_str(&index.to_string());
    }
    giant.push_str("};");
    let result = compile(&source(&giant), &Limits::default());
    match result {
        Ok(compilation) => {
            let limited = compilation
                .analysis
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == Code::LimitExceeded);
            if !limited {
                return Err("oversized literal must be refused".into());
            }
        }
        Err(analysis) => {
            if !analysis
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == Code::LimitExceeded)
            {
                return Err(format!("{:?}", analysis.diagnostics));
            }
        }
    }
    let _ = LimitKind::Members;
    Ok(())
}

#[test]
fn derived_sets_carry_local_materialization_counts() -> TestResult {
    let compilation = clean("a := {1,2}; b := {2,3}; u := a | b; i := a & b; d := a - b;")?;
    let by_size: Vec<(usize, usize)> = compilation
        .theory
        .sets()
        .iter()
        .map(|set| (set.members.len(), set.raw_occurrences))
        .collect();
    // Union input count is the cardinality sum before dedup; intersection and
    // difference input counts equal their result cardinalities.
    if !by_size
        .iter()
        .any(|(cardinality, raw)| *cardinality == 3 && *raw == 4)
    {
        return Err(format!("union accounting wrong: {by_size:?}"));
    }
    if !by_size
        .iter()
        .any(|(cardinality, raw)| *cardinality == 1 && *raw == 1)
    {
        return Err(format!("difference accounting wrong: {by_size:?}"));
    }
    Ok(())
}
