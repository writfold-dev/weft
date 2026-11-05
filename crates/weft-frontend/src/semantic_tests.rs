use crate::{analyze, compile};
use weft_domain::{CheckState, Code, Compilation, FormulaOp, Limits, OriginKind, Scalar};

type TestResult = Result<(), String>;
fn source(body: &str) -> String {
    format!(
        "review r {{ context \"c\" at \"s\"; profile \"weft.symbolic/1\"; target t = proposal \"p\"; {body} }}"
    )
}
fn compiled(body: &str) -> Result<Compilation, String> {
    compile(&source(body), &Limits::default())
        .map_err(|analysis| format!("{:?}", analysis.diagnostics))
}
fn clean(body: &str) -> Result<Compilation, String> {
    let compilation = compiled(body)?;
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
fn lexical_shadowing_and_outer_domains() -> TestResult {
    let compilation =
        clean("xs := {1,2}; check q: forall xs in xs { exists xs in {xs} { xs == xs } };")?;
    if compilation.theory.binders().len() != 2 || compilation.theory.quantifiers().len() != 3 {
        return Err("lexical binders or expanded nested quantifiers were conflated".into());
    }
    let nested: Vec<_> = compilation
        .theory
        .quantifiers()
        .iter()
        .filter_map(|q| q.enclosing)
        .collect();
    if nested.len() != 2
        || nested.first().map(|item| item.member) != Some(0)
        || nested.get(1).map(|item| item.member) != Some(1)
    {
        return Err("nested containment does not identify actual outer members".into());
    }
    Ok(())
}

#[test]
fn empty_domains_do_not_skip_validation() -> TestResult {
    diagnoses(
        "check q: forall x in {} { missing == 1 };",
        Code::UnknownName,
    )?;
    diagnoses("check q: exists x in {} { P(x) };", Code::AmbiguousType)?;
    diagnoses("check q: forall x in {} { true == 1 };", Code::TypeMismatch)?;
    diagnoses(
        "check q: forall x in {} { P(1) and P() };",
        Code::ArityMismatch,
    )?;
    diagnoses(
        "check q: forall x in {} { t.field == 1 };",
        Code::UnresolvedInput,
    )
}

#[test]
fn empty_types_unify_without_defaulting() -> TestResult {
    let compilation =
        clean("e := {}; check q: forall x in e { x == 1 and P(x) }; check z: {} == {};")?;
    if !compilation
        .theory
        .sets()
        .iter()
        .any(|set| set.element_type.is_none() && set.members.is_empty())
    {
        return Err("type-irrelevant empty sets lost parametric type".into());
    }
    clean("e := {}; check q: forall x in e { P(x) }; check later: P(1);")?;
    Ok(())
}

#[test]
fn extensional_sets_retain_duplicate_and_empty_spread_origins() -> TestResult {
    let compilation = clean("e := {}; xs := {1,1,...e,2}; check q: xs == {2,1};")?;
    let set = compilation
        .theory
        .sets()
        .iter()
        .find(|set| set.raw_occurrences == 3)
        .ok_or("missing raw duplicate occurrence count")?;
    if set.members.len() != 2 {
        return Err("duplicates were not normalized".into());
    }
    if !compilation
        .theory
        .origins()
        .iter()
        .any(|origin| matches!(origin.kind, OriginKind::Spread(_)))
    {
        return Err("empty spread provenance disappeared".into());
    }
    let check = compilation
        .checks
        .first()
        .ok_or("missing comparison check")?;
    let CheckState::Ready(prepared) = &check.state else {
        return Err("comparison blocked".into());
    };
    if !matches!(
        compilation
            .theory
            .node(prepared.query())
            .map(|node| node.operation),
        Some(FormulaOp::Literal(true))
    ) {
        return Err("set equality was not extensional".into());
    }
    Ok(())
}

#[test]
fn spread_comparison_and_scalar_types_do_not_coerce() -> TestResult {
    diagnoses("xs := {1,...{true}};", Code::TypeMismatch)?;
    diagnoses("xs := {1}; check q: xs == 1;", Code::TypeMismatch)?;
    diagnoses("check q: {1} == {\"1\"};", Code::TypeMismatch)?;
    diagnoses(
        "check q: forall x in {1} { exists y in x { true } };",
        Code::WrongNameKind,
    )?;
    diagnoses("check q: P(true) and P(1);", Code::TypeMismatch)
}

#[test]
fn naturals_are_exact_and_atoms_use_full_typed_arguments() -> TestResult {
    let huge = "9".repeat(200);
    let compilation = clean(&format!(
        "check q: P({huge}) and P({huge}) and P(1); check text: Q(\"1\");"
    ))?;
    if compilation.theory.atoms().len() != 3 {
        return Err("ground atoms were not exactly interned".into());
    }
    if !compilation
        .theory
        .values()
        .iter()
        .any(|value| matches!(value.as_ref(), Scalar::Natural(value) if value.as_str() == huge))
    {
        return Err("large natural was truncated".into());
    }
    diagnoses("check q: 1 == \"1\";", Code::TypeMismatch)
}

#[test]
fn invalid_assumptions_block_only_subsequent_checks() -> TestResult {
    let compilation =
        compiled("check before: true; assume broken: missing == 1; check after: true;")?;
    if !matches!(
        compilation.checks.first().map(|check| &check.state),
        Some(CheckState::Ready(_))
    ) || !matches!(
        compilation.checks.get(1).map(|check| &check.state),
        Some(CheckState::Blocked(_))
    ) {
        return Err("invalid assumption either erased or contaminated an earlier finding".into());
    }
    if !compilation
        .analysis
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == Code::InvalidPremise)
    {
        return Err("dependent check did not explain invalid premise".into());
    }
    Ok(())
}

#[test]
fn checks_are_not_premises_and_hypotheses_are_ordered() -> TestResult {
    let compilation =
        clean("check first: P(); assume h: Q(); check second: P(); assume later: false;")?;
    if compilation
        .checks
        .first()
        .map(|check| check.hypotheses.len())
        != Some(0)
        || compilation
            .checks
            .get(1)
            .map(|check| check.hypotheses.len())
            != Some(1)
    {
        return Err("checks or later assumptions became preceding premises".into());
    }
    if compilation.materializations.hypotheses.len() != 2 {
        return Err("unused final hypothesis was discarded".into());
    }
    Ok(())
}

#[test]
fn required_unused_external_requests_survive_true_queries() -> TestResult {
    let compilation = compiled("asset a = citation \"opaque\"; need a; check q: true;")?;
    if compilation.analysis.bindings.len() != 1 || compilation.analysis.requirements.len() != 1 {
        return Err("requested reference or explicit requirement disappeared".into());
    }
    if !compilation
        .analysis
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == Code::UnresolvedInput)
    {
        return Err("required external input was reported resolved".into());
    }
    if !matches!(
        compilation.checks.first().map(|check| &check.state),
        Some(CheckState::Ready(_))
    ) {
        return Err("independent hypothetical finding was discarded".into());
    }
    Ok(())
}

#[test]
fn instance_budget_is_shared_across_nested_and_separate_checks() -> TestResult {
    let limits = Limits {
        instances: 3,
        ..Limits::default()
    };
    let compilation = compile(
        &source("check a: forall x in {1,2} { true }; check b: forall x in {1,2} { true };"),
        &limits,
    )
    .map_err(|analysis| format!("{:?}", analysis.diagnostics))?;
    if !matches!(
        compilation.checks.first().map(|check| &check.state),
        Some(CheckState::Ready(_))
    ) || !matches!(
        compilation.checks.get(1).map(|check| &check.state),
        Some(CheckState::Blocked(_))
    ) {
        return Err("per-check instance budget was reset".into());
    }
    let nested = compile(
        &source("check q: forall x in {1,2} { exists y in {1,2} { true } };"),
        &limits,
    )
    .map_err(|analysis| format!("{:?}", analysis.diagnostics))?;
    if !matches!(
        nested.checks.first().map(|check| &check.state),
        Some(CheckState::Blocked(_))
    ) {
        return Err("per-instance nested expansion budget was reset".into());
    }
    Ok(())
}

#[test]
fn declaration_kinds_and_order_are_enforced() -> TestResult {
    diagnoses("check q: later == {}; later := {};", Code::UnknownName)?;
    diagnoses("xs := {}; xs := {};", Code::DuplicateName)?;
    diagnoses("assume h: true; check q: h == true;", Code::WrongNameKind)?;
    diagnoses("check q: true; need q;", Code::WrongNameKind)?;
    diagnoses(
        "asset a = citation \"x\"; check q: true by a;",
        Code::WrongNameKind,
    )?;
    diagnoses(
        "rule r1 = citation \"x\"; check q: true by r1,r1;",
        Code::DuplicateRule,
    )
}
