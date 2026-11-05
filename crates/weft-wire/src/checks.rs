use crate::{
    Report,
    json::{Json, RenderError, Result},
    models, trace, values,
};
use weft_domain::{Analysis, Check, CheckState, Conclusion, Declaration, DeclarationKind};

pub(crate) fn checks(j: &mut Json, report: &Report<'_>) -> Result<()> {
    j.array(|j| {
        if let Some(compilation) = report.compilation {
            for check in &compilation.checks {
                j.item(|j| finding(j, report, check))?;
            }
        } else if let Some(analysis) = report.analysis {
            for (index, declaration) in analysis
                .declarations
                .entries()
                .iter()
                .filter(|d| d.kind == DeclarationKind::Check)
                .enumerate()
            {
                j.item(|j| analysis_finding(j, analysis, declaration, index))?;
            }
        }
        Ok(())
    })
}
pub(crate) fn conclusion<'a>(
    report: &'a Report<'_>,
    check: &Check,
) -> Result<Option<&'a Conclusion>> {
    match report.assessment {
        Some(assessment) => {
            let outcome = assessment
                .checks
                .get(check.id.index())
                .ok_or(RenderError::InvalidRecord("missing check outcome"))?;
            if outcome.check != check.id {
                return Err(RenderError::InvalidRecord("misordered check outcome"));
            }
            if matches!(&check.state, CheckState::Blocked(_))
                != matches!(&outcome.conclusion, Conclusion::Blocked)
            {
                return Err(RenderError::InvalidRecord(
                    "outcome contradicts check availability",
                ));
            }
            Ok(Some(&outcome.conclusion))
        }
        None => Ok(None),
    }
}
fn finding(j: &mut Json, report: &Report<'_>, check: &Check) -> Result<()> {
    let compilation = report
        .compilation
        .ok_or(RenderError::InvalidRecord("check compilation"))?;
    let declaration = compilation
        .analysis
        .declarations
        .get(check.declaration)
        .ok_or(RenderError::InvalidRecord("check declaration"))?;
    let conclusion = conclusion(report, check)?;
    let prepared = match &check.state {
        CheckState::Ready(p) => Some(p),
        CheckState::Blocked(_) => None,
    };
    j.object(|j| {
        j.count("id", check.id.index())?;
        j.count("declaration", check.declaration.index())?;
        j.text("name", &declaration.name)?;
        j.field("span", |j| values::span(j, declaration.span))?;
        summary(j, check, conclusion, &compilation.theory)?;
        j.field("atoms", |j| match prepared {
            Some(p) => models::atoms(j, &compilation.theory, p),
            None => j.array(|_| Ok(())),
        })?;
        j.field("coverage", |j| models::coverage(j, prepared, conclusion))?;
        if let (Some(Conclusion::Complete(e)), Some(p)) = (conclusion, prepared) {
            j.field("models", |j| models::models(j, e, p))?;
        }
        if conclusion.is_some() {
            j.count(
                "trace_root",
                trace::classification_id(compilation, check.id.index())?,
            )?;
        }
        if let CheckState::Blocked(diagnostics) = &check.state {
            j.field("diagnostics", |j| {
                j.array(|j| {
                    for diagnostic in diagnostics {
                        j.item(|j| values::diagnostic(j, diagnostic))?;
                    }
                    Ok(())
                })
            })?;
        }
        Ok(())
    })
}
fn summary(
    j: &mut Json,
    check: &Check,
    conclusion: Option<&Conclusion>,
    theory: &weft_domain::Theory,
) -> Result<()> {
    j.text(
        "result",
        match conclusion {
            Some(Conclusion::Complete(e)) => models::verdict(e.verdict),
            Some(Conclusion::Incomplete(_)) => "unknown",
            _ => "not-evaluated",
        },
    )?;
    j.text(
        "basis",
        if matches!(&check.state, CheckState::Ready(_)) {
            "hypothetical"
        } else {
            "unresolved"
        },
    )?;
    j.text("explanation", match conclusion {
        Some(Conclusion::Complete(e)) => explanation(e.verdict, check, theory)?,
        Some(Conclusion::Incomplete(_)) => "The finite search did not complete within its admitted resource bounds; no entailment or refutation is established.",
        _ => "This check was not evaluated. Required interpretation, a preceding assumption, or local elaboration is unavailable; independent completed checks remain visible.",
    })?;
    j.field("hypotheses", |j| {
        values::indices(j, check.hypotheses.iter().map(|h| h.declaration.index()))
    })?;
    j.field("needs", |j| {
        values::indices(j, check.requirements.iter().map(|r| r.declaration.index()))
    })?;
    j.field("dependencies", |j| {
        values::indices(j, check.dependencies.iter().map(|id| id.index()))
    })
}
fn analysis_finding(
    j: &mut Json,
    analysis: &Analysis,
    declaration: &Declaration,
    index: usize,
) -> Result<()> {
    j.object(|j| {
        j.count("id", index)?;
        j.count("declaration", declaration.id.index())?;
        j.text("name", &declaration.name)?;
        j.field("span", |j| values::span(j, declaration.span))?;
        j.text("result", "not-evaluated")?;
        j.text("basis", "unresolved")?;
        j.text("explanation", "Structural analysis does not evaluate this check; no logical or grounded conclusion is asserted.")?;
        j.field("hypotheses", |j| values::indices(j, analysis.hypotheses.iter()
            .filter(|h| h.declaration.index() < declaration.id.index()).map(|h| h.declaration.index())))?;
        j.field("needs", |j| values::indices(j, analysis.requirements.iter()
            .filter(|r| r.span.end() <= declaration.span.start()).map(|r| r.declaration.index())))?;
        j.field("dependencies", |j| values::indices(j, analysis.declarations.entries().iter()
            .filter(|d| d.id.index() < declaration.id.index() && d.kind != DeclarationKind::Check)
            .map(|d| d.id.index())))?;
        j.text("dependency_scope", "conservative-preceding-declarations; not an elaborated used subset")?;
        j.field("atoms", |j| j.array(|_| Ok(())))?;
        j.text("atoms_status", "not-elaborated")?;
        j.field("coverage", |j| models::coverage(j, None, None))
    })
}
fn explanation(
    verdict: weft_domain::LogicalVerdict,
    check: &Check,
    theory: &weft_domain::Theory,
) -> Result<&'static str> {
    use weft_domain::{Comparison, LogicalVerdict, NodeDetail};
    if verdict == LogicalVerdict::Refuted
        && let CheckState::Ready(prepared) = &check.state
    {
        let node = theory
            .node(prepared.query())
            .ok_or(RenderError::InvalidRecord("explanation query"))?;
        match node.detail {
            NodeDetail::Comparison {
                operation: Comparison::Equal,
                ..
            }
            | NodeDetail::SetComparison {
                operation: Comparison::Equal,
                ..
            } => {
                return Ok(
                    "The exact typed operands differ, so this equality is false; their values are shown in the comparison trace. Every model of the preceding assumptions refutes this local check. No real-world falsity is asserted.",
                );
            }
            NodeDetail::Comparison {
                operation: Comparison::NotEqual,
                ..
            }
            | NodeDetail::SetComparison {
                operation: Comparison::NotEqual,
                ..
            } => {
                return Ok(
                    "The exact typed operands are equal, so this inequality is false; their values are shown in the comparison trace. Every model of the preceding assumptions refutes this local check. No real-world falsity is asserted.",
                );
            }
            _ => {}
        }
    }
    Ok(models::explanation(verdict))
}
