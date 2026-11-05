use crate::{
    Report, checks, finite, formula,
    json::{Json, RenderError, Result},
    metadata, models,
    publication::{self, Publication},
    rows, values,
};
use weft_domain::{Compilation, Conclusion};

pub(crate) fn classification_id(compilation: &Compilation, check: usize) -> Result<usize> {
    let mut count = compilation.theory.nodes().len();
    for q in compilation.theory.quantifiers() {
        count = count
            .checked_add(q.instances.len())
            .and_then(|n| n.checked_add(1))
            .ok_or(RenderError::InvalidRecord("trace size"))?;
    }
    count
        .checked_add(
            check
                .checked_mul(2)
                .ok_or(RenderError::InvalidRecord("trace index"))?,
        )
        .and_then(|n| n.checked_add(1))
        .ok_or(RenderError::InvalidRecord("trace index"))
}
pub(crate) fn trace(
    j: &mut Json,
    report: &Report<'_>,
    publication: Option<&Publication>,
) -> Result<()> {
    j.array(|j| {
        if let Some(compilation) = report.compilation {
            let publication = publication.ok_or(RenderError::InvalidRecord("trace publication"))?;
            let theory = &compilation.theory;
            for (id, node) in theory.nodes().iter().enumerate() {
                j.item(|j| formula::node(j, theory, id, node, publication.node(id)?))?;
            }
            quantifiers(j, compilation, report, publication)?;
            if report.assessment.is_some() {
                for check in &compilation.checks {
                    let classification = classification_id(compilation, check.id.index())?;
                    let evaluation = classification
                        .checked_sub(1)
                        .ok_or(RenderError::InvalidRecord("evaluation trace"))?;
                    let outcome = checks::conclusion(report, check)?
                        .ok_or(RenderError::InvalidRecord("trace outcome"))?;
                    j.item(|j| rows::evaluation(j, report, check, outcome, evaluation))?;
                    j.item(|j| classification_node(j, check, outcome, classification, evaluation))?;
                }
            }
            let check_count = if report.assessment.is_some() {
                compilation.checks.len()
            } else {
                0
            };
            let next = classification_id(compilation, check_count)?
                .checked_sub(1)
                .ok_or(RenderError::InvalidRecord("metadata trace index"))?;
            metadata::trace(j, compilation, next, publication)?;
        }
        Ok(())
    })
}
fn quantifiers(
    j: &mut Json,
    compilation: &Compilation,
    report: &Report<'_>,
    publication: &Publication,
) -> Result<()> {
    let theory = &compilation.theory;
    let mut next = theory.nodes().len();
    for q in theory.quantifiers() {
        let domain = theory
            .set(q.domain)
            .ok_or(RenderError::InvalidRecord("instance domain"))?;
        let published = publication.node(q.root.index())?;
        let first_instance = next;
        for instance in &q.instances {
            let member = domain
                .members
                .get(instance.member)
                .ok_or(RenderError::InvalidRecord("instance member"))?;
            j.item(|j| {
                j.object(|j| {
                    j.count("id", next)?;
                    j.text("kind", "quantifier-instance")?;
                    j.text("publication", publication::status(published))?;
                    j.field("inputs", |j| values::indices(j, [instance.body.index()]))?;
                    j.field("span", |j| values::span(j, q.span))?;
                    j.count("quantifier", q.id.index())?;
                    j.count("member", instance.member)?;
                    j.count("binder", q.binder.index())?;
                    j.field("value", |j| values::value(j, theory, member.value))?;
                    j.count("body", instance.body.index())?;
                    j.field("environment", |j| {
                        finite::environment(j, theory, q, instance.member)
                    })?;
                    rows::instance_models(j, report, q, instance)
                })
            })?;
            next = next
                .checked_add(1)
                .ok_or(RenderError::InvalidRecord("trace size"))?;
        }
        j.item(|j| {
            j.object(|j| {
                j.count("id", next)?;
                j.text("kind", "quantifier")?;
                j.field("inputs", |j| {
                    values::indices(
                        j,
                        std::iter::once(q.root.index()).chain(first_instance..next),
                    )
                })?;
                finite::quantifier(j, theory, q, published)?;
                j.count("expansion_budget", report.limits.instances)
            })
        })?;
        next = next
            .checked_add(1)
            .ok_or(RenderError::InvalidRecord("trace size"))?;
    }
    Ok(())
}
fn classification_node(
    j: &mut Json,
    check: &weft_domain::Check,
    outcome: &Conclusion,
    id: usize,
    evaluation: usize,
) -> Result<()> {
    j.object(|j| {
        let prepared = match &check.state {
            weft_domain::CheckState::Ready(p) => Some(p),
            weft_domain::CheckState::Blocked(_) => None,
        };
        j.count("id", id)?;
        j.text("kind", "classification")?;
        j.field("inputs", |j| values::indices(j, [evaluation]))?;
        j.count("check", check.id.index())?;
        j.text(
            "basis",
            if matches!(outcome, Conclusion::Blocked) {
                "unresolved"
            } else {
                "hypothetical"
            },
        )?;
        j.text(
            "result",
            match outcome {
                Conclusion::Complete(e) => models::verdict(e.verdict),
                Conclusion::Incomplete(_) => "unknown",
                Conclusion::Blocked => "not-evaluated",
            },
        )?;
        j.field("coverage", |j| models::coverage(j, prepared, Some(outcome)))?;
        if let (Conclusion::Complete(e), Some(prepared)) = (outcome, prepared) {
            j.field("models", |j| models::models(j, e, prepared))?;
        }
        Ok(())
    })
}
