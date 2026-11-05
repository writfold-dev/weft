use crate::{
    Report,
    json::{Json, RenderError, Result},
    models, values,
};
use weft_domain::{
    Check, CheckState, CompleteEvaluation, Conclusion, Instance, Model, PreparedCheck, Quantified,
    QuantifierKind,
};

pub(crate) fn evaluation(
    j: &mut Json,
    report: &Report<'_>,
    check: &Check,
    conclusion: &Conclusion,
    id: usize,
) -> Result<()> {
    let prepared = match &check.state {
        CheckState::Ready(p) => Some(p),
        CheckState::Blocked(_) => None,
    };
    j.object(|j| {
        j.count("id", id)?;
        j.text("kind", "evaluation")?;
        j.count("check", check.id.index())?;
        j.field("inputs", |j| match prepared {
            Some(p) => values::indices(
                j,
                p.premises()
                    .iter()
                    .map(|n| n.index())
                    .chain(std::iter::once(p.query().index())),
            ),
            None => j.array(|_| Ok(())),
        })?;
        if let Some(p) = prepared {
            j.count("query", p.query().index())?;
            j.field("premises", |j| {
                values::indices(j, p.premises().iter().map(|n| n.index()))
            })?;
            j.field("atoms", |j| {
                values::indices(j, p.atoms().iter().map(|a| a.index()))
            })?;
        }
        j.field("coverage", |j| {
            models::coverage(j, prepared, Some(conclusion))
        })?;
        j.count("valuation_budget", report.limits.valuations)?;
        j.count("step_budget", report.limits.evaluation_steps)?;
        if let (Conclusion::Complete(e), Some(p)) = (conclusion, prepared) {
            j.count("premise_models", e.premise_models)?;
            j.field("rows", |j| valuation_rows(j, e, p))?;
        }
        Ok(())
    })
}
fn valuation_rows(
    j: &mut Json,
    evaluation: &CompleteEvaluation,
    prepared: &PreparedCheck,
) -> Result<()> {
    if evaluation.premise_count != prepared.premises().len() {
        return Err(RenderError::InvalidRecord("premise row width"));
    }
    j.array(|j| {
        for (index, row) in evaluation.rows.iter().enumerate() {
            if u64::try_from(index).ok() != Some(row.valuation) {
                return Err(RenderError::InvalidRecord("valuation row order"));
            }
            j.item(|j| {
                j.object(|j| {
                    j.count("valuation", row.valuation)?;
                    j.field("assignment", |j| {
                        models::assignment(j, row.valuation, prepared.atoms().len())
                    })?;
                    j.flag("premises_hold", row.premises_hold)?;
                    let mut premises_hold = true;
                    j.field("premise_values", |j| {
                        j.array(|j| {
                            for premise in 0..evaluation.premise_count {
                                let truth = evaluation
                                    .premise_holds(index, premise)
                                    .ok_or(RenderError::InvalidRecord("premise row"))?;
                                premises_hold &= truth;
                                j.item(|j| j.boolean(truth))?;
                            }
                            Ok(())
                        })
                    })?;
                    if premises_hold != row.premises_hold {
                        return Err(RenderError::InvalidRecord(
                            "premise conjunction disagrees with captured row",
                        ));
                    }
                    j.flag("query", row.query)
                })
            })?;
        }
        Ok(())
    })
}
pub(crate) fn instance_models(
    j: &mut Json,
    report: &Report<'_>,
    q: &Quantified,
    instance: &Instance,
) -> Result<()> {
    j.field("models", |j| {
        j.array(|j| {
            if let (Some(assessment), Some(compilation)) = (report.assessment, report.compilation) {
                for outcome in &assessment.checks {
                    let check = compilation
                        .checks
                        .get(outcome.check.index())
                        .ok_or(RenderError::InvalidRecord("instance check"))?;
                    if let (Conclusion::Complete(e), CheckState::Ready(p)) =
                        (&outcome.conclusion, &check.state)
                    {
                        if !p.quantifiers().contains(&q.id) {
                            continue;
                        }
                        for model in [&e.supporting, &e.refuting].into_iter().flatten() {
                            j.item(|j| instance_model(j, model, check, q, instance))?;
                        }
                    }
                }
            }
            Ok(())
        })
    })
}
fn instance_model(
    j: &mut Json,
    model: &Model,
    check: &Check,
    q: &Quantified,
    instance: &Instance,
) -> Result<()> {
    let truth = model
        .value(instance.body)
        .ok_or(RenderError::InvalidRecord("instance model body"))?;
    j.object(|j| {
        j.count("check", check.id.index())?;
        j.count("valuation", model.valuation)?;
        j.flag("body", truth)?;
        j.text(
            "role",
            match (q.kind, truth) {
                (QuantifierKind::Exists, true) => "model-relative-witness",
                (QuantifierKind::Forall, false) => "model-relative-counterexample",
                _ => "model-relative-instance",
            },
        )?;
        j.field("hypotheses", |j| {
            values::indices(j, check.hypotheses.iter().map(|h| h.declaration.index()))
        })?;
        j.field("dependencies", |j| {
            values::indices(j, check.dependencies.iter().map(|id| id.index()))
        })
    })
}
