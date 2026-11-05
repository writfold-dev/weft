use crate::{
    json::{Json, RenderError, Result},
    values,
};
use weft_domain::{
    CompleteEvaluation, Conclusion, LogicalVerdict, Model, PreparedCheck, Theory, ValuationCount,
};

pub(crate) fn verdict(value: LogicalVerdict) -> &'static str {
    match value {
        LogicalVerdict::Entailed => "entailed",
        LogicalVerdict::Refuted => "refuted",
        LogicalVerdict::Undetermined => "undetermined",
        LogicalVerdict::InconsistentPremises => "inconsistent-premises",
    }
}
pub(crate) fn explanation(value: LogicalVerdict) -> &'static str {
    match value {
        LogicalVerdict::Entailed => {
            "Every checked valuation satisfying all preceding assumptions satisfies this check. This is hypothetical entailment over the listed atoms and exact finite domains, not a real-world truth or effect permission."
        }
        LogicalVerdict::Refuted => {
            "The assumptions have models, but every such valuation makes the check false. Inspect the negative assignment and typed comparison operands: unequal literals cannot satisfy equality. This conflicts with the check only within this local theory, not with a real-world fact."
        }
        LogicalVerdict::Undetermined => {
            "The assumptions allow both the positive and negative assignments shown. They therefore neither imply the check nor imply its negation; the negative assignment explains the missing implication without asserting real-world falsity."
        }
        LogicalVerdict::InconsistentPremises => {
            "No checked valuation satisfies all preceding assumptions. No substantive conclusion is reported from these inconsistent premises; revise or discharge the conflicting assumptions."
        }
    }
}
pub(crate) fn assignment(j: &mut Json, valuation: u64, atoms: usize) -> Result<()> {
    j.array(|j| {
        for index in 0..atoms {
            let shift = atoms
                .checked_sub(index + 1)
                .and_then(|n| u32::try_from(n).ok())
                .ok_or(RenderError::InvalidRecord("valuation atom shift"))?;
            let bit = valuation
                .checked_shr(shift)
                .ok_or(RenderError::InvalidRecord("valuation width"))?
                & 1
                == 1;
            j.item(|j| j.boolean(bit))?;
        }
        Ok(())
    })
}
pub(crate) fn model(j: &mut Json, model: &Model, prepared: &PreparedCheck) -> Result<()> {
    j.object(|j| {
        j.count("valuation", model.valuation)?;
        j.field("assignment", |j| {
            assignment(j, model.valuation, prepared.atoms().len())
        })?;
        j.field("node_values", |j| {
            j.array(|j| {
                for entry in &model.values {
                    j.item(|j| {
                        j.object(|j| {
                            j.count("node", entry.node.index())?;
                            j.flag("value", entry.value)
                        })
                    })?;
                }
                Ok(())
            })
        })
    })
}
pub(crate) fn models(
    j: &mut Json,
    evaluation: &CompleteEvaluation,
    prepared: &PreparedCheck,
) -> Result<()> {
    j.object(|j| {
        if let Some(positive) = &evaluation.supporting {
            validate_model(evaluation, prepared, positive, true)?;
            j.field("positive", |j| model(j, positive, prepared))?;
        }
        if let Some(negative) = &evaluation.refuting {
            validate_model(evaluation, prepared, negative, false)?;
            j.field("negative", |j| model(j, negative, prepared))?;
        }
        Ok(())
    })
}
pub(crate) fn coverage(
    j: &mut Json,
    prepared: Option<&PreparedCheck>,
    conclusion: Option<&Conclusion>,
) -> Result<()> {
    j.object(|j| {
        if let Some(prepared) = prepared {
            j.count("atom_count", prepared.atoms().len())?;
        }
        match conclusion {
            Some(Conclusion::Complete(e)) => {
                complete_coverage(e, prepared)?;
                j.decimal("required_valuations", e.required_valuations)?;
                j.count("checked_valuations", e.checked_valuations)?;
                j.flag("complete", true)
            }
            Some(Conclusion::Incomplete(e)) => {
                match e.required {
                    ValuationCount::Exact(count) => j.decimal("required_valuations", count)?,
                    ValuationCount::BeyondU64 { atoms } => {
                        j.count("required_power_of_two", atoms)?
                    }
                }
                j.count("checked_valuations", e.checked_valuations)?;
                j.count("admitted", e.admitted)?;
                j.text("limiting_resource", limit(e.limit))?;
                j.flag("complete", false)
            }
            _ => {
                j.count("checked_valuations", 0)?;
                j.flag("complete", false)
            }
        }
    })
}
pub(crate) fn atoms(j: &mut Json, theory: &Theory, prepared: &PreparedCheck) -> Result<()> {
    j.array(|j| {
        for (local, id) in prepared.atoms().iter().enumerate() {
            let atom = theory
                .atom(*id)
                .ok_or(RenderError::InvalidRecord("atom reference"))?;
            j.item(|j| {
                j.object(|j| {
                    j.count("index", local)?;
                    j.count("id", id.index())?;
                    j.text("name", &atom.name)?;
                    j.field("arguments", |j| {
                        j.array(|j| {
                            for argument in &atom.arguments {
                                j.item(|j| values::value(j, theory, *argument))?;
                            }
                            Ok(())
                        })
                    })
                })
            })?;
        }
        Ok(())
    })
}
pub(crate) fn limit(limit: weft_domain::LimitKind) -> &'static str {
    use weft_domain::LimitKind;
    match limit {
        LimitKind::SourceBytes => "source-bytes",
        LimitKind::Tokens => "tokens",
        LimitKind::Nesting => "nesting",
        LimitKind::NaturalDigits => "natural-digits",
        LimitKind::Work => "construction-work",
        LimitKind::Members => "members",
        LimitKind::Instances => "instances",
        LimitKind::Nodes => "nodes",
        LimitKind::Atoms => "atoms",
        LimitKind::Valuations => "valuations",
        LimitKind::EvaluationSteps => "evaluation-steps",
        LimitKind::TraceRows => "trace-rows",
        LimitKind::OutputBytes => "output-bytes",
    }
}
pub(crate) fn limit_diagnostic(
    j: &mut Json,
    incomplete: &weft_domain::IncompleteEvaluation,
    span: weft_domain::SourceSpan,
) -> Result<()> {
    j.object(|j| {
        j.text("code", weft_domain::Code::LimitExceeded.as_str())?;
        j.text("phase", "evaluate")?;
        j.text("severity", "error")?;
        j.text("message", "A resource bound prevented complete finite evaluation; no entailment or refutation is established")?;
        j.field("primary", |j| values::span(j, span))?;
        j.field("secondary", |j| j.array(|_| Ok(())))?;
        j.text("actual", limit(incomplete.limit))?;
        j.text("help", "Reduce the finite domain, independent atoms, or instantiated formula size")
    })
}
fn complete_coverage(
    evaluation: &CompleteEvaluation,
    prepared: Option<&PreparedCheck>,
) -> Result<()> {
    let prepared = prepared.ok_or(RenderError::InvalidRecord("completed blocked check"))?;
    let exponent = u32::try_from(prepared.atoms().len())
        .map_err(|_| RenderError::InvalidRecord("completed atom count"))?;
    let required = 1_u64
        .checked_shl(exponent)
        .ok_or(RenderError::InvalidRecord("completed valuation count"))?;
    let rows = u64::try_from(evaluation.rows.len())
        .map_err(|_| RenderError::InvalidRecord("completed row count"))?;
    if evaluation.required_valuations != required
        || evaluation.checked_valuations != required
        || rows != required
    {
        return Err(RenderError::InvalidRecord(
            "incomplete coverage marked complete",
        ));
    }
    let positive = evaluation.supporting.is_some();
    let negative = evaluation.refuting.is_some();
    let valid = match evaluation.verdict {
        LogicalVerdict::Entailed => positive && !negative && evaluation.premise_models > 0,
        LogicalVerdict::Refuted => !positive && negative && evaluation.premise_models > 0,
        LogicalVerdict::Undetermined => positive && negative && evaluation.premise_models > 0,
        LogicalVerdict::InconsistentPremises => {
            !positive && !negative && evaluation.premise_models == 0
        }
    };
    if !valid || evaluation.premise_models > required {
        return Err(RenderError::InvalidRecord("verdict model coverage"));
    }
    Ok(())
}
fn validate_model(
    evaluation: &CompleteEvaluation,
    prepared: &PreparedCheck,
    model: &Model,
    positive: bool,
) -> Result<()> {
    let index = usize::try_from(model.valuation)
        .map_err(|_| RenderError::InvalidRecord("model valuation"))?;
    let row = evaluation
        .rows
        .get(index)
        .ok_or(RenderError::InvalidRecord("model valuation row"))?;
    if row.valuation != model.valuation
        || !row.premises_hold
        || row.query != positive
        || model.value(prepared.query()) != Some(positive)
        || model.values.len() != prepared.nodes().len()
        || !model
            .values
            .iter()
            .zip(prepared.nodes())
            .all(|(value, node)| value.node == *node)
    {
        return Err(RenderError::InvalidRecord(
            "model does not match its checked valuation",
        ));
    }
    for (premise, node) in prepared.premises().iter().enumerate() {
        if model.value(*node) != Some(true)
            || evaluation.premise_holds(index, premise) != Some(true)
        {
            return Err(RenderError::InvalidRecord(
                "model does not satisfy captured premises",
            ));
        }
    }
    Ok(())
}
