use crate::{
    Command, RenderError, Report, Result, Source, checks, finite, json::Json, models, review,
    trace, values,
};
use weft_domain::{Conclusion, Limits};
pub(crate) fn envelope(
    j: &mut Json,
    report: &Report<'_>,
    publication: Option<&crate::publication::Publication>,
) -> Result<()> {
    j.object(|j| {
        j.text("schema", "weft.report/1")?;
        j.text(
            "kind",
            match report.command {
                Command::Analyze if report.analysis.is_some_and(|a| a.header.is_some()) => {
                    "analysis"
                }
                Command::Prove if report.compilation.is_some() => "assessment",
                _ => "diagnostics",
            },
        )?;
        j.text(
            "scope",
            match report.command {
                Command::Analyze => "local-analysis",
                Command::Prove => "local-symbolic",
            },
        )?;
        j.field("source", |j| source(j, report.source))?;
        j.text("execution", report.execution())?;
        j.flag("writfold_grounded", false)?;
        j.flag("effect_authority", false)?;
        j.field("diagnostics", |j| diagnostics(j, report))?;
        if let Some(analysis) = report.analysis.filter(|a| a.header.is_some()) {
            j.field("review", |j| {
                review::review(j, analysis, report.compilation)
            })?;
        }
        j.field("checks", |j| checks::checks(j, report))?;
        j.field("trace", |j| trace::trace(j, report, publication))?;
        if let Some(compilation) = report.compilation {
            let publication =
                publication.ok_or(RenderError::InvalidRecord("missing publication graph"))?;
            j.field("origins", |j| {
                finite::origins(j, &compilation.theory, publication)
            })?;
        }
        j.field("budgets", |j| {
            budgets(j, report.limits, report.compilation.map(|c| &c.theory))
        })?;
        Ok(())
    })
}
fn source(j: &mut Json, source: Source<'_>) -> Result<()> {
    j.object(|j| match source {
        Source::Unavailable { path, reason } => {
            j.text("kind", "unavailable")?;
            if let Some(path) = path {
                j.text("path", path)?;
            }
            j.text("reason", reason)
        }
        Source::Loaded {
            path,
            sha256,
            bytes,
        } => {
            j.text("kind", "loaded")?;
            j.text("path", path)?;
            j.text("sha256", sha256)?;
            j.count("bytes", bytes.len())?;
            j.field("content", |j| {
                j.object(|j| match std::str::from_utf8(bytes) {
                    Ok(text) => {
                        j.text("encoding", "utf-8")?;
                        j.text("text", text)
                    }
                    Err(_) => {
                        j.text("encoding", "hex")?;
                        j.field("hex", |j| {
                            use std::fmt::Write;
                            j.raw("\"")?;
                            for byte in bytes {
                                write!(j, "{byte:02x}").map_err(|_| RenderError::OutputLimit)?;
                            }
                            j.raw("\"")
                        })
                    }
                })
            })
        }
    })
}
fn budgets(j: &mut Json, limits: &Limits, theory: Option<&weft_domain::Theory>) -> Result<()> {
    j.object(|j| {
        if let Some(theory) = theory {
            let work = theory.work();
            j.count("construction_admitted", work.admitted)?;
            j.count("construction_used", work.used)?;
            j.count("construction_remaining", work.remaining)?;
        }
        j.count("construction_work", limits.work)?;
        j.count("source_bytes", limits.source_bytes)?;
        j.count("tokens", limits.tokens)?;
        j.count("nesting", limits.nesting)?;
        j.count("natural_digits", limits.natural_digits)?;
        j.count("nodes", limits.nodes)?;
        j.count("instances", limits.instances)?;
        j.count("members", limits.members)?;
        j.count("atoms", limits.atoms)?;
        j.count("valuations", limits.valuations)?;
        j.count("evaluation_steps", limits.evaluation_steps)?;
        j.count("trace_rows", limits.trace_rows)?;
        j.count("output_bytes", limits.output_bytes)
    })
}
fn diagnostics(j: &mut Json, report: &Report<'_>) -> Result<()> {
    j.array(|j| {
        if let Some(analysis) = report.analysis {
            for diagnostic in &analysis.diagnostics {
                j.item(|j| values::diagnostic(j, diagnostic))?;
            }
        }
        for diagnostic in report.diagnostics {
            j.item(|j| values::diagnostic(j, diagnostic))?;
        }
        if let (Some(assessment), Some(compilation)) = (report.assessment, report.compilation) {
            for outcome in &assessment.checks {
                if let Conclusion::Incomplete(incomplete) = &outcome.conclusion {
                    let check = compilation
                        .checks
                        .get(outcome.check.index())
                        .ok_or(RenderError::InvalidRecord("limited check"))?;
                    let declaration = compilation
                        .analysis
                        .declarations
                        .get(check.declaration)
                        .ok_or(RenderError::InvalidRecord("limited declaration"))?;
                    j.item(|j| models::limit_diagnostic(j, incomplete, declaration.span))?;
                }
            }
        }
        Ok(())
    })
}
