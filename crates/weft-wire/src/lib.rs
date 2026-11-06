#![forbid(unsafe_code)]
mod checks;
pub mod control;
mod envelope;
mod finite;
mod formula;
mod json;
mod metadata;
mod models;
mod publication;
pub mod reuse;
mod review;
mod rows;
pub mod rpc;
mod trace;
mod values;

use json::Json;
pub use json::{RenderError, Result};
use weft_domain::{Analysis, Assessment, Compilation, Conclusion, Diagnostic, Limits};

#[derive(Clone, Copy)]
pub enum View {
    Json,
    Human,
}
#[derive(Clone, Copy)]
pub enum Source<'a> {
    Loaded {
        path: &'a str,
        sha256: &'a str,
        bytes: &'a [u8],
    },
    Unavailable {
        path: Option<&'a str>,
        reason: &'a str,
    },
}
#[derive(Clone, Copy)]
pub enum Command {
    Analyze,
    Prove,
}
pub struct Report<'a> {
    pub command: Command,
    pub source: Source<'a>,
    pub analysis: Option<&'a Analysis>,
    pub compilation: Option<&'a Compilation>,
    pub assessment: Option<&'a Assessment>,
    pub diagnostics: &'a [Diagnostic],
    pub limits: &'a Limits,
}
impl Report<'_> {
    pub fn execution(&self) -> &'static str {
        if self
            .diagnostics
            .iter()
            .chain(self.analysis.into_iter().flat_map(|a| &a.diagnostics))
            .any(|d| d.code == weft_domain::Code::LimitExceeded)
        {
            return "incomplete";
        }
        if !self.diagnostics.is_empty() || self.analysis.is_some_and(|a| !a.diagnostics.is_empty())
        {
            return "failed";
        }
        if self
            .analysis
            .is_none_or(|analysis| analysis.header.is_none())
            || matches!(self.command, Command::Prove) && self.assessment.is_none()
        {
            return "failed";
        }
        if let Some(assessment) = self.assessment
            && assessment
                .checks
                .iter()
                .any(|c| !matches!(c.conclusion, Conclusion::Complete(_)))
        {
            return "incomplete";
        }
        "complete"
    }
    pub fn exit_code(&self) -> u8 {
        if self.execution() != "complete" {
            2
        } else {
            match self.command {
                Command::Analyze => 0,
                Command::Prove => 1,
            }
        }
    }
}
pub fn render(report: &Report<'_>, view: View) -> Result<Vec<u8>> {
    if let Some(assessment) = report.assessment {
        let compilation = report
            .compilation
            .ok_or(RenderError::InvalidRecord("assessment without compilation"))?;
        if assessment.checks.len() != compilation.checks.len() {
            return Err(RenderError::InvalidRecord("assessment check inventory"));
        }
    }
    let publication = report
        .compilation
        .map(publication::Publication::collect)
        .transpose()?;
    let mut j = Json::new(report.limits.output_bytes, matches!(view, View::Human));
    if matches!(view, View::Human) {
        j.raw("Weft local review — not Writfold-grounded; no effect authority.\n")?;
    }
    envelope::envelope(&mut j, report, publication.as_ref())?;
    j.raw("\n")?;
    Ok(j.finish())
}
