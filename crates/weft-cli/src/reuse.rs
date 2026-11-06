//! `weft reuse`: decide whether a prior local report's recorded scope still
//! applies to an exact candidate source. Refusal names every difference.

use crate::input;
use std::path::Path;
use weft_domain::{Code, Diagnostic, Limits, Phase};
use weft_wire::{
    View,
    reuse::{self, Decision, Difference, PriorError, PriorScope, ReuseView},
};

pub(crate) fn run(report: &str, source: &str, view: View, limits: &Limits) -> u8 {
    let loaded_report = match input::load(Path::new(report), limits.output_bytes) {
        Ok(loaded) => loaded,
        Err(diagnostic) => return malformed(report, source, diagnostic, view, limits),
    };
    let loaded_source = match input::load(Path::new(source), limits.source_bytes) {
        Ok(loaded) => loaded,
        Err(diagnostic) => return malformed(report, source, diagnostic, view, limits),
    };
    let (prior, decision) = match PriorScope::parse(&loaded_report.bytes) {
        Ok(prior) => {
            let decision = prior.compare(&loaded_source.sha256, limits);
            (Some(prior), decision)
        }
        Err(PriorError::NoReusableScope) => (
            None,
            Decision::Refused {
                differences: vec![Difference {
                    field: "review",
                    expected: "a report that records its review scope".into(),
                    observed: "no reusable review scope".into(),
                }],
            },
        ),
        Err(error) => {
            let mut diagnostic = Diagnostic::new(
                Code::InvalidArguments,
                Phase::Input,
                error.to_string(),
                None,
            );
            diagnostic.help =
                Some("Reuse needs a prior weft report/1 artifact with recorded scope".into());
            return malformed(report, source, diagnostic, view, limits);
        }
    };
    let rendered = reuse::render_decision(
        &ReuseView {
            report_path: report,
            report_sha256: &loaded_report.sha256,
            candidate_path: source,
            candidate_sha256: &loaded_source.sha256,
            prior: prior.as_ref(),
            decision: &decision,
        },
        view,
        limits.output_bytes,
    );
    match rendered {
        Ok(bytes) => {
            let code = match decision {
                Decision::Reusable => 0,
                Decision::Refused { .. } => 1,
            };
            crate::run::write_out(&bytes, code)
        }
        Err(_) => 2,
    }
}
fn malformed(
    report: &str,
    source: &str,
    diagnostic: Diagnostic,
    view: View,
    limits: &Limits,
) -> u8 {
    let reason = diagnostic.message.clone();
    let rendered = reuse::render_failure(
        &reuse::FailureView {
            report_path: report,
            candidate_path: source,
            reason: &reason,
        },
        view,
        limits.output_bytes,
    );
    match rendered {
        Ok(bytes) => crate::run::write_out(&bytes, 2),
        Err(_) => 2,
    }
}
