use crate::input;
use std::{
    io::{self, Write},
    path::Path,
};
use weft_domain::{Code, Diagnostic, Limits, Phase};
use weft_wire::{Command, Report, Source, View};

pub(crate) fn file(command: Command, path: &str, view: View, limits: &Limits) -> u8 {
    let loaded = match input::load(Path::new(path), limits.source_bytes) {
        Ok(loaded) => loaded,
        Err(diagnostic) => {
            let reason = diagnostic.message.clone();
            return failure(
                command,
                Source::Unavailable {
                    path: Some(path),
                    reason: &reason,
                },
                diagnostic,
                view,
                limits,
            );
        }
    };
    let source = Source::Loaded {
        path,
        sha256: &loaded.sha256,
        bytes: &loaded.bytes,
    };
    let text = match std::str::from_utf8(&loaded.bytes) {
        Ok(text) => text,
        Err(error) => {
            let mut diagnostic = Diagnostic::new(
                Code::InvalidUtf8,
                Phase::Input,
                "Source is not UTF-8; exact bytes are retained as hex and no replacement-decoded spans are created",
                None,
            );
            diagnostic.actual =
                Some(format!("invalid UTF-8 at byte {}", error.valid_up_to()).into_boxed_str());
            diagnostic.help = Some("Save the source as valid UTF-8".into());
            return failure(command, source, diagnostic, view, limits);
        }
    };
    match command {
        Command::Analyze => {
            let analysis = weft_frontend::analyze(text, limits);
            emit(
                &Report {
                    command,
                    source,
                    analysis: Some(&analysis),
                    compilation: None,
                    assessment: None,
                    diagnostics: &[],
                    limits,
                },
                view,
            )
        }
        Command::Prove => prove(text, source, view, limits),
    }
}
fn prove(text: &str, source: Source<'_>, view: View, limits: &Limits) -> u8 {
    let compilation = match weft_frontend::compile(text, limits) {
        Ok(compilation) => compilation,
        Err(analysis) => {
            return emit(
                &Report {
                    command: Command::Prove,
                    source,
                    analysis: Some(&analysis),
                    compilation: None,
                    assessment: None,
                    diagnostics: &[],
                    limits,
                },
                view,
            );
        }
    };
    match weft_kernel::assess(&compilation, limits) {
        Ok(assessment) => emit(
            &Report {
                command: Command::Prove,
                source,
                analysis: Some(&compilation.analysis),
                compilation: Some(&compilation),
                assessment: Some(&assessment),
                diagnostics: &[],
                limits,
            },
            view,
        ),
        Err(diagnostic) => emit(
            &Report {
                command: Command::Prove,
                source,
                analysis: Some(&compilation.analysis),
                compilation: Some(&compilation),
                assessment: None,
                diagnostics: &[diagnostic],
                limits,
            },
            view,
        ),
    }
}
pub(crate) fn failure(
    command: Command,
    source: Source<'_>,
    diagnostic: Diagnostic,
    view: View,
    limits: &Limits,
) -> u8 {
    emit(
        &Report {
            command,
            source,
            analysis: None,
            compilation: None,
            assessment: None,
            diagnostics: &[diagnostic],
            limits,
        },
        view,
    )
}
fn emit(report: &Report<'_>, view: View) -> u8 {
    match weft_wire::render(report, view) {
        Ok(bytes) => output(&bytes, report.exit_code()),
        Err(error) => {
            let diagnostic = match error {
                weft_wire::RenderError::OutputLimit => Diagnostic::new(
                    Code::LimitExceeded,
                    Phase::Report,
                    "The complete report exceeds the output byte bound. Findings and trace are omitted, not truncated or certified complete; this diagnostic retains the exact source",
                    None,
                ),
                weft_wire::RenderError::InvalidRecord(reason) => Diagnostic::new(
                    Code::InvalidProgram,
                    Phase::Report,
                    format!("Report projection rejected an inconsistent record: {reason}"),
                    None,
                ),
            };
            let fallback = Report {
                command: report.command,
                source: report.source,
                analysis: None,
                compilation: None,
                assessment: None,
                diagnostics: &[diagnostic],
                limits: report.limits,
            };
            match weft_wire::render(&fallback, view) {
                Ok(bytes) => output(&bytes, 2),
                Err(_) => {
                    let _ = writeln!(
                        io::stderr().lock(),
                        "weft: no complete source-bound diagnostic fits the report bound; stdout is empty"
                    );
                    2
                }
            }
        }
    }
}
fn output(bytes: &[u8], code: u8) -> u8 {
    let mut stdout = io::stdout().lock();
    if stdout
        .write_all(bytes)
        .and_then(|()| stdout.flush())
        .is_err()
    {
        let _ = writeln!(
            io::stderr().lock(),
            "weft: output unavailable; delivery of the complete report failed"
        );
        2
    } else {
        code
    }
}
