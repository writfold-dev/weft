#![forbid(unsafe_code)]

use serde_json::Value;
use std::error::Error;
use weft_domain::{Code, Diagnostic, Limits, Phase};
use weft_wire::{Command, Report, Source, View};

#[test]
fn invalid_utf8_is_exact_hex_without_fabricated_span_or_digest() -> Result<(), Box<dyn Error>> {
    let limits = Limits::default();
    let diagnostic = Diagnostic::new(Code::InvalidUtf8, Phase::Input, "invalid encoding", None);
    let digest = "561b0edd0770bff8f6840475753f0f6c9da34a3cc69c097929a39318f2ee0255";
    let report = Report {
        command: Command::Analyze,
        source: Source::Loaded {
            path: "source",
            sha256: digest,
            bytes: &[0xff, 0, 0xc0],
        },
        analysis: None,
        compilation: None,
        assessment: None,
        diagnostics: &[diagnostic],
        limits: &limits,
    };
    let json: Value = serde_json::from_slice(&weft_wire::render(&report, View::Json)?)?;
    assert_eq!(json["source"]["content"]["hex"], "ff00c0");
    assert!(json["diagnostics"][0].get("primary").is_none());
    let missing = Report {
        source: Source::Unavailable {
            path: Some("missing"),
            reason: "not read",
        },
        ..report
    };
    let json: Value = serde_json::from_slice(&weft_wire::render(&missing, View::Json)?)?;
    assert!(json["source"].get("sha256").is_none());
    Ok(())
}
#[test]
fn human_view_preserves_data_and_escapes_terminal_controls() -> Result<(), Box<dyn Error>> {
    let limits = Limits::default();
    let diagnostic = Diagnostic::new(
        Code::InvalidArguments,
        Phase::Input,
        "\u{1b}]0;owned\u{7}\u{9b}\u{202e}",
        None,
    );
    let report = Report {
        command: Command::Analyze,
        source: Source::Unavailable {
            path: Some("evil\nname"),
            reason: "not read",
        },
        analysis: None,
        compilation: None,
        assessment: None,
        diagnostics: &[diagnostic],
        limits: &limits,
    };
    let human = String::from_utf8(weft_wire::render(&report, View::Human)?)?;
    assert!(!human.contains(['\u{1b}', '\u{7}', '\u{9b}', '\u{202e}']));
    let (_, object) = human.split_once('\n').ok_or("missing human header")?;
    let projected: Value = serde_json::from_str(object)?;
    let machine: Value = serde_json::from_slice(&weft_wire::render(&report, View::Json)?)?;
    assert_eq!(projected, machine);
    Ok(())
}
