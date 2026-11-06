use std::ffi::OsString;
use weft_domain::{Code, Diagnostic, Phase};
use weft_wire::{Command, View};

pub(crate) const USAGE: &str = "Usage: weft analyze FILE [--json|--human]\n\
       weft prove FILE [--json|--human]\n\
       weft reuse REPORT SOURCE [--json|--human]\n\
       weft control WRITFOLD_BIN [--expect-sha256 HEX] [--json|--human]\n\
       weft --version\n\
Use -- before a filename beginning with '-'. JSON is the default.\n\
Analyze checks local structure; prove is hypothetical and never grants effect authority.\n\
Reuse decides prior-report scope equality locally; control exercises the pinned\n\
writfold.agent/1 transport contract only and grounds nothing.\n\
Live citation/assessment/retention/effect commands remain unavailable pending\n\
owner-published Writfold data services.";
pub(crate) enum Arguments {
    Version,
    Help,
    Review {
        command: Command,
        path: String,
        view: View,
    },
    Reuse {
        report: String,
        source: String,
        view: View,
    },
    Control {
        program: String,
        expect_sha256: Option<String>,
        view: View,
    },
}
pub(crate) fn parse(
    arguments: impl IntoIterator<Item = OsString>,
) -> Result<Arguments, Diagnostic> {
    let mut arguments = arguments.into_iter();
    let first = arguments.next().ok_or_else(|| invalid("Missing command"))?;
    let first = first
        .to_str()
        .ok_or_else(|| invalid("Command must be UTF-8"))?;
    if first == "--version" || first == "--help" || first == "-h" {
        if arguments.next().is_some() {
            return Err(invalid("This option accepts no additional arguments"));
        }
        return Ok(if first == "--version" {
            Arguments::Version
        } else {
            Arguments::Help
        });
    }
    match first {
        "analyze" => review(Command::Analyze, arguments),
        "prove" => review(Command::Prove, arguments),
        "reuse" => reuse(arguments),
        "control" => control(arguments),
        _ => Err(invalid(
            "Unknown command; expected analyze, prove, reuse, control, or --version",
        )),
    }
}
fn review(
    command: Command,
    arguments: impl Iterator<Item = OsString>,
) -> Result<Arguments, Diagnostic> {
    let mut path = None;
    let mut view = View::Json;
    let mut selected_view = false;
    let mut positional = false;
    for argument in arguments {
        let argument = utf8(argument)?;
        if !positional && argument == "--" {
            positional = true;
            continue;
        }
        if !positional && (argument == "--human" || argument == "--json") {
            view = view_once(selected_view, &argument)?;
            selected_view = true;
        } else if !positional && argument.starts_with('-') {
            return Err(invalid(
                "Unknown option; use --human or --json, or -- before a filename beginning with '-'",
            ));
        } else if path.replace(argument).is_some() {
            return Err(invalid(
                "Expected one source file, not multiple positional arguments",
            ));
        }
    }
    let path = path.ok_or_else(|| invalid("Missing source file"))?;
    Ok(Arguments::Review {
        command,
        path,
        view,
    })
}
fn reuse(arguments: impl Iterator<Item = OsString>) -> Result<Arguments, Diagnostic> {
    let mut paths: Vec<String> = Vec::new();
    let mut view = View::Json;
    let mut selected_view = false;
    let mut positional = false;
    for argument in arguments {
        let argument = utf8(argument)?;
        if !positional && argument == "--" {
            positional = true;
            continue;
        }
        if !positional && (argument == "--human" || argument == "--json") {
            view = view_once(selected_view, &argument)?;
            selected_view = true;
        } else if !positional && argument.starts_with('-') {
            return Err(invalid("Unknown option; use --human or --json"));
        } else if paths.len() == 2 {
            return Err(invalid("Expected exactly report and source paths"));
        } else {
            paths.push(argument);
        }
    }
    if paths.len() != 2 {
        return Err(invalid("Expected exactly report and source paths"));
    }
    let report = paths.remove(0);
    let source = paths.remove(0);
    Ok(Arguments::Reuse {
        report,
        source,
        view,
    })
}
fn control(arguments: impl Iterator<Item = OsString>) -> Result<Arguments, Diagnostic> {
    let mut program = None;
    let mut expect_sha256 = None;
    let mut view = View::Json;
    let mut selected_view = false;
    let mut positional = false;
    let mut pending_digest = false;
    for argument in arguments {
        let argument = utf8(argument)?;
        if pending_digest {
            if valid_digest(&argument).is_none() {
                return Err(invalid(
                    "Expected a lowercase 64-character hex SHA-256 after --expect-sha256",
                ));
            }
            if expect_sha256.replace(argument).is_some() {
                return Err(invalid("Select exactly one expected digest"));
            }
            pending_digest = false;
            continue;
        }
        if !positional && argument == "--" {
            positional = true;
            continue;
        }
        if !positional && argument == "--expect-sha256" {
            pending_digest = true;
            continue;
        }
        if !positional && argument.starts_with("--expect-sha256=") {
            let value = argument
                .strip_prefix("--expect-sha256=")
                .unwrap_or_default();
            if valid_digest(value).is_none() {
                return Err(invalid(
                    "Expected a lowercase 64-character hex SHA-256 after --expect-sha256=",
                ));
            }
            if expect_sha256.replace(value.to_string()).is_some() {
                return Err(invalid("Select exactly one expected digest"));
            }
            continue;
        }
        if !positional && (argument == "--human" || argument == "--json") {
            view = view_once(selected_view, &argument)?;
            selected_view = true;
        } else if !positional && argument.starts_with('-') {
            return Err(invalid(
                "Unknown option; use --expect-sha256 HEX and --human or --json",
            ));
        } else if program.replace(argument).is_some() {
            return Err(invalid("Expected exactly one writfold executable path"));
        }
    }
    if pending_digest {
        return Err(invalid(
            "Missing value; --expect-sha256 takes one lowercase 64-hex digest",
        ));
    }
    let program = program.ok_or_else(|| invalid("Missing writfold executable path"))?;
    Ok(Arguments::Control {
        program,
        expect_sha256,
        view,
    })
}
fn view_once(selected: bool, argument: &str) -> Result<View, Diagnostic> {
    if selected {
        return Err(invalid("Select exactly one output view"));
    }
    Ok(if argument == "--human" {
        View::Human
    } else {
        View::Json
    })
}
fn utf8(argument: OsString) -> Result<String, Diagnostic> {
    argument.into_string().map_err(|_| {
        invalid("Arguments and source paths must be UTF-8; no lossy replacement is used")
    })
}
fn valid_digest(value: &str) -> Option<()> {
    (value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)))
    .then_some(())
}
fn invalid(message: &str) -> Diagnostic {
    let mut diagnostic = Diagnostic::new(Code::InvalidArguments, Phase::Input, message, None);
    diagnostic.help = Some(USAGE.into());
    diagnostic
}
