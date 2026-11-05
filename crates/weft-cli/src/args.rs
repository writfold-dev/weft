use std::ffi::OsString;
use weft_domain::{Code, Diagnostic, Phase};
use weft_wire::{Command, View};

pub(crate) const USAGE: &str = "Usage: weft analyze FILE [--json|--human]\n       weft prove FILE [--json|--human]\n       weft --version\nUse -- before a filename beginning with '-'. JSON is the default.\nAnalyze checks local structure; prove is hypothetical and never grants effect authority.\nLive check/admit/run commands are unavailable pending owner-published Writfold services.";
pub(crate) enum Arguments {
    Version,
    Help,
    Review {
        command: Command,
        path: String,
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
    let command = match first {
        "analyze" => Command::Analyze,
        "prove" => Command::Prove,
        _ => {
            return Err(invalid(
                "Unknown command; expected analyze, prove, or --version",
            ));
        }
    };
    review(command, arguments)
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
        let argument = argument.into_string().map_err(|_| {
            invalid("Arguments and source paths must be UTF-8; no lossy replacement is used")
        })?;
        if !positional && argument == "--" {
            positional = true;
            continue;
        }
        if !positional && (argument == "--human" || argument == "--json") {
            if selected_view {
                return Err(invalid("Select exactly one output view"));
            }
            selected_view = true;
            view = if argument == "--human" {
                View::Human
            } else {
                View::Json
            };
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
fn invalid(message: &str) -> Diagnostic {
    let mut diagnostic = Diagnostic::new(Code::InvalidArguments, Phase::Input, message, None);
    diagnostic.help = Some(USAGE.into());
    diagnostic
}
