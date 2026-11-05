#![forbid(unsafe_code)]

use serde::Serialize;
use std::{
    env, fs,
    io::{self, Write},
    process::ExitCode,
};
use weft_quality::{Policy, Report, check_dependencies, check_source, workspace};

const USAGE: &str = "weft-quality --metadata <cargo-metadata.json> [--nominal <Type>]\n\
  weft-quality --crate <name> [--dependency <package>] [--nominal <Type>] <root.rs>...\n\
Emits deterministic JSON. Exit 0: no errors; 1: policy errors; 2: input/output failure.\n\
Explicit-source mode checks only listed crate roots and declared dependencies.\n\
Metadata mode scans every workspace member's Rust sources, including cfg/test code.\n\
Warnings do not fail. Source positions use one-based lines and zero-based columns.";

#[derive(Default)]
struct Arguments {
    metadata: Option<String>,
    crate_name: Option<String>,
    dependencies: Vec<String>,
    nominal_types: Vec<String>,
    sources: Vec<String>,
}

#[derive(Serialize)]
struct Envelope {
    schema: &'static str,
    mode: &'static str,
    report: Option<Report>,
    input_error: Option<String>,
}

fn main() -> ExitCode {
    let result = run(env::args().skip(1));
    let (envelope, status) = match result {
        Ok(None) => return ExitCode::SUCCESS,
        Ok(Some((report, mode))) => {
            let status = if report.failed() { 1 } else { 0 };
            (
                Envelope {
                    schema: "weft-quality/1",
                    mode,
                    report: Some(report),
                    input_error: None,
                },
                status,
            )
        }
        Err(error) => (
            Envelope {
                schema: "weft-quality/1",
                mode: "input_error",
                report: None,
                input_error: Some(error),
            },
            2,
        ),
    };
    let stdout = io::stdout();
    let mut output = stdout.lock();
    if serde_json::to_writer_pretty(&mut output, &envelope).is_err()
        || output.write_all(b"\n").is_err()
    {
        return ExitCode::from(2);
    }
    ExitCode::from(status)
}

fn run(arguments: impl Iterator<Item = String>) -> Result<Option<(Report, &'static str)>, String> {
    let mut arguments = arguments.peekable();
    if arguments
        .peek()
        .is_some_and(|argument| argument == "--help" || argument == "-h")
    {
        io::stdout()
            .write_all(format!("{USAGE}\n").as_bytes())
            .map_err(|error| error.to_string())?;
        return Ok(None);
    }
    let args = parse(arguments)?;
    if let Some(path) = &args.metadata {
        if args.crate_name.is_some() || !args.sources.is_empty() || !args.dependencies.is_empty() {
            return Err("--metadata cannot be combined with explicit-source mode".into());
        }
        let json = fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?;
        return workspace::check_metadata_json(&json, &args.nominal_types)
            .map(|report| Some((report, "workspace_metadata")));
    }
    let name = args
        .crate_name
        .ok_or_else(|| format!("missing --crate or --metadata\n{USAGE}"))?;
    if args.sources.is_empty() {
        return Err("explicit-source mode requires at least one crate root".into());
    }
    let mut policy = Policy::new(name);
    policy.nominal_types = args.nominal_types;
    let mut report = check_dependencies(&policy, "<explicit-dependencies>", &args.dependencies);
    for path in args.sources {
        let source = fs::read_to_string(&path).map_err(|error| format!("{path}: {error}"))?;
        report.append(check_source(&policy, &path, &source, true));
    }
    Ok(Some((report, "explicit_sources")))
}

fn parse(mut arguments: impl Iterator<Item = String>) -> Result<Arguments, String> {
    let mut result = Arguments::default();
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--metadata" => set_once(
                &mut result.metadata,
                value(&mut arguments, &argument)?,
                &argument,
            )?,
            "--crate" => set_once(
                &mut result.crate_name,
                value(&mut arguments, &argument)?,
                &argument,
            )?,
            "--dependency" => result.dependencies.push(value(&mut arguments, &argument)?),
            "--nominal" => result.nominal_types.push(value(&mut arguments, &argument)?),
            "--" => {
                result.sources.extend(arguments);
                break;
            }
            flag if flag.starts_with('-') => return Err(format!("unknown option {flag}")),
            _ => result.sources.push(argument),
        }
    }
    result.sources.sort();
    result.sources.dedup();
    Ok(result)
}

fn value(arguments: &mut impl Iterator<Item = String>, flag: &str) -> Result<String, String> {
    let value = arguments
        .next()
        .ok_or_else(|| format!("{flag} requires a value"))?;
    if value.is_empty() || value.starts_with('-') {
        return Err(format!("{flag} requires a non-option value"));
    }
    Ok(value)
}

fn set_once(slot: &mut Option<String>, value: String, flag: &str) -> Result<(), String> {
    if slot.is_some() {
        return Err(format!("duplicate {flag}"));
    }
    *slot = Some(value);
    Ok(())
}
