#![forbid(unsafe_code)]
mod args;
mod control;
mod input;
mod reuse;
mod run;

use std::{
    io::{self, Write},
    process::ExitCode,
};
use weft_domain::Limits;
use weft_wire::{Command, Source, View};

fn main() -> ExitCode {
    let limits = Limits::default();
    let code = match args::parse(std::env::args_os().skip(1)) {
        Ok(args::Arguments::Review {
            command,
            path,
            view,
        }) => run::file(command, &path, view, &limits),
        Ok(args::Arguments::Reuse {
            report,
            source,
            view,
        }) => reuse::run(&report, &source, view, &limits),
        Ok(args::Arguments::Control {
            program,
            expect_sha256,
            view,
        }) => control::run(&program, expect_sha256.as_deref(), view, &limits),
        Ok(args::Arguments::Version) => version(),
        Ok(args::Arguments::Help) => {
            if writeln!(io::stdout().lock(), "{}", args::USAGE).is_ok() {
                0
            } else {
                2
            }
        }
        Err(diagnostic) => run::failure(
            Command::Analyze,
            Source::Unavailable {
                path: None,
                reason: "No source was loaded because the command arguments are invalid",
            },
            diagnostic,
            View::Json,
            &limits,
        ),
    };
    ExitCode::from(code)
}
fn version() -> u8 {
    let identity = match option_env!("WEFT_SOURCE_SHA256") {
        Some(digest) if digest.len() == 64 && digest.bytes().all(|b| b.is_ascii_hexdigit()) => {
            format!("build-source-sha256={digest} (build-supplied, not qualification)")
        }
        Some(_) => "build-source=unbound (invalid supplied digest)".into(),
        None => "build-source=unbound (development build)".into(),
    };
    if writeln!(io::stdout().lock(), "weft {}\nprofile=weft.symbolic/1\n{identity}\nwritfold_grounded=false effect_authority=false\nFull Writfold release flow remains externally blocked.", env!("CARGO_PKG_VERSION")).is_ok() { 0 } else { 2 }
}
