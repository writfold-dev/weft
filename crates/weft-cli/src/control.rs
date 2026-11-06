//! `weft control`: exercise the real control client against a supplied
//! owner-pinned writfold executable and report transport identity only.

use crate::input;
use std::{path::Path, time::Duration};
use weft_domain::Limits;
use weft_wire::{
    View,
    control::{self, FailureView, SessionView},
};

const CONTROL_TIMEOUT: Duration = Duration::from_secs(30);
pub(crate) fn run(program: &str, expect_sha256: Option<&str>, view: View, limits: &Limits) -> u8 {
    let observed = input::load(Path::new(program), BINARY_BYTE_BOUND);
    let binary_sha256 = match observed {
        Ok(loaded) => {
            let digest = &loaded.sha256;
            if let Some(expected) = expect_sha256
                && expected != digest
            {
                return failure(
                    program,
                    None,
                    &format!(
                        "executable SHA-256 {digest} does not match the expected pin {expected}"
                    ),
                    view,
                    limits,
                );
            }
            digest.clone()
        }
        Err(diagnostic) => {
            return failure(program, None, &diagnostic.message, view, limits);
        }
    };
    match session(program) {
        Ok(completed) => {
            let rendered = control::render_session(
                &SessionView {
                    command: program,
                    binary_sha256: Some(&binary_sha256),
                    instance: &completed.shutdown.session().instance,
                    incarnation: &completed.shutdown.session().incarnation,
                    server_version: &completed.server_version,
                    contract_sha256: &completed.contract_sha256,
                    initialize_generation: completed.initialize_generation,
                    shutdown_generation: completed.shutdown.generation,
                    exit_code: completed.exit_code,
                },
                view,
                limits.output_bytes,
            );
            match rendered {
                Ok(bytes) => crate::run::write_out(&bytes, 0),
                Err(_) => 2,
            }
        }
        Err(reason) => failure(program, Some(&binary_sha256), &reason, view, limits),
    }
}
/// The pinned static server is ~0.6 MiB; anything beyond this bound is not
/// the pinned artifact shape and is refused before spawning.
const BINARY_BYTE_BOUND: usize = 8 * 1024 * 1024;
fn session(program: &str) -> Result<CompletedView, String> {
    let mut client = weft_writfold::Client::spawn(program, "serve", CONTROL_TIMEOUT)
        .map_err(|error| error.to_string())?;
    let admission = client.initialize(&[]).map_err(|error| error.to_string())?;
    let initialize_generation = admission.generation();
    let server_version = admission.server_version().to_string();
    let contract_sha256 = admission.contract_sha256().to_string();
    let completed = client.shutdown().map_err(|error| error.to_string())?;
    Ok(CompletedView {
        shutdown: completed.shutdown,
        exit_code: completed.exit_code,
        initialize_generation,
        server_version,
        contract_sha256,
    })
}
struct CompletedView {
    shutdown: weft_wire::rpc::ShutdownResult,
    exit_code: u64,
    initialize_generation: u64,
    server_version: String,
    contract_sha256: String,
}
fn failure(
    program: &str,
    binary_sha256: Option<&str>,
    reason: &str,
    view: View,
    limits: &Limits,
) -> u8 {
    let rendered = control::render_failure(
        &FailureView {
            command: program,
            binary_sha256,
            reason,
        },
        view,
        limits.output_bytes,
    );
    match rendered {
        Ok(bytes) => crate::run::write_out(&bytes, 2),
        Err(_) => 2,
    }
}
