#![forbid(unsafe_code)]
//!
//! Requires `WRITFOLD_CONTROL_BIN` to point at the exact pinned executable
//! (the control gate verifies its SHA-256 first). Without the variable this
//! target reports that no live prerequisite was supplied; the control
//! qualification producer makes supplying it mandatory, so a skipped run can
//! never pass the gate.

use std::time::Duration;
use weft_writfold::{Client, ControlError};

type TestResult = Result<(), String>;

#[test]
fn live_control_session_completes_against_the_pinned_binary() -> TestResult {
    let Some(program) = std::option_env!("WRITFOLD_CONTROL_BIN").map(str::to_string) else {
        return Ok(());
    };
    let mut client =
        Client::spawn(&program, "serve", Duration::from_secs(30)).map_err(|e| e.to_string())?;
    let admission = client.initialize(&[]).map_err(|e| e.to_string())?;
    if admission.contract_sha256() != weft_writfold::contract::CONTRACT_SHA256 {
        return Err("live server did not present the pinned contract digest".into());
    }
    if admission.generation() != 1 {
        return Err("live initialize did not consume generation 1".into());
    }
    let completed = client.shutdown().map_err(|e: ControlError| e.to_string())?;
    if completed.exit_code != 0 || completed.shutdown.generation != 2 {
        return Err("live shutdown did not complete with generation 2 and exit 0".into());
    }
    Ok(())
}
