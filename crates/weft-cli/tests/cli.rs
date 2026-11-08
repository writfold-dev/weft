#![forbid(unsafe_code)]

use serde_json::Value;
use std::{
    error::Error,
    fs,
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);
struct Fixture {
    directory: PathBuf,
}
impl Fixture {
    fn new() -> Result<Self, Box<dyn Error>> {
        let directory = std::env::temp_dir().join(format!(
            "weft-cli-test-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory)?;
        Ok(Self { directory })
    }
    fn file(&self, name: &str, bytes: &[u8]) -> Result<PathBuf, Box<dyn Error>> {
        let path = self.directory.join(name);
        fs::write(&path, bytes)?;
        Ok(path)
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}
fn cli(arguments: &[&std::ffi::OsStr]) -> Result<Output, Box<dyn Error>> {
    Ok(Command::new(env!("CARGO_BIN_EXE_weft"))
        .args(arguments)
        .output()?)
}
fn source(body: &str) -> String {
    format!(
        "review test {{ context \"ctx\" at \"cut\"; profile \"weft.symbolic/1\"; target plan = proposal \"plan\"; {body} }}"
    )
}
#[test]
fn invalid_encoding_keeps_exact_hex_and_real_digest() -> Result<(), Box<dyn Error>> {
    let fixture = Fixture::new()?;
    let bytes = [0xff, 0x1b, 0, 0xc0];
    let path = fixture.file("invalid.weft", &bytes)?;
    let output = cli(&["analyze".as_ref(), path.as_os_str()])?;
    assert_eq!(output.status.code(), Some(2));
    let report: Value = serde_json::from_slice(&output.stdout)?;
    assert_eq!(report["source"]["content"]["hex"], "ff1b00c0");
    assert_eq!(report["source"]["bytes"], 4);
    assert_eq!(
        report["source"]["sha256"],
        "79526bc4285ce6d6ec3040a83ef2c36b7f8d2ee7f90096541bacbb50d8cef82f"
    );
    assert!(report["diagnostics"][0].get("primary").is_none());
    Ok(())
}
#[test]
fn unavailable_and_oversized_files_never_receive_digest() -> Result<(), Box<dyn Error>> {
    let fixture = Fixture::new()?;
    let missing = fixture.directory.join("missing.weft");
    let output = cli(&["prove".as_ref(), missing.as_os_str()])?;
    assert_eq!(output.status.code(), Some(2));
    let report: Value = serde_json::from_slice(&output.stdout)?;
    assert_eq!(report["source"]["kind"], "unavailable");
    assert!(report["source"].get("sha256").is_none());
    let large = fixture.file("large.weft", b"")?;
    fs::OpenOptions::new()
        .write(true)
        .open(&large)?
        .set_len(1_048_577)?;
    let output = cli(&["analyze".as_ref(), large.as_os_str()])?;
    assert_eq!(output.status.code(), Some(2));
    let report: Value = serde_json::from_slice(&output.stdout)?;
    assert_eq!(report["execution"], "incomplete");
    assert!(report["source"].get("sha256").is_none());
    Ok(())
}
#[test]
fn mixed_findings_and_invalid_assumption_remain_distinct() -> Result<(), Box<dyn Error>> {
    let fixture = Fixture::new()?;
    let text = source("check before: true; assume broken: missing.field == 1; check after: true;");
    let path = fixture.file("mixed.weft", text.as_bytes())?;
    let output = cli(&["prove".as_ref(), path.as_os_str()])?;
    assert_eq!(output.status.code(), Some(2));
    let report: Value = serde_json::from_slice(&output.stdout)?;
    assert_eq!(report["checks"][0]["result"], "entailed");
    assert_eq!(report["checks"][1]["result"], "not-evaluated");
    assert_eq!(report["writfold_grounded"], false);
    assert_eq!(report["effect_authority"], false);
    Ok(())
}
#[test]
fn complete_local_proof_is_never_grounded_success() -> Result<(), Box<dyn Error>> {
    let fixture = Fixture::new()?;
    let path = fixture.file("proof.weft", source("check theorem: true;").as_bytes())?;
    assert_eq!(
        cli(&["analyze".as_ref(), path.as_os_str()])?.status.code(),
        Some(0)
    );
    let output = cli(&["prove".as_ref(), path.as_os_str()])?;
    assert_eq!(output.status.code(), Some(1));
    let report: Value = serde_json::from_slice(&output.stdout)?;
    assert_eq!(report["checks"][0]["result"], "entailed");
    assert_eq!(report["checks"][0]["basis"], "hypothetical");
    let needed = fixture.file(
        "needed.weft",
        source("claim evidence = citation \"opaque\"; need evidence; check theorem: true;")
            .as_bytes(),
    )?;
    let output = cli(&["prove".as_ref(), needed.as_os_str()])?;
    assert_eq!(output.status.code(), Some(2));
    let report: Value = serde_json::from_slice(&output.stdout)?;
    assert_eq!(report["checks"][0]["result"], "entailed");
    assert!(
        !report["review"]["needs"]
            .as_array()
            .ok_or("needs")?
            .is_empty()
    );
    Ok(())
}
#[test]
fn output_limit_replaces_the_whole_report_with_source_bound_diagnostic()
-> Result<(), Box<dyn Error>> {
    use std::fmt::Write;
    let fixture = Fixture::new()?;
    let mut body = String::new();
    for index in 0..16 {
        write!(&mut body, "assume h{index}: p{index}(); ")?;
    }
    body.push_str("check theorem: true;");
    let text = source(&body);
    let path = fixture.file("large-report.weft", text.as_bytes())?;
    let output = cli(&["prove".as_ref(), path.as_os_str()])?;
    assert_eq!(output.status.code(), Some(2));
    let report: Value = serde_json::from_slice(&output.stdout)?;
    assert_eq!(report["kind"], "diagnostics");
    assert_eq!(report["execution"], "incomplete");
    assert_eq!(report["source"]["content"]["text"], text);
    assert_eq!(report["diagnostics"][0]["phase"], "report");
    assert!(report["checks"].as_array().ok_or("checks")?.is_empty());
    assert!(report["trace"].as_array().ok_or("trace")?.is_empty());
    Ok(())
}
#[test]
fn reuse_parses_reports_beyond_transport_node_bound() -> Result<(), Box<dyn Error>> {
    let fixture = Fixture::new()?;
    let path = fixture.file("proof.weft", source("check theorem: true;").as_bytes())?;
    let output = cli(&["prove".as_ref(), path.as_os_str()])?;
    let mut report: Value = serde_json::from_slice(&output.stdout)?;
    let plain = fixture.file("plain.json", &output.stdout)?;
    let baseline = cli(&["reuse".as_ref(), plain.as_os_str(), path.as_os_str()])?;
    let padding = vec![Value::Null; 70_000];
    report
        .as_object_mut()
        .ok_or("report object")?
        .insert("padding".into(), Value::Array(padding));
    let large = fixture.file("large.json", &serde_json::to_vec(&report)?)?;
    let padded = cli(&["reuse".as_ref(), large.as_os_str(), path.as_os_str()])?;
    assert_eq!(padded.status.code(), baseline.status.code());
    assert_ne!(padded.status.code(), Some(2));
    Ok(())
}
