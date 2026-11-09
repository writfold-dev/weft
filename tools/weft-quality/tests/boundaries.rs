#![forbid(unsafe_code)]

use weft_quality::{Policy, check_dependencies, check_source, workspace};

#[test]
fn core_serde_any_json_and_io_are_rejected() {
    for item in [
        "use serde::Deserialize;",
        "#[derive(serde::Serialize)] struct Value;",
        "type Data = serde_json::Value;",
        "fn f(x: &dyn std::any::Any) {}",
        "use std::{fs, time::Instant};",
        "use std as platform; fn f() { platform::fs::read(\"x\"); }",
        "fn f() { println!(\"IO\"); }",
        "fn f() { let _ = env!(\"HOME\"); }",
        "fn f() { tokio::spawn(work()); }",
        "use std::*;",
        "wrapper!(serde_json::Value);",
    ] {
        let source = format!("#![forbid(unsafe_code)]\n{item}");
        for package in ["weft-core", "weft-domain", "weft-frontend", "weft-kernel"] {
            let report = check_source(&Policy::new(package), "core.rs", &source, true);
            assert!(report.failed(), "accepted {item} in {package}");
        }
    }
}

#[test]
fn wire_json_cli_io_and_client_stdio_are_admitted() {
    for (package, item) in [
        (
            "weft-wire",
            "use serde_json::Value; #[derive(serde::Deserialize)] struct Dto { value: Value }",
        ),
        ("weft-cli", "fn f() { let _ = std::fs::read(\"source\"); }"),
        (
            "weft-writfold",
            "fn f() { let _ = std::process::Command::new(\"client\"); }",
        ),
    ] {
        let source = format!("#![forbid(unsafe_code)]\n{item}");
        assert!(!check_source(&Policy::new(package), "admitted.rs", &source, true).failed());
    }
}

#[test]
fn client_network_and_wire_io_are_rejected() {
    for (package, item) in [
        ("weft-writfold", "use std::net::TcpStream;"),
        ("weft-wire", "use std::fs;"),
    ] {
        let source = format!("#![forbid(unsafe_code)]\n{item}");
        assert!(check_source(&Policy::new(package), "io.rs", &source, true).failed());
    }
}

#[test]
fn all_internal_dependency_directions_are_calibrated() {
    let crates = [
        "weft-core",
        "weft-domain",
        "weft-frontend",
        "weft-kernel",
        "weft-wire",
        "weft-writfold",
        "weft-cli",
    ];
    let allowed = [
        ("weft-domain", "weft-core"),
        ("weft-frontend", "weft-domain"),
        ("weft-kernel", "weft-core"),
        ("weft-kernel", "weft-domain"),
        ("weft-wire", "weft-core"),
        ("weft-wire", "weft-domain"),
        ("weft-writfold", "weft-domain"),
        ("weft-writfold", "weft-wire"),
        ("weft-cli", "weft-frontend"),
        ("weft-cli", "weft-domain"),
        ("weft-cli", "weft-kernel"),
        ("weft-cli", "weft-wire"),
        ("weft-cli", "weft-writfold"),
    ];
    for owner in crates {
        for dependency in crates {
            let report =
                check_dependencies(&Policy::new(owner), "Cargo.toml", &[dependency.into()]);
            assert_eq!(
                !report.failed(),
                allowed.contains(&(owner, dependency)),
                "{owner} -> {dependency}"
            );
            assert!(report.findings.iter().all(|finding| finding.span.is_none()));
        }
    }
}

#[test]
fn unadmitted_dependencies_and_unknown_crates_fail_closed() {
    for (owner, dependency) in [
        ("weft-domain", "serde"),
        ("weft-kernel", "tokio"),
        ("weft-writfold", "writfold-unpublished"),
        ("weft-mystery", "num-bigint"),
    ] {
        assert!(
            check_dependencies(&Policy::new(owner), "Cargo.toml", &[dependency.into()]).failed()
        );
    }
    assert!(
        !check_dependencies(
            &Policy::new("weft-domain"),
            "Cargo.toml",
            &["num-bigint".into()]
        )
        .failed()
    );
}

#[test]
fn source_paths_also_enforce_internal_direction() {
    let report = check_source(
        &Policy::new("weft-domain"),
        "wrong-way.rs",
        "#![forbid(unsafe_code)]\nuse weft_kernel::Evaluator;",
        true,
    );
    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.code == "WQ401")
    );
}

#[test]
fn invalid_or_incomplete_metadata_is_not_a_pass() {
    for input in [
        "not json",
        "{}",
        r#"{"packages":[],"workspace_members":[]}"#,
        r#"{"packages":[],"workspace_members":["missing"]}"#,
    ] {
        assert!(workspace::check_metadata_json(input, &[]).is_err());
    }
}
