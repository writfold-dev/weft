#![forbid(unsafe_code)]

use weft_quality::{Policy, check_dependencies, check_source};

#[test]
fn integration_drivers_do_not_add_production_edges() {
    let source = "#![forbid(unsafe_code)]\nuse weft_kernel::assess;";
    let mut policy = Policy::new("weft-wire");
    assert!(
        check_source(&policy, "lib.rs", source, true)
            .findings
            .iter()
            .any(|f| f.code == "WQ401")
    );
    policy.test_target = true;
    assert!(!check_source(&policy, "tests/report.rs", source, true).failed());
    assert!(check_dependencies(&policy, "Cargo.toml", &["weft-kernel".into()]).failed());
}

#[test]
fn inline_test_permission_ends_at_its_lexical_scope() {
    let test = "#![forbid(unsafe_code)]\n#[cfg(test)] mod tests { use weft_kernel::assess; }";
    let policy = Policy::new("weft-wire");
    assert!(!check_source(&policy, "lib.rs", test, true).failed());
    let outside = format!("{test}\nuse weft_kernel::assess;");
    assert!(
        check_source(&policy, "lib.rs", &outside, true)
            .findings
            .iter()
            .any(|f| f.code == "WQ401")
    );
    let optional = "#![forbid(unsafe_code)]\n#[cfg(any(test, feature = \"production\"))] mod tests { use weft_kernel::assess; }";
    assert!(check_source(&policy, "lib.rs", optional, true).failed());
}

#[test]
fn cli_json_is_test_only_and_core_stays_pure() {
    let source = "#![forbid(unsafe_code)]\nuse serde_json::Value;";
    let mut cli = Policy::new("weft-cli");
    assert!(check_source(&cli, "lib.rs", source, true).failed());
    cli.test_target = true;
    assert!(!check_source(&cli, "tests/cli.rs", source, true).failed());
    for owner in ["weft-domain", "weft-frontend", "weft-kernel"] {
        let mut core = Policy::new(owner);
        core.test_target = true;
        assert!(check_source(&core, "tests.rs", source, true).failed());
        assert!(
            check_source(
                &core,
                "tests.rs",
                "#![forbid(unsafe_code)]\nuse std::fs;",
                true
            )
            .failed()
        );
    }
}
