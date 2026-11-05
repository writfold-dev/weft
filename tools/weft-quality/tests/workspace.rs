#![forbid(unsafe_code)]

use std::{
    error::Error,
    fs,
    path::PathBuf,
    sync::atomic::{AtomicUsize, Ordering},
};
use weft_quality::workspace::check_metadata_json;

static SEQUENCE: AtomicUsize = AtomicUsize::new(0);

struct Fixture {
    root: PathBuf,
}

impl Fixture {
    fn new() -> Result<Self, Box<dyn Error>> {
        let sequence = SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "weft-quality-calibration-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&root)?;
        let fixture = Self { root };
        fs::create_dir(fixture.root.join("src"))?;
        fs::write(
            fixture.root.join("Cargo.toml"),
            "[package]\nname = \"weft-domain\"\nversion = \"0.1.0\"\n",
        )?;
        fs::write(
            fixture.root.join("src/lib.rs"),
            "#![forbid(unsafe_code)]\nmod value;\n",
        )?;
        fs::write(
            fixture.root.join("src/value.rs"),
            "pub struct Value { pub count: u32 }\n",
        )?;
        Ok(fixture)
    }

    fn metadata(&self, dependency: &str) -> String {
        serde_json::json!({
            "workspace_members": ["domain"],
            "packages": [{
                "id": "domain", "name": "weft-domain",
                "manifest_path": self.root.join("Cargo.toml"),
                "targets": [{"src_path": self.root.join("src/lib.rs")}],
                "dependencies": [{"name": dependency, "rename": "local_alias", "kind": "dev", "target": "cfg(any())"}]
            }]
        }).to_string()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

#[test]
fn metadata_checks_real_sources_and_declared_roots() -> Result<(), Box<dyn Error>> {
    let fixture = Fixture::new()?;
    let report = check_metadata_json(&fixture.metadata("num-bigint"), &[])?;
    assert!(!report.failed());
    assert_eq!(
        report
            .counts
            .iter()
            .filter(|count| count.kind == "module")
            .count(),
        2
    );
    fs::write(fixture.root.join("src/value.rs"), "fn bad() { todo!(); }\n")?;
    let invalid = check_metadata_json(&fixture.metadata("num-bigint"), &[])?;
    assert!(
        invalid
            .findings
            .iter()
            .any(|finding| finding.code == "WQ205")
    );
    fs::write(fixture.root.join("src/lib.rs"), "mod value;\n")?;
    let root = check_metadata_json(&fixture.metadata("num-bigint"), &[])?;
    assert!(root.findings.iter().any(|finding| finding.code == "WQ002"));
    Ok(())
}

#[test]
fn renamed_dev_target_dependencies_are_not_exempt() -> Result<(), Box<dyn Error>> {
    let fixture = Fixture::new()?;
    let report = check_metadata_json(&fixture.metadata("serde"), &[])?;
    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.code == "WQ402")
    );
    Ok(())
}

#[test]
fn missing_targets_and_unreadable_sources_cannot_pass() -> Result<(), Box<dyn Error>> {
    let fixture = Fixture::new()?;
    fs::remove_file(fixture.root.join("src/lib.rs"))?;
    assert!(check_metadata_json(&fixture.metadata("num-bigint"), &[]).is_err());
    Ok(())
}

#[test]
fn nested_packages_and_build_output_are_not_member_sources() -> Result<(), Box<dyn Error>> {
    let fixture = Fixture::new()?;
    for name in ["target", "nested"] {
        fs::create_dir(fixture.root.join(name))?;
        fs::write(fixture.root.join(name).join("invalid.rs"), "not Rust")?;
    }
    fs::write(fixture.root.join("nested/Cargo.toml"), "[workspace]\n")?;
    assert!(!check_metadata_json(&fixture.metadata("num-bigint"), &[])?.failed());
    Ok(())
}

#[cfg(unix)]
#[test]
fn source_symlinks_fail_closed_instead_of_escaping_inventory() -> Result<(), Box<dyn Error>> {
    let fixture = Fixture::new()?;
    std::os::unix::fs::symlink(
        fixture.root.join("src/value.rs"),
        fixture.root.join("src/alias.rs"),
    )?;
    assert!(check_metadata_json(&fixture.metadata("num-bigint"), &[]).is_err());
    Ok(())
}
