use crate::{Policy, Report, check_dependencies, check_source};
use serde::Deserialize;
use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
};

#[derive(Deserialize)]
struct Metadata {
    packages: Vec<Package>,
    workspace_members: Vec<String>,
}

#[derive(Deserialize)]
struct Package {
    id: String,
    name: String,
    manifest_path: PathBuf,
    targets: Vec<Target>,
    dependencies: Vec<Dependency>,
}

#[derive(Deserialize)]
struct Target {
    src_path: PathBuf,
    #[serde(default)]
    kind: Vec<String>,
}

#[derive(Deserialize)]
struct Dependency {
    name: String,
    kind: Option<DependencyKind>,
}
#[derive(Deserialize)]
#[serde(rename_all = "lowercase")]
enum DependencyKind {
    Normal,
    Dev,
    Build,
}

/// Consumes `cargo metadata --format-version 1 --no-deps --locked --offline`
/// output. Scans all .rs files below each member, excluding nested packages,
/// .git and target. Every declared target must exist and is checked as a root.
/// Filesystem/metadata failures are returned as errors, never success findings.
pub fn check_metadata_json(json: &str, nominal_types: &[String]) -> Result<Report, String> {
    let metadata: Metadata = serde_json::from_str(json).map_err(|error| error.to_string())?;
    if metadata.workspace_members.is_empty() {
        return Err("metadata has no workspace members".into());
    }
    let mut report = Report::default();
    let members: BTreeSet<_> = metadata.workspace_members.iter().collect();
    for member in members {
        let package = metadata
            .packages
            .iter()
            .find(|package| &package.id == member)
            .ok_or_else(|| format!("workspace member is absent from packages: {member}"))?;
        report.append(check_package(package, nominal_types)?);
    }
    Ok(report)
}

fn check_package(package: &Package, nominal_types: &[String]) -> Result<Report, String> {
    let mut policy = Policy::new(&package.name);
    policy.nominal_types = nominal_types.to_vec();
    let dependencies: Vec<_> = package
        .dependencies
        .iter()
        .filter(|dependency| !matches!(dependency.kind, Some(DependencyKind::Dev)))
        .map(|dependency| dependency.name.clone())
        .collect();
    let development: Vec<_> = package
        .dependencies
        .iter()
        .filter(|dependency| matches!(dependency.kind, Some(DependencyKind::Dev)))
        .map(|dependency| dependency.name.clone())
        .collect();
    let manifest = display_path(&package.manifest_path);
    let mut report = check_dependencies(&policy, &manifest, &dependencies);
    report.append(crate::dependencies::check(
        &policy,
        &manifest,
        &development,
        true,
    ));
    let root = package
        .manifest_path
        .parent()
        .ok_or("manifest has no parent directory")?;
    if !package.manifest_path.is_file() {
        return Err(format!("manifest is absent: {manifest}"));
    }
    let mut files = BTreeSet::new();
    collect_files(root, root, &mut files)?;
    let mut roots = BTreeSet::new();
    let mut test_roots = BTreeSet::new();
    for target in &package.targets {
        reject_symlink(&target.src_path)?;
        let source = fs::canonicalize(&target.src_path)
            .map_err(|error| format!("{}: {error}", display_path(&target.src_path)))?;
        roots.insert(source.clone());
        if target
            .kind
            .iter()
            .any(|kind| matches!(kind.as_str(), "test" | "bench"))
        {
            test_roots.insert(source.clone());
        }
        files.insert(source);
    }
    if roots.is_empty() {
        return Err(format!("{} has no declared Rust targets", package.name));
    }
    for path in files {
        policy.test_target = test_roots.contains(&path) || path.starts_with(root.join("tests"));
        let source = fs::read_to_string(&path)
            .map_err(|error| format!("{}: {error}", display_path(&path)))?;
        report.append(check_source(
            &policy,
            &display_path(&path),
            &source,
            roots.contains(&path),
        ));
    }
    Ok(report)
}

fn collect_files(
    directory: &Path,
    root: &Path,
    files: &mut BTreeSet<PathBuf>,
) -> Result<(), String> {
    let entries =
        fs::read_dir(directory).map_err(|error| format!("{}: {error}", display_path(directory)))?;
    let mut paths = Vec::new();
    for entry in entries {
        paths.push(entry.map_err(|error| error.to_string())?.path());
    }
    paths.sort();
    for path in paths {
        let name = path.file_name().and_then(|name| name.to_str());
        if matches!(name, Some("target" | ".git")) {
            continue;
        }
        reject_symlink(&path)?;
        if path.is_dir() {
            if path != root && path.join("Cargo.toml").is_file() {
                continue;
            }
            collect_files(&path, root, files)?;
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            files.insert(fs::canonicalize(&path).map_err(|error| error.to_string())?);
        }
    }
    Ok(())
}

fn reject_symlink(path: &Path) -> Result<(), String> {
    let metadata =
        fs::symlink_metadata(path).map_err(|error| format!("{}: {error}", display_path(path)))?;
    if metadata.file_type().is_symlink() {
        return Err(format!(
            "symlink source paths require explicit resolution: {}",
            display_path(path)
        ));
    }
    Ok(())
}

fn display_path(path: &Path) -> String {
    path.to_string_lossy().replace('\\', "/")
}
