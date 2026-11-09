#![forbid(unsafe_code)]

mod ast;
mod dependencies;
mod lines;
mod nominal;
mod paths;
mod report;
pub mod workspace;

pub use report::{Count, Finding, Position, Report, Severity, SourceRange};

use proc_macro2::Span;
use syn::visit::Visit;

/// The caller supplies the real package name, resolved dependency names, and
/// whether this source is a crate root. No cfg branch is exempt from checking.
#[derive(Clone, Debug)]
pub struct Policy {
    pub crate_name: String,
    pub nominal_types: Vec<String>,
    pub test_target: bool,
}

impl Policy {
    pub fn new(crate_name: impl Into<String>) -> Self {
        Self {
            crate_name: crate_name.into(),
            nominal_types: Vec::new(),
            test_target: false,
        }
    }

    pub fn is_core(&self) -> bool {
        matches!(
            self.crate_name.as_str(),
            "weft-core" | "weft-domain" | "weft-frontend" | "weft-kernel"
        )
    }

    pub fn is_orchestration(&self) -> bool {
        matches!(
            self.crate_name.as_str(),
            "weft-cli" | "weft-writfold" | "weft-quality"
        )
    }
}

/// Checks a complete Rust source file, not a textual excerpt. Parse failure is
/// an error finding, never an empty successful report.
pub fn check_source(policy: &Policy, path: &str, source: &str, crate_root: bool) -> Report {
    let mut report = Report::default();
    let file = match syn::parse_file(source) {
        Ok(file) => file,
        Err(error) => {
            report.push(
                path,
                "WQ001",
                Severity::Error,
                error.span(),
                error.to_string(),
            );
            return report;
        }
    };
    let tokens = match source.parse::<proc_macro2::TokenStream>() {
        Ok(tokens) => tokens,
        Err(error) => {
            report.push(
                path,
                "WQ001",
                Severity::Error,
                error.span(),
                error.to_string(),
            );
            return report;
        }
    };
    let lines = lines::CodeLines::new(source, tokens);
    if crate_root && !ast::forbids_unsafe(&file.attrs) {
        report.push(
            path,
            "WQ002",
            Severity::Error,
            Span::call_site(),
            "crate root must declare #![forbid(unsafe_code)]".into(),
        );
    }
    ast::check(policy, path, &file, &lines, &mut report);
    nominal::check(policy, path, &file, &mut report);
    paths::PathCheck::new(policy, path, &mut report).visit_file(&file);
    report.normalize();
    report
}

/// Dependencies must be canonical package names, not local Cargo aliases.
/// This entrypoint checks production/build dependencies; metadata keeps explicit
/// Cargo development dependencies separate and admits only selected test drivers.
pub fn check_dependencies(policy: &Policy, manifest: &str, dependencies: &[String]) -> Report {
    dependencies::check(policy, manifest, dependencies, false)
}
