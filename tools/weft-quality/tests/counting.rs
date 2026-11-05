#![forbid(unsafe_code)]

use weft_quality::{Policy, Report, Severity, check_source};

fn check(source: &str, package: &str) -> Report {
    check_source(&Policy::new(package), "calibration.rs", source, true)
}

#[test]
fn comments_and_raw_strings_have_distinct_syntax() {
    let source = r###"#![forbid(unsafe_code)]
/// Documentation is not a code line.
/** Neither is nested documentation: /* nested */ */
fn sample() {
    // Ordinary comment.
    let url = "https://example.invalid//still-a-string";
    let raw = r#"
// literal data, not a comment
/* also literal data */
"#;
    /* outer /* nested */ comment */
    let _ = (url, raw);
}
"###;
    let report = check(source, "weft-kernel");
    assert!(!report.failed());
    let function = report.counts.iter().find(|count| count.kind == "function");
    assert_eq!(function.map(|count| count.code_lines), Some(8));
    let module = report.counts.iter().find(|count| count.name == "<file>");
    assert_eq!(module.map(|count| count.code_lines), Some(9));
}

#[test]
fn function_boundaries_are_inclusive() {
    for (lines, warning, error) in [
        (49, false, false),
        (50, true, false),
        (80, true, false),
        (81, false, true),
    ] {
        let source = format!(
            "#![forbid(unsafe_code)]\nfn f() {{\n{}}}\n",
            "let _ = 0;\n".repeat(lines - 2)
        );
        let report = check(&source, "weft-kernel");
        assert_eq!(
            report
                .findings
                .iter()
                .any(|finding| finding.code == "WQ111"),
            warning
        );
        assert_eq!(
            report
                .findings
                .iter()
                .any(|finding| finding.code == "WQ112"),
            error
        );
        assert_eq!(
            report
                .counts
                .iter()
                .find(|count| count.kind == "function")
                .map(|count| count.code_lines),
            Some(lines)
        );
    }
}

#[test]
fn module_limits_and_orchestration_limit_are_distinct() {
    for (package, lines, expected) in [
        ("weft-kernel", 249, None),
        ("weft-kernel", 250, Some(Severity::Warning)),
        ("weft-kernel", 400, Some(Severity::Warning)),
        ("weft-kernel", 401, Some(Severity::Error)),
        ("weft-cli", 250, Some(Severity::Warning)),
        ("weft-cli", 251, Some(Severity::Error)),
    ] {
        let source = format!(
            "#![forbid(unsafe_code)]\n{}",
            "const _: () = ();\n".repeat(lines - 1)
        );
        let report = check(&source, package);
        assert_eq!(
            report.findings.first().map(|finding| finding.severity),
            expected
        );
        assert_eq!(
            report.counts.first().map(|count| count.code_lines),
            Some(lines)
        );
    }
}

#[test]
fn nested_modules_methods_and_closures_are_measured() {
    let source = "#![forbid(unsafe_code)]\nmod nested { struct S; impl S { fn method() { let _ = || 0; } } }";
    let report = check(source, "weft-kernel");
    assert!(!report.failed());
    for name in ["<file>", "nested", "method", "<closure>"] {
        assert!(report.counts.iter().any(|count| count.name == name));
    }
}

#[test]
fn blank_lines_in_literals_are_not_code_lines() {
    let source = "#![forbid(unsafe_code)]\nfn f() {\nlet _ = r#\"\n\ntext\n\"#;\n}\n";
    let report = check(source, "weft-kernel");
    assert_eq!(
        report
            .counts
            .iter()
            .find(|count| count.kind == "function")
            .map(|count| count.code_lines),
        Some(5)
    );
}
