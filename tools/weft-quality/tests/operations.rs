#![forbid(unsafe_code)]

use weft_quality::{Policy, check_source};

#[test]
fn each_forbidden_operation_has_a_stable_code() {
    for (body, code) in [
        ("unsafe { f(); }", "WQ201"),
        ("panic!(\"stop\");", "WQ202"),
        ("unreachable!();", "WQ202"),
        ("todo!();", "WQ205"),
        ("unimplemented!();", "WQ206"),
        ("wrapper!({ panic!(\"hidden\"); });", "WQ202"),
        ("wrapper!({ unsafe { f(); } });", "WQ201"),
        ("wrapper!(unsafe fn f() {});", "WQ201"),
        ("wrapper!(unsafe impl Trait for Type {});", "WQ201"),
        ("wrapper!(unsafe trait Trait {});", "WQ201"),
        ("wrapper!(unsafe extern \"C\" { fn f(); });", "WQ201"),
        ("wrapper!(#[unsafe(no_mangle)] fn f() {});", "WQ201"),
        ("wrapper!({ std::panic::panic_any(0); });", "WQ202"),
        ("wrapper!({ std::panic::resume_unwind(x); });", "WQ202"),
        ("wrapper!({ todo!(); });", "WQ205"),
        ("wrapper!({ unimplemented!(); });", "WQ206"),
        ("wrapper!({ value.unwrap(); });", "WQ203"),
        ("wrapper!({ value.expect(\"value\"); });", "WQ204"),
        ("wrapper!({ value.unwrap_err(); });", "WQ203"),
        ("wrapper!({ value.expect_err(\"error\"); });", "WQ204"),
    ] {
        let source = format!("#![forbid(unsafe_code)]\nfn f() {{ {body} }}");
        let report = check_source(&Policy::new("weft-kernel"), "bad.rs", &source, true);
        assert!(report.failed());
        assert!(
            report.findings.iter().any(|finding| finding.code == code),
            "missing {code}"
        );
    }
}

#[test]
fn unsafe_declarations_and_attributes_are_rejected() {
    for item in [
        "unsafe fn f() {}",
        "unsafe impl Trait for Type {}",
        "unsafe trait Trait {}",
        "unsafe extern \"C\" { fn f(); }",
        "#[unsafe(no_mangle)] fn f() {}",
    ] {
        let source = format!("#![forbid(unsafe_code)]\n{item}");
        let report = check_source(&Policy::new("weft-kernel"), "unsafe.rs", &source, true);
        assert!(
            report
                .findings
                .iter()
                .any(|finding| finding.code == "WQ201")
        );
    }
}

#[test]
fn strings_and_comments_do_not_create_operation_findings() {
    let source = r##"#![forbid(unsafe_code)]
// panic!(); unsafe {} x.unwrap()
fn f() { let _ = r#"todo!(); unimplemented!(); x.expect("x");"#; }
"##;
    let report = check_source(&Policy::new("weft-kernel"), "valid.rs", source, true);
    assert!(!report.failed());
    assert!(report.findings.is_empty());
}

#[test]
fn syntax_tokens_are_not_executable_unsafe() {
    for item in [
        "fn f(_: Option<syn::Token![unsafe]>) {}",
        "fn f() { quote!(syn::Token![unsafe]); }",
        "macro_rules! token { (unsafe) => { syn::Token![unsafe] }; }",
        "fn f() { wrapper!(unsafe, panic, todo, unimplemented); }",
    ] {
        let source = format!("#![forbid(unsafe_code)]\n{item}");
        let report = check_source(&Policy::new("weft-quality"), "tokens.rs", &source, true);
        assert!(!report.failed(), "{:?}", report.findings);
    }
}

#[test]
fn direct_fallible_methods_are_distinct_from_macro_lint_gaps() {
    // Typed lints cover direct calls; ambiguous macro calls are rejected because
    // the admitted compiler does not diagnose std unwrap/expect in expansions.
    let source = r#"#![forbid(unsafe_code)]
struct Cursor;
impl Cursor {
    fn expect(&self, _: &str) -> Result<(), ()> { Ok(()) }
    fn unwrap(&self) -> Result<(), ()> { Ok(()) }
}
fn f(cursor: Cursor) -> Result<(), ()> {
    cursor.expect("token")?;
    Cursor::expect(&cursor, "token")?;
    cursor.unwrap()?;
    wrapper!(cursor.expect("token"));
    Ok(())
}
"#;
    let report = check_source(&Policy::new("weft-kernel"), "cursor.rs", source, true);
    let errors: Vec<_> = report
        .findings
        .iter()
        .filter(|finding| finding.severity == weft_quality::Severity::Error)
        .collect();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].code, "WQ204");
    let direct = source.replace("wrapper!(cursor.expect(\"token\"));", "");
    let report = check_source(&Policy::new("weft-kernel"), "cursor.rs", &direct, true);
    assert!(!report.failed(), "{:?}", report.findings);
}

#[test]
fn parse_failure_and_missing_forbid_fail_closed() {
    let policy = Policy::new("weft-kernel");
    let invalid = check_source(&policy, "invalid.rs", "fn {", true);
    assert!(
        invalid
            .findings
            .iter()
            .any(|finding| finding.code == "WQ001")
    );
    let missing = check_source(&policy, "missing.rs", "fn f() {}", true);
    assert!(
        missing
            .findings
            .iter()
            .any(|finding| finding.code == "WQ002")
    );
    let module = check_source(&policy, "module.rs", "fn f() {}", false);
    assert!(!module.failed());
}

#[test]
fn cfg_disabled_code_is_not_an_exception_and_spans_are_real() {
    let source = "#![forbid(unsafe_code)]\n#[cfg(any())]\nfn f() {\n    panic!(\"stop\");\n}\n";
    let report = check_source(&Policy::new("weft-kernel"), "span.rs", source, true);
    assert!(report.findings.iter().any(|finding| {
        finding.code == "WQ202"
            && finding
                .span
                .is_some_and(|span| span.start.line == 4 && span.start.column == 4)
    }));
}

#[test]
fn aliased_panic_paths_are_not_hidden() {
    let source = "#![forbid(unsafe_code)]\nuse std::panic as p; fn f() { p::panic_any(0); }";
    let report = check_source(&Policy::new("weft-cli"), "alias.rs", source, true);
    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.code == "WQ202")
    );
}

#[test]
fn report_order_is_deterministic() -> Result<(), serde_json::Error> {
    let policy = Policy::new("weft-kernel");
    let source = "#![forbid(unsafe_code)]\nfn f() { todo!(); panic!(); x.unwrap(); }";
    let first = check_source(&policy, "stable.rs", source, true);
    let second = check_source(&policy, "stable.rs", source, true);
    assert_eq!(
        serde_json::to_string(&first)?,
        serde_json::to_string(&second)?
    );
    assert!(first.findings.windows(2).all(|pair| pair[0] < pair[1]));
    Ok(())
}
