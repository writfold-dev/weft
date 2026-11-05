use crate::{analyze, compile};
use weft_domain::{CheckState, Code, Limits};

type TestResult = Result<(), String>;

#[test]
fn real_external_examples_refuse_without_inventing_inputs() -> TestResult {
    let source = r#"review external {
        context "requested" at "unresolved-snapshot";
        profile "owner.unavailable/1";
        target draft = proposal "prospective";
        asset source = citation "unresolved-citation";
        need source;
        check contract: source.order == "stable";
    }"#;
    let analysis = analyze(source, &Limits::default());
    if !analysis
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code == Code::UnsupportedProfile)
        || !analysis
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == Code::UnresolvedInput)
    {
        return Err(format!(
            "external fixture did not preserve unresolved causes: {:?}",
            analysis.diagnostics
        ));
    }
    let compilation = compile(source, &Limits::default())
        .map_err(|analysis| format!("{:?}", analysis.diagnostics))?;
    if compilation
        .checks
        .iter()
        .any(|check| matches!(check.state, CheckState::Ready(_)))
    {
        return Err("external fixture received an invented local interpretation".into());
    }
    if !compilation.theory.values().is_empty() {
        return Err("external fixture synthesized captured values".into());
    }
    Ok(())
}
