//! Revision-3 report surface: set-operation provenance, retained operand
//! closure on empty results, membership/subset comparison traces with the
//! deterministic first-left counterexample.

#![forbid(unsafe_code)]

use serde_json::Value;
use std::error::Error;
use weft_domain::Limits;
use weft_wire::{Command, Report, Source, View};

fn body_report(body: &str) -> Result<Value, Box<dyn Error>> {
    let source = format!(
        "review r {{ context \"c\" at \"s\"; profile \"weft.symbolic/1\"; target t = proposal \"p\"; {body} }}"
    );
    let compilation = weft_frontend::compile(&source, &Limits::default())
        .map_err(|analysis| format!("{:?}", analysis.diagnostics))?;
    let limits = Limits::default();
    let report = Report {
        command: Command::Prove,
        source: Source::Loaded {
            path: "source",
            sha256: &"0".repeat(64),
            bytes: source.as_bytes(),
        },
        analysis: Some(&compilation.analysis),
        compilation: Some(&compilation),
        assessment: None,
        diagnostics: &[],
        limits: &limits,
    };
    let bytes = weft_wire::render(&report, View::Json)?;
    Ok(serde_json::from_slice(&bytes)?)
}

#[test]
fn set_operations_project_origins_and_members() -> Result<(), Box<dyn Error>> {
    let report = body_report(
        "a := {1,2}; b := {2,3}; u := a | b; i := a & b; d := a - b; check q: 1 in d;",
    )?;
    let origins = &report["origins"];
    let operations: Vec<&Value> = origins
        .as_array()
        .ok_or("origins array")?
        .iter()
        .filter(|origin| origin["kind"] == "set-operation")
        .collect();
    if operations.len() != 3 {
        return Err(format!("expected three set operations: {operations:?}").into());
    }
    for operation in &operations {
        if operation["left_set"].is_null() || operation["right_set"].is_null() {
            return Err("operation origin must link both whole operands".into());
        }
    }
    let operators: Vec<&str> = operations
        .iter()
        .filter_map(|operation| operation["operator"].as_str())
        .collect();
    for expected in ["union", "intersection", "difference"] {
        if !operators.contains(&expected) {
            return Err(format!("missing {expected} in {operators:?}").into());
        }
    }
    Ok(())
}

#[test]
fn empty_difference_keeps_published_operand_evidence() -> Result<(), Box<dyn Error>> {
    let report = body_report("a := {1,2}; e := a - a; need e; check q: not (3 in e);")?;
    let sets = &report["review"]["sets"];
    let empty = sets
        .as_array()
        .ok_or("sets array")?
        .iter()
        .find(|set| set["cardinality"] == 0 && set["element_type"] == "natural");
    let empty = empty.ok_or("empty typed difference result missing")?;
    if empty["publication"] != "published" {
        return Err("need-on-empty-derived-set must stay published".into());
    }
    // The operand sets stay reachable through the operation origin.
    let origins = report["origins"].as_array().ok_or("origins")?;
    if !origins
        .iter()
        .any(|origin| origin["kind"] == "set-operation" && origin["operator"] == "difference")
    {
        return Err("difference origin missing on empty result".into());
    }
    Ok(())
}

#[test]
fn subset_counterexample_appears_in_comparison_trace() -> Result<(), Box<dyn Error>> {
    let report = body_report("a := {2,4}; b := {1,2,3}; check q: a <= b;")?;
    let trace = report["trace"].as_array().ok_or("trace array")?;
    let comparison = trace
        .iter()
        .find(|node| node["kind"] == "comparison" && node["operator"] == "<=")
        .ok_or("subset comparison node missing")?;
    if comparison["counterexample"]["value"] != "4" {
        return Err(format!("wrong counterexample: {}", comparison["counterexample"]).into());
    }
    Ok(())
}

#[test]
fn membership_trace_links_scalar_and_whole_set() -> Result<(), Box<dyn Error>> {
    let report = body_report("s := {2,3}; check q: 2 in s; check r: not (1 in s);")?;
    let trace = report["trace"].as_array().ok_or("trace")?;
    let memberships: Vec<&Value> = trace
        .iter()
        .filter(|node| node["kind"] == "comparison" && node["operator"] == "in")
        .collect();
    if memberships.len() != 2 {
        return Err(format!("expected two membership nodes: {memberships:?}").into());
    }
    if memberships.iter().any(|node| node["right_set"].is_null()) {
        return Err("membership must link the whole right-hand set".into());
    }
    if report["writfold_grounded"] != false || report["effect_authority"] != false {
        return Err("local algebra must stay non-grounded and non-authoritative".into());
    }
    Ok(())
}
