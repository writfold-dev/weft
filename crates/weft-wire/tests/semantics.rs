#![forbid(unsafe_code)]

use serde_json::Value;
use std::error::Error;
use weft_domain::Limits;
use weft_wire::{Command, Report, Source, View};

fn project(body: &str) -> Result<Value, Box<dyn Error>> {
    let source = format!(
        "review test {{ context \"ctx\" at \"cut\"; profile \"weft.symbolic/1\"; target plan = proposal \"p\"; {body} }}"
    );
    let limits = Limits::default();
    let compilation = weft_frontend::compile(&source, &limits)
        .map_err(|analysis| format!("compile: {:?}", analysis.diagnostics))?;
    let assessment = weft_kernel::assess(&compilation, &limits)
        .map_err(|diagnostic| format!("assess: {diagnostic:?}"))?;
    let digest = source_digest(&source)?;
    let report = Report {
        command: Command::Prove,
        source: Source::Loaded {
            path: "test.weft",
            sha256: &digest,
            bytes: source.as_bytes(),
        },
        analysis: Some(&compilation.analysis),
        compilation: Some(&compilation),
        assessment: Some(&assessment),
        diagnostics: &[],
        limits: &limits,
    };
    Ok(serde_json::from_slice(&weft_wire::render(
        &report,
        View::Json,
    )?)?)
}
#[test]
fn projection_keeps_model_relative_existential_witnesses_and_trace_closure()
-> Result<(), Box<dyn Error>> {
    let report = project(
        "members := {0,1,0}; assume either: p(0) or p(1); check some: exists x in members { p(x) };",
    )?;
    assert_eq!(report["checks"][0]["result"], "entailed");
    let trace = report["trace"].as_array().ok_or("trace array")?;
    for (index, node) in trace.iter().enumerate() {
        assert_eq!(node["id"].as_u64(), Some(u64::try_from(index)?));
        for input in node["inputs"].as_array().ok_or("trace inputs")? {
            assert!(input.as_u64().ok_or("trace input id")? < u64::try_from(index)?);
        }
    }
    let instances: Vec<_> = trace
        .iter()
        .filter(|n| n["kind"] == "quantifier-instance")
        .collect();
    assert_eq!(instances.len(), 2);
    for instance in instances {
        assert!(instance.get("body").is_some());
        for model in instance["models"].as_array().ok_or("instance models")? {
            assert!(model.get("valuation").is_some());
            assert!(model.get("check").is_some());
            assert!(model.get("uniformly_entailed").is_none());
        }
    }
    let sets = report["review"]["sets"].as_array().ok_or("sets")?;
    assert!(
        sets.iter()
            .any(|set| set["raw_occurrences"] == 3 && set["cardinality"] == 2)
    );
    Ok(())
}
#[test]
fn valuation_atoms_are_active_local_indices_not_global_ids() -> Result<(), Box<dyn Error>> {
    let report = project(
        "check earlier: z(); assume first: a(); assume second: b(); check both: a() and b();",
    )?;
    let trace = report["trace"].as_array().ok_or("trace")?;
    let evaluation = trace
        .iter()
        .find(|n| n["kind"] == "evaluation" && n["check"] == 1)
        .ok_or("evaluation")?;
    let rows = evaluation["rows"].as_array().ok_or("rows")?;
    assert_eq!(rows.len(), 4);
    assert_eq!(rows[1]["assignment"], serde_json::json!([false, true]));
    assert_eq!(rows[1]["premise_values"], serde_json::json!([false, true]));
    assert_eq!(rows[2]["assignment"], serde_json::json!([true, false]));
    assert_eq!(rows[2]["premise_values"], serde_json::json!([true, false]));
    assert_eq!(report["checks"][1]["coverage"]["atom_count"], 2);
    Ok(())
}
#[test]
fn empty_domain_vacuity_does_not_create_existential_witness() -> Result<(), Box<dyn Error>> {
    let report = project(
        "empty := {}; check all: forall x in empty { true }; check some: exists x in empty { true };",
    )?;
    assert_eq!(report["checks"][0]["result"], "entailed");
    assert_eq!(report["checks"][1]["result"], "refuted");
    let trace = report["trace"].as_array().ok_or("trace")?;
    assert!(
        trace
            .iter()
            .any(|n| n["kind"] == "quantifier" && n["vacuous"] == true)
    );
    assert!(!trace.iter().any(|n| n["kind"] == "quantifier-instance"));
    assert!(report["checks"][1]["models"].get("positive").is_none());
    Ok(())
}
#[test]
fn missing_premise_bits_or_truncated_rows_cannot_project_complete() -> Result<(), Box<dyn Error>> {
    let source = "review test { context \"ctx\" at \"cut\"; profile \"weft.symbolic/1\"; target plan = proposal \"p\"; assume h: a(); check c: a(); }";
    let limits = Limits::default();
    let compilation =
        weft_frontend::compile(source, &limits).map_err(|a| format!("{:?}", a.diagnostics))?;
    for truncate_rows in [false, true] {
        let mut assessment =
            weft_kernel::assess(&compilation, &limits).map_err(|d| format!("{d:?}"))?;
        let outcome = assessment.checks.first_mut().ok_or("missing outcome")?;
        let weft_domain::Conclusion::Complete(evaluation) = &mut outcome.conclusion else {
            return Err("expected complete evaluation".into());
        };
        if truncate_rows {
            evaluation.rows.pop();
        } else {
            evaluation.premise_truth_words.clear();
        }
        let digest = source_digest(source)?;
        let report = Report {
            command: Command::Prove,
            source: Source::Loaded {
                path: "test",
                sha256: &digest,
                bytes: source.as_bytes(),
            },
            analysis: Some(&compilation.analysis),
            compilation: Some(&compilation),
            assessment: Some(&assessment),
            diagnostics: &[],
            limits: &limits,
        };
        assert!(matches!(
            weft_wire::render(&report, View::Json),
            Err(weft_wire::RenderError::InvalidRecord(_))
        ));
    }
    Ok(())
}
#[test]
fn failed_expansion_cannot_publish_its_intermediate_set() -> Result<(), Box<dyn Error>> {
    let source = "review r { context \"c\" at \"s\"; profile \"weft.symbolic/1\"; target t = proposal \"p\"; check c: exists x in {1} { true }; }";
    let limits = Limits {
        instances: 0,
        ..Limits::default()
    };
    let compilation =
        weft_frontend::compile(source, &limits).map_err(|a| format!("{:?}", a.diagnostics))?;
    let assessment = weft_kernel::assess(&compilation, &limits).map_err(|d| format!("{d:?}"))?;
    let digest = source_digest(source)?;
    let report = Report {
        command: Command::Prove,
        source: Source::Loaded {
            path: "test",
            sha256: &digest,
            bytes: source.as_bytes(),
        },
        analysis: Some(&compilation.analysis),
        compilation: Some(&compilation),
        assessment: Some(&assessment),
        diagnostics: &[],
        limits: &limits,
    };
    let value: Value = serde_json::from_slice(&weft_wire::render(&report, View::Json)?)?;
    assert_eq!(value["checks"][0]["result"], "not-evaluated");
    let sets: Vec<_> = value["trace"]
        .as_array()
        .ok_or("trace")?
        .iter()
        .filter(|node| node["kind"] == "set-binding")
        .collect();
    assert!(!sets.is_empty());
    for node in sets {
        assert_eq!(node["set"]["publication"], "unreferenced-intermediate");
        assert_ne!(node["set"]["materialization"], "complete");
    }
    assert!(
        value["review"]["sets"]
            .as_array()
            .ok_or("named sets")?
            .is_empty()
    );
    Ok(())
}
fn source_digest(source: &str) -> Result<String, std::fmt::Error> {
    use sha2::{Digest, Sha256};
    use std::fmt::Write;
    let mut digest = String::with_capacity(64);
    for byte in Sha256::digest(source.as_bytes()) {
        write!(&mut digest, "{byte:02x}")?;
    }
    Ok(digest)
}
