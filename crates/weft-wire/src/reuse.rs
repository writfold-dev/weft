//! Local reuse decisions over prior `weft.report/1` assessments.
//!
//! Reuse requires exact scope equality between what the prior report recorded
//! and the candidate source: identical source bytes (by SHA-256), identical
//! evaluator profile and identical evaluation bounds. Any difference, a
//! diagnostics-only report or a malformed artifact is a refusal naming the
//! exact field; nothing is re-evaluated and no live binding is consulted.

use crate::View;
use crate::json::{Json, Result};
use crate::rpc::{Bounds, Value};

pub const REUSE_SCHEMA: &str = "weft.reuse/1";
const REPORT_SCHEMA: &str = "weft.report/1";
const PROFILE: &str = "weft.symbolic/1";

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Difference {
    pub field: &'static str,
    pub expected: String,
    pub observed: String,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Decision {
    Reusable,
    Refused { differences: Vec<Difference> },
}
/// The scope a prior report records about itself.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PriorScope {
    pub kind: String,
    pub source_sha256: String,
    pub profile: String,
    pub requested_context: String,
    pub requested_snapshot: String,
    pub target_reference: String,
    pub budgets: Vec<(String, String)>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PriorError {
    Malformed(&'static str),
    NotAReport,
    NoReusableScope,
}
impl std::fmt::Display for PriorError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed(part) => write!(formatter, "prior report is malformed: {part}"),
            Self::NotAReport => write!(formatter, "artifact is not a weft.report/1 report"),
            Self::NoReusableScope => {
                write!(formatter, "report records no reusable review scope")
            }
        }
    }
}
impl std::error::Error for PriorError {}
impl PriorScope {
    /// Checked conversion from prior-report bytes.
    pub fn parse(bytes: &[u8]) -> std::result::Result<Self, PriorError> {
        let value = crate::rpc::parse::parse(bytes, Bounds::artifact(bytes.len()))
            .map_err(|_| PriorError::Malformed("not one bounded JSON value"))?;
        let Value::Object(members) = &value else {
            return Err(PriorError::NotAReport);
        };
        if member(members.as_slice(), "schema") != Some(&Value::Text(REPORT_SCHEMA.into())) {
            return Err(PriorError::NotAReport);
        }
        let source = object(members.as_slice(), "source")?;
        let source_sha256 = text(source, "sha256")?;
        if source_sha256.len() != 64
            || !source_sha256
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            return Err(PriorError::Malformed(
                "source digest is not lowercase hex64",
            ));
        }
        let review = object(members.as_slice(), "review")?;
        let target = object(review, "target")?;
        Ok(Self {
            kind: text(members.as_slice(), "kind")?.into(),
            source_sha256: source_sha256.into(),
            profile: text(review, "profile")?.into(),
            requested_context: text(review, "requested_context")?.into(),
            requested_snapshot: text(review, "requested_snapshot")?.into(),
            target_reference: text(target, "reference")?.into(),
            budgets: budgets(members)?,
        })
    }
    /// Compares the recorded scope against the candidate source digest and the
    /// current evaluator identity; every inequality becomes a named refusal.
    pub fn compare(&self, candidate_sha256: &str, limits: &weft_domain::Limits) -> Decision {
        let mut differences = Vec::new();
        if self.source_sha256 != candidate_sha256 {
            differences.push(Difference {
                field: "source.sha256",
                expected: self.source_sha256.clone(),
                observed: candidate_sha256.to_string(),
            });
        }
        if self.profile != PROFILE {
            differences.push(Difference {
                field: "review.profile",
                expected: PROFILE.into(),
                observed: self.profile.clone(),
            });
        }
        if self.kind == "diagnostics" {
            differences.push(Difference {
                field: "kind",
                expected: "analysis or assessment".into(),
                observed: self.kind.clone(),
            });
        }
        for (name, recorded) in &self.budgets {
            if matches!(
                name.as_str(),
                "construction_admitted" | "construction_used" | "construction_remaining"
            ) {
                continue;
            }
            let current = budget_value(limits, name);
            if recorded != &current {
                differences.push(Difference {
                    field: "budgets",
                    expected: format!("{name}={recorded}"),
                    observed: format!("{name}={current}"),
                });
            }
        }
        if differences.is_empty() {
            Decision::Reusable
        } else {
            Decision::Refused { differences }
        }
    }
}
fn budget_value(limits: &weft_domain::Limits, name: &str) -> String {
    match name {
        "construction_work" => limits.work.to_string(),
        "source_bytes" => limits.source_bytes.to_string(),
        "tokens" => limits.tokens.to_string(),
        "nesting" => limits.nesting.to_string(),
        "natural_digits" => limits.natural_digits.to_string(),
        "nodes" => limits.nodes.to_string(),
        "instances" => limits.instances.to_string(),
        "members" => limits.members.to_string(),
        "atoms" => limits.atoms.to_string(),
        "valuations" => limits.valuations.to_string(),
        "evaluation_steps" => limits.evaluation_steps.to_string(),
        "trace_rows" => limits.trace_rows.to_string(),
        "output_bytes" => limits.output_bytes.to_string(),
        _ => "0".into(),
    }
}
fn budgets(
    members: &[(Box<str>, Value)],
) -> std::result::Result<Vec<(String, String)>, PriorError> {
    let budgets = object(members, "budgets")?;
    budgets
        .iter()
        .map(|(name, value)| match value {
            Value::Number(token) => Ok((name.to_string(), token.to_string())),
            _ => Err(PriorError::Malformed("budget entry is not numeric")),
        })
        .collect()
}
fn member<'v>(members: &'v [(Box<str>, Value)], key: &str) -> Option<&'v Value> {
    members
        .iter()
        .find(|(known, _)| &**known == key)
        .map(|(_, value)| value)
}
fn object<'v>(
    members: &'v [(Box<str>, Value)],
    key: &str,
) -> std::result::Result<&'v [(Box<str>, Value)], PriorError> {
    match member(members, key) {
        Some(Value::Object(inner)) => Ok(inner),
        _ => Err(PriorError::NoReusableScope),
    }
}
fn text<'v>(
    members: &'v [(Box<str>, Value)],
    key: &str,
) -> std::result::Result<&'v str, PriorError> {
    match member(members, key) {
        Some(Value::Text(value)) => Ok(value),
        _ => Err(PriorError::Malformed("expected a string field")),
    }
}
pub struct ReuseView<'a> {
    pub report_path: &'a str,
    pub report_sha256: &'a str,
    pub candidate_path: &'a str,
    pub candidate_sha256: &'a str,
    pub prior: Option<&'a PriorScope>,
    pub decision: &'a Decision,
}
pub fn render_decision(view: &ReuseView<'_>, view_kind: View, limit: usize) -> Result<Vec<u8>> {
    let mut j = Json::new(limit, matches!(view_kind, View::Human));
    if matches!(view_kind, View::Human) {
        j.raw("Weft reuse decision — report-recorded scope equality only; not grounded; no effect authority.\n")?;
    }
    j.object(|j| {
        j.text("schema", REUSE_SCHEMA)?;
        j.text("kind", "reuse-decision")?;
        j.text("scope", "local-report-scope-equality-only")?;
        j.field("prior", |j| {
            j.object(|j| {
                j.text("path", view.report_path)?;
                j.text("sha256", view.report_sha256)?;
                if let Some(prior) = view.prior {
                    j.text("kind", &prior.kind)?;
                    j.text("profile", &prior.profile)?;
                    j.text("source_sha256", &prior.source_sha256)?;
                    j.text("requested_context", &prior.requested_context)?;
                    j.text("requested_snapshot", &prior.requested_snapshot)?;
                    j.text("target_reference", &prior.target_reference)?;
                }
                Ok(())
            })
        })?;
        j.field("candidate", |j| {
            j.object(|j| {
                j.text("path", view.candidate_path)?;
                j.text("sha256", view.candidate_sha256)?;
                Ok(())
            })
        })?;
        match view.decision {
            Decision::Reusable => j.text("decision", "reusable")?,
            Decision::Refused { .. } => j.text("decision", "refused")?,
        }
        j.field("differences", |j| {
            j.array(|j| {
                if let Decision::Refused { differences } = view.decision {
                    for difference in differences {
                        j.object(|j| {
                            j.text("field", difference.field)?;
                            j.text("expected", &difference.expected)?;
                            j.text("observed", &difference.observed)?;
                            Ok(())
                        })?;
                    }
                }
                Ok(())
            })
        })?;
        j.text(
            "basis",
            "identical report-recorded scope only; no re-evaluation, no live binding",
        )?;
        j.flag("writfold_grounded", false)?;
        j.flag("effect_authority", false)
    })?;
    j.raw("\n")?;
    Ok(j.finish())
}

/// A refused-before-decision input failure: unreadable or malformed artifact.
pub struct FailureView<'a> {
    pub report_path: &'a str,
    pub candidate_path: &'a str,
    pub reason: &'a str,
}
pub fn render_failure(view: &FailureView<'_>, view_kind: View, limit: usize) -> Result<Vec<u8>> {
    let mut j = Json::new(limit, matches!(view_kind, View::Human));
    if matches!(view_kind, View::Human) {
        j.raw("Weft reuse decision — input failed; no decision was made.\n")?;
    }
    j.object(|j| {
        j.text("schema", REUSE_SCHEMA)?;
        j.text("kind", "reuse-decision")?;
        j.text("scope", "local-report-scope-equality-only")?;
        j.field("prior", |j| {
            j.object(|j| {
                j.text("path", view.report_path)?;
                Ok(())
            })
        })?;
        j.field("candidate", |j| {
            j.object(|j| {
                j.text("path", view.candidate_path)?;
                Ok(())
            })
        })?;
        j.text("execution", "failed")?;
        j.field("diagnostics", |j| {
            j.array(|j| {
                j.object(|j| {
                    j.text("code", "ReuseInputUnavailable")?;
                    j.text("phase", "input")?;
                    j.text("message", view.reason)?;
                    Ok(())
                })
            })
        })?;
        j.flag("writfold_grounded", false)?;
        j.flag("effect_authority", false)
    })?;
    j.raw("\n")?;
    Ok(j.finish())
}
