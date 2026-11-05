use proc_macro2::Span;
use serde::Serialize;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Severity {
    Warning,
    Error,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Position {
    pub line: usize,
    pub column: usize,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct SourceRange {
    pub start: Position,
    pub end: Position,
}

impl From<Span> for SourceRange {
    fn from(span: Span) -> Self {
        let start = span.start();
        let end = span.end();
        Self {
            start: Position {
                line: start.line,
                column: start.column,
            },
            end: Position {
                line: end.line,
                column: end.column,
            },
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Finding {
    pub path: String,
    pub span: Option<SourceRange>,
    pub code: String,
    pub severity: Severity,
    pub message: String,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Count {
    pub path: String,
    pub span: SourceRange,
    pub kind: String,
    pub name: String,
    pub code_lines: usize,
    pub warning_at: usize,
    pub maximum: usize,
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct Report {
    pub findings: Vec<Finding>,
    pub counts: Vec<Count>,
}

impl Report {
    pub fn failed(&self) -> bool {
        self.findings
            .iter()
            .any(|finding| finding.severity == Severity::Error)
    }

    pub fn append(&mut self, mut other: Self) {
        self.findings.append(&mut other.findings);
        self.counts.append(&mut other.counts);
        self.normalize();
    }

    pub(crate) fn normalize(&mut self) {
        self.findings.sort();
        self.findings.dedup();
        self.counts.sort();
        self.counts.dedup();
    }

    pub(crate) fn push(
        &mut self,
        path: &str,
        code: &str,
        severity: Severity,
        span: Span,
        message: String,
    ) {
        self.findings.push(Finding {
            path: path.into(),
            span: Some(span.into()),
            code: code.into(),
            severity,
            message,
        });
    }

    pub(crate) fn manifest_error(&mut self, path: &str, code: &str, message: String) {
        self.findings.push(Finding {
            path: path.into(),
            span: None,
            code: code.into(),
            severity: Severity::Error,
            message,
        });
    }
}
