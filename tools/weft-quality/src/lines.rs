use crate::{Count, Position, Report, Severity, SourceRange};
use proc_macro2::{Span, TokenStream, TokenTree};
use std::collections::BTreeSet;

pub(crate) struct CodeLines<'a> {
    source: Vec<&'a str>,
    occupied: BTreeSet<usize>,
}

impl<'a> CodeLines<'a> {
    pub(crate) fn new(source: &'a str, tokens: TokenStream) -> Self {
        let mut lines = Self {
            source: source.lines().collect(),
            occupied: BTreeSet::new(),
        };
        lines.collect(tokens);
        lines
    }

    fn doc_comment(&self, span: Span) -> bool {
        let start = span.start();
        let Some(line) = self.source.get(start.line.saturating_sub(1)) else {
            return false;
        };
        let mut suffix = line.chars().skip(start.column);
        matches!(
            (suffix.next(), suffix.next(), suffix.next()),
            (Some('/'), Some('/'), Some('/' | '!')) | (Some('/'), Some('*'), Some('*' | '!'))
        )
    }

    fn collect(&mut self, tokens: TokenStream) {
        for token in tokens {
            if self.doc_comment(token.span()) {
                continue;
            }
            match token {
                TokenTree::Group(group) => {
                    self.mark(group.span_open());
                    self.collect(group.stream());
                    self.mark(group.span_close());
                }
                other => self.mark(other.span()),
            }
        }
    }

    fn mark(&mut self, span: Span) {
        for line in span.start().line..=span.end().line {
            if self
                .source
                .get(line.saturating_sub(1))
                .is_some_and(|text| !text.trim().is_empty())
            {
                self.occupied.insert(line);
            }
        }
    }

    pub(crate) fn record_file(&self, path: &str, maximum: usize, report: &mut Report) {
        let end = self.source.len().max(1);
        let span = SourceRange {
            start: Position { line: 1, column: 0 },
            end: Position {
                line: end,
                column: self.source.last().map_or(0, |line| line.len()),
            },
        };
        self.record(
            Count {
                path: path.into(),
                span,
                kind: "module".into(),
                name: "<file>".into(),
                code_lines: 0,
                warning_at: 250,
                maximum,
            },
            report,
        );
    }

    pub(crate) fn record_span(
        &self,
        path: &str,
        kind: &str,
        name: &str,
        span: Span,
        maximum: usize,
        report: &mut Report,
    ) {
        let warning = if kind == "function" { 50 } else { 250 };
        self.record(
            Count {
                path: path.into(),
                span: span.into(),
                kind: kind.into(),
                name: name.into(),
                code_lines: 0,
                warning_at: warning,
                maximum,
            },
            report,
        );
    }

    fn record(&self, mut count: Count, report: &mut Report) {
        count.code_lines = self
            .occupied
            .range(count.span.start.line..=count.span.end.line)
            .count();
        if count.code_lines >= count.warning_at {
            let severity = if count.code_lines > count.maximum {
                Severity::Error
            } else {
                Severity::Warning
            };
            let code = match (count.kind.as_str(), severity) {
                ("function", Severity::Error) => "WQ112",
                ("function", Severity::Warning) => "WQ111",
                (_, Severity::Error) => "WQ102",
                (_, Severity::Warning) => "WQ101",
            };
            report.findings.push(crate::Finding {
                path: count.path.clone(),
                span: Some(count.span),
                code: code.into(),
                severity,
                message: format!(
                    "{} {}: {} code lines; maximum {}",
                    count.kind, count.name, count.code_lines, count.maximum
                ),
            });
        }
        report.counts.push(count);
    }
}
