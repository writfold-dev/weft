use super::Lower;
use weft_domain::{
    Analysis, Code, Compilation, Diagnostic, InvariantError, OriginId, OriginKind, Phase,
    SourceSpan,
};

impl Lower<'_, '_> {
    pub(super) fn snapshot_work(
        &mut self,
        dependencies: usize,
        span: SourceSpan,
    ) -> Result<(), Diagnostic> {
        let count = self
            .hypotheses
            .len()
            .checked_add(self.checked.analysis.requirements.len())
            .and_then(|count| count.checked_add(self.hypothesis_dependencies.len()))
            .and_then(|count| count.checked_add(dependencies))
            .and_then(|count| count.checked_add(1))
            .ok_or_else(|| self.limit(span, "check dependency snapshot size overflows"))?;
        self.checked
            .builder
            .charge(count)
            .map_err(|error| self.failure(error, span))
    }
    pub(super) fn required_inputs(&mut self) {
        for requirement in &self.checked.analysis.requirements {
            let Some(declaration) = self
                .checked
                .analysis
                .declarations
                .get(requirement.declaration)
            else {
                continue;
            };
            if matches!(
                declaration.kind,
                weft_domain::DeclarationKind::Target
                    | weft_domain::DeclarationKind::Claim
                    | weft_domain::DeclarationKind::Asset
                    | weft_domain::DeclarationKind::Rule
            ) {
                self.checked.analysis.diagnostics.push(Diagnostic::new(Code::UnresolvedInput, Phase::Capture,
                    "explicitly required external input remains unresolved independently of local logic", Some(requirement.span)));
            }
        }
    }
    pub fn failure(&self, error: InvariantError, span: SourceSpan) -> Diagnostic {
        crate::semantic::invariant(error, span)
    }
    pub fn invalid(&self, span: SourceSpan, message: &str) -> Diagnostic {
        Diagnostic::new(Code::InvalidProgram, Phase::Lower, message, Some(span))
    }
    pub fn limit(&self, span: SourceSpan, message: &str) -> Diagnostic {
        Diagnostic::new(Code::LimitExceeded, Phase::Lower, message, Some(span))
    }
    pub fn origin(
        &mut self,
        kind: OriginKind,
        span: SourceSpan,
        parents: Vec<OriginId>,
    ) -> Result<OriginId, Diagnostic> {
        self.checked
            .builder
            .add_origin(kind, span, parents)
            .map_err(|error| self.failure(error, span))
    }
    pub(super) fn finish(self) -> Result<Compilation, Box<Analysis>> {
        let sets = self
            .checked
            .analysis
            .set_bindings
            .iter()
            .map(|binding| weft_domain::BoundSet {
                declaration: binding.declaration,
                value: self.sets.get(&binding.declaration).copied(),
            })
            .collect();
        let materializations = weft_domain::Materializations {
            hypotheses: self.hypotheses,
            sets,
        };
        let span = self.parsed.header.span;
        Compilation::checked(
            self.checked.analysis,
            self.checked.builder.finish(),
            self.requests,
            materializations,
        )
        .map_err(|error| {
            Box::new(Analysis {
                diagnostics: vec![crate::semantic::invariant(error, span)],
                ..Analysis::default()
            })
        })
    }
}
