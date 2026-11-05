use crate::{
    ast,
    semantic::{Checker, Resolution},
    types::TypeVar,
};
use std::collections::HashSet;
use weft_domain::{BindingRequest, Code, DeclId, DeclarationKind, Label, Phase, Requirement};

impl<'s> Checker<'_, 's> {
    pub fn statement(&mut self, statement: &ast::Statement<'s>) {
        match statement {
            ast::Statement::Binding {
                kind,
                name,
                citation,
                span,
            } => {
                if let Some(declaration) = self.declare(*name, *kind, *span) {
                    self.checked.analysis.bindings.push(BindingRequest {
                        declaration,
                        citation: citation.value.to_string(),
                        span: *span,
                    });
                }
            }
            ast::Statement::Set { name, value, span } => {
                let ty = self.set_type(*value);
                if let Some(declaration) = self.declare(*name, DeclarationKind::Set, *span) {
                    self.sets.insert(declaration, ty);
                    match self.checked.builder.charge(self.current.dependencies.len()) {
                        Ok(()) => {
                            self.set_dependencies
                                .insert(declaration, self.current.dependencies.clone());
                        }
                        Err(error) => self
                            .current
                            .diagnostics
                            .push(crate::semantic::invariant(error, *span)),
                    }
                    if let Some(initializer) = self.parsed.set(*value) {
                        self.checked
                            .analysis
                            .set_bindings
                            .push(weft_domain::SetDeclaration {
                                declaration,
                                span: *span,
                                initializer_span: initializer.span,
                            });
                    }
                }
            }
            ast::Statement::Need { name, span } => self.need(*name, *span),
            ast::Statement::Assume {
                name,
                expression,
                span,
            } => {
                self.expression(*expression);
                if let Some(declaration) = self.declare(*name, DeclarationKind::Hypothesis, *span)
                    && let Some(expression) = self.parsed.expression(*expression)
                {
                    self.checked
                        .analysis
                        .hypotheses
                        .push(weft_domain::HypothesisDeclaration {
                            declaration,
                            span: *span,
                            expression_span: expression.span,
                        });
                }
            }
            ast::Statement::Check {
                name,
                expression,
                rules,
                span,
            } => {
                self.expression(*expression);
                self.rules(rules);
                self.declare(*name, DeclarationKind::Check, *span);
            }
        }
    }
    fn declare(
        &mut self,
        name: ast::Name<'s>,
        kind: DeclarationKind,
        span: weft_domain::SourceSpan,
    ) -> Option<DeclId> {
        if let Some(prior) = self.checked.analysis.declarations.find(name.text) {
            self.error(
                Code::DuplicateName,
                Phase::Resolve,
                name.span,
                "top-level name is already declared",
            );
            if let (Some(declaration), Some(diagnostic)) = (
                self.checked.analysis.declarations.get(prior),
                self.current.diagnostics.last_mut(),
            ) {
                diagnostic.secondary.push(Label {
                    span: declaration.span,
                    message: "first declaration".into(),
                });
            }
            return None;
        }
        match self
            .checked
            .analysis
            .declarations
            .insert(name.text.into(), kind, span)
        {
            Ok(id) => {
                self.current.declaration = Some(id);
                Some(id)
            }
            Err(error) => {
                self.current
                    .diagnostics
                    .push(crate::semantic::invariant(error, name.span));
                None
            }
        }
    }
    pub fn declaration(&mut self, name: ast::Name<'s>) -> Option<DeclId> {
        let declaration = self.checked.analysis.declarations.find(name.text);
        if declaration.is_none() {
            self.error(
                Code::UnknownName,
                Phase::Resolve,
                name.span,
                format!("name '{}' is not declared before this use", name.text),
            );
        }
        declaration
    }
    fn need(&mut self, name: ast::Name<'s>, span: weft_domain::SourceSpan) {
        let Some(declaration) = self.declaration(name) else {
            return;
        };
        if self
            .checked
            .analysis
            .declarations
            .get(declaration)
            .is_some_and(|value| value.kind == DeclarationKind::Check)
        {
            self.error(
                Code::WrongNameKind,
                Phase::Resolve,
                name.span,
                "a check result cannot be required as an input",
            );
            return;
        }
        if !self
            .checked
            .analysis
            .requirements
            .iter()
            .any(|item| item.declaration == declaration)
        {
            self.checked
                .analysis
                .requirements
                .push(Requirement { declaration, span });
        }
    }
    fn rules(&mut self, rules: &[ast::Name<'s>]) {
        let mut seen = HashSet::new();
        for name in rules {
            if !seen.insert(name.text) {
                self.error(
                    Code::DuplicateRule,
                    Phase::Resolve,
                    name.span,
                    "rule candidate is repeated",
                );
            }
            let Some(declaration) = self.declaration(*name) else {
                continue;
            };
            self.dependency(declaration);
            if self
                .checked
                .analysis
                .declarations
                .get(declaration)
                .is_some_and(|value| value.kind == DeclarationKind::Rule)
            {
                self.error(
                    Code::UnqualifiedRule,
                    Phase::Capture,
                    name.span,
                    "rule has no acquired qualified interpretation; naming it does not apply it",
                );
            } else {
                self.error(
                    Code::WrongNameKind,
                    Phase::Resolve,
                    name.span,
                    "by requires a rule binding",
                );
            }
        }
    }
    pub fn path(&mut self, path: &ast::Path<'s>, set: bool) -> TypeVar {
        if let Some((_, binder, ty)) = self
            .scope
            .iter()
            .rev()
            .find(|(name, _, _)| *name == path.root.text)
        {
            let (binder, ty) = (*binder, *ty);
            if set {
                self.error(
                    Code::WrongNameKind,
                    Phase::Type,
                    path.span,
                    "a scalar binder is not a set",
                );
            } else if !path.fields.is_empty() {
                self.error(
                    Code::UnresolvedInput,
                    Phase::Capture,
                    path.span,
                    "field selection requires an acquired typed interpretation",
                );
            } else {
                self.checked
                    .paths
                    .insert(path.span, Resolution::Binder(binder));
            }
            return ty;
        }
        let Some(id) = self.declaration(path.root) else {
            return self.checked.types.fresh(None);
        };
        self.dependency(id);
        let kind = self
            .checked
            .analysis
            .declarations
            .get(id)
            .map(|declaration| declaration.kind);
        if path.fields.is_empty()
            && kind == Some(DeclarationKind::Set)
            && set
            && let Some(ty) = self.sets.get(&id)
        {
            self.checked
                .paths
                .insert(path.span, Resolution::Declaration(id));
            return *ty;
        }
        match kind {
            Some(DeclarationKind::Target | DeclarationKind::Claim | DeclarationKind::Asset) => self
                .error(
                    Code::UnresolvedInput,
                    Phase::Capture,
                    path.span,
                    "requested external input has no acquired scalar or finite-set interpretation",
                ),
            _ => self.error(
                Code::WrongNameKind,
                Phase::Resolve,
                path.span,
                if set {
                    "this name does not denote a finite set"
                } else {
                    "this name does not denote a scalar value"
                },
            ),
        }
        self.checked.types.fresh(None)
    }
}
