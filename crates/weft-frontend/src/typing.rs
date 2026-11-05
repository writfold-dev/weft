use crate::{
    ast,
    semantic::{Checker, Signature},
    types::TypeVar,
};
use weft_domain::{Code, DeclarationKind, Label, Phase, ScalarType};

impl<'s> Checker<'_, 's> {
    pub fn expression(&mut self, id: ast::ExprId) {
        let Some(expression) = self.parsed.expression(id) else {
            self.error(
                Code::InvalidProgram,
                Phase::Type,
                self.parsed.header.span,
                "missing source expression",
            );
            return;
        };
        match &expression.kind {
            ast::ExprKind::Boolean(_) => {}
            ast::ExprKind::Not(child) => self.expression(*child),
            ast::ExprKind::And(left, right) | ast::ExprKind::Or(left, right) => {
                self.expression(*left);
                self.expression(*right);
            }
            ast::ExprKind::Compare {
                operation,
                left,
                right,
            } => self.comparison(*operation, left, right, expression.span),
            ast::ExprKind::Predicate { name, arguments } => self.predicate(*name, arguments),
            ast::ExprKind::Quantifier {
                binder,
                domain,
                body,
                ..
            } => {
                let ty = self.set_type(*domain);
                match self
                    .checked
                    .builder
                    .add_binder(binder.text.into(), binder.span)
                {
                    Ok(binder_id) => {
                        self.checked.binders.insert(id, binder_id);
                        self.scope.push((binder.text, binder_id, ty));
                        self.expression(*body);
                        self.scope.pop();
                    }
                    Err(error) => self
                        .current
                        .diagnostics
                        .push(crate::semantic::invariant(error, binder.span)),
                }
            }
        }
    }
    fn comparison(
        &mut self,
        operation: weft_domain::Comparison,
        left: &ast::Comparable<'s>,
        right: &ast::Comparable<'s>,
        span: weft_domain::SourceSpan,
    ) {
        let (left_set, left_type) = self.comparable(left);
        let (right_set, right_type) = self.comparable(right);
        match operation {
            weft_domain::Comparison::Member => {
                if left_set || !right_set {
                    self.error(
                        Code::TypeMismatch,
                        Phase::Type,
                        span,
                        "membership takes a scalar or reference on the left and a finite set on the right",
                    );
                } else {
                    self.unify(left_type, right_type, span);
                }
            }
            weft_domain::Comparison::Subset => {
                if !left_set || !right_set {
                    self.error(
                        Code::TypeMismatch,
                        Phase::Type,
                        span,
                        "subset compares two finite sets of the same element type",
                    );
                } else {
                    self.unify(left_type, right_type, span);
                }
            }
            weft_domain::Comparison::Equal | weft_domain::Comparison::NotEqual => {
                if left_set != right_set {
                    self.error(
                        Code::TypeMismatch,
                        Phase::Type,
                        span,
                        "a set and a scalar cannot be compared",
                    );
                } else {
                    self.unify(left_type, right_type, span);
                }
            }
        }
    }

    fn comparable(&mut self, comparable: &ast::Comparable<'s>) -> (bool, TypeVar) {
        match comparable {
            ast::Comparable::Set(id) => (true, self.set_type(*id)),
            ast::Comparable::Value(ast::Value::Path(path)) if self.is_set_path(path) => {
                (true, self.path(path, true))
            }
            ast::Comparable::Value(value) => (false, self.value_type(value)),
        }
    }
    fn is_set_path(&self, path: &ast::Path<'s>) -> bool {
        if !path.fields.is_empty()
            || self
                .scope
                .iter()
                .any(|(name, _, _)| *name == path.root.text)
        {
            return false;
        }
        self.checked
            .analysis
            .declarations
            .find(path.root.text)
            .and_then(|id| self.checked.analysis.declarations.get(id))
            .is_some_and(|declaration| declaration.kind == DeclarationKind::Set)
    }
    pub fn value_type(&mut self, value: &ast::Value<'s>) -> TypeVar {
        let ty = match value {
            ast::Value::Boolean(..) => ScalarType::Boolean,
            ast::Value::Natural(..) => ScalarType::Natural,
            ast::Value::Text(_) => ScalarType::Text,
            ast::Value::Path(path) => return self.path(path, false),
        };
        self.checked.types.fresh(Some(ty))
    }
    pub fn set_type(&mut self, id: ast::SetExprId) -> TypeVar {
        if let Some(ty) = self.checked.set_types.get(&id) {
            return *ty;
        }
        let Some(set) = self.parsed.set(id) else {
            self.error(
                Code::InvalidProgram,
                Phase::Type,
                self.parsed.header.span,
                "missing source set expression",
            );
            return self.checked.types.fresh(None);
        };
        let ty = match &set.kind {
            ast::SetKind::Path(path) => self.path(path, true),
            ast::SetKind::Binary { left, right, .. } => {
                let ty = self.set_type(*left);
                let right_type = self.set_type(*right);
                self.unify(ty, right_type, set.span);
                ty
            }
            ast::SetKind::Literal(items) => {
                let ty = self.checked.types.fresh(None);
                for item in items {
                    let (item_type, span) = match item {
                        ast::SetItem::Value(value) => (self.value_type(value), value.span()),
                        ast::SetItem::Spread(set, span) => (self.set_type(*set), *span),
                    };
                    self.unify(ty, item_type, span);
                }
                ty
            }
        };
        self.checked.set_types.insert(id, ty);
        ty
    }
    fn predicate(&mut self, name: ast::Name<'s>, arguments: &[ast::Value<'s>]) {
        let argument_types: Vec<_> = arguments
            .iter()
            .map(|value| self.value_type(value))
            .collect();
        if let Some(signature) = self.signatures.get(name.text) {
            let previous = signature.arguments.clone();
            let previous_span = signature.span;
            if previous.len() != arguments.len() {
                self.error(
                    Code::ArityMismatch,
                    Phase::Type,
                    name.span,
                    "predicate arity differs from its first occurrence",
                );
                if let Some(diagnostic) = self.current.diagnostics.last_mut() {
                    diagnostic.expected = Some(previous.len().to_string().into_boxed_str());
                    diagnostic.actual = Some(arguments.len().to_string().into_boxed_str());
                    diagnostic.secondary.push(Label {
                        span: previous_span,
                        message: "first predicate signature".into(),
                    });
                }
            }
            for (expected, actual) in previous.iter().zip(&argument_types) {
                self.unify(*expected, *actual, name.span);
            }
        } else {
            self.signatures.insert(
                name.text,
                Signature {
                    arguments: argument_types.clone(),
                    span: name.span,
                },
            );
        }
        for (ty, value) in argument_types.into_iter().zip(arguments) {
            self.required_types.push((ty, value.span(), self.statement));
        }
    }
}
