use crate::{ast, lower::Lower, semantic::Resolution};
use weft_domain::{
    Comparison, Diagnostic, FormulaNode, FormulaOp, NodeDetail, NodeId, OriginId, OriginKind,
    QuantifierId, SourceSpan,
};

pub(crate) struct Lowered {
    pub node: NodeId,
    pub origin: OriginId,
    pub nested: Vec<QuantifierId>,
}
impl<'s> Lower<'_, 's> {
    pub fn expression(&mut self, id: ast::ExprId) -> Result<Lowered, Diagnostic> {
        let expression = self
            .parsed
            .expression(id)
            .ok_or_else(|| self.invalid(self.parsed.header.span, "missing expression"))?;
        let span = expression.span;
        self.checked
            .builder
            .charge(1)
            .map_err(|error| self.failure(error, span))?;
        match &expression.kind {
            ast::ExprKind::Boolean(value) => self.node(
                FormulaOp::Literal(*value),
                NodeDetail::Literal,
                OriginKind::Literal,
                span,
                Vec::new(),
                Vec::new(),
            ),
            ast::ExprKind::Not(child) => {
                let child = self.expression(*child)?;
                self.node(
                    FormulaOp::Not(child.node),
                    NodeDetail::Boolean,
                    OriginKind::Boolean,
                    span,
                    vec![child.origin],
                    child.nested,
                )
            }
            ast::ExprKind::And(left, right) => self.binary(*left, *right, FormulaOp::And, span),
            ast::ExprKind::Or(left, right) => self.binary(*left, *right, FormulaOp::Or, span),
            ast::ExprKind::Compare {
                operation,
                left,
                right,
            } => self.compare(*operation, left, right, span),
            ast::ExprKind::Predicate { name, arguments } => self.predicate(*name, arguments, span),
            ast::ExprKind::Quantifier {
                kind, domain, body, ..
            } => self.quantifier(id, *kind, *domain, *body, span),
        }
    }
    fn binary(
        &mut self,
        left: ast::ExprId,
        right: ast::ExprId,
        operation: fn(NodeId, NodeId) -> FormulaOp,
        span: SourceSpan,
    ) -> Result<Lowered, Diagnostic> {
        let mut left = self.expression(left)?;
        let right = self.expression(right)?;
        left.nested.extend(right.nested);
        self.node(
            operation(left.node, right.node),
            NodeDetail::Boolean,
            OriginKind::Boolean,
            span,
            vec![left.origin, right.origin],
            left.nested,
        )
    }
    fn predicate(
        &mut self,
        name: ast::Name<'s>,
        arguments: &[ast::Value<'s>],
        span: SourceSpan,
    ) -> Result<Lowered, Diagnostic> {
        let mut values = Vec::with_capacity(arguments.len());
        let mut origins = Vec::with_capacity(arguments.len());
        for argument in arguments {
            let (value, origin) = self.value(argument)?;
            values.push(value);
            origins.push(origin);
        }
        let atom = self
            .checked
            .builder
            .intern_atom(name.text.into(), values)
            .map_err(|error| self.failure(error, span))?;
        self.node(
            FormulaOp::Atom(atom),
            NodeDetail::Predicate,
            OriginKind::Predicate,
            span,
            origins,
            Vec::new(),
        )
    }
    fn node(
        &mut self,
        operation: FormulaOp,
        detail: NodeDetail,
        kind: OriginKind,
        span: SourceSpan,
        parents: Vec<OriginId>,
        nested: Vec<QuantifierId>,
    ) -> Result<Lowered, Diagnostic> {
        let origin = self.origin(kind, span, parents)?;
        let node = self
            .checked
            .builder
            .add_node(FormulaNode {
                operation,
                span,
                origin,
                detail,
            })
            .map_err(|error| self.failure(error, span))?;
        Ok(Lowered {
            node,
            origin,
            nested,
        })
    }
    fn compare(
        &mut self,
        operation: Comparison,
        left: &ast::Comparable<'s>,
        right: &ast::Comparable<'s>,
        span: SourceSpan,
    ) -> Result<Lowered, Diagnostic> {
        match operation {
            Comparison::Member => return self.membership(left, right, span),
            Comparison::Subset => return self.subset(left, right, span),
            Comparison::Equal | Comparison::NotEqual => {}
        }
        let (equal, detail, origins) = if self.is_set(left) {
            let left = self.comparable_set(left, span)?;
            let right = self.comparable_set(right, span)?;
            let equal = self
                .checked
                .builder
                .sets_equal(left, right)
                .map_err(|error| self.failure(error, span))?;
            let left_origin = self
                .checked
                .builder
                .set(left)
                .ok_or_else(|| self.invalid(span, "missing comparison set"))?
                .origin;
            let right_origin = self
                .checked
                .builder
                .set(right)
                .ok_or_else(|| self.invalid(span, "missing comparison set"))?
                .origin;
            (
                equal,
                NodeDetail::SetComparison {
                    operation,
                    left,
                    right,
                    counterexample: None,
                },
                vec![left_origin, right_origin],
            )
        } else {
            let ast::Comparable::Value(left) = left else {
                return Err(self.invalid(span, "expected scalar comparison"));
            };
            let ast::Comparable::Value(right) = right else {
                return Err(self.invalid(span, "expected scalar comparison"));
            };
            let (left, left_origin) = self.value(left)?;
            let (right, right_origin) = self.value(right)?;
            (
                left == right,
                NodeDetail::Comparison {
                    operation,
                    left,
                    right,
                },
                vec![left_origin, right_origin],
            )
        };
        let result = match operation {
            Comparison::Equal => equal,
            Comparison::NotEqual => !equal,
            Comparison::Member | Comparison::Subset => {
                return Err(self.invalid(span, "unreachable comparison operation"));
            }
        };
        self.node(
            FormulaOp::Literal(result),
            detail,
            OriginKind::Comparison,
            span,
            origins,
            Vec::new(),
        )
    }

    /// `x in s`: the scalar and the whole right-hand set are materialized
    /// before the typed probe; an unavailable set is never non-membership.
    fn membership(
        &mut self,
        left: &ast::Comparable<'s>,
        right: &ast::Comparable<'s>,
        span: SourceSpan,
    ) -> Result<Lowered, Diagnostic> {
        let ast::Comparable::Value(left_value) = left else {
            return Err(self.invalid(span, "membership probe must be a scalar value"));
        };
        let (value, value_origin) = self.value(left_value)?;
        let set = self.comparable_set(right, span)?;
        let member = self
            .checked
            .builder
            .set_member(value, set)
            .map_err(|error| self.failure(error, span))?;
        let set_origin = self
            .checked
            .builder
            .set(set)
            .ok_or_else(|| self.invalid(span, "missing membership set"))?
            .origin;
        self.node(
            FormulaOp::Literal(member),
            NodeDetail::Membership { value, set },
            OriginKind::Comparison,
            span,
            vec![value_origin, set_origin],
            Vec::new(),
        )
    }

    /// `a <= b`: both whole sets materialized; a false subset keeps the
    /// deterministic first-left counterexample member for the report.
    fn subset(
        &mut self,
        left: &ast::Comparable<'s>,
        right: &ast::Comparable<'s>,
        span: SourceSpan,
    ) -> Result<Lowered, Diagnostic> {
        let left = self.comparable_set(left, span)?;
        let right = self.comparable_set(right, span)?;
        let (holds, counterexample) = self
            .checked
            .builder
            .set_subset(left, right)
            .map_err(|error| self.failure(error, span))?;
        let left_origin = self
            .checked
            .builder
            .set(left)
            .ok_or_else(|| self.invalid(span, "missing comparison set"))?
            .origin;
        let right_origin = self
            .checked
            .builder
            .set(right)
            .ok_or_else(|| self.invalid(span, "missing comparison set"))?
            .origin;
        self.node(
            FormulaOp::Literal(holds),
            NodeDetail::SetComparison {
                operation: Comparison::Subset,
                left,
                right,
                counterexample: counterexample.map(|member| member.value),
            },
            OriginKind::Comparison,
            span,
            vec![left_origin, right_origin],
            Vec::new(),
        )
    }
    fn is_set(&self, value: &ast::Comparable<'s>) -> bool {
        match value {
            ast::Comparable::Set(_) => true,
            ast::Comparable::Value(ast::Value::Path(path)) => matches!(
                self.checked.paths.get(&path.span),
                Some(Resolution::Declaration(_))
            ),
            ast::Comparable::Value(_) => false,
        }
    }
    fn comparable_set(
        &mut self,
        value: &ast::Comparable<'s>,
        span: SourceSpan,
    ) -> Result<weft_domain::SetId, Diagnostic> {
        match value {
            ast::Comparable::Set(id) => self.set(*id),
            ast::Comparable::Value(ast::Value::Path(path)) => self.set_path(path),
            _ => Err(self.invalid(span, "expected finite-set comparison")),
        }
    }
}
