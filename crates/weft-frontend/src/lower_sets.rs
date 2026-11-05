use crate::{ast, lower::Lower, semantic::Resolution};
use weft_domain::{
    Code, Diagnostic, Natural, OriginId, OriginKind, Phase, Scalar, SetId, SetMember, SourceSpan,
    ValueId,
};

impl<'s> Lower<'_, 's> {
    pub fn value(&mut self, value: &ast::Value<'s>) -> Result<(ValueId, OriginId), Diagnostic> {
        let span = value.span();
        if let Some(value) = self.literals.get(&span) {
            return Ok(*value);
        }
        let scalar = match value {
            ast::Value::Boolean(value, _) => Scalar::Boolean(*value),
            ast::Value::Natural(digits, _) => {
                Scalar::Natural(Natural::parse(digits).map_err(|error| self.failure(error, span))?)
            }
            ast::Value::Text(text) => Scalar::Text(text.value.to_string()),
            ast::Value::Path(path) => return self.bound_value(path),
        };
        let id = self
            .checked
            .builder
            .intern_value(scalar)
            .map_err(|error| self.failure(error, span))?;
        let origin = self.origin(OriginKind::Literal, span, Vec::new())?;
        self.literals.insert(span, (id, origin));
        Ok((id, origin))
    }
    fn bound_value(&mut self, path: &ast::Path<'s>) -> Result<(ValueId, OriginId), Diagnostic> {
        let Some(Resolution::Binder(binder)) = self.checked.paths.get(&path.span).copied() else {
            return Err(self.invalid(path.span, "scalar path has no checked binder resolution"));
        };
        let member = self
            .environment
            .iter()
            .rev()
            .find(|(id, _)| *id == binder)
            .map(|(_, member)| *member)
            .ok_or_else(|| self.invalid(path.span, "bound value is unavailable"))?;
        let origin = self.origin(
            OriginKind::Bound {
                binder,
                value: member.value,
            },
            path.span,
            vec![member.origin],
        )?;
        Ok((member.value, origin))
    }
    pub fn set(&mut self, id: ast::SetExprId) -> Result<SetId, Diagnostic> {
        let expression = self
            .parsed
            .set(id)
            .ok_or_else(|| self.invalid(self.parsed.header.span, "missing set expression"))?;
        match &expression.kind {
            ast::SetKind::Path(path) => self.set_path(path),
            ast::SetKind::Binary {
                operation,
                left,
                right,
            } => {
                let left = self.set(*left)?;
                let right = self.set(*right)?;
                let result = match operation {
                    weft_domain::SetOperation::Union => {
                        self.checked.builder.set_union(left, right, expression.span)
                    }
                    weft_domain::SetOperation::Intersection => self
                        .checked
                        .builder
                        .set_intersection(left, right, expression.span),
                    weft_domain::SetOperation::Difference => {
                        self.checked
                            .builder
                            .set_difference(left, right, expression.span)
                    }
                };
                result.map_err(|error| self.failure(error, expression.span))
            }
            ast::SetKind::Literal(items) => {
                let mut raw = Vec::new();
                let mut extras = Vec::new();
                for item in items {
                    match item {
                        ast::SetItem::Value(value) => {
                            self.reserve_members(raw.len(), 1, value.span())?;
                            let (value_id, source) = self.value(value)?;
                            let origin =
                                self.origin(OriginKind::SetMember, value.span(), vec![source])?;
                            raw.push(SetMember {
                                value: value_id,
                                origin,
                            });
                        }
                        ast::SetItem::Spread(set, span) => {
                            let set = self.set(*set)?;
                            self.spread(set, *span, &mut raw, &mut extras)?;
                        }
                    }
                }
                let ty = self
                    .checked
                    .set_types
                    .get(&id)
                    .and_then(|ty| self.checked.types.concrete(*ty))
                    .cloned();
                self.checked
                    .builder
                    .add_set(ty, raw, expression.span, extras)
                    .map_err(|error| self.failure(error, expression.span))
            }
        }
    }
    pub fn set_path(&mut self, path: &ast::Path<'s>) -> Result<SetId, Diagnostic> {
        let Some(Resolution::Declaration(declaration)) =
            self.checked.paths.get(&path.span).copied()
        else {
            return Err(self.invalid(path.span, "set path has no checked declaration resolution"));
        };
        let set = self.sets.get(&declaration).copied().ok_or_else(|| {
            Diagnostic::new(
                Code::UnresolvedInput,
                Phase::Lower,
                "set initializer could not be completely materialized",
                Some(path.span),
            )
        })?;
        let source = self
            .checked
            .builder
            .set(set)
            .ok_or_else(|| self.invalid(path.span, "missing bound set"))?;
        let (count, origin, ty) = (
            source.members.len(),
            source.origin,
            source.element_type.clone(),
        );
        self.reserve_members(0, count, path.span)?;
        let reference = self.origin(OriginKind::Reference(declaration), path.span, vec![origin])?;
        let mut raw = Vec::with_capacity(count);
        for index in 0..count {
            let member = self.member(set, index, path.span)?;
            let origin = self.origin(
                OriginKind::SetMember,
                path.span,
                vec![reference, member.origin],
            )?;
            raw.push(SetMember {
                value: member.value,
                origin,
            });
        }
        self.checked
            .builder
            .add_set(ty, raw, path.span, vec![reference])
            .map_err(|error| self.failure(error, path.span))
    }
    fn spread(
        &mut self,
        set: SetId,
        span: SourceSpan,
        raw: &mut Vec<SetMember>,
        extras: &mut Vec<OriginId>,
    ) -> Result<(), Diagnostic> {
        let source = self
            .checked
            .builder
            .set(set)
            .ok_or_else(|| self.invalid(span, "missing spread set"))?;
        let (count, parent) = (source.members.len(), source.origin);
        self.reserve_members(raw.len(), count, span)?;
        let spread = self.origin(OriginKind::Spread(set), span, vec![parent])?;
        extras.push(spread);
        raw.reserve(count);
        for index in 0..count {
            let member = self.member(set, index, span)?;
            let origin = self.origin(OriginKind::SetMember, span, vec![spread, member.origin])?;
            raw.push(SetMember {
                value: member.value,
                origin,
            });
        }
        Ok(())
    }
    fn reserve_members(
        &mut self,
        current: usize,
        additional: usize,
        span: SourceSpan,
    ) -> Result<(), Diagnostic> {
        let count = current
            .checked_add(additional)
            .ok_or_else(|| self.limit(span, "set member count overflows"))?;
        if count > self.limits.members {
            return Err(self.limit(span, "set materialization exceeds member limit"));
        }
        self.checked
            .builder
            .charge(additional)
            .map_err(|error| self.failure(error, span))
    }
    pub fn member(
        &self,
        set: SetId,
        index: usize,
        span: SourceSpan,
    ) -> Result<SetMember, Diagnostic> {
        self.checked
            .builder
            .set(set)
            .and_then(|set| set.members.get(index))
            .copied()
            .ok_or_else(|| self.invalid(span, "missing normalized member"))
    }
}
