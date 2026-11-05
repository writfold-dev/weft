use crate::{ast, lower::Lower, lower_expr::Lowered};
use weft_domain::{Diagnostic, QuantifierKind, SourceSpan};

impl Lower<'_, '_> {
    pub fn quantifier(
        &mut self,
        expression: ast::ExprId,
        kind: QuantifierKind,
        domain: ast::SetExprId,
        body: ast::ExprId,
        span: SourceSpan,
    ) -> Result<Lowered, Diagnostic> {
        let binder = self
            .checked
            .binders
            .get(&expression)
            .copied()
            .ok_or_else(|| self.invalid(span, "missing lexical binder"))?;
        let domain = self.set(domain)?;
        let count = self
            .checked
            .builder
            .set(domain)
            .ok_or_else(|| self.invalid(span, "missing quantifier domain"))?
            .members
            .len();
        let instances = self
            .instances
            .checked_add(count)
            .ok_or_else(|| self.limit(span, "instance count overflows"))?;
        if instances > self.limits.instances {
            return Err(self.limit(span, "aggregate quantifier instance limit exceeded"));
        }
        self.checked
            .builder
            .charge(count)
            .map_err(|error| self.failure(error, span))?;
        self.instances = instances;
        let mut bodies = Vec::with_capacity(count);
        let mut nested = Vec::new();
        for index in 0..count {
            let member = self.member(domain, index, span)?;
            self.environment.push((binder, member));
            let result = self.expression(body);
            self.environment.pop();
            let lowered = result?;
            bodies.push(lowered.node);
            nested.extend(lowered.nested.into_iter().map(|child| (index, child)));
        }
        let (quantifier, node) = self
            .checked
            .builder
            .quantify(kind, binder, domain, bodies, span)
            .map_err(|error| self.failure(error, span))?;
        for (member, child) in nested {
            self.checked
                .builder
                .attach_enclosing(child, quantifier, member)
                .map_err(|error| self.failure(error, span))?;
        }
        let origin = self
            .checked
            .builder
            .node(node)
            .ok_or_else(|| self.invalid(span, "missing quantified root"))?
            .origin;
        Ok(Lowered {
            node,
            origin,
            nested: vec![quantifier],
        })
    }
}
