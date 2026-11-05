use crate::{
    BinderId, EnclosingInstance, FiniteSet, FormulaNode, FormulaOp, Instance, InvariantError,
    LimitKind, NodeDetail, NodeId, OriginId, OriginKind, Quantified, QuantifierId, QuantifierKind,
    ScalarType, SetId, SetMember, SourceSpan, TheoryBuilder,
};
use std::collections::HashMap;

impl TheoryBuilder {
    pub fn set(&self, id: SetId) -> Option<&FiniteSet> {
        self.sets.get(id.index())
    }
    pub fn add_set(
        &mut self,
        element_type: Option<ScalarType>,
        raw: Vec<SetMember>,
        span: SourceSpan,
        extra_origins: Vec<OriginId>,
    ) -> Result<SetId, InvariantError> {
        self.charge(
            raw.len()
                .saturating_add(extra_origins.len())
                .saturating_add(1),
        )?;
        if raw.len() > self.limits.members {
            return Err(InvariantError::Limit(LimitKind::Members));
        }
        let raw_occurrences = raw.len();
        let element_type = match (element_type, raw.first()) {
            (Some(ty), _) => Some(ty),
            (None, Some(first)) => Some(
                self.value(first.value)
                    .ok_or(InvariantError::InvalidReference("set member"))?
                    .scalar_type(),
            ),
            (None, None) => None,
        };
        let mut parents = extra_origins;
        let mut members: Vec<SetMember> = Vec::new();
        let mut positions: HashMap<crate::ValueId, usize> = HashMap::new();
        for member in raw {
            let value = self
                .value(member.value)
                .ok_or(InvariantError::InvalidReference("set member"))?;
            if !element_type.as_ref().is_some_and(|ty| value.has_type(ty)) {
                return Err(InvariantError::MixedSetTypes);
            }
            if member.origin.index() >= self.origins.len() {
                return Err(InvariantError::InvalidReference("set origin"));
            }
            parents.push(member.origin);
            if let Some(&position) = positions.get(&member.value) {
                let prior: &SetMember = members
                    .get(position)
                    .ok_or(InvariantError::InvalidReference("member index"))?;
                let origin = self.add_origin(
                    OriginKind::Normalize,
                    span,
                    vec![prior.origin, member.origin],
                )?;
                let prior = members
                    .get_mut(position)
                    .ok_or(InvariantError::InvalidReference("member index"))?;
                prior.origin = origin;
            } else {
                positions.insert(member.value, members.len());
                members.push(member);
            }
        }
        let origin = self.add_origin(OriginKind::Normalize, span, parents)?;
        let id = SetId::at(self.sets.len());
        self.sets.push(FiniteSet {
            id,
            element_type,
            members,
            raw_occurrences,
            origin,
            span,
        });
        Ok(id)
    }
    pub fn sets_equal(&mut self, left: SetId, right: SetId) -> Result<bool, InvariantError> {
        let a = self
            .set(left)
            .ok_or(InvariantError::InvalidReference("left set"))?;
        let b = self
            .set(right)
            .ok_or(InvariantError::InvalidReference("right set"))?;
        let work = a
            .members
            .len()
            .saturating_add(b.members.len())
            .saturating_add(1);
        self.charge(work)?;
        let a = self
            .set(left)
            .ok_or(InvariantError::InvalidReference("left set"))?;
        let b = self
            .set(right)
            .ok_or(InvariantError::InvalidReference("right set"))?;
        if matches!((&a.element_type, &b.element_type), (Some(x), Some(y)) if x != y) {
            return Err(InvariantError::MixedSetTypes);
        }
        if a.members.len() != b.members.len() {
            return Ok(false);
        }
        let membership: std::collections::HashSet<_> =
            a.members.iter().map(|entry| entry.value).collect();
        Ok(b.members
            .iter()
            .all(|entry| membership.contains(&entry.value)))
    }
    pub fn quantify(
        &mut self,
        kind: QuantifierKind,
        binder: BinderId,
        domain: SetId,
        bodies: Vec<NodeId>,
        span: SourceSpan,
    ) -> Result<(QuantifierId, NodeId), InvariantError> {
        let set = self
            .set(domain)
            .ok_or(InvariantError::InvalidReference("quantifier domain"))?;
        if bodies.len() != set.members.len()
            || binder.index() >= self.binders.len()
            || bodies.iter().any(|id| id.index() >= self.nodes.len())
        {
            return Err(InvariantError::InvalidReference("quantifier coverage"));
        }
        let domain_origin = set.origin;
        let count = self
            .instance_count
            .checked_add(bodies.len())
            .ok_or(InvariantError::Limit(LimitKind::Instances))?;
        if count > self.limits.instances {
            return Err(InvariantError::Limit(LimitKind::Instances));
        }
        self.charge(bodies.len().saturating_add(1))?;
        let mut parents = Vec::with_capacity(bodies.len().saturating_add(1));
        parents.push(domain_origin);
        for body in &bodies {
            parents.push(
                self.node(*body)
                    .ok_or(InvariantError::InvalidReference("instance origin"))?
                    .origin,
            );
        }
        let origin = self.add_origin(OriginKind::Quantifier, span, parents)?;
        let root = self.quantifier_fold(kind, &bodies, span, origin)?;
        let id = QuantifierId::at(self.quantifiers.len());
        let instances = bodies
            .into_iter()
            .enumerate()
            .map(|(member, body)| Instance { member, body })
            .collect();
        self.quantifiers.push(Quantified {
            id,
            kind,
            binder,
            domain,
            instances,
            root,
            span,
            enclosing: None,
        });
        self.instance_count = count;
        Ok((id, root))
    }
    fn quantifier_fold(
        &mut self,
        kind: QuantifierKind,
        bodies: &[NodeId],
        span: SourceSpan,
        origin: OriginId,
    ) -> Result<NodeId, InvariantError> {
        let mut root = self.add_node(FormulaNode {
            operation: FormulaOp::Literal(kind == QuantifierKind::Forall),
            span,
            origin,
            detail: NodeDetail::QuantifierFold,
        })?;
        for body in bodies.iter().rev() {
            let operation = match kind {
                QuantifierKind::Forall => FormulaOp::And(*body, root),
                QuantifierKind::Exists => FormulaOp::Or(*body, root),
            };
            root = self.add_node(FormulaNode {
                operation,
                span,
                origin,
                detail: NodeDetail::QuantifierFold,
            })?;
        }
        Ok(root)
    }
    pub fn attach_enclosing(
        &mut self,
        child: QuantifierId,
        parent: QuantifierId,
        member: usize,
    ) -> Result<(), InvariantError> {
        if child.index() >= parent.index() {
            return Err(InvariantError::InvalidReference("quantifier containment"));
        }
        let enclosing = self
            .quantifiers
            .get(parent.index())
            .ok_or(InvariantError::InvalidReference("enclosing quantifier"))?;
        let instance = enclosing
            .instances
            .get(member)
            .ok_or(InvariantError::InvalidReference("enclosing member"))?;
        let nested = self
            .quantifiers
            .get(child.index())
            .ok_or(InvariantError::InvalidReference("nested quantifier"))?;
        if nested.enclosing.is_some() || !self.reachable(instance.body, nested.root)? {
            return Err(InvariantError::InvalidReference("nested body"));
        }
        let nested = self
            .quantifiers
            .get_mut(child.index())
            .ok_or(InvariantError::InvalidReference("nested quantifier"))?;
        nested.enclosing = Some(EnclosingInstance {
            quantifier: parent,
            member,
        });
        Ok(())
    }
    fn reachable(&mut self, root: NodeId, target: NodeId) -> Result<bool, InvariantError> {
        let mut pending = vec![root];
        let mut seen = std::collections::HashSet::new();
        while let Some(id) = pending.pop() {
            self.charge(1)?;
            if id == target {
                return Ok(true);
            }
            if !seen.insert(id) {
                continue;
            }
            match self
                .nodes
                .get(id.index())
                .ok_or(InvariantError::InvalidReference("body edge"))?
                .operation
            {
                FormulaOp::Not(child) => pending.push(child),
                FormulaOp::And(a, b) | FormulaOp::Or(a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                _ => {}
            }
        }
        Ok(false)
    }
}
