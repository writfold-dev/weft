use super::{Binder, FiniteSet, pool::Pool};
use crate::{
    AtomId, BinderId, FormulaNode, FormulaOp, GroundAtom, InvariantError, LimitKind, Limits,
    NodeId, Origin, OriginId, OriginKind, Quantified, Scalar, SourceSpan, Theory, ValueId,
    WorkUsage,
};

#[derive(Debug)]
pub struct TheoryBuilder {
    pub(super) values: Pool<Scalar>,
    pub(super) atoms: Pool<GroundAtom>,
    pub(super) nodes: Vec<FormulaNode>,
    pub(super) origins: Vec<Origin>,
    pub(super) sets: Vec<FiniteSet>,
    pub(super) binders: Vec<Binder>,
    pub(super) quantifiers: Vec<Quantified>,
    pub(super) limits: Limits,
    pub(super) used: usize,
    pub(super) instance_count: usize,
}
impl TheoryBuilder {
    pub fn new(limits: Limits) -> Self {
        Self {
            values: Pool::default(),
            atoms: Pool::default(),
            nodes: Vec::new(),
            origins: Vec::new(),
            sets: Vec::new(),
            binders: Vec::new(),
            quantifiers: Vec::new(),
            limits,
            used: 0,
            instance_count: 0,
        }
    }
    pub fn charge(&mut self, amount: usize) -> Result<(), InvariantError> {
        let used = self
            .used
            .checked_add(amount)
            .ok_or(InvariantError::Limit(LimitKind::Work))?;
        if used > self.limits.work {
            return Err(InvariantError::Limit(LimitKind::Work));
        }
        self.used = used;
        Ok(())
    }
    pub fn intern_value(&mut self, value: Scalar) -> Result<ValueId, InvariantError> {
        self.charge(1)?;
        Ok(ValueId::at(self.values.intern(value)))
    }
    pub fn value(&self, id: ValueId) -> Option<&Scalar> {
        self.values
            .values
            .get(id.index())
            .map(|value| value.as_ref())
    }
    pub fn node(&self, id: NodeId) -> Option<&FormulaNode> {
        self.nodes.get(id.index())
    }
    pub fn quantifiers(&self) -> &[Quantified] {
        &self.quantifiers
    }
    pub fn intern_atom(
        &mut self,
        name: String,
        arguments: Vec<ValueId>,
    ) -> Result<AtomId, InvariantError> {
        self.charge(arguments.len().saturating_add(1))?;
        if arguments.iter().any(|id| self.value(*id).is_none()) {
            return Err(InvariantError::InvalidReference("atom argument"));
        }
        Ok(AtomId::at(
            self.atoms.intern(GroundAtom { name, arguments }),
        ))
    }
    pub fn add_origin(
        &mut self,
        kind: OriginKind,
        span: SourceSpan,
        parents: Vec<OriginId>,
    ) -> Result<OriginId, InvariantError> {
        self.charge(parents.len().saturating_add(1))?;
        if parents.iter().any(|id| id.index() >= self.origins.len()) {
            return Err(InvariantError::InvalidReference("origin edge"));
        }
        match kind {
            OriginKind::Bound { binder, value } => {
                if binder.index() >= self.binders.len() || self.value(value).is_none() {
                    return Err(InvariantError::InvalidReference("bound origin"));
                }
            }
            OriginKind::Spread(set) if set.index() >= self.sets.len() => {
                return Err(InvariantError::InvalidReference("spread origin"));
            }
            _ => {}
        }
        let id = OriginId::at(self.origins.len());
        self.origins.push(Origin {
            kind,
            span,
            parents,
        });
        Ok(id)
    }
    pub fn add_node(&mut self, node: FormulaNode) -> Result<NodeId, InvariantError> {
        self.charge(1)?;
        if self.nodes.len() >= self.limits.nodes {
            return Err(InvariantError::Limit(LimitKind::Nodes));
        }
        if node.origin.index() >= self.origins.len() {
            return Err(InvariantError::InvalidReference("node origin"));
        }
        let valid = |id: NodeId| id.index() < self.nodes.len();
        let valid_operation = match node.operation {
            FormulaOp::Literal(_) => true,
            FormulaOp::Atom(id) => id.index() < self.atoms.values.len(),
            FormulaOp::Not(child) => valid(child),
            FormulaOp::And(a, b) | FormulaOp::Or(a, b) => valid(a) && valid(b),
        };
        if !valid_operation {
            return Err(InvariantError::InvalidReference("formula edge"));
        }
        self.validate_detail(&node)?;
        let id = NodeId::at(self.nodes.len());
        self.nodes.push(node);
        Ok(id)
    }
    fn validate_detail(&self, node: &FormulaNode) -> Result<(), InvariantError> {
        use crate::NodeDetail;
        match node.detail {
            NodeDetail::Comparison { left, right, .. } => {
                if self.value(left).is_none() || self.value(right).is_none() {
                    return Err(InvariantError::InvalidReference("comparison detail"));
                }
            }
            NodeDetail::SetComparison { left, right, .. }
                if left.index() >= self.sets.len() || right.index() >= self.sets.len() =>
            {
                return Err(InvariantError::InvalidReference("set comparison detail"));
            }
            _ => {}
        }
        Ok(())
    }
    pub fn add_binder(
        &mut self,
        name: String,
        span: SourceSpan,
    ) -> Result<BinderId, InvariantError> {
        self.charge(1)?;
        let id = BinderId::at(self.binders.len());
        self.binders.push(Binder { id, name, span });
        Ok(id)
    }
    pub fn quantifier_count(&self) -> usize {
        self.quantifiers.len()
    }
    pub fn work(&self) -> WorkUsage {
        WorkUsage {
            admitted: self.limits.work,
            used: self.used,
            remaining: self.limits.work - self.used,
        }
    }
    pub fn finish(self) -> Theory {
        let work = self.work();
        let quantifier_roots = self
            .quantifiers
            .iter()
            .map(|entry| (entry.root, entry.id))
            .collect();
        Theory {
            values: self.values.values,
            atoms: self.atoms.values,
            nodes: self.nodes,
            origins: self.origins,
            sets: self.sets,
            binders: self.binders,
            quantifiers: self.quantifiers,
            quantifier_roots,
            work,
        }
    }
}
