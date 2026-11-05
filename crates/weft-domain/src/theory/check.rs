use crate::{
    AtomId, DeclId, FormulaOp, InvariantError, LimitKind, NodeId, OriginKind, QuantifierId, Theory,
};
use std::collections::{BTreeSet, HashSet};

#[derive(Debug)]
pub struct PreparedCheck {
    query: NodeId,
    premises: Vec<NodeId>,
    nodes: Vec<NodeId>,
    atoms: Vec<AtomId>,
    quantifiers: Vec<QuantifierId>,
    dependencies: Vec<DeclId>,
}
impl PreparedCheck {
    pub fn query(&self) -> NodeId {
        self.query
    }
    pub fn premises(&self) -> &[NodeId] {
        &self.premises
    }
    pub fn nodes(&self) -> &[NodeId] {
        &self.nodes
    }
    pub fn atoms(&self) -> &[AtomId] {
        &self.atoms
    }
    pub fn quantifiers(&self) -> &[QuantifierId] {
        &self.quantifiers
    }
    pub fn dependencies(&self) -> &[DeclId] {
        &self.dependencies
    }
}
impl Theory {
    pub(crate) fn prepare(
        &mut self,
        query: NodeId,
        premises: Vec<NodeId>,
    ) -> Result<PreparedCheck, InvariantError> {
        self.charge_preparation(premises.len().saturating_add(1))?;
        let mut pending = premises.clone();
        pending.push(query);
        let mut seen = HashSet::new();
        let mut atoms = BTreeSet::new();
        while let Some(id) = pending.pop() {
            self.charge_preparation(1)?;
            if !seen.insert(id) {
                continue;
            }
            let node = self
                .node(id)
                .ok_or(InvariantError::InvalidReference("query node"))?;
            match node.operation {
                FormulaOp::Literal(_) => {}
                FormulaOp::Atom(atom) => {
                    atoms.insert(atom);
                }
                FormulaOp::Not(child) => pending.push(child),
                FormulaOp::And(left, right) | FormulaOp::Or(left, right) => {
                    pending.push(left);
                    pending.push(right);
                }
            }
        }
        self.charge_preparation(seen.len())?;
        let mut nodes: Vec<NodeId> = seen.into_iter().collect();
        nodes.sort_unstable();
        let quantifiers = nodes
            .iter()
            .filter_map(|id| self.quantifier_roots.get(id).copied())
            .collect();
        let dependencies = self.origin_dependencies(&nodes)?;
        Ok(PreparedCheck {
            query,
            premises,
            nodes,
            atoms: atoms.into_iter().collect(),
            quantifiers,
            dependencies,
        })
    }
    fn origin_dependencies(&mut self, nodes: &[NodeId]) -> Result<Vec<DeclId>, InvariantError> {
        self.charge_preparation(nodes.len())?;
        let mut pending = Vec::with_capacity(nodes.len());
        for id in nodes {
            pending.push(
                self.node(*id)
                    .ok_or(InvariantError::InvalidReference("origin node"))?
                    .origin,
            );
        }
        let mut seen = HashSet::new();
        let mut declarations = BTreeSet::new();
        while let Some(id) = pending.pop() {
            self.charge_preparation(1)?;
            if !seen.insert(id) {
                continue;
            }
            let parents = self
                .origin(id)
                .ok_or(InvariantError::InvalidReference("origin closure"))?
                .parents
                .len();
            self.charge_preparation(parents)?;
            let origin = self
                .origin(id)
                .ok_or(InvariantError::InvalidReference("origin record"))?;
            if let OriginKind::Reference(declaration) = origin.kind {
                declarations.insert(declaration);
            }
            pending.extend(origin.parents.iter().copied());
        }
        Ok(declarations.into_iter().collect())
    }
    pub(crate) fn charge_preparation(&mut self, amount: usize) -> Result<(), InvariantError> {
        if amount > self.work.remaining {
            return Err(InvariantError::Limit(LimitKind::Work));
        }
        self.work.remaining -= amount;
        self.work.used += amount;
        Ok(())
    }
}
