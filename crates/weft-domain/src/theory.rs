mod algebra;
mod builder;
mod check;
mod finite;
mod pool;
mod records;

pub use crate::theory::records::*;
use crate::{AtomId, BinderId, NodeId, OriginId, QuantifierId, Scalar, SetId, ValueId, WorkUsage};
pub use builder::TheoryBuilder;
pub use check::PreparedCheck;
use std::{collections::HashMap, sync::Arc};

#[derive(Debug)]
pub struct Theory {
    values: Vec<Arc<Scalar>>,
    atoms: Vec<Arc<GroundAtom>>,
    nodes: Vec<FormulaNode>,
    origins: Vec<Origin>,
    sets: Vec<FiniteSet>,
    binders: Vec<Binder>,
    quantifiers: Vec<Quantified>,
    quantifier_roots: HashMap<NodeId, QuantifierId>,
    work: WorkUsage,
}
impl Theory {
    pub fn value(&self, id: ValueId) -> Option<&Scalar> {
        self.values.get(id.index()).map(Arc::as_ref)
    }
    pub fn atom(&self, id: AtomId) -> Option<&GroundAtom> {
        self.atoms.get(id.index()).map(Arc::as_ref)
    }
    pub fn node(&self, id: NodeId) -> Option<&FormulaNode> {
        self.nodes.get(id.index())
    }
    pub fn origin(&self, id: OriginId) -> Option<&Origin> {
        self.origins.get(id.index())
    }
    pub fn set(&self, id: SetId) -> Option<&FiniteSet> {
        self.sets.get(id.index())
    }
    pub fn binder(&self, id: BinderId) -> Option<&Binder> {
        self.binders.get(id.index())
    }
    pub fn quantified(&self, id: QuantifierId) -> Option<&Quantified> {
        self.quantifiers.get(id.index())
    }
    pub fn values(&self) -> &[Arc<Scalar>] {
        &self.values
    }
    pub fn atoms(&self) -> &[Arc<GroundAtom>] {
        &self.atoms
    }
    pub fn nodes(&self) -> &[FormulaNode] {
        &self.nodes
    }
    pub fn origins(&self) -> &[Origin] {
        &self.origins
    }
    pub fn sets(&self) -> &[FiniteSet] {
        &self.sets
    }
    pub fn binders(&self) -> &[Binder] {
        &self.binders
    }
    pub fn quantifiers(&self) -> &[Quantified] {
        &self.quantifiers
    }
    pub fn work(&self) -> WorkUsage {
        self.work
    }
}
