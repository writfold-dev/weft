use crate::{
    AtomId, BinderId, DeclId, NodeId, OriginId, QuantifierId, ScalarType, SetId, SourceSpan,
    ValueId,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GroundAtom {
    pub name: String,
    pub arguments: Vec<ValueId>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FormulaOp {
    Literal(bool),
    Atom(AtomId),
    Not(NodeId),
    And(NodeId, NodeId),
    Or(NodeId, NodeId),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Comparison {
    Equal,
    NotEqual,
    Member,
    Subset,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetOperation {
    Union,
    Intersection,
    Difference,
}
#[derive(Clone, Copy, Debug)]
pub enum NodeDetail {
    Literal,
    Predicate,
    Boolean,
    QuantifierFold,
    Comparison {
        operation: Comparison,
        left: ValueId,
        right: ValueId,
    },
    SetComparison {
        operation: Comparison,
        left: SetId,
        right: SetId,
        /// Deterministic first-left member absent from the right operand for
        /// a false subset; `None` otherwise.
        counterexample: Option<ValueId>,
    },
    Membership {
        value: ValueId,
        set: SetId,
    },
}
#[derive(Clone, Debug)]
pub struct FormulaNode {
    pub operation: FormulaOp,
    pub span: SourceSpan,
    pub origin: OriginId,
    pub detail: NodeDetail,
}
#[derive(Clone, Copy, Debug)]
pub enum OriginKind {
    Literal,
    Reference(DeclId),
    Bound {
        binder: BinderId,
        value: ValueId,
    },
    SetMember,
    Spread(SetId),
    SetOperation {
        operation: SetOperation,
        left: SetId,
        right: SetId,
    },
    Normalize,
    Comparison,
    Predicate,
    Boolean,
    Quantifier,
}
#[derive(Clone, Debug)]
pub struct Origin {
    pub kind: OriginKind,
    pub span: SourceSpan,
    pub parents: Vec<OriginId>,
}
#[derive(Clone, Copy, Debug)]
pub struct SetMember {
    pub value: ValueId,
    pub origin: OriginId,
}
#[derive(Clone, Debug)]
pub struct FiniteSet {
    pub id: SetId,
    pub element_type: Option<ScalarType>,
    pub members: Vec<SetMember>,
    pub raw_occurrences: usize,
    pub origin: OriginId,
    pub span: SourceSpan,
}
#[derive(Clone, Debug)]
pub struct Binder {
    pub id: BinderId,
    pub name: String,
    pub span: SourceSpan,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuantifierKind {
    Forall,
    Exists,
}
#[derive(Clone, Copy, Debug)]
pub struct Instance {
    pub member: usize,
    pub body: NodeId,
}
#[derive(Clone, Copy, Debug)]
pub struct EnclosingInstance {
    pub quantifier: QuantifierId,
    pub member: usize,
}
#[derive(Clone, Debug)]
pub struct Quantified {
    pub id: QuantifierId,
    pub kind: QuantifierKind,
    pub binder: BinderId,
    pub domain: SetId,
    pub instances: Vec<Instance>,
    pub root: NodeId,
    pub span: SourceSpan,
    pub enclosing: Option<EnclosingInstance>,
}
