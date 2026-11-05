use crate::{
    CheckId, DeclId, Diagnostic, InvariantError, NodeId, PreparedCheck, SetId, SourceSpan, Theory,
};
use std::collections::HashMap;

mod compile;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeclarationKind {
    Target,
    Claim,
    Asset,
    Rule,
    Set,
    Hypothesis,
    Check,
}
#[derive(Clone, Debug)]
pub struct Declaration {
    pub id: DeclId,
    pub name: String,
    pub kind: DeclarationKind,
    pub span: SourceSpan,
}
#[derive(Debug, Default)]
pub struct Declarations {
    entries: Vec<Declaration>,
    names: HashMap<String, DeclId>,
}
impl Declarations {
    pub fn insert(
        &mut self,
        name: String,
        kind: DeclarationKind,
        span: SourceSpan,
    ) -> Result<DeclId, InvariantError> {
        if self.names.contains_key(&name) {
            return Err(InvariantError::DuplicateName(name));
        }
        let id = DeclId::at(self.entries.len());
        self.names.insert(name.clone(), id);
        self.entries.push(Declaration {
            id,
            name,
            kind,
            span,
        });
        Ok(id)
    }
    pub fn find(&self, name: &str) -> Option<DeclId> {
        self.names.get(name).copied()
    }
    pub fn get(&self, id: DeclId) -> Option<&Declaration> {
        self.entries.get(id.index())
    }
    pub fn entries(&self) -> &[Declaration] {
        &self.entries
    }
}
#[derive(Clone, Debug)]
pub struct Header {
    pub name: String,
    pub context: String,
    pub snapshot: String,
    pub profile: String,
    pub target: DeclId,
    pub proposal: String,
    pub span: SourceSpan,
}
#[derive(Clone, Debug)]
pub struct BindingRequest {
    pub declaration: DeclId,
    pub citation: String,
    pub span: SourceSpan,
}
#[derive(Clone, Debug)]
pub struct Requirement {
    pub declaration: DeclId,
    pub span: SourceSpan,
}
#[derive(Clone, Debug)]
pub struct HypothesisDeclaration {
    pub declaration: DeclId,
    pub span: SourceSpan,
    pub expression_span: SourceSpan,
}
#[derive(Clone, Debug)]
pub struct SetDeclaration {
    pub declaration: DeclId,
    pub span: SourceSpan,
    pub initializer_span: SourceSpan,
}
#[derive(Debug, Default)]
pub struct Analysis {
    pub header: Option<Header>,
    pub declarations: Declarations,
    pub bindings: Vec<BindingRequest>,
    pub requirements: Vec<Requirement>,
    pub hypotheses: Vec<HypothesisDeclaration>,
    pub set_bindings: Vec<SetDeclaration>,
    pub diagnostics: Vec<Diagnostic>,
}
#[derive(Clone, Debug)]
pub struct HypothesisUse {
    pub declaration: DeclId,
    pub root: Option<NodeId>,
}
#[derive(Clone, Debug)]
pub struct BoundSet {
    pub declaration: DeclId,
    pub value: Option<SetId>,
}
#[derive(Debug, Default)]
pub struct Materializations {
    pub hypotheses: Vec<HypothesisUse>,
    pub sets: Vec<BoundSet>,
}
#[derive(Debug)]
pub enum CheckInput {
    Ready(NodeId),
    Blocked(Vec<Diagnostic>),
}
#[derive(Debug)]
pub struct CheckRequest {
    pub declaration: DeclId,
    pub hypotheses: Vec<HypothesisUse>,
    pub requirements: Vec<Requirement>,
    pub dependencies: Vec<DeclId>,
    pub input: CheckInput,
}
#[derive(Debug)]
pub enum CheckState {
    Ready(PreparedCheck),
    Blocked(Vec<Diagnostic>),
}
#[derive(Debug)]
pub struct Check {
    pub id: CheckId,
    pub declaration: DeclId,
    pub hypotheses: Vec<HypothesisUse>,
    pub requirements: Vec<Requirement>,
    pub dependencies: Vec<DeclId>,
    pub state: CheckState,
}
#[derive(Debug)]
pub struct Compilation {
    pub analysis: Analysis,
    pub theory: Theory,
    pub checks: Vec<Check>,
    pub materializations: Materializations,
}
