use crate::{CheckId, LimitKind, NodeId};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LogicalVerdict {
    Entailed,
    Refuted,
    Undetermined,
    InconsistentPremises,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValuationCount {
    Exact(u64),
    BeyondU64 { atoms: usize },
}
#[derive(Clone, Copy, Debug)]
pub struct TraceRow {
    pub valuation: u64,
    pub premises_hold: bool,
    pub query: bool,
}
#[derive(Clone, Copy, Debug)]
pub struct NodeValue {
    pub node: NodeId,
    pub value: bool,
}
#[derive(Debug)]
pub struct Model {
    pub valuation: u64,
    pub values: Vec<NodeValue>,
}
impl Model {
    pub fn value(&self, node: NodeId) -> Option<bool> {
        self.values
            .binary_search_by_key(&node, |entry| entry.node)
            .ok()
            .and_then(|index| self.values.get(index))
            .map(|entry| entry.value)
    }
}
#[derive(Debug)]
pub struct CompleteEvaluation {
    pub verdict: LogicalVerdict,
    pub required_valuations: u64,
    pub checked_valuations: u64,
    pub premise_models: u64,
    pub rows: Vec<TraceRow>,
    pub premise_count: usize,
    pub premise_truth_words: Vec<u64>,
    pub supporting: Option<Model>,
    pub refuting: Option<Model>,
}
impl CompleteEvaluation {
    pub fn premise_holds(&self, row: usize, premise: usize) -> Option<bool> {
        if row >= self.rows.len() || premise >= self.premise_count {
            return None;
        }
        let bit = row.checked_mul(self.premise_count)?.checked_add(premise)?;
        self.premise_truth_words
            .get(bit / 64)
            .map(|word| word & (1_u64 << (bit % 64)) != 0)
    }
}
#[derive(Debug)]
pub struct IncompleteEvaluation {
    pub limit: LimitKind,
    pub required: ValuationCount,
    pub admitted: u64,
    pub checked_valuations: u64,
}
#[derive(Debug)]
pub enum Conclusion {
    Complete(CompleteEvaluation),
    Incomplete(IncompleteEvaluation),
    Blocked,
}
#[derive(Debug)]
pub struct CheckOutcome {
    pub check: CheckId,
    pub conclusion: Conclusion,
}
#[derive(Debug, Default)]
pub struct Assessment {
    pub checks: Vec<CheckOutcome>,
}
