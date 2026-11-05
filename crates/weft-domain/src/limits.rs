pub const MAX_SOURCE_DEPTH: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LimitKind {
    SourceBytes,
    Tokens,
    Nesting,
    NaturalDigits,
    Work,
    Members,
    Instances,
    Nodes,
    Atoms,
    Valuations,
    EvaluationSteps,
    TraceRows,
    OutputBytes,
}

#[derive(Clone, Debug)]
pub struct Limits {
    pub source_bytes: usize,
    pub tokens: usize,
    pub nesting: usize,
    pub natural_digits: usize,
    pub work: usize,
    pub members: usize,
    pub instances: usize,
    pub nodes: usize,
    pub atoms: usize,
    pub valuations: u64,
    pub evaluation_steps: u64,
    pub trace_rows: usize,
    pub output_bytes: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            source_bytes: 1_048_576,
            tokens: 100_000,
            nesting: MAX_SOURCE_DEPTH,
            natural_digits: 4096,
            work: 200_000,
            members: 16_384,
            instances: 50_000,
            nodes: 100_000,
            atoms: 20,
            valuations: 65_536,
            evaluation_steps: 10_000_000,
            trace_rows: 65_536,
            output_bytes: 16_777_216,
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WorkUsage {
    pub admitted: usize,
    pub used: usize,
    pub remaining: usize,
}
