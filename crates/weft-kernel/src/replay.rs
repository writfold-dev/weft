use crate::{invalid, reserve};
use weft_domain::{Diagnostic, FormulaOp, NodeId, NodeValue, PreparedCheck, Theory};

#[derive(Clone, Copy)]
enum Operation {
    Literal(bool),
    Atom(usize),
    Not(usize),
    And(usize, usize),
    Or(usize, usize),
}

/// Replays exact active nodes, with the first active atom as the most significant bit.
/// Values are valuation-relative, not uniform quantified witnesses.
pub(crate) struct Replay {
    operations: Vec<Operation>,
    values: Vec<NodeValue>,
    atoms: Vec<bool>,
    count: u64,
}

impl Replay {
    pub(crate) fn prepared(
        theory: &Theory,
        check: &PreparedCheck,
        count: u64,
    ) -> Result<Self, Diagnostic> {
        if check.nodes().windows(2).any(|pair| pair[0] >= pair[1])
            || check.atoms().windows(2).any(|pair| pair[0] >= pair[1])
        {
            return Err(invalid(
                "Active node and atom mappings must be strictly ordered",
            ));
        }
        for atom in check.atoms() {
            if theory.atom(*atom).is_none() {
                return Err(invalid("Missing active atom"));
            }
        }
        let mut operations = reserve(check.nodes().len())?;
        let mut values = reserve(check.nodes().len())?;
        for (index, id) in check.nodes().iter().copied().enumerate() {
            let node = theory
                .node(id)
                .ok_or_else(|| invalid("Missing active formula node"))?;
            operations.push(translate(node.operation, check, index)?);
            values.push(NodeValue {
                node: id,
                value: false,
            });
        }
        position(check, check.query())?;
        for premise in check.premises() {
            position(check, *premise)?;
        }
        let mut atoms = reserve(check.atoms().len())?;
        atoms.resize(check.atoms().len(), false);
        Ok(Self {
            operations,
            values,
            atoms,
            count,
        })
    }

    pub(crate) fn evaluate(&mut self, valuation: u64) -> Result<&[NodeValue], Diagnostic> {
        if valuation >= self.count {
            return Err(invalid("Valuation outside active atom domain"));
        }
        let mut bits = valuation;
        for value in self.atoms.iter_mut().rev() {
            *value = bits & 1 != 0;
            bits >>= 1;
        }
        for (index, operation) in self.operations.iter().enumerate() {
            let value = match *operation {
                Operation::Literal(value) => value,
                Operation::Atom(atom) => *self
                    .atoms
                    .get(atom)
                    .ok_or_else(|| invalid("Missing atom value"))?,
                Operation::Not(child) => !at(&self.values, child)?,
                Operation::And(left, right) => at(&self.values, left)? & at(&self.values, right)?,
                Operation::Or(left, right) => at(&self.values, left)? | at(&self.values, right)?,
            };
            self.values
                .get_mut(index)
                .ok_or_else(|| invalid("Missing node buffer entry"))?
                .value = value;
        }
        Ok(&self.values)
    }
}

pub(crate) fn position(check: &PreparedCheck, id: NodeId) -> Result<usize, Diagnostic> {
    check
        .nodes()
        .binary_search(&id)
        .map_err(|_| invalid("Root or edge absent from active nodes"))
}

pub(crate) fn at(values: &[NodeValue], index: usize) -> Result<bool, Diagnostic> {
    values
        .get(index)
        .map(|entry| entry.value)
        .ok_or_else(|| invalid("Missing node value"))
}

fn translate(
    operation: FormulaOp,
    check: &PreparedCheck,
    index: usize,
) -> Result<Operation, Diagnostic> {
    let child = |id| {
        let position = position(check, id)?;
        if position >= index {
            return Err(invalid("Formula edge is not backward-only"));
        }
        Ok(position)
    };
    Ok(match operation {
        FormulaOp::Literal(value) => Operation::Literal(value),
        FormulaOp::Atom(atom) => Operation::Atom(
            check
                .atoms()
                .binary_search(&atom)
                .map_err(|_| invalid("Formula atom absent from active mapping"))?,
        ),
        FormulaOp::Not(id) => Operation::Not(child(id)?),
        FormulaOp::And(left, right) => Operation::And(child(left)?, child(right)?),
        FormulaOp::Or(left, right) => Operation::Or(child(left)?, child(right)?),
    })
}
