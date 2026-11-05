use crate::{
    json::{Json, RenderError, Result},
    values,
};
use weft_domain::{Comparison, FormulaNode, FormulaOp, NodeDetail, Theory};

pub(crate) fn node(
    j: &mut Json,
    theory: &Theory,
    id: usize,
    node: &FormulaNode,
    published: bool,
) -> Result<()> {
    j.object(|j| {
        j.count("id", id)?;
        j.text("publication", crate::publication::status(published))?;
        j.field("span", |j| values::span(j, node.span))?;
        j.count("origin", node.origin.index())?;
        j.field("inputs", |j| {
            j.array(|j| {
                match node.operation {
                    FormulaOp::Not(child) => j.item(|j| j.number(child.index()))?,
                    FormulaOp::And(left, right) | FormulaOp::Or(left, right) => {
                        j.item(|j| j.number(left.index()))?;
                        j.item(|j| j.number(right.index()))?;
                    }
                    _ => {}
                }
                Ok(())
            })
        })?;
        match node.detail {
            NodeDetail::Comparison {
                operation,
                left,
                right,
            } => {
                j.text("kind", "comparison")?;
                j.text("operator", comparison(operation))?;
                j.field("left", |j| values::value(j, theory, left))?;
                j.field("right", |j| values::value(j, theory, right))?;
            }
            NodeDetail::SetComparison {
                operation,
                left,
                right,
                counterexample,
            } => {
                j.text("kind", "comparison")?;
                j.text("operator", comparison(operation))?;
                j.count("left_set", left.index())?;
                j.count("right_set", right.index())?;
                if let Some(member) = counterexample {
                    j.field("counterexample", |j| values::value(j, theory, member))?;
                }
            }
            NodeDetail::Membership { value, set } => {
                j.text("kind", "comparison")?;
                j.text("operator", "in")?;
                j.field("left", |j| values::value(j, theory, value))?;
                j.count("right_set", set.index())?;
            }
            _ => j.text(
                "kind",
                match node.operation {
                    FormulaOp::Literal(_) => "literal",
                    FormulaOp::Atom(_) => "predicate",
                    FormulaOp::Not(_) => "not",
                    FormulaOp::And(_, _) => "and",
                    FormulaOp::Or(_, _) => "or",
                },
            )?,
        }
        operation(j, theory, node.operation)
    })
}
fn comparison(comparison: Comparison) -> &'static str {
    match comparison {
        Comparison::Equal => "==",
        Comparison::NotEqual => "!=",
        Comparison::Member => "in",
        Comparison::Subset => "<=",
    }
}
fn operation(j: &mut Json, theory: &Theory, operation: FormulaOp) -> Result<()> {
    match operation {
        FormulaOp::Literal(value) => j.flag("value", value),
        FormulaOp::Atom(id) => {
            let atom = theory
                .atom(id)
                .ok_or(RenderError::InvalidRecord("formula atom"))?;
            j.count("atom", id.index())?;
            j.text("name", &atom.name)?;
            j.field("arguments", |j| {
                j.array(|j| {
                    for argument in &atom.arguments {
                        j.item(|j| values::value(j, theory, *argument))?;
                    }
                    Ok(())
                })
            })
        }
        FormulaOp::Not(_) => j.text("operator", "not"),
        FormulaOp::And(_, _) => j.text("operator", "and"),
        FormulaOp::Or(_, _) => j.text("operator", "or"),
    }
}
