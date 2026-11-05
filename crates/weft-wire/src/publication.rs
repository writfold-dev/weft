use crate::{RenderError, Result};
use weft_domain::{CheckState, Compilation, FormulaOp, NodeDetail, OriginKind, SetId, Theory};

pub(crate) struct Publication {
    pub(crate) nodes: Vec<bool>,
    pub(crate) sets: Vec<bool>,
    pub(crate) origins: Vec<bool>,
}
impl Publication {
    pub(crate) fn collect(compilation: &Compilation) -> Result<Self> {
        let theory = &compilation.theory;
        let mut publication = Self {
            nodes: vec![false; theory.nodes().len()],
            sets: vec![false; theory.sets().len()],
            origins: vec![false; theory.origins().len()],
        };
        for check in &compilation.checks {
            if let CheckState::Ready(prepared) = &check.state {
                mark(&mut publication.nodes, prepared.query().index())?;
                for premise in prepared.premises() {
                    mark(&mut publication.nodes, premise.index())?;
                }
            }
        }
        for hypothesis in &compilation.materializations.hypotheses {
            if let Some(root) = hypothesis.root {
                mark(&mut publication.nodes, root.index())?;
            }
        }
        for binding in &compilation.materializations.sets {
            if let Some(set) = binding.value {
                publication.set(theory, set)?;
            }
        }
        publication.formulas(theory)?;
        for quantifier in theory.quantifiers() {
            if publication.node(quantifier.root.index())? {
                publication.set(theory, quantifier.domain)?;
            }
        }
        publication.provenance(theory)?;
        Ok(publication)
    }
    pub(crate) fn node(&self, index: usize) -> Result<bool> {
        get(&self.nodes, index)
    }
    pub(crate) fn set_published(&self, index: usize) -> Result<bool> {
        get(&self.sets, index)
    }
    pub(crate) fn origin(&self, index: usize) -> Result<bool> {
        get(&self.origins, index)
    }
    fn formulas(&mut self, theory: &Theory) -> Result<()> {
        for (index, node) in theory.nodes().iter().enumerate().rev() {
            if !self.node(index)? {
                continue;
            }
            mark(&mut self.origins, node.origin.index())?;
            match node.operation {
                FormulaOp::Not(child) => mark(&mut self.nodes, child.index())?,
                FormulaOp::And(left, right) | FormulaOp::Or(left, right) => {
                    mark(&mut self.nodes, left.index())?;
                    mark(&mut self.nodes, right.index())?;
                }
                _ => {}
            }
            if let NodeDetail::SetComparison { left, right, .. } = node.detail {
                self.set(theory, left)?;
                self.set(theory, right)?;
            }
        }
        Ok(())
    }
    fn set(&mut self, theory: &Theory, id: SetId) -> Result<()> {
        if self.set_published(id.index())? {
            return Ok(());
        }
        mark(&mut self.sets, id.index())?;
        let set = theory
            .set(id)
            .ok_or(RenderError::InvalidRecord("published set"))?;
        mark(&mut self.origins, set.origin.index())?;
        for member in &set.members {
            mark(&mut self.origins, member.origin.index())?;
        }
        Ok(())
    }
    fn provenance(&mut self, theory: &Theory) -> Result<()> {
        for (index, origin) in theory.origins().iter().enumerate().rev() {
            if !self.origin(index)? {
                continue;
            }
            for parent in &origin.parents {
                mark(&mut self.origins, parent.index())?;
            }
            if let OriginKind::Spread(set) = origin.kind {
                self.set(theory, set)?;
            }
        }
        Ok(())
    }
}
fn mark(bits: &mut [bool], index: usize) -> Result<()> {
    *bits
        .get_mut(index)
        .ok_or(RenderError::InvalidRecord("publication reference"))? = true;
    Ok(())
}
fn get(bits: &[bool], index: usize) -> Result<bool> {
    bits.get(index)
        .copied()
        .ok_or(RenderError::InvalidRecord("publication reference"))
}
pub(crate) fn status(published: bool) -> &'static str {
    if published {
        "published"
    } else {
        "unreferenced-intermediate"
    }
}
