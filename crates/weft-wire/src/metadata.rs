use crate::{
    finite,
    json::{Json, RenderError, Result},
    review, values,
};
use weft_domain::Compilation;

pub(crate) fn trace(
    j: &mut Json,
    compilation: &Compilation,
    next: usize,
    publication: &crate::publication::Publication,
) -> Result<()> {
    let next = requests(j, compilation, next)?;
    let next = hypotheses(j, compilation, next)?;
    sets(j, compilation, next, publication)
}
fn requests(j: &mut Json, compilation: &Compilation, mut next: usize) -> Result<usize> {
    let analysis = &compilation.analysis;
    if let Some(header) = &analysis.header {
        let declaration = analysis
            .declarations
            .get(header.target)
            .ok_or(RenderError::InvalidRecord("target trace"))?;
        j.item(|j| {
            j.object(|j| {
                base(j, next, "binding-request")?;
                j.field("inputs", |j| values::indices(j, []))?;
                j.field("binding", |j| {
                    review::binding(j, declaration, &header.proposal)
                })
            })
        })?;
        next = advance(next)?;
    }
    for request in &analysis.bindings {
        let declaration = analysis
            .declarations
            .get(request.declaration)
            .ok_or(RenderError::InvalidRecord("binding trace"))?;
        j.item(|j| {
            j.object(|j| {
                base(j, next, "binding-request")?;
                j.field("inputs", |j| values::indices(j, []))?;
                j.field("binding", |j| {
                    review::binding(j, declaration, &request.citation)
                })
            })
        })?;
        next = advance(next)?;
    }
    Ok(next)
}
fn hypotheses(j: &mut Json, compilation: &Compilation, mut next: usize) -> Result<usize> {
    let analysis = &compilation.analysis;
    for hypothesis in &compilation.materializations.hypotheses {
        let declaration = analysis
            .declarations
            .get(hypothesis.declaration)
            .ok_or(RenderError::InvalidRecord("hypothesis trace"))?;
        j.item(|j| {
            j.object(|j| {
                base(j, next, "assumption")?;
                j.field("span", |j| values::span(j, declaration.span))?;
                j.field("inputs", |j| {
                    values::indices(j, hypothesis.root.iter().map(|id| id.index()))
                })?;
                j.count("hypothesis", hypothesis.declaration.index())?;
                if let Some(root) = hypothesis.root {
                    j.count("formula", root.index())?;
                } else {
                    j.text("status", "not-elaborated")?;
                }
                Ok(())
            })
        })?;
        next = advance(next)?;
    }
    Ok(next)
}
fn sets(
    j: &mut Json,
    compilation: &Compilation,
    mut next: usize,
    publication: &crate::publication::Publication,
) -> Result<()> {
    for set in compilation.theory.sets() {
        j.item(|j| {
            j.object(|j| {
                base(j, next, "set-binding")?;
                j.field("inputs", |j| values::indices(j, []))?;
                j.field("set", |j| {
                    finite::set(
                        j,
                        &compilation.theory,
                        set,
                        publication.set_published(set.id.index())?,
                    )
                })
            })
        })?;
        next = advance(next)?;
    }
    Ok(())
}
fn base(j: &mut Json, id: usize, kind: &str) -> Result<()> {
    j.count("id", id)?;
    j.text("kind", kind)
}
fn advance(id: usize) -> Result<usize> {
    id.checked_add(1)
        .ok_or(RenderError::InvalidRecord("metadata trace size"))
}
