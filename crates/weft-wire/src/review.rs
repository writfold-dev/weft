use crate::{
    finite,
    json::{Json, RenderError, Result},
    values,
};
use weft_domain::{Analysis, Compilation, Declaration};

pub(crate) fn declaration(j: &mut Json, declaration: &Declaration) -> Result<()> {
    j.count("id", declaration.id.index())?;
    j.text("name", &declaration.name)?;
    j.text("kind", values::declaration_kind(declaration.kind))?;
    j.field("span", |j| values::span(j, declaration.span))
}
pub(crate) fn binding(j: &mut Json, declaration: &Declaration, reference: &str) -> Result<()> {
    j.object(|j| {
        self::declaration(j, declaration)?;
        j.text("reference", reference)?;
        j.text("resolution", "unresolved")
    })
}
pub(crate) fn review(
    j: &mut Json,
    analysis: &Analysis,
    compilation: Option<&Compilation>,
) -> Result<()> {
    let header = analysis
        .header
        .as_ref()
        .ok_or(RenderError::InvalidRecord("review header"))?;
    j.object(|j| {
        j.text("name", &header.name)?;
        j.text("profile", &header.profile)?;
        j.text("requested_context", &header.context)?;
        j.text("requested_snapshot", &header.snapshot)?;
        let target = analysis
            .declarations
            .get(header.target)
            .ok_or(RenderError::InvalidRecord("target declaration"))?;
        j.field("target", |j| binding(j, target, &header.proposal))?;
        j.field("bindings", |j| {
            j.array(|j| {
                for request in &analysis.bindings {
                    let declaration = analysis
                        .declarations
                        .get(request.declaration)
                        .ok_or(RenderError::InvalidRecord("binding declaration"))?;
                    j.item(|j| binding(j, declaration, &request.citation))?;
                }
                Ok(())
            })
        })?;
        j.field("needs", |j| {
            values::indices(
                j,
                analysis.requirements.iter().map(|r| r.declaration.index()),
            )
        })?;
        j.field("hypotheses", |j| hypotheses(j, analysis, compilation))?;
        j.field("sets", |j| sets(j, analysis, compilation))?;
        j.field("declarations", |j| {
            j.array(|j| {
                for entry in analysis.declarations.entries() {
                    j.item(|j| j.object(|j| declaration(j, entry)))?;
                }
                Ok(())
            })
        })
    })
}
fn hypotheses(j: &mut Json, analysis: &Analysis, compilation: Option<&Compilation>) -> Result<()> {
    j.array(|j| {
        for hypothesis in &analysis.hypotheses {
            let entry = analysis
                .declarations
                .get(hypothesis.declaration)
                .ok_or(RenderError::InvalidRecord("hypothesis declaration"))?;
            j.item(|j| {
                j.object(|j| {
                    declaration(j, entry)?;
                    j.field("expression_span", |j| {
                        values::span(j, hypothesis.expression_span)
                    })?;
                    let root = compilation.and_then(|c| {
                        c.materializations
                            .hypotheses
                            .iter()
                            .find(|h| h.declaration == entry.id)
                            .and_then(|h| h.root)
                    });
                    if let Some(root) = root {
                        j.count("formula", root.index())?;
                    } else {
                        j.text("formula_status", "not-elaborated")?;
                    }
                    Ok(())
                })
            })?;
        }
        Ok(())
    })
}
fn sets(j: &mut Json, analysis: &Analysis, compilation: Option<&Compilation>) -> Result<()> {
    j.array(|j| {
        for binding in &analysis.set_bindings {
            let entry = analysis
                .declarations
                .get(binding.declaration)
                .ok_or(RenderError::InvalidRecord("set declaration"))?;
            j.item(|j| {
                j.object(|j| {
                    declaration(j, entry)?;
                    j.field("initializer_span", |j| {
                        values::span(j, binding.initializer_span)
                    })?;
                    let materialized = compilation.and_then(|c| {
                        c.materializations
                            .sets
                            .iter()
                            .find(|set| set.declaration == binding.declaration)
                            .and_then(|set| set.value)
                            .map(|id| (c, id))
                    });
                    if let Some((compilation, id)) = materialized {
                        let set = compilation
                            .theory
                            .set(id)
                            .ok_or(RenderError::InvalidRecord("bound set"))?;
                        j.count("set", id.index())?;
                        finite::contents(j, &compilation.theory, set, true)
                    } else {
                        j.text(
                            "materialization",
                            if compilation.is_some() {
                                "unresolved"
                            } else {
                                "not-evaluated"
                            },
                        )
                    }
                })
            })?;
        }
        Ok(())
    })
}
