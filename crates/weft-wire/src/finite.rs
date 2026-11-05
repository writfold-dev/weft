use crate::{
    json::{Json, RenderError, Result},
    values,
};
use weft_domain::{FiniteSet, OriginKind, Quantified, QuantifierKind, Theory};

pub(crate) fn set(j: &mut Json, theory: &Theory, set: &FiniteSet, published: bool) -> Result<()> {
    j.object(|j| {
        j.count("id", set.id.index())?;
        j.text("kind", "set")?;
        j.field("span", |j| values::span(j, set.span))?;
        contents(j, theory, set, published)
    })
}
pub(crate) fn contents(
    j: &mut Json,
    theory: &Theory,
    set: &FiniteSet,
    published: bool,
) -> Result<()> {
    j.field("element_type", |j| {
        values::scalar_type(j, set.element_type.as_ref())
    })?;
    j.text("publication", crate::publication::status(published))?;
    j.text(
        "materialization",
        if published {
            "complete"
        } else {
            "unreferenced-intermediate"
        },
    )?;
    j.count("origin", set.origin.index())?;
    j.count("raw_occurrences", set.raw_occurrences)?;
    j.count("cardinality", set.members.len())?;
    j.field("members", |j| {
        j.array(|j| {
            for (index, member) in set.members.iter().enumerate() {
                j.item(|j| {
                    j.object(|j| {
                        j.count("index", index)?;
                        j.field("value", |j| values::value(j, theory, member.value))?;
                        j.count("origin", member.origin.index())
                    })
                })?;
            }
            Ok(())
        })
    })
}
pub(crate) fn origins(
    j: &mut Json,
    theory: &Theory,
    publication: &crate::publication::Publication,
) -> Result<()> {
    j.array(|j| {
        for (index, origin) in theory.origins().iter().enumerate() {
            j.item(|j| {
                j.object(|j| {
                    j.count("id", index)?;
                    j.text(
                        "publication",
                        crate::publication::status(publication.origin(index)?),
                    )?;
                    j.field("span", |j| values::span(j, origin.span))?;
                    j.field("inputs", |j| {
                        values::indices(j, origin.parents.iter().map(|id| id.index()))
                    })?;
                    match origin.kind {
                        OriginKind::Literal => j.text("kind", "literal"),
                        OriginKind::Reference(id) => {
                            j.text("kind", "reference")?;
                            j.count("declaration", id.index())
                        }
                        OriginKind::Bound { binder, value } => {
                            j.text("kind", "bound")?;
                            j.count("binder", binder.index())?;
                            j.field("value", |j| values::value(j, theory, value))
                        }
                        OriginKind::Spread(id) => {
                            j.text("kind", "set-spread")?;
                            j.count("set", id.index())
                        }
                        OriginKind::SetMember => j.text("kind", "set-member"),
                        OriginKind::Normalize => j.text("kind", "normalize"),
                        OriginKind::Comparison => j.text("kind", "comparison"),
                        OriginKind::Predicate => j.text("kind", "predicate"),
                        OriginKind::Boolean => j.text("kind", "boolean"),
                        OriginKind::Quantifier => j.text("kind", "quantifier"),
                    }
                })
            })?;
        }
        Ok(())
    })
}
pub(crate) fn quantifier(
    j: &mut Json,
    theory: &Theory,
    q: &Quantified,
    published: bool,
) -> Result<()> {
    let domain = theory
        .set(q.domain)
        .ok_or(RenderError::InvalidRecord("quantifier domain"))?;
    let binder = theory
        .binder(q.binder)
        .ok_or(RenderError::InvalidRecord("quantifier binder"))?;
    j.count("quantifier", q.id.index())?;
    j.text("publication", crate::publication::status(published))?;
    j.text(
        "quantifier_kind",
        match q.kind {
            QuantifierKind::Forall => "forall",
            QuantifierKind::Exists => "exists",
        },
    )?;
    j.field("span", |j| values::span(j, q.span))?;
    j.count("binder", binder.id.index())?;
    j.text("binder_name", &binder.name)?;
    j.count("domain", q.domain.index())?;
    j.count("domain_size", domain.members.len())?;
    j.count("instantiated_count", q.instances.len())?;
    j.flag(
        "complete",
        published && q.instances.len() == domain.members.len(),
    )?;
    j.flag(
        "vacuous",
        q.kind == QuantifierKind::Forall && domain.members.is_empty(),
    )?;
    j.count("formula", q.root.index())?;
    if let Some(enclosing) = q.enclosing {
        j.field("enclosing", |j| {
            j.object(|j| {
                j.count("quantifier", enclosing.quantifier.index())?;
                j.count("member", enclosing.member)
            })
        })?;
    }
    Ok(())
}
pub(crate) fn environment(
    j: &mut Json,
    theory: &Theory,
    quantifier: &Quantified,
    member: usize,
) -> Result<()> {
    j.array(|j| {
        let mut current = Some((quantifier, member));
        let mut remaining = theory.quantifiers().len();
        while let Some((q, member)) = current {
            remaining = remaining
                .checked_sub(1)
                .ok_or(RenderError::InvalidRecord("cyclic instance environment"))?;
            let domain = theory
                .set(q.domain)
                .ok_or(RenderError::InvalidRecord("environment domain"))?;
            let value = domain
                .members
                .get(member)
                .ok_or(RenderError::InvalidRecord("environment member"))?;
            let binder = theory
                .binder(q.binder)
                .ok_or(RenderError::InvalidRecord("environment binder"))?;
            j.item(|j| {
                j.object(|j| {
                    j.count("binder", q.binder.index())?;
                    j.text("name", &binder.name)?;
                    j.field("value", |j| values::value(j, theory, value.value))
                })
            })?;
            current = match q.enclosing {
                Some(enclosing) => Some((
                    theory
                        .quantified(enclosing.quantifier)
                        .ok_or(RenderError::InvalidRecord("enclosing environment"))?,
                    enclosing.member,
                )),
                None => None,
            };
        }
        Ok(())
    })
}
