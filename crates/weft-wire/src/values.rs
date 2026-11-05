use crate::json::{Json, RenderError, Result};
use weft_domain::{
    DeclarationKind, Diagnostic, Phase, Scalar, ScalarType, SourceSpan, Theory, ValueId,
};

pub(crate) fn span(j: &mut Json, value: SourceSpan) -> Result<()> {
    j.object(|j| {
        j.count("start", value.start())?;
        j.count("end", value.end())
    })
}
pub(crate) fn scalar(j: &mut Json, value: &Scalar) -> Result<()> {
    j.object(|j| match value {
        Scalar::Boolean(v) => {
            j.text("kind", "boolean")?;
            j.flag("value", *v)
        }
        Scalar::Natural(v) => {
            j.text("kind", "natural")?;
            j.text("value", v.as_str())
        }
        Scalar::Text(v) => {
            j.text("kind", "text")?;
            j.text("value", v)
        }
        Scalar::Identity(_) => Err(RenderError::InvalidRecord(
            "external identity has no local interpretation contract",
        )),
    })
}
pub(crate) fn value(j: &mut Json, theory: &Theory, id: ValueId) -> Result<()> {
    scalar(
        j,
        theory
            .value(id)
            .ok_or(RenderError::InvalidRecord("value reference"))?,
    )
}
pub(crate) fn scalar_type(j: &mut Json, ty: Option<&ScalarType>) -> Result<()> {
    match ty {
        None => j.string("parametric-empty"),
        Some(ScalarType::Boolean) => j.string("boolean"),
        Some(ScalarType::Natural) => j.string("natural"),
        Some(ScalarType::Text) => j.string("text"),
        Some(ScalarType::Identity { .. }) => {
            Err(RenderError::InvalidRecord("external identity type"))
        }
    }
}
pub(crate) fn declaration_kind(kind: DeclarationKind) -> &'static str {
    match kind {
        DeclarationKind::Target => "target",
        DeclarationKind::Claim => "claim",
        DeclarationKind::Asset => "asset",
        DeclarationKind::Rule => "rule",
        DeclarationKind::Set => "set",
        DeclarationKind::Hypothesis => "hypothesis",
        DeclarationKind::Check => "check",
    }
}
pub(crate) fn diagnostic(j: &mut Json, diagnostic: &Diagnostic) -> Result<()> {
    j.object(|j| {
        j.text("code", diagnostic.code.as_str())?;
        j.text("phase", phase(diagnostic))?;
        j.text("severity", "error")?;
        j.text("message", &diagnostic.message)?;
        if let Some(primary) = diagnostic.primary {
            j.field("primary", |j| span(j, primary))?;
        }
        j.field("secondary", |j| {
            j.array(|j| {
                for label in &diagnostic.secondary {
                    j.item(|j| {
                        j.object(|j| {
                            j.count("start", label.span.start())?;
                            j.count("end", label.span.end())?;
                            j.text("label", &label.message)
                        })
                    })?;
                }
                Ok(())
            })
        })?;
        if let Some(expected) = &diagnostic.expected {
            j.text("expected", expected)?;
        }
        if let Some(actual) = &diagnostic.actual {
            j.text("actual", actual)?;
        }
        if let Some(help) = &diagnostic.help {
            j.text("help", help)?;
        }
        Ok(())
    })
}
pub(crate) fn indices(j: &mut Json, indices: impl IntoIterator<Item = usize>) -> Result<()> {
    j.array(|j| {
        for index in indices {
            j.item(|j| j.number(index))?;
        }
        Ok(())
    })
}
fn phase(diagnostic: &Diagnostic) -> &'static str {
    if diagnostic.code == weft_domain::Code::UnsupportedProfile {
        return "profile";
    }
    match diagnostic.phase {
        Phase::Input => "io",
        Phase::Lex => "lex",
        Phase::Parse => "parse",
        Phase::Resolve => "resolve",
        Phase::Type => "type",
        Phase::Capture => "evidence",
        Phase::Lower | Phase::Evaluate => "evaluate",
        Phase::Report => "report",
    }
}
