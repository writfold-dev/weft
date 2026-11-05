use crate::{
    ast,
    types::{TypeVar, Types},
};
use std::collections::{HashMap, HashSet};
use weft_domain::{
    Analysis, BinderId, Code, DeclId, DeclarationKind, Diagnostic, Header, InvariantError, Limits,
    Phase, SourceSpan, TheoryBuilder,
};

#[derive(Clone, Copy)]
pub(crate) enum Resolution {
    Declaration(DeclId),
    Binder(BinderId),
}
pub(crate) struct Signature {
    pub arguments: Vec<TypeVar>,
    pub span: SourceSpan,
}
pub(crate) struct StatementInfo {
    pub declaration: Option<DeclId>,
    pub diagnostics: Vec<Diagnostic>,
    pub dependencies: Vec<DeclId>,
}
pub(crate) struct Checked {
    pub analysis: Analysis,
    pub builder: TheoryBuilder,
    pub types: Types,
    pub set_types: HashMap<ast::SetExprId, TypeVar>,
    pub paths: HashMap<SourceSpan, Resolution>,
    pub binders: HashMap<ast::ExprId, BinderId>,
    pub statements: Vec<StatementInfo>,
    pub profile_valid: bool,
}
pub(crate) struct Checker<'p, 's> {
    pub parsed: &'p ast::Parsed<'s>,
    pub checked: Checked,
    pub sets: HashMap<DeclId, TypeVar>,
    pub set_dependencies: HashMap<DeclId, Vec<DeclId>>,
    pub scope: Vec<(&'s str, BinderId, TypeVar)>,
    pub signatures: HashMap<&'s str, Signature>,
    pub required_types: Vec<(TypeVar, SourceSpan, usize)>,
    pub current: StatementInfo,
    pub dependency_seen: HashSet<DeclId>,
    pub statement: usize,
}

pub(crate) fn invariant(error: InvariantError, span: SourceSpan) -> Diagnostic {
    let code = match error {
        InvariantError::Limit(_) => Code::LimitExceeded,
        _ => Code::InvalidProgram,
    };
    Diagnostic::new(code, Phase::Lower, format!("{error:?}"), Some(span))
}

pub(crate) fn check(parsed: &ast::Parsed<'_>, limits: &Limits) -> Checked {
    let profile_valid = parsed.header.profile.value == "weft.symbolic/1";
    let mut checker = Checker {
        parsed,
        checked: Checked {
            analysis: Analysis::default(),
            builder: TheoryBuilder::new(limits.clone()),
            types: Types::default(),
            set_types: HashMap::new(),
            paths: HashMap::new(),
            binders: HashMap::new(),
            statements: Vec::new(),
            profile_valid,
        },
        sets: HashMap::new(),
        set_dependencies: HashMap::new(),
        scope: Vec::new(),
        signatures: HashMap::new(),
        required_types: Vec::new(),
        current: StatementInfo {
            declaration: None,
            diagnostics: Vec::new(),
            dependencies: Vec::new(),
        },
        statement: 0,
        dependency_seen: HashSet::new(),
    };
    checker.header();
    for (index, statement) in parsed.statements.iter().enumerate() {
        checker.statement = index;
        checker.statement(statement);
        let info = std::mem::replace(
            &mut checker.current,
            StatementInfo {
                declaration: None,
                diagnostics: Vec::new(),
                dependencies: Vec::new(),
            },
        );
        checker.checked.statements.push(info);
        checker.dependency_seen.clear();
    }
    checker.finish()
}

impl Checker<'_, '_> {
    fn header(&mut self) {
        let header = &self.parsed.header;
        match self.checked.analysis.declarations.insert(
            header.target.text.into(),
            DeclarationKind::Target,
            header.target.span,
        ) {
            Ok(target) => {
                self.checked.analysis.header = Some(Header {
                    name: header.name.text.into(),
                    context: header.context.value.to_string(),
                    snapshot: header.snapshot.value.to_string(),
                    profile: header.profile.value.to_string(),
                    target,
                    proposal: header.proposal.value.to_string(),
                    span: header.span,
                })
            }
            Err(error) => self
                .checked
                .analysis
                .diagnostics
                .push(invariant(error, header.target.span)),
        }
        if !self.checked.profile_valid {
            let mut diagnostic = Diagnostic::new(
                Code::UnsupportedProfile,
                Phase::Capture,
                "profile interpretation is unavailable; no external profile was acquired",
                Some(header.profile.span),
            );
            diagnostic.actual = Some(header.profile.value.as_ref().into());
            diagnostic.help = Some("Use weft.symbolic/1 for an explicitly hypothetical local theory, or acquire the qualified external profile.".into());
            self.checked.analysis.diagnostics.push(diagnostic);
        }
    }
    fn finish(mut self) -> Checked {
        for (ty, span, statement) in self.required_types {
            if self.checked.types.concrete(ty).is_none() {
                let diagnostic = Diagnostic::new(
                    Code::AmbiguousType,
                    Phase::Type,
                    "predicate argument requires a concrete scalar type",
                    Some(span),
                );
                if let Some(info) = self.checked.statements.get_mut(statement) {
                    info.diagnostics.push(diagnostic);
                }
            }
        }
        for info in &self.checked.statements {
            self.checked
                .analysis
                .diagnostics
                .extend(info.diagnostics.iter().cloned());
        }
        self.checked
    }
    pub fn error(
        &mut self,
        code: Code,
        phase: Phase,
        span: SourceSpan,
        message: impl Into<String>,
    ) {
        self.current
            .diagnostics
            .push(Diagnostic::new(code, phase, message, Some(span)));
    }
    pub fn unify(&mut self, a: TypeVar, b: TypeVar, span: SourceSpan) {
        if let Err(diagnostic) = self.checked.types.unify(a, b, span) {
            self.current.diagnostics.push(diagnostic);
        }
    }
    pub fn dependency(&mut self, declaration: DeclId) {
        // Rejected check-label uses are diagnostics, never logical dependencies.
        if self
            .checked
            .analysis
            .declarations
            .get(declaration)
            .is_some_and(|entry| entry.kind == DeclarationKind::Check)
        {
            return;
        }
        let count = self
            .set_dependencies
            .get(&declaration)
            .map_or(1, |entries| entries.len().saturating_add(1));
        if let Err(error) = self.checked.builder.charge(count) {
            let span = self
                .checked
                .analysis
                .declarations
                .get(declaration)
                .map_or(self.parsed.header.span, |entry| entry.span);
            self.current.diagnostics.push(invariant(error, span));
            return;
        }
        if self.dependency_seen.insert(declaration) {
            self.current.dependencies.push(declaration);
        }
        if let Some(dependencies) = self.set_dependencies.get(&declaration) {
            for dependency in dependencies {
                if self.dependency_seen.insert(*dependency) {
                    self.current.dependencies.push(*dependency);
                }
            }
        }
    }
}
