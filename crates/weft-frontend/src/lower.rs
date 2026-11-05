mod finish;

use crate::{
    ast,
    semantic::{Checked, StatementInfo},
};
use std::collections::{BTreeSet, HashMap};
use weft_domain::{
    Analysis, BinderId, CheckInput, CheckRequest, Code, Compilation, DeclId, Diagnostic,
    HypothesisUse, Limits, OriginId, Phase, SetId, SetMember, SourceSpan,
};

pub(crate) struct Lower<'p, 's> {
    pub parsed: &'p ast::Parsed<'s>,
    pub checked: Checked,
    pub limits: &'p Limits,
    pub sets: HashMap<DeclId, SetId>,
    pub literals: HashMap<SourceSpan, (weft_domain::ValueId, OriginId)>,
    pub environment: Vec<(BinderId, SetMember)>,
    pub instances: usize,
    hypotheses: Vec<HypothesisUse>,
    hypothesis_dependencies: BTreeSet<DeclId>,
    invalid_premise: bool,
    requests: Vec<CheckRequest>,
}

pub(crate) fn compile(
    parsed: &ast::Parsed<'_>,
    checked: Checked,
    limits: &Limits,
) -> Result<Compilation, Box<Analysis>> {
    let mut lower = Lower {
        parsed,
        checked,
        limits,
        sets: HashMap::new(),
        environment: Vec::new(),
        instances: 0,
        hypotheses: Vec::new(),
        hypothesis_dependencies: BTreeSet::new(),
        invalid_premise: false,
        requests: Vec::new(),
        literals: HashMap::new(),
    };
    lower.required_inputs();
    let statements = std::mem::take(&mut lower.checked.statements);
    for (statement, info) in parsed.statements.iter().zip(statements) {
        if let Err(diagnostic) = lower.statement(statement, info) {
            lower.checked.analysis.diagnostics.push(diagnostic);
            return Err(Box::new(lower.checked.analysis));
        }
    }
    lower.finish()
}

impl<'s> Lower<'_, 's> {
    fn statement(
        &mut self,
        statement: &ast::Statement<'s>,
        info: StatementInfo,
    ) -> Result<(), Diagnostic> {
        match statement {
            ast::Statement::Set { value, .. } => {
                if info.diagnostics.is_empty() && self.checked.profile_valid {
                    match self.set(*value) {
                        Ok(set) => {
                            if let Some(id) = info.declaration {
                                self.sets.insert(id, set);
                            }
                        }
                        Err(diagnostic) => self.checked.analysis.diagnostics.push(diagnostic),
                    }
                }
            }
            ast::Statement::Assume { expression, .. } => self.assumption(*expression, info),
            ast::Statement::Check {
                expression, span, ..
            } => self.check(*expression, *span, info)?,
            ast::Statement::Binding { .. } | ast::Statement::Need { .. } => {}
        }
        Ok(())
    }
    fn assumption(&mut self, expression: ast::ExprId, info: StatementInfo) {
        let root = if info.diagnostics.is_empty() && self.checked.profile_valid {
            match self.expression(expression) {
                Ok(value) => Some(value.node),
                Err(diagnostic) => {
                    self.checked.analysis.diagnostics.push(diagnostic);
                    None
                }
            }
        } else {
            None
        };
        if root.is_none() {
            self.invalid_premise = true;
        }
        if let Some(declaration) = info.declaration {
            self.hypotheses.push(HypothesisUse { declaration, root });
        }
        self.hypothesis_dependencies.extend(info.dependencies);
    }
    fn check(
        &mut self,
        expression: ast::ExprId,
        span: SourceSpan,
        mut info: StatementInfo,
    ) -> Result<(), Diagnostic> {
        let Some(declaration) = info.declaration else {
            return Ok(());
        };
        self.snapshot_work(info.dependencies.len(), span)?;
        if !self.checked.profile_valid {
            info.diagnostics.push(Diagnostic::new(
                Code::UnsupportedProfile,
                Phase::Capture,
                "check requires an unavailable profile",
                Some(span),
            ));
        }
        if self.invalid_premise {
            let diagnostic = Diagnostic::new(
                Code::InvalidPremise,
                Phase::Lower,
                "a preceding assumption is invalid; this dependent check cannot be evaluated",
                Some(span),
            );
            self.checked.analysis.diagnostics.push(diagnostic.clone());
            info.diagnostics.push(diagnostic);
        }
        let input = if info.diagnostics.is_empty() {
            match self.expression(expression) {
                Ok(value) => CheckInput::Ready(value.node),
                Err(diagnostic) => {
                    self.checked.analysis.diagnostics.push(diagnostic.clone());
                    CheckInput::Blocked(vec![diagnostic])
                }
            }
        } else {
            CheckInput::Blocked(info.diagnostics)
        };
        let mut dependencies: BTreeSet<_> = info.dependencies.into_iter().collect();
        dependencies.extend(&self.hypothesis_dependencies);
        self.requests.push(CheckRequest {
            declaration,
            hypotheses: self.hypotheses.clone(),
            requirements: self.checked.analysis.requirements.clone(),
            dependencies: dependencies.into_iter().collect(),
            input,
        });
        Ok(())
    }
}
