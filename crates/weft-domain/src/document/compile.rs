use crate::{
    Analysis, Check, CheckId, CheckInput, CheckRequest, CheckState, Code, Compilation, DeclId,
    DeclarationKind, Diagnostic, HypothesisUse, InvariantError, Materializations, NodeId, Phase,
    PreparedCheck, Theory,
};
use std::collections::BTreeSet;

impl Compilation {
    pub fn checked(
        analysis: Analysis,
        mut theory: Theory,
        requests: Vec<CheckRequest>,
        materializations: Materializations,
    ) -> Result<Self, InvariantError> {
        validate_materializations(&analysis, &theory, &materializations)?;
        let declared = analysis
            .declarations
            .entries()
            .iter()
            .filter(|entry| entry.kind == DeclarationKind::Check)
            .map(|entry| entry.id);
        if declared.ne(requests.iter().map(|entry| entry.declaration)) {
            return Err(InvariantError::InvalidReference("check inventory"));
        }
        let mut checks = Vec::with_capacity(requests.len());
        for request in requests {
            checks.push(prepare_check(
                &analysis,
                &mut theory,
                &materializations,
                request,
                CheckId::at(checks.len()),
            )?);
        }
        Ok(Self {
            analysis,
            theory,
            checks,
            materializations,
        })
    }
}

fn validate_materializations(
    analysis: &Analysis,
    theory: &Theory,
    materializations: &Materializations,
) -> Result<(), InvariantError> {
    let declarations = analysis.declarations.entries();
    let hypotheses = declarations
        .iter()
        .filter(|entry| entry.kind == DeclarationKind::Hypothesis)
        .map(|entry| entry.id);
    if hypotheses.ne(materializations
        .hypotheses
        .iter()
        .map(|entry| entry.declaration))
    {
        return Err(InvariantError::InvalidReference("hypothesis inventory"));
    }
    let sets = declarations
        .iter()
        .filter(|entry| entry.kind == DeclarationKind::Set)
        .map(|entry| entry.id);
    if sets.ne(materializations.sets.iter().map(|entry| entry.declaration)) {
        return Err(InvariantError::InvalidReference("set binding inventory"));
    }
    if analysis
        .hypotheses
        .iter()
        .map(|entry| entry.declaration)
        .ne(materializations
            .hypotheses
            .iter()
            .map(|entry| entry.declaration))
        || analysis
            .set_bindings
            .iter()
            .map(|entry| entry.declaration)
            .ne(materializations.sets.iter().map(|entry| entry.declaration))
    {
        return Err(InvariantError::InvalidReference("source declaration links"));
    }
    for hypothesis in &materializations.hypotheses {
        if hypothesis
            .root
            .is_some_and(|root| theory.node(root).is_none())
        {
            return Err(InvariantError::InvalidReference("hypothesis root"));
        }
    }
    for set in &materializations.sets {
        if set.value.is_some_and(|id| theory.set(id).is_none()) {
            return Err(InvariantError::InvalidReference("set binding value"));
        }
    }
    Ok(())
}

fn prepare_check(
    analysis: &Analysis,
    theory: &mut Theory,
    materializations: &Materializations,
    request: CheckRequest,
    id: CheckId,
) -> Result<Check, InvariantError> {
    let prior_count = materializations
        .hypotheses
        .partition_point(|entry| entry.declaration < request.declaration);
    let prior = &materializations.hypotheses[..prior_count];
    if prior.len() != request.hypotheses.len()
        || prior
            .iter()
            .zip(&request.hypotheses)
            .any(|(a, b)| a.declaration != b.declaration || a.root != b.root)
    {
        return Err(InvariantError::InvalidReference(
            "preceding hypothesis closure",
        ));
    }
    let state = match request.input {
        CheckInput::Ready(query) => match prepare_ready(theory, prior, query) {
            Ok(prepared) => CheckState::Ready(prepared),
            Err(InvariantError::Limit(limit)) => {
                let span = analysis
                    .declarations
                    .get(request.declaration)
                    .map(|entry| entry.span);
                CheckState::Blocked(vec![Diagnostic::new(
                    Code::LimitExceeded,
                    Phase::Lower,
                    format!("Complete query preparation exceeds {limit:?} admission"),
                    span,
                )])
            }
            Err(error) => return Err(error),
        },
        CheckInput::Blocked(diagnostics) => CheckState::Blocked(diagnostics),
    };
    let mut dependencies: BTreeSet<DeclId> = request.dependencies.into_iter().collect();
    dependencies.extend(request.hypotheses.iter().map(|entry| entry.declaration));
    dependencies.extend(request.requirements.iter().map(|entry| entry.declaration));
    if let CheckState::Ready(prepared) = &state {
        dependencies.extend(prepared.dependencies());
    }
    for declaration in &dependencies {
        let entry = analysis
            .declarations
            .get(*declaration)
            .ok_or(InvariantError::InvalidReference("dependency declaration"))?;
        if entry.kind == DeclarationKind::Check {
            return Err(InvariantError::InvalidReference(
                "check result used as dependency",
            ));
        }
    }
    Ok(Check {
        id,
        declaration: request.declaration,
        hypotheses: request.hypotheses,
        requirements: request.requirements,
        dependencies: dependencies.into_iter().collect(),
        state,
    })
}

fn prepare_ready(
    theory: &mut Theory,
    hypotheses: &[HypothesisUse],
    query: NodeId,
) -> Result<PreparedCheck, InvariantError> {
    theory.charge_preparation(hypotheses.len().saturating_add(1))?;
    let roots: Result<Vec<NodeId>, _> = hypotheses
        .iter()
        .map(|entry| {
            entry
                .root
                .ok_or(InvariantError::InvalidReference("invalid premise"))
        })
        .collect();
    theory.prepare(query, roots?)
}
