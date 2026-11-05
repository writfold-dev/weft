mod budgets;
mod models;
mod packed;

use crate::assess;
use weft_domain::{
    Analysis, Assessment, CheckInput, CheckRequest, CheckState, Code, Compilation,
    CompleteEvaluation, Conclusion, DeclarationKind, Diagnostic, FormulaNode, FormulaOp,
    HypothesisDeclaration, HypothesisUse, LimitKind, Limits, LogicalVerdict, Materializations,
    NodeDetail, NodeId, OriginId, OriginKind, Phase, QuantifierKind, Scalar, ScalarType, SetMember,
    SourceSpan, TheoryBuilder, ValuationCount,
};

type TestResult<T = ()> = Result<T, String>;
fn error(value: impl std::fmt::Debug) -> String {
    format!("{value:?}")
}

struct Fixture {
    builder: TheoryBuilder,
    analysis: Analysis,
    requests: Vec<CheckRequest>,
    materializations: Materializations,
    span: SourceSpan,
    origin: OriginId,
}
impl Fixture {
    fn new() -> TestResult<Self> {
        let span = SourceSpan::checked("", 0, 0).map_err(error)?;
        let mut builder = TheoryBuilder::new(Limits::default());
        let origin = builder
            .add_origin(OriginKind::Literal, span, Vec::new())
            .map_err(error)?;
        Ok(Self {
            builder,
            analysis: Analysis::default(),
            requests: Vec::new(),
            materializations: Materializations::default(),
            span,
            origin,
        })
    }
    fn node(&mut self, operation: FormulaOp) -> TestResult<NodeId> {
        self.builder
            .add_node(FormulaNode {
                operation,
                span: self.span,
                origin: self.origin,
                detail: NodeDetail::Boolean,
            })
            .map_err(error)
    }
    fn atom(&mut self, name: &str) -> TestResult<NodeId> {
        let atom = self
            .builder
            .intern_atom(name.into(), Vec::new())
            .map_err(error)?;
        self.node(FormulaOp::Atom(atom))
    }
    fn check(&mut self, query: NodeId, premises: &[NodeId]) -> TestResult {
        for root in premises {
            let name = format!("h{}", self.analysis.declarations.entries().len());
            let declaration = self
                .analysis
                .declarations
                .insert(name, DeclarationKind::Hypothesis, self.span)
                .map_err(error)?;
            self.materializations.hypotheses.push(HypothesisUse {
                declaration,
                root: Some(*root),
            });
            self.analysis.hypotheses.push(HypothesisDeclaration {
                declaration,
                span: self.span,
                expression_span: self.span,
            });
        }
        let name = format!("c{}", self.requests.len());
        let declaration = self
            .analysis
            .declarations
            .insert(name, DeclarationKind::Check, self.span)
            .map_err(error)?;
        self.requests.push(CheckRequest {
            declaration,
            hypotheses: self.materializations.hypotheses.clone(),
            requirements: Vec::new(),
            dependencies: Vec::new(),
            input: CheckInput::Ready(query),
        });
        Ok(())
    }
    fn finish(self) -> TestResult<Compilation> {
        Compilation::checked(
            self.analysis,
            self.builder.finish(),
            self.requests,
            self.materializations,
        )
        .map_err(error)
    }
}

fn complete(assessment: &Assessment, index: usize) -> TestResult<&CompleteEvaluation> {
    match assessment.checks.get(index).map(|check| &check.conclusion) {
        Some(Conclusion::Complete(result)) => Ok(result),
        other => Err(format!("Expected complete evaluation, got {other:?}")),
    }
}

#[test]
fn all_four_classifications_and_polarity() -> TestResult {
    for expected in [
        LogicalVerdict::Entailed,
        LogicalVerdict::Refuted,
        LogicalVerdict::Undetermined,
        LogicalVerdict::InconsistentPremises,
    ] {
        let mut f = Fixture::new()?;
        let p = f.atom("p")?;
        let not_p = f.node(FormulaOp::Not(p))?;
        let premises = match expected {
            LogicalVerdict::Entailed | LogicalVerdict::Refuted => vec![p],
            LogicalVerdict::Undetermined => Vec::new(),
            LogicalVerdict::InconsistentPremises => vec![p, not_p],
        };
        let query = if expected == LogicalVerdict::Refuted {
            not_p
        } else {
            p
        };
        f.check(query, &premises)?;
        let result = assess(&f.finish()?, &Limits::default()).map_err(error)?;
        let evaluation = complete(&result, 0)?;
        assert_eq!(evaluation.verdict, expected);
        assert_eq!(evaluation.checked_valuations, 2);
        assert_eq!(evaluation.rows.len(), 2);
        if expected == LogicalVerdict::InconsistentPremises {
            assert_eq!(evaluation.premise_models, 0);
            assert!(evaluation.supporting.is_none());
            assert!(evaluation.refuting.is_none());
        }
    }
    Ok(())
}

#[test]
fn empty_atom_domain_has_one_valuation() -> TestResult {
    let mut f = Fixture::new()?;
    let yes = f.node(FormulaOp::Literal(true))?;
    let no = f.node(FormulaOp::Literal(false))?;
    f.check(yes, &[])?;
    f.check(no, &[])?;
    let result = assess(&f.finish()?, &Limits::default()).map_err(error)?;
    assert_eq!(complete(&result, 0)?.verdict, LogicalVerdict::Entailed);
    assert_eq!(complete(&result, 1)?.verdict, LogicalVerdict::Refuted);
    for index in 0..2 {
        assert_eq!(complete(&result, index)?.required_valuations, 1);
        assert_eq!(complete(&result, index)?.premise_models, 1);
    }
    Ok(())
}

#[test]
fn blocked_check_never_becomes_a_logical_result() -> TestResult {
    let mut f = Fixture::new()?;
    let yes = f.node(FormulaOp::Literal(true))?;
    f.check(yes, &[])?;
    let request = f.requests.get_mut(0).ok_or("Missing test request")?;
    request.input = CheckInput::Blocked(vec![Diagnostic::new(
        Code::UnresolvedInput,
        Phase::Capture,
        "external",
        None,
    )]);
    let result = assess(&f.finish()?, &Limits::default()).map_err(error)?;
    assert!(matches!(
        result.checks.first().map(|c| &c.conclusion),
        Some(Conclusion::Blocked)
    ));
    Ok(())
}
