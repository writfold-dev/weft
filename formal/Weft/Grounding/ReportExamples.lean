import Weft.Grounding.Examples
import Weft.Grounding.DetailedTrace

namespace Weft.Grounding.Examples

open Weft.Logic Weft.Language

/-! Inhabited report/explanation contracts. These are kernel declarations, not an
assertion that a build was run. The accepted rich trace includes actual field and
literal interpretation, typed comparison, a hypothesis, and a qualified ground
rule. The retained core supplies exhaustive evaluation and classification. -/

theorem positiveReportAxes :
    (reportView positiveReview true).logical = .entailed ∧
    (reportView positiveReview true).execution = .complete ∧
    (reportView positiveReview true).basis = .grounded ∧
    (reportView positiveReview true).groundedSuccess = true := by decide

/-- Grounded basis is not synonymous with a successful plan. -/
theorem negativeGroundedBasis :
    (reportView refutedReview true).logical = .refuted ∧
    (reportView refutedReview true).basis = .grounded ∧
    (reportView refutedReview true).groundedSuccess = false := by decide

theorem hypothesisBasis :
    (reportView hypotheticalReview true).basis = .hypothetical ∧
    (reportView hypotheticalReview true).hasHypotheses = true := by decide

theorem unusableBasis : (reportView staleReview true).basis = .unusable := by decide

theorem unresolvedBasis :
    (reportView requiredUnused true).basis = .unresolved ∧
    (reportView requiredUnused true).closureMissing = true := by decide

def invalidReview : Review := { positiveReview with atomCount := 0 }
def exhaustedReview : Review := { positiveReview with budget := 0 }

theorem invalidVersusExhausted :
    outcome invalidReview = .unknown ∧ outcome exhaustedReview = .unknown ∧
    (reportView invalidReview true).logical = .notEvaluated ∧
    (reportView invalidReview true).failure = some .invalidDomain ∧
    (reportView invalidReview true).execution = .failed ∧
    (reportView exhaustedReview true).logical = .unknown ∧
    (reportView exhaustedReview true).failure = some .budgetExhausted ∧
    (reportView exhaustedReview true).execution = .incomplete := by decide

theorem noEvaluationRequested :
    (reportView positiveReview false).logical = .notEvaluated ∧
    (reportView positiveReview false).failure = some .notRequested ∧
    (reportView positiveReview false).groundedSuccess = false := by decide

theorem changedBudgetReuseRejected :
    outcome positiveReview = .entailed ∧ outcome exhaustedReview = .unknown ∧
    checkReuse positiveReview exhaustedReview = false := by decide

theorem sameBudgetOutcomePreserved :
    classify positiveReview.atomCount (premises positiveReview) positiveReview.query
        positiveReview.budget =
      classify positiveReview.atomCount (premises positiveReview) positiveReview.query
        positiveReview.budget ∧
    checkGrounding positiveReview = checkGrounding positiveReview ∧
    positiveReview.budget = positiveReview.budget :=
  reuseOutcomeSound positiveReview positiveReview sameContextReuseAccepted

def forgedView : ReportView :=
  { reportView refutedReview true with
    logical := .entailed
    groundedSuccess := true }

theorem forgedViewRejected : viewAccepted refutedReview true forgedView = false := by decide

def authoritativeView : ReportView :=
  { reportView positiveReview true with effectAuthority := true }

theorem authoritativeViewRejected :
    viewAccepted positiveReview true authoritativeView = false := by decide

def countPath : Path := ⟨0, ["count"]⟩
def countEnvironment : Environment := ⟨fun _ => some .natural, fun _ => some (.natural 42)⟩
def noPredicates : Profile := ⟨fun _ => none⟩
def noIntern : GroundCall → Option Nat := fun _ => none

def comparedSurface : Surface := .equal (.field countPath) (.literal (.natural 42))
def localHypothesis : Input := { observation with origin := .hypothesis 7 }

def richReview : Review :=
  { positiveReview with
    query := .literal true
    captured := [observation, pinnedRule, localHypothesis] }

def richTrace : DetailedTrace :=
  ⟨canonicalTrace richReview, requiredDetails countEnvironment comparedSurface richReview⟩

theorem honestRichExplanationAccepted :
    checkDetailedTrace countEnvironment noPredicates noIntern comparedSurface
      richReview richTrace = true := by decide


theorem emptyInterpretation : Interpretation noIntern (fun _ => true) world := by
  constructor
  · intro a b index first _second
    simp [noIntern] at first
  · intro call index captured
    simp [noIntern] at captured

/-- The denotational explanation theorem has an actual checked inhabitant. -/
theorem richExplanationFaithful :
    DetailedFaithful countEnvironment noPredicates noIntern (fun _ => true) world
      comparedSurface richReview richTrace :=
  detailedTraceFaithful countEnvironment noPredicates noIntern (fun _ => true) world
    emptyInterpretation comparedSurface richReview richTrace honestRichExplanationAccepted

/-- Extra honest detail is accepted without changing the canonical core. -/
def richerTrace : DetailedTrace :=
  { richTrace with
    details := .term (.field countPath) (.natural 42) :: richTrace.details }

theorem honestNoncanonicalDetailsAccepted :
    richerTrace ≠ richTrace ∧
    checkDetailedTrace countEnvironment noPredicates noIntern comparedSurface
      richReview richerTrace = true := by decide

theorem richFieldFacts :
    countEnvironment.fieldTypes countPath = some (.natural 42 : Value).type ∧
    countEnvironment.fieldValues countPath = some (.natural 42) :=
  fieldDetailFacts countEnvironment comparedSurface richReview countPath (.natural 42)
    (by decide)

theorem richComparisonMeaning :
    ComparisonMeaning countEnvironment (.field countPath) (.literal (.natural 42)) true :=
  comparisonDetailFacts countEnvironment comparedSurface richReview false
    (.field countPath) (.literal (.natural 42)) true (by decide)

def forgedComparisonTrace : DetailedTrace :=
  { richTrace with
    details := .comparison false (.field countPath) (.literal (.natural 42)) false :: richTrace.details }

theorem forgedComparisonRejected :
    checkDetailedTrace countEnvironment noPredicates noIntern comparedSurface
      richReview forgedComparisonTrace = false := by decide

def forgedHypothesisTrace : DetailedTrace :=
  { richTrace with details := .hypothesis localHypothesis 8 :: richTrace.details }

theorem forgedHypothesisProvenanceRejected :
    checkDetailedTrace countEnvironment noPredicates noIntern comparedSurface
      richReview forgedHypothesisTrace = false := by decide

def forgedRuleTrace : DetailedTrace :=
  { richTrace with details := .groundRule observation currentAssessment :: richTrace.details }

theorem forgedRuleProvenanceRejected :
    checkDetailedTrace countEnvironment noPredicates noIntern comparedSurface
      richReview forgedRuleTrace = false := by decide

theorem wrongQueryExplanationRejected :
    checkDetailedTrace countEnvironment noPredicates noIntern (.boolean false)
      richReview richTrace = false := by decide

def omittedDetailsTrace : DetailedTrace := ⟨canonicalTrace richReview, []⟩

theorem omittedRichDetailsRejected :
    checkDetailedTrace countEnvironment noPredicates noIntern comparedSurface
      richReview omittedDetailsTrace = false := by decide

theorem negativeViewProjectionAccepted :
    projectView refutedReview true (reportView refutedReview true) =
      some (reportView refutedReview true) := by decide

theorem strengthenedViewProjectionRejected :
    projectView refutedReview true forgedView = none := by decide

theorem authorityViewProjectionRejected :
    projectView positiveReview true authoritativeView = none := by decide

end Weft.Grounding.Examples
