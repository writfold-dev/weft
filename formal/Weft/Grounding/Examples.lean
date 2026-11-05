import Weft.Grounding.Trace

namespace Weft.Grounding.Examples

open Weft.Logic

/-! Kernel-reducible calibration declarations, not a claim of an already executed
build. Mutation targets: remove explicitNeeds from required (L08); omit one status
or admit hypotheses in EligibleOrigin (L09); omit context/revision/profile/subject
from reuseKey (L10); trust supplied classifications, omit backward/root checks or
strip captured origins (L11); append a grant or admission in analysisStep (L12).
The positive fixture imports an assessed observation and a qualified pinned rule;
the real-world proof explicitly supplies EvidenceSound for the chosen valuation.
-/

def scope : Scope := ⟨1, 10, 20, 30, 40, 50⟩

def observationBinding : Binding := ⟨scope, 1, 100, 30, 2, 0⟩
def ruleBinding : Binding := ⟨scope, 2, 200, 30, 2, 0⟩
def missingBinding : Binding := ⟨scope, 1, 300, 30, 2, 0⟩

def currentAssessment : Assessment :=
  ⟨.positive, .current, .applicable, .valid, .available, .clear, .admitted⟩

def observation : Input :=
  ⟨observationBinding, .atom 0, [], .observation currentAssessment⟩

def pinnedRule : Input :=
  ⟨ruleBinding, implication (.atom 0) (.atom 1), [observationBinding],
    .rule currentAssessment true⟩

def positiveReview : Review :=
  ⟨scope, 2, .atom 1, [observationBinding, ruleBinding],
    [observationBinding, ruleBinding], [observation, pinnedRule], 4⟩

/-- Observation A and a separately assessed rule A → B establish B. -/
theorem positiveLogical : outcome positiveReview = .entailed := by decide

theorem positiveAccepted : checkGrounding positiveReview = true := by decide

def world : Nat → Bool := fun _ => true

theorem positiveEvidenceSound : EvidenceSound positiveReview world := by
  intro input member _eligible
  simp [positiveReview] at member
  rcases member with rfl | rfl <;> rfl

/-- The environmental premise is inhabited, not hidden behind an implication
whose antecedent is impossible. The result includes consistency and world truth. -/
theorem positiveGrounded : GroundedMeaning positiveReview world :=
  groundedSound positiveReview world positiveAccepted positiveEvidenceSound

theorem positiveTraceAccepted :
    checkTrace positiveReview (canonicalTrace positiveReview) = true := by decide

theorem positiveProjectionFaithful : FaithfulProjection positiveReview
    (canonicalTrace positiveReview) (reportFor positiveReview (canonicalTrace positiveReview)) :=
  traceFaithful _ _ _ (by decide)

/-- A constant query does not erase an unused explicit need. -/
def requiredUnused : Review :=
  { positiveReview with
    query := .literal true
    explicitNeeds := [missingBinding]
    usedInputs := [] }

theorem requiredUnusedLogical : outcome requiredUnused = .entailed := by decide

theorem requiredUnusedRetained : missingBinding ∈ required requiredUnused := by decide

theorem requiredUnusedRejected : checkGrounding requiredUnused = false := by decide

theorem requiredUnusedTraceRetainsNeed :
    (reportFor requiredUnused (canonicalTrace requiredUnused)).explicitNeeds = [missingBinding] := rfl

/-- Conversely, an eligible captured explicit need can support a constant query. -/
def constantWithNeed : Review :=
  { positiveReview with
    query := .literal true
    explicitNeeds := [observationBinding]
    usedInputs := []
    captured := [observation] }

theorem constantWithNeedAccepted : checkGrounding constantWithNeed = true := by decide

def hypotheticalReview : Review :=
  { positiveReview with captured :=
    [{ observation with origin := .hypothesis 7 }, pinnedRule] }

theorem hypotheticalLogical : outcome hypotheticalReview = .entailed := by decide

theorem hypothesisLaunderingRejected : checkGrounding hypotheticalReview = false := by decide

theorem hypothesisRetained : (hypotheses hypotheticalReview).length = 1 := by decide

def staleReview : Review :=
  { positiveReview with captured :=
    [{ observation with origin := .observation { currentAssessment with freshness := .stale } },
      pinnedRule] }

theorem staleLogical : outcome staleReview = .entailed := by decide

theorem staleRejected : checkGrounding staleReview = false := by decide

def contestedReview : Review :=
  { positiveReview with captured :=
    [{ observation with origin := .observation { currentAssessment with contestation := .contested } },
      pinnedRule] }

theorem contestedRejected : checkGrounding contestedReview = false := by decide

def unknownReview : Review :=
  { positiveReview with captured :=
    [{ observation with origin := .observation { currentAssessment with validation := .unknown } },
      pinnedRule] }

theorem unknownAssessmentRejected : checkGrounding unknownReview = false := by decide

def unsupportedReview : Review :=
  { positiveReview with captured :=
    [{ observation with origin := .observation { currentAssessment with support := .both } },
      pinnedRule] }

theorem contradictorySupportRejected : checkGrounding unsupportedReview = false := by decide

def missingClosure : Review :=
  { positiveReview with captured :=
    [{ observation with dependencies := [missingBinding] }, pinnedRule] }

theorem missingTransitiveDependencyRejected : checkGrounding missingClosure = false := by decide

def unqualifiedRule : Review :=
  { positiveReview with captured :=
    [observation, { pinnedRule with origin := .rule currentAssessment false }] }

theorem unqualifiedRuleRejected : checkGrounding unqualifiedRule = false := by decide

def foreignScope : Scope := { scope with context := 21 }

def foreignBinding (b : Binding) : Binding := { b with scope := foreignScope }

def foreignInput (input : Input) : Input :=
  { input with
    binding := foreignBinding input.binding
    dependencies := input.dependencies.map foreignBinding }

def foreignReview : Review :=
  { positiveReview with
    scope := foreignScope
    explicitNeeds := positiveReview.explicitNeeds.map foreignBinding
    usedInputs := positiveReview.usedInputs.map foreignBinding
    captured := positiveReview.captured.map foreignInput }

/-- Both contexts are internally grounded; pooling them is still forbidden. -/
theorem foreignIndependentlyGrounded : checkGrounding foreignReview = true := by decide

theorem sameSpelledIdentity :
    (foreignBinding observationBinding).identity = observationBinding.identity := rfl

theorem crossContextReuseRejected : checkReuse positiveReview foreignReview = false := by decide

theorem sameContextReuseAccepted : checkReuse positiveReview positiveReview = true := by decide

theorem crossSubjectReuseRejected : checkReuse positiveReview
    { positiveReview with scope := { scope with subject := 11 } } = false := by decide

theorem crossRevisionReuseRejected : checkReuse positiveReview
    { positiveReview with scope := { scope with revision := 31 } } = false := by decide

theorem crossProfileReuseRejected : checkReuse positiveReview
    { positiveReview with scope := { scope with profile := 41 } } = false := by decide

def crossScopeCapture : Review :=
  { positiveReview with captured := [foreignInput observation, pinnedRule] }

theorem crossScopeEvidenceRejected : checkGrounding crossScopeCapture = false := by decide

def danglingTrace : Trace :=
  ⟨[⟨[99], .classification .entailed true⟩], [0]⟩

theorem danglingLinksRejected : backwards danglingTrace = false := by decide

theorem danglingTraceRejected : checkTrace positiveReview danglingTrace = false := by decide

def cyclicTrace : Trace :=
  ⟨[⟨[1], .classification .entailed true⟩,
    ⟨[0], .classification .entailed true⟩], [0]⟩

theorem cyclicLinksRejected : backwards cyclicTrace = false := by decide

theorem cyclicTraceRejected : checkTrace positiveReview cyclicTrace = false := by decide

def danglingRootTrace : Trace :=
  { canonicalTrace positiveReview with roots := [99] }

theorem danglingRootRejected : rootsPresent danglingRootTrace = false := by decide

theorem danglingRootTraceRejected : checkTrace positiveReview danglingRootTrace = false := by decide

/-- A syntactically well-linked graph with a forged classification is not trusted. -/
def forgedTrace : Trace :=
  ⟨[⟨[], .classification .refuted false⟩], [0]⟩

theorem forgedTraceStructurallyValid : backwards forgedTrace = true ∧
    rootsPresent forgedTrace = true := by decide

theorem forgedTraceRejected : checkTrace positiveReview forgedTrace = false := by decide

def unauthorizedProjection : ProjectedReport :=
  { reportFor positiveReview (canonicalTrace positiveReview) with executionPermission := true }

theorem unauthorizedProjectionRejected :
    project positiveReview (canonicalTrace positiveReview) unauthorizedProjection = none := by decide

def launderedProjection : ProjectedReport :=
  { reportFor hypotheticalReview (canonicalTrace hypotheticalReview) with
    hypotheses := [], grounded := true }

theorem launderedProjectionRejected :
    project hypotheticalReview (canonicalTrace hypotheticalReview) launderedProjection = none := by decide

def droppedNeedProjection : ProjectedReport :=
  { reportFor requiredUnused (canonicalTrace requiredUnused) with explicitNeeds := [] }

theorem droppedNeedProjectionRejected :
    project requiredUnused (canonicalTrace requiredUnused) droppedNeedProjection = none := by decide

/-- Public positive witness and exhaustive row count, not a prose-only trace. -/
theorem positiveWitnessRow :
    (⟨[true, true], [true, true], true⟩ : EvaluationRow) ∈
      evaluationRows positiveReview := by decide

theorem positiveExhaustiveAccounting :
    (evaluationRows positiveReview).length = 4 := by decide

def refutedReview : Review := { positiveReview with query := .neg (.atom 0) }

theorem refutedLogical : outcome refutedReview = .refuted := by decide

theorem negativeWitnessRow :
    (⟨[true, true], [true, true], false⟩ : EvaluationRow) ∈
      evaluationRows refutedReview := by decide

theorem negativeTraceAccepted :
    checkTrace refutedReview (canonicalTrace refutedReview) = true := by decide

theorem negativeProjectionFaithful : FaithfulProjection refutedReview
    (canonicalTrace refutedReview) (reportFor refutedReview (canonicalTrace refutedReview)) :=
  traceFaithful _ _ _ (by decide)

theorem conditionalTraceAccepted :
    checkTrace hypotheticalReview (canonicalTrace hypotheticalReview) = true := by decide

theorem conditionalProjectionFaithful : FaithfulProjection hypotheticalReview
    (canonicalTrace hypotheticalReview)
    (reportFor hypotheticalReview (canonicalTrace hypotheticalReview)) :=
  traceFaithful _ _ _ (by decide)

theorem exhaustedTraceHasNoInventedRows :
    evaluationRows { positiveReview with budget := 0 } = [] := by decide

def initialState : AnalysisState := ⟨⟨[], [], 0⟩, []⟩

def positiveRequest : AnalysisRequest :=
  ⟨positiveReview, canonicalTrace positiveReview,
    reportFor positiveReview (canonicalTrace positiveReview)⟩

theorem analysisActuallyProducesReport :
    (analysisStep initialState positiveRequest).state.reports.length = 1 := by decide

theorem analysisDoesNotAdmitOrAuthorize :
    (analysisStep initialState positiveRequest).state.authority = initialState.authority ∧
    (analysisStep initialState positiveRequest).issuedExecutionPermission = none :=
  analysisNonAuthority initialState positiveRequest

end Weft.Grounding.Examples
