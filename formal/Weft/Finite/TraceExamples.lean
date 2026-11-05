import Weft.Finite.SetExamples
import Weft.Finite.Traces

namespace Weft.Finite.TraceExamples

open Weft.Language Weft.Logic Weft.Grounding
open Weft.Finite.Sets Weft.Finite.Syntax Weft.Finite.Traces

/-! Inhabited mathematical captures, not Writfold acquisition or source spans.
Every example uses the real finite AST, capture/lowering and checked report. -/

def binding (identity : Nat) : Binding :=
  ⟨⟨1, 2, 3, 4, 5, 6⟩, 7, identity, 8, 9, 10⟩

def hypothesis : Input :=
  ⟨binding 30, .literal true, [binding 31], .hypothesis 12⟩

def metadata : TraceContext :=
  ⟨some (binding 20), .incomplete [binding 21], [binding 22], [binding 23], [hypothesis]⟩

def ctx : Context :=
  { legacy := ⟨fun _ => none, fun _ => none⟩
    profile := ⟨fun _ => none⟩
    named := fun _ => none
    sets := fun _ => none
    fieldType := fun _ _ => none
    field := fun _ _ => none
    collectionType := fun _ _ => none
    collection := fun _ _ => none
    globalOrigins := fun _ => [] }

def outer : Env := fun _ => none

def intern : GroundCall → Option Nat := fun _ => none

def valuation : Nat → Bool := fun _ => false

def one : Member := ⟨.natural 1, [binding 1]⟩
def two : Member := ⟨.natural 2, [binding 2]⟩

def domain : SetExpr :=
  .union .natural (.singleton (.captured one)) (.singleton (.captured two))

def reflexiveBody : Expr := .atom (.equal (.bound 0) (.bound 0))
def oneBody : Expr := .atom (.equal (.bound 0) (.literal (.natural 1)))
def absentBody : Expr := .atom (.equal (.bound 0) (.literal (.natural 3)))

/-- Structural capture/expansion admission; classifier valuation limits remain 4. -/
def workProfile : Nat := 512

theorem hypotheticalInventoryRetained :
    (contextView metadata).hypothetical = true ∧
      (contextView metadata).captured.inventory = .incomplete [binding 21] ∧
      (contextView metadata).captured.requiredGaps = [binding 23] ∧
      (contextView metadata).effectAuthority = false := by decide

def universalReport : QuantifiedReport :=
  (makeReport workProfile 2 ctx intern outer .universal domain reflexiveBody metadata valuation).get (by decide)

def refutingReport : QuantifiedReport :=
  (makeReport workProfile 2 ctx intern outer .universal domain oneBody metadata valuation).get (by decide)

def existentialReport : QuantifiedReport :=
  (makeReport workProfile 2 ctx intern outer .existential domain oneBody metadata valuation).get (by decide)

def absenceReport : QuantifiedReport :=
  (makeReport workProfile 2 ctx intern outer .existential domain absentBody metadata valuation).get (by decide)

def emptyUniversalReport : QuantifiedReport :=
  (makeReport 3 0 ctx intern outer .universal (.empty .natural) reflexiveBody metadata valuation).get (by decide)

def emptyExistentialReport : QuantifiedReport :=
  (makeReport 3 0 ctx intern outer .existential (.empty .natural) reflexiveBody metadata valuation).get (by decide)

theorem positiveUniversal :
    checkQuantifiedTrace workProfile 2 ctx intern outer .universal domain reflexiveBody
      metadata valuation universalReport = true ∧
    universalReport.result = true ∧ universalReport.domainSize = 2 ∧
    universalReport.instantiatedCount = 2 ∧ universalReport.vacuous = false := by decide

theorem concreteRefutingMember :
    checkQuantifiedTrace workProfile 2 ctx intern outer .universal domain oneBody
      metadata valuation refutingReport = true ∧
    refutingReport.result = false ∧
    refutingReport.counterexamples.map Member.value = [.natural 2] := by decide

theorem concreteExistentialWitness :
    checkQuantifiedTrace workProfile 2 ctx intern outer .existential domain oneBody
      metadata valuation existentialReport = true ∧
    existentialReport.result = true ∧
    existentialReport.witnesses.map Member.value = [.natural 1] := by decide

theorem completeExistentialAbsence :
    checkQuantifiedTrace workProfile 2 ctx intern outer .existential domain absentBody
      metadata valuation absenceReport = true ∧
    absenceReport.result = false ∧ absenceReport.witnesses = [] ∧
    absenceReport.rows.length = 2 := by decide

theorem emptyDomainReporting :
    emptyUniversalReport.result = true ∧ emptyUniversalReport.vacuous = true ∧
    emptyUniversalReport.domainSize = 0 ∧ emptyUniversalReport.instantiatedCount = 0 ∧
    emptyExistentialReport.result = false ∧ emptyExistentialReport.vacuous = false ∧
    emptyExistentialReport.witnesses = [] ∧
    emptyUniversalReport.context.captured.inventory = .incomplete [binding 21] := by decide

def forgedMember : QuantifiedReport :=
  { universalReport with
    rows := universalReport.rows.map (fun row => { row with member := ⟨.natural 99, []⟩ }) }

def forgedSubstitution : QuantifiedReport :=
  { universalReport with
    rows := universalReport.rows.map
      (fun row => { row with substitution := .atom (.legacy (.boolean true)) }) }

def forgedOutcome : QuantifiedReport :=
  { universalReport with
    rows := universalReport.rows.map (fun row => { row with result := false }) }

def forgedCoverage : QuantifiedReport :=
  { universalReport with rows := universalReport.rows.take 1, instantiatedCount := 1 }

def forgedWitness : QuantifiedReport :=
  { existentialReport with witnesses := [two] }

theorem forgedMemberRejected :
    checkQuantifiedTrace workProfile 2 ctx intern outer .universal domain reflexiveBody
      metadata valuation forgedMember = false := by decide

theorem forgedSubstitutionRejected :
    checkQuantifiedTrace workProfile 2 ctx intern outer .universal domain reflexiveBody
      metadata valuation forgedSubstitution = false := by decide

theorem forgedOutcomeRejected :
    checkQuantifiedTrace workProfile 2 ctx intern outer .universal domain reflexiveBody
      metadata valuation forgedOutcome = false := by decide

theorem forgedCoverageRejected :
    checkQuantifiedTrace workProfile 2 ctx intern outer .universal domain reflexiveBody
      metadata valuation forgedCoverage = false := by decide

theorem forgedWitnessRejected :
    checkQuantifiedTrace workProfile 2 ctx intern outer .existential domain oneBody
      metadata valuation forgedWitness = false := by decide

def duplicateDomain : SetExpr :=
  .union .natural (.singleton (.captured one))
    (.singleton (.captured ⟨.natural 1, [binding 3]⟩))

def duplicateReport : QuantifiedReport :=
  (makeReport workProfile 1 ctx intern outer .universal duplicateDomain
    (.atom (.legacy (.boolean true))) metadata valuation).get (by decide)

theorem duplicateProvenance :
    duplicateReport.domainSize = 1 ∧
    duplicateReport.domain.members = [⟨.natural 1, [binding 1, binding 3]⟩] ∧
    binding 1 ∈ duplicateReport.dependencies ∧ binding 3 ∈ duplicateReport.dependencies ∧
    binding 30 ∈ duplicateReport.dependencies ∧ binding 31 ∈ duplicateReport.dependencies ∧
    duplicateReport.context.captured.inputs = [hypothesis] ∧
    duplicateReport.context.hypothetical = true := by decide

def emptySpreadContext : Context :=
  { ctx with sets := fun _ => some ⟨.natural, [], [binding 9], none⟩ }

def emptySpreadReport : QuantifiedReport :=
  (makeReport workProfile 1 emptySpreadContext intern outer .universal
    (.union .natural (.singleton (.captured one)) (.named .natural 0))
    reflexiveBody metadata valuation).get (by decide)

theorem emptySpreadOriginRetained :
    emptySpreadReport.domainSize = 1 ∧ binding 9 ∈ emptySpreadReport.dependencies := by decide

theorem partialDomainFailure :
    makeReport workProfile 2 ctx intern outer .universal
      (.union .natural (.singleton (.captured one)) (.named .natural 0))
      reflexiveBody metadata valuation = none := by decide

theorem partialExpansionFailure :
    makeReport 60 2 ctx intern outer .universal domain reflexiveBody metadata valuation = none := by decide

theorem partialReportFailure :
    makeReport workProfile 1 ctx intern outer .universal domain reflexiveBody metadata valuation = none := by decide

theorem illTypedEmptyBodyRejected :
    makeReport 3 0 ctx intern outer .universal (.empty .natural)
      (.atom (.equal (.bound 0) (.literal (.text "wrong")))) metadata valuation = none := by decide

theorem forgedInventoryRejected :
    checkQuantifiedTrace workProfile 2 ctx intern outer .universal domain reflexiveBody metadata valuation
      { universalReport with context :=
        { universalReport.context with captured :=
          { metadata with inventory := .claimedComplete (binding 99), requiredGaps := [] } } } = false := by decide

theorem literalInterpretation : Interpretation intern (fun _ => false) valuation := by
  constructor
  · intro a b index impossible _other
    simp [intern] at impossible
  · intro call index impossible
    simp [intern] at impossible

theorem inhabitedQ08 :
    QuantifiedFaithful ctx intern (fun _ => false) valuation outer .universal
      domain reflexiveBody metadata universalReport :=
  quantifiedTraceFaithful workProfile 2 ctx intern (fun _ => false) valuation literalInterpretation
    outer .universal domain reflexiveBody metadata universalReport positiveUniversal.1

def predicateName : PredicateName := ⟨"calibration", "p"⟩

def predicateContext : Context :=
  { ctx with profile := ⟨fun name => if name = predicateName then some [.natural] else none⟩ }

def predicateIntern (call : GroundCall) : Option Nat :=
  if call = ⟨predicateName, [.natural 1]⟩ then some 0
  else if call = ⟨predicateName, [.natural 2]⟩ then some 1 else none

def predicateBody : Expr := .atom (.predicate predicateName [.bound 0])
def leftModel : Nat → Bool := fun index => index == 0
def rightModel : Nat → Bool := fun index => index == 1
def existentialPremise : Formula := .disj (.atom 0) (.atom 1)
def universalPremise : Formula := .neg (.conj (.atom 0) (.atom 1))

def existentialMetadata : TraceContext :=
  { metadata with inputs := [⟨binding 40, existentialPremise, [], .hypothesis 40⟩] }

def universalMetadata : TraceContext :=
  { metadata with inputs := [⟨binding 41, universalPremise, [], .hypothesis 41⟩] }

def leftExists : QuantifiedReport :=
  (makeReport workProfile 2 predicateContext predicateIntern outer .existential domain predicateBody
    existentialMetadata leftModel).get (by decide)

def rightExists : QuantifiedReport :=
  (makeReport workProfile 2 predicateContext predicateIntern outer .existential domain predicateBody
    existentialMetadata rightModel).get (by decide)

def leftForall : QuantifiedReport :=
  (makeReport workProfile 2 predicateContext predicateIntern outer .universal domain predicateBody
    universalMetadata leftModel).get (by decide)

def rightForall : QuantifiedReport :=
  (makeReport workProfile 2 predicateContext predicateIntern outer .universal domain predicateBody
    universalMetadata rightModel).get (by decide)

/-- P = A ∨ B entails the expanded existential, but neither member is entailed.
The reports explicitly retain two different premise-model valuations/witnesses. -/
theorem nonuniformExistentialWitness :
    classify 2 [existentialPremise] leftExists.formula 4 = .entailed ∧
    leftExists.rows.map (fun row => classify 2 [existentialPremise] row.formula 4) =
      [.undetermined, .undetermined] ∧
    leftExists.premiseResults = [true] ∧ rightExists.premiseResults = [true] ∧
    leftExists.witnesses.map Member.value = [.natural 1] ∧
    rightExists.witnesses.map Member.value = [.natural 2] ∧
    leftExists.valuationBindings ≠ rightExists.valuationBindings ∧
    checkQuantifiedTrace workProfile 2 predicateContext predicateIntern outer .existential domain
      predicateBody existentialMetadata leftModel leftExists = true ∧
    checkQuantifiedTrace workProfile 2 predicateContext predicateIntern outer .existential domain
      predicateBody existentialMetadata rightModel rightExists = true := by decide

/-- P = ¬(A ∧ B) refutes the expanded universal, but refutes neither individual
member uniformly. Counterexamples are indexed by their checked premise model. -/
theorem nonuniformUniversalCounterexample :
    classify 2 [universalPremise] leftForall.formula 4 = .refuted ∧
    leftForall.rows.map (fun row => classify 2 [universalPremise] row.formula 4) =
      [.undetermined, .undetermined] ∧
    leftForall.premiseResults = [true] ∧ rightForall.premiseResults = [true] ∧
    leftForall.counterexamples.map Member.value = [.natural 2] ∧
    rightForall.counterexamples.map Member.value = [.natural 1] ∧
    leftForall.valuationBindings ≠ rightForall.valuationBindings ∧
    checkQuantifiedTrace workProfile 2 predicateContext predicateIntern outer .universal domain
      predicateBody universalMetadata leftModel leftForall = true ∧
    checkQuantifiedTrace workProfile 2 predicateContext predicateIntern outer .universal domain
      predicateBody universalMetadata rightModel rightForall = true := by decide

theorem forgedValuationRejected :
    checkQuantifiedTrace workProfile 2 predicateContext predicateIntern outer .existential domain
      predicateBody existentialMetadata leftModel
      { leftExists with valuationBindings := rightExists.valuationBindings } = false := by decide

/-- Integrated accounting anchors: provenance traversal makes 61 admission units
despite only three semantic expansion nodes. Neither count replaces the other. -/
theorem structuralUsageRetained :
    universalReport.expansionCost = 61 ∧ universalReport.expansionNodes = 3 ∧
      universalReport.admittedBudget = workProfile ∧
      universalReport.remainingBudget = workProfile - 61 := by decide

theorem exactWorkBoundary :
    ((makeReport 61 2 ctx intern outer .universal domain reflexiveBody metadata valuation).map
      (fun report => (report.result, report.expansionCost, report.remainingBudget))) =
      some (true, 61, 0) := by decide

theorem forgedUsageRejected :
    checkQuantifiedTrace workProfile 2 ctx intern outer .universal domain reflexiveBody
      metadata valuation { universalReport with expansionCost := 3 } = false := by decide

theorem forgedRemainingRejected :
    checkQuantifiedTrace workProfile 2 ctx intern outer .universal domain reflexiveBody
      metadata valuation { universalReport with remainingBudget := workProfile } = false := by decide

theorem reboundAdmissionBudgetRejected :
    checkQuantifiedTrace (workProfile + 1) 2 ctx intern outer .universal domain reflexiveBody
      metadata valuation universalReport = false := by decide

/-- Raw occurrence accounting is distinct from both domain cardinality and row
coverage. This local union has two input aliases but one resulting member. -/
theorem duplicateRawCountReported :
    duplicateReport.rawDomainOccurrences = some 2 ∧ duplicateReport.domainSize = 1 ∧
      duplicateReport.instantiatedCount = 1 ∧
      duplicateReport.domainCapture = some ⟨⟨.materialization, 2⟩, none⟩ := by decide

def duplicateHeavyContext : Context :=
  { ctx with sets := fun _ => some ⟨.natural, List.replicate 64 one, [binding 1], none⟩ }

set_option maxRecDepth 8192 in
def duplicateHeavyReport : QuantifiedReport :=
  (makeReport workProfile 1 duplicateHeavyContext intern outer .universal
    (.named .natural 0) (.atom (.legacy (.boolean true))) metadata valuation).get (by decide)

set_option maxRecDepth 8192 in
theorem duplicateHeavyRawCountReported :
    duplicateHeavyReport.rawDomainOccurrences = some 64 ∧
      duplicateHeavyReport.domainSize = 1 ∧ duplicateHeavyReport.instantiatedCount = 1 ∧
      duplicateHeavyReport.domainCapture = some ⟨⟨.importedPayload, 64⟩, none⟩ ∧
      binding 1 ∈ duplicateHeavyReport.dependencies := by decide

def boundCaptureContext : Context :=
  { ctx with sets := fun _ =>
      Bindings.lookup SetExamples.priorEnvironment "inputs" }

def boundCaptureReport : QuantifiedReport :=
  (makeReport workProfile 1 boundCaptureContext intern outer .universal
    (.named .natural 0) (.atom (.legacy (.boolean true))) metadata valuation).get (by decide)

/-- Binding and lookup retain the original source count, but do not claim that a
normalized imported payload still contains those two raw aliases. -/
theorem boundSourceCountReported :
    boundCaptureReport.rawDomainOccurrences = some 1 ∧
      boundCaptureReport.domainCapture = some
        ⟨⟨.importedPayload, 1⟩, some ⟨.materialization, 2⟩⟩ ∧
      SetExamples.firstOrigin ∈ boundCaptureReport.dependencies ∧
      SetExamples.secondOrigin ∈ boundCaptureReport.dependencies := by decide

theorem forgedRawCountRejected :
    checkQuantifiedTrace workProfile 1 ctx intern outer .universal duplicateDomain
      (.atom (.legacy (.boolean true))) metadata valuation
      { duplicateReport with rawDomainOccurrences := some 1 } = false := by decide

set_option maxRecDepth 8192 in
theorem forgedCaptureScopeRejected :
    checkQuantifiedTrace workProfile 1 duplicateHeavyContext intern outer .universal
      (.named .natural 0) (.atom (.legacy (.boolean true))) metadata valuation
      { duplicateHeavyReport with
        domainCapture := some ⟨⟨.materialization, 64⟩, none⟩ } = false := by decide

end Weft.Finite.TraceExamples
