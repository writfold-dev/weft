import Weft.Finite.Quantifiers
import Weft.Finite.Substitution
import Weft.Finite.TraceContext

namespace Weft.Finite.Traces

open Weft.Language Weft.Logic Weft.Grounding
open Weft.Finite.Sets Weft.Finite.Syntax

/-! Checked quantified annotations are valuation-relative, not a new entailment or
world-grounding oracle. The supplied context, interpretation and outer lexical
environment are fixed checker inputs. Source spans and live IO are outside this
model. A trace is complete only after successful finite lowering, not after an
arbitrary prefix of instances. Inventory claims remain independent of coverage of
the declared finite domain. -/

inductive QuantifierKind where
  | universal
  | existential
  deriving DecidableEq, Repr

def quantify (kind : QuantifierKind) (domain : SetExpr) (body : Expr) : Expr :=
  match kind with
  | .universal => .all domain body
  | .existential => .any domain body

/-- Remove precisely the new de Bruijn slot, preserving every outer reference.
Nested binders are protected by Expr.substitute's lifted substitution. -/
def instanceBody (member : Member) (body : Expr) : Expr :=
  body.substitute (instantiate member)

structure InstanceRow where
  member : Member
  binderIndex : Nat
  substitution : Expr
  formula : Formula
  dependencies : List Binding
  result : Bool
  deriving DecidableEq, Repr

structure QuantifiedReport where
  kind : QuantifierKind
  domainSource : SetExpr
  body : Expr
  domain : CapturedSet
  rows : List InstanceRow
  formula : Formula
  valuationBindings : List (Nat × Bool)
  premiseResults : List Bool
  dependencies : List Binding
  result : Bool
  domainSize : Nat
  /-- Count before deduplication in this local materialization/import event.
  `none` means unavailable history, never a fabricated zero or distinct count. -/
  rawDomainOccurrences : Option Nat
  domainCapture : Option CaptureStatistics
  instantiatedCount : Nat
  /-- Actual structural admission units, not just final formula nodes. -/
  expansionCost : Nat
  admittedBudget : Nat
  remainingBudget : Nat
  expansionNodes : Nat
  vacuous : Bool
  witnesses : List Member
  counterexamples : List Member
  context : ContextView
  deriving DecidableEq, Repr

/-- Capture every atom occurrence used by this query or its premises. Duplicate
occurrences share the same supplied valuation; no arbitrary hidden model is added. -/
def formulaValuation (valuation : Nat → Bool) : Formula → List (Nat × Bool)
  | .atom index => [(index, valuation index)]
  | .literal _ => []
  | .neg body => formulaValuation valuation body
  | .conj left right | .disj left right =>
      formulaValuation valuation left ++ formulaValuation valuation right

/-- All positive and negative instances remain in rows; these lists select the
member findings appropriate to the quantifier rather than invent discovery hits. -/
def selectedMembers (outcome : Bool) (rows : List InstanceRow) : List Member :=
  (rows.filter (fun row => row.result == outcome)).map InstanceRow.member

theorem selectedMemberFacts (outcome : Bool) (rows : List InstanceRow)
    (member : Member) (selected : member ∈ selectedMembers outcome rows) :
    ∃ row ∈ rows, row.member = member ∧ row.result = outcome := by
  obtain ⟨row, filtered, equality⟩ := List.mem_map.mp selected
  have facts := List.mem_filter.mp filtered
  exact ⟨row, facts.1, equality, by simpa using facts.2⟩

open Weft.Finite.Lowering

def instanceRows {ctx intern env body members} (valuation : Nat → Bool) :
    Instances ctx intern env body members → List InstanceRow
  | .nil => []
  | .cons member child tail =>
      ⟨member, 0, instanceBody member body, child.formula,
        member.origins ++ child.origins, evaluate valuation child.formula⟩ ::
        instanceRows valuation tail

theorem instanceCoverage {ctx intern env body members} (valuation : Nat → Bool)
    (children : Instances ctx intern env body members) :
    (instanceRows valuation children).map InstanceRow.member = members := by
  induction members with
  | nil => cases children; rfl
  | cons member rest ih =>
      cases children with
      | cons actual child tail => simp [instanceRows, ih tail]

theorem instanceOrigins {ctx intern env body members} (valuation : Nat → Bool)
    (children : Instances ctx intern env body members) :
    (instanceRows valuation children).flatMap InstanceRow.dependencies = children.origins := by
  induction members with
  | nil => cases children; rfl
  | cons member rest ih =>
      cases children with
      | cons actual child tail =>
          simp [instanceRows, Instances.origins, ih tail, List.append_assoc]

/-- A row is tied to a real checked body expansion under the exact pushed lexical
environment. Neither member identity nor a claimed Boolean can replace that link. -/
theorem instanceDerivation {ctx intern env body members} (valuation : Nat → Bool)
    (children : Instances ctx intern env body members) (row : InstanceRow)
    (member : row ∈ instanceRows valuation children) :
    row.binderIndex = 0 ∧ row.substitution = instanceBody row.member body ∧
      ∃ child : Expansion ctx intern (push row.member env) body,
        row.formula = child.formula ∧
        row.dependencies = row.member.origins ++ child.origins ∧
        row.result = evaluate valuation child.formula := by
  induction members with
  | nil => cases children; simp [instanceRows] at member
  | cons first rest ih =>
      cases children with
      | cons actual child tail =>
          rcases List.mem_cons.mp member with equality | later
          · subst row
            exact ⟨rfl, rfl, child, rfl, rfl, rfl⟩
          · exact ih tail later

structure QuantifiedExpansion (ctx : Context) (intern : GroundCall → Option Nat)
    (env : Env) (source : SetExpr) (body : Expr) where
  domain : CapturedSet
  captured : evalSet ctx env source = some domain
  children : Instances ctx intern env body domain.members

def expansionView {ctx intern env source body} (kind : QuantifierKind)
    (expansion : Expansion ctx intern env (quantify kind source body)) :
    QuantifiedExpansion ctx intern env source body :=
  match kind, expansion with
  | .universal, .all domain captured _ children => ⟨domain, captured, children⟩
  | .existential, .any domain captured _ children => ⟨domain, captured, children⟩

/-- Deterministic projection of a successful derivation, never a supplied answer
list. Duplicate provenance occurrences are intentionally not deduplicated. -/
def reportOf {ctx intern env source body budget} (kind : QuantifierKind)
    (metadata : TraceContext) (valuation : Nat → Bool)
    (expansion : WorkExpansion ctx intern env (quantify kind source body) budget) : QuantifiedReport :=
  let view := expansionView kind expansion.value
  let rows := instanceRows valuation view.children
  { kind := kind
    domainSource := source
    body := body
    domain := view.domain
    rows := rows
    formula := expansion.formula
    valuationBindings := formulaValuation valuation expansion.formula ++
      metadata.inputs.flatMap (fun input => formulaValuation valuation input.proposition)
    premiseResults := metadata.inputs.map (fun input => evaluate valuation input.proposition)
    dependencies := (view.domain.origins ++ rows.flatMap InstanceRow.dependencies) ++
      contextOrigins metadata
    result := evaluate valuation expansion.formula
    domainSize := view.domain.members.length
    rawDomainOccurrences := view.domain.rawOccurrences
    domainCapture := view.domain.capture
    instantiatedCount := rows.length
    expansionCost := expansion.used
    admittedBudget := budget
    remainingBudget := expansion.remaining
    expansionNodes := expansion.value.cost
    vacuous := kind == .universal && view.domain.members.isEmpty
    witnesses := if kind = .existential then selectedMembers true rows else []
    counterexamples := if kind = .universal then selectedMembers false rows else []
    context := contextView metadata }

/-- Report capacity is checked before publication; no truncated report is success.
Rows, structural admission work, valuation enumeration, and serialized bytes are
distinct limits. This function checks the first two, not byte or machine-time use. -/
def makeReport (budget rowBudget : Nat) (ctx : Context)
    (intern : GroundCall → Option Nat) (env : Env) (kind : QuantifierKind)
    (source : SetExpr) (body : Expr) (metadata : TraceContext)
    (valuation : Nat → Bool) : Option QuantifiedReport := do
  let expansion ← lower budget ctx intern env (quantify kind source body)
  let report := reportOf kind metadata valuation expansion
  if report.rows.length ≤ rowBudget then some report else none

/-- Mutation anchors: successful lowering, entire report equality, and row-budget
test. Deleting any one admits incomplete or forged reports. -/
def checkQuantifiedTrace (budget rowBudget : Nat) (ctx : Context)
    (intern : GroundCall → Option Nat) (env : Env) (kind : QuantifierKind)
    (source : SetExpr) (body : Expr) (metadata : TraceContext)
    (valuation : Nat → Bool) (report : QuantifiedReport) : Bool :=
  decide (makeReport budget rowBudget ctx intern env kind source body metadata valuation = some report)

theorem checkedReportExpansion (budget rowBudget : Nat) (ctx : Context)
    (intern : GroundCall → Option Nat) (env : Env) (kind : QuantifierKind)
    (source : SetExpr) (body : Expr) (metadata : TraceContext)
    (valuation : Nat → Bool) (report : QuantifiedReport)
    (checked : checkQuantifiedTrace budget rowBudget ctx intern env kind source body
      metadata valuation report = true) :
    ∃ expansion : WorkExpansion ctx intern env (quantify kind source body) budget,
      lower budget ctx intern env (quantify kind source body) = some expansion ∧
      report = reportOf kind metadata valuation expansion ∧ report.rows.length ≤ rowBudget := by
  have accepted : makeReport budget rowBudget ctx intern env kind source body metadata valuation =
      some report := of_decide_eq_true checked
  cases lowered : lower budget ctx intern env (quantify kind source body) with
  | none => simp [makeReport, lowered] at accepted
  | some expansion =>
      by_cases fits : (reportOf kind metadata valuation expansion).rows.length ≤ rowBudget
      · have equality : reportOf kind metadata valuation expansion = report := by
          simpa [makeReport, lowered, fits] using accepted
        exact ⟨expansion, rfl, equality.symm, equality ▸ fits⟩
      · simp [makeReport, lowered, fits] at accepted

structure QuantifiedFaithful (ctx : Context) (intern : GroundCall → Option Nat)
    (interpret : GroundCall → Bool) (valuation : Nat → Bool) (env : Env)
    (kind : QuantifierKind) (source : SetExpr) (body : Expr) (metadata : TraceContext)
    (report : QuantifiedReport) : Prop where
  domainCaptured : evalSet ctx env source = some report.domain
  sourceBound : report.kind = kind ∧ report.domainSource = source ∧ report.body = body
  coverage : report.rows.map InstanceRow.member = report.domain.members
  counts : report.domainSize = report.domain.members.length ∧
    report.instantiatedCount = report.rows.length ∧ report.instantiatedCount = report.domainSize
  captureAccounting : report.rawDomainOccurrences = report.domain.rawOccurrences ∧
    report.domainCapture = report.domain.capture
  instances : ∀ row ∈ report.rows,
    row.binderIndex = 0 ∧ row.substitution = instanceBody row.member body ∧
      ∃ child : Expansion ctx intern (push row.member env) body,
        row.formula = child.formula ∧
        row.dependencies = row.member.origins ++ child.origins ∧
        row.result = evaluate valuation child.formula
  instanceMeaning : ∀ row ∈ report.rows,
    row.result = true ↔ Semantics.meaning ctx interpret (push row.member env) body
  quantifiedMeaning : report.result = true ↔
    Semantics.meaning ctx interpret env (quantify kind source body)
  vacuity : report.vacuous = (kind == .universal && report.domain.members.isEmpty)
  dependencies : report.dependencies =
    (report.domain.origins ++ report.rows.flatMap InstanceRow.dependencies) ++ contextOrigins metadata
  witnesses : report.witnesses =
    if kind = .existential then selectedMembers true report.rows else []
  counterexamples : report.counterexamples =
    if kind = .universal then selectedMembers false report.rows else []
  context : report.context = contextView metadata
  valuationCaptured : report.valuationBindings = formulaValuation valuation report.formula ++
    metadata.inputs.flatMap (fun input => formulaValuation valuation input.proposition)
  premiseEvaluation : report.premiseResults =
    metadata.inputs.map (fun input => evaluate valuation input.proposition)

/-- Q08: checker acceptance implies actual source-domain capture, exact complete
member coverage, hygienic instance lowering, independent semantic outcomes and
unaltered provenance/coverage metadata. Interpretation is an explicit premise,
not an assertion that external predicates are true in the current world. -/
theorem quantifiedTraceFaithful (budget rowBudget : Nat) (ctx : Context)
    (intern : GroundCall → Option Nat) (interpret : GroundCall → Bool)
    (valuation : Nat → Bool) (interpretation : Interpretation intern interpret valuation)
    (env : Env) (kind : QuantifierKind) (source : SetExpr) (body : Expr)
    (metadata : TraceContext) (report : QuantifiedReport)
    (checked : checkQuantifiedTrace budget rowBudget ctx intern env kind source body
      metadata valuation report = true) :
    QuantifiedFaithful ctx intern interpret valuation env kind source body metadata report := by
  obtain ⟨expansion, _lowered, equality, _fits⟩ :=
    checkedReportExpansion budget rowBudget ctx intern env kind source body metadata valuation report checked
  subst report
  let view := expansionView kind expansion.value
  have coverage := instanceCoverage valuation view.children
  refine ⟨view.captured, ⟨rfl, rfl, rfl⟩, coverage, ?_, ⟨rfl, rfl⟩, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨rfl, rfl, ?_⟩
    simpa only [List.length_map] using congrArg List.length coverage
  · exact instanceDerivation valuation view.children
  · intro row member
    obtain ⟨_binder, _substitution, child, _formula, _origins, result⟩ :=
      instanceDerivation valuation view.children row member
    rw [result]
    exact Quantifiers.sound ctx intern interpret valuation interpretation child
  · exact Quantifiers.sound ctx intern interpret valuation interpretation expansion.value

section Corollaries

variable {ctx : Context} {intern : GroundCall → Option Nat}
  {interpret : GroundCall → Bool} {valuation : Nat → Bool} {env : Env}
  {kind : QuantifierKind} {source : SetExpr} {body : Expr}
  {metadata : TraceContext} {report : QuantifiedReport}

theorem rowIsDomainMember
    (faithful : QuantifiedFaithful ctx intern interpret valuation env kind source body metadata report)
    (row : InstanceRow) (present : row ∈ report.rows) : row.member ∈ report.domain.members := by
  rw [← faithful.coverage]
  exact List.mem_map.mpr ⟨row, present, rfl⟩

theorem instanceSubstitutionMeaning
    (faithful : QuantifiedFaithful ctx intern interpret valuation env kind source body metadata report)
    (row : InstanceRow) (present : row ∈ report.rows) :
    row.result = true ↔ Semantics.meaning ctx interpret env row.substitution := by
  rw [(faithful.instances row present).2.1]
  exact (faithful.instanceMeaning row present).trans
    (instantiateMeaning ctx interpret env row.member body).symm

theorem existentialWitness
    (faithful : QuantifiedFaithful ctx intern interpret valuation env .existential source body metadata report)
    (member : Member) (selected : member ∈ report.witnesses) :
    member ∈ report.domain.members ∧ Semantics.meaning ctx interpret (push member env) body := by
  rw [faithful.witnesses] at selected
  simp only [ite_true] at selected
  obtain ⟨row, present, equality, positive⟩ := selectedMemberFacts true report.rows member selected
  subst member
  exact ⟨rowIsDomainMember faithful row present, (faithful.instanceMeaning row present).mp positive⟩

theorem universalCounterexample
    (faithful : QuantifiedFaithful ctx intern interpret valuation env .universal source body metadata report)
    (member : Member) (selected : member ∈ report.counterexamples) :
    member ∈ report.domain.members ∧ ¬ Semantics.meaning ctx interpret (push member env) body := by
  rw [faithful.counterexamples] at selected
  simp only [ite_true] at selected
  obtain ⟨row, present, equality, negative⟩ := selectedMemberFacts false report.rows member selected
  subst member
  refine ⟨rowIsDomainMember faithful row present, ?_⟩
  intro holds
  have positive := (faithful.instanceMeaning row present).mpr holds
  simp [negative] at positive

theorem existentialSuccessHasWitness
    (faithful : QuantifiedFaithful ctx intern interpret valuation env .existential source body metadata report)
    (positive : report.result = true) :
    ∃ member ∈ report.witnesses, member ∈ report.domain.members ∧
      Semantics.meaning ctx interpret (push member env) body := by
  obtain ⟨set, captured, member, present, holds⟩ := faithful.quantifiedMeaning.mp positive
  have same : set = report.domain := Option.some.inj (captured.symm.trans faithful.domainCaptured)
  subst set
  have covered : member ∈ report.rows.map InstanceRow.member := faithful.coverage.symm ▸ present
  obtain ⟨row, rowPresent, equality⟩ := List.mem_map.mp covered
  have outcome : row.result = true := (faithful.instanceMeaning row rowPresent).mpr
    (by simpa only [equality] using holds)
  refine ⟨member, ?_, present, holds⟩
  rw [faithful.witnesses]
  simp only [ite_true, selectedMembers]
  exact List.mem_map.mpr ⟨row, List.mem_filter.mpr ⟨rowPresent, by simp [outcome]⟩, equality⟩

theorem existentialAbsence
    (faithful : QuantifiedFaithful ctx intern interpret valuation env .existential source body metadata report)
    (negative : report.result = false) :
    ∀ member ∈ report.domain.members, ¬ Semantics.meaning ctx interpret (push member env) body := by
  intro member present holds
  have positive := faithful.quantifiedMeaning.mpr
    ⟨report.domain, faithful.domainCaptured, member, present, holds⟩
  simp [negative] at positive

theorem universalSuccess
    (faithful : QuantifiedFaithful ctx intern interpret valuation env .universal source body metadata report)
    (positive : report.result = true) :
    ∀ member ∈ report.domain.members, Semantics.meaning ctx interpret (push member env) body := by
  obtain ⟨set, captured, holds⟩ := faithful.quantifiedMeaning.mp positive
  have same : set = report.domain := Option.some.inj (captured.symm.trans faithful.domainCaptured)
  exact same ▸ holds

theorem universalFailureHasCounterexample
    (faithful : QuantifiedFaithful ctx intern interpret valuation env .universal source body metadata report)
    (negative : report.result = false) :
    ∃ member ∈ report.counterexamples, member ∈ report.domain.members ∧
      ¬ Semantics.meaning ctx interpret (push member env) body := by
  have bad : ∃ row ∈ report.rows, row.result = false := by
    apply Classical.byContradiction
    intro missing
    have allHold : ∀ member ∈ report.domain.members,
        Semantics.meaning ctx interpret (push member env) body := by
      intro member present
      have covered : member ∈ report.rows.map InstanceRow.member := faithful.coverage.symm ▸ present
      obtain ⟨row, rowPresent, equality⟩ := List.mem_map.mp covered
      have positive : row.result = true := by
        cases outcome : row.result with
        | false => exact False.elim (missing ⟨row, rowPresent, outcome⟩)
        | true => rfl
      have holds := (faithful.instanceMeaning row rowPresent).mp positive
      exact equality ▸ holds
    have positive := faithful.quantifiedMeaning.mpr ⟨report.domain, faithful.domainCaptured, allHold⟩
    simp [negative] at positive
  obtain ⟨row, present, outcome⟩ := bad
  have selected : row.member ∈ report.counterexamples := by
    rw [faithful.counterexamples]
    simp only [ite_true, selectedMembers]
    exact List.mem_map.mpr ⟨row, List.mem_filter.mpr ⟨present, by simp [outcome]⟩, rfl⟩
  exact ⟨row.member, selected, universalCounterexample faithful row.member selected⟩

theorem emptyUniversalVacuity
    (faithful : QuantifiedFaithful ctx intern interpret valuation env .universal source body metadata report)
    (empty : report.domain.members = []) : report.result = true ∧ report.vacuous = true := by
  refine ⟨faithful.quantifiedMeaning.mpr ⟨report.domain, faithful.domainCaptured, ?_⟩, ?_⟩
  · simp [empty]
  · simp [faithful.vacuity, empty]

theorem emptyExistentialNoWitness
    (faithful : QuantifiedFaithful ctx intern interpret valuation env .existential source body metadata report)
    (empty : report.domain.members = []) : report.result = false ∧ report.witnesses = [] := by
  have noPositive : report.result ≠ true := by
    intro positive
    obtain ⟨member, _selected, present, _holds⟩ := existentialSuccessHasWitness faithful positive
    simp [empty] at present
  have noWitness : report.witnesses = [] := by
    cases members : report.witnesses with
    | nil => rfl
    | cons first rest =>
        have selected : first ∈ report.witnesses := by simp [members]
        have present := (existentialWitness faithful first selected).1
        simp [empty] at present
  exact ⟨by cases result : report.result <;> simp_all, noWitness⟩

theorem domainOriginPreserved
    (faithful : QuantifiedFaithful ctx intern interpret valuation env kind source body metadata report)
    (binding : Binding) (origin : binding ∈ report.domain.origins) : binding ∈ report.dependencies := by
  rw [faithful.dependencies]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl origin)))

theorem instanceOriginPreserved
    (faithful : QuantifiedFaithful ctx intern interpret valuation env kind source body metadata report)
    (row : InstanceRow) (present : row ∈ report.rows)
    (binding : Binding) (origin : binding ∈ row.dependencies) : binding ∈ report.dependencies := by
  rw [faithful.dependencies]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inr (List.mem_flatMap.mpr ⟨row, present, origin⟩))))

theorem memberOriginPreserved
    (faithful : QuantifiedFaithful ctx intern interpret valuation env kind source body metadata report)
    (member : Member) (present : member ∈ report.domain.members)
    (binding : Binding) (origin : binding ∈ member.origins) : binding ∈ report.dependencies := by
  have covered : member ∈ report.rows.map InstanceRow.member := faithful.coverage.symm ▸ present
  obtain ⟨row, rowPresent, equality⟩ := List.mem_map.mp covered
  obtain ⟨_binder, _subst, child, _formula, dependencies, _result⟩ := faithful.instances row rowPresent
  apply instanceOriginPreserved faithful row rowPresent binding
  rw [dependencies]
  exact List.mem_append.mpr (Or.inl (by simpa only [equality] using origin))

theorem contextOriginPreserved
    (faithful : QuantifiedFaithful ctx intern interpret valuation env kind source body metadata report)
    (binding : Binding) (origin : binding ∈ contextOrigins metadata) : binding ∈ report.dependencies := by
  rw [faithful.dependencies]
  exact List.mem_append.mpr (Or.inr origin)

theorem traceInventoryNotUpgraded
    (faithful : QuantifiedFaithful ctx intern interpret valuation env kind source body metadata report) :
    report.context.captured.inventory = metadata.inventory ∧
      report.context.captured.requiredGaps = metadata.requiredGaps ∧
      report.context.effectAuthority = false ∧ report.context.writfoldGrounded = false := by
  rw [faithful.context]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem traceHypothesisRetained
    (faithful : QuantifiedFaithful ctx intern interpret valuation env kind source body metadata report)
    (input : Input) (present : input ∈ metadata.inputs) (identity : Nat)
    (origin : input.origin = .hypothesis identity) :
    input ∈ report.context.captured.inputs ∧ input.origin = .hypothesis identity ∧
      report.context.hypothetical = true := by
  rw [faithful.context]
  exact hypothesisNotLaundered metadata input present identity origin

theorem traceObservationNotRefreshed
    (faithful : QuantifiedFaithful ctx intern interpret valuation env kind source body metadata report)
    (input : Input) (present : input ∈ metadata.inputs) (assessment : Assessment)
    (origin : input.origin = .observation assessment) :
    input ∈ report.context.captured.inputs ∧ input.origin = .observation assessment := by
  rw [faithful.context]
  exact observationNotRefreshed metadata input present assessment origin

end Corollaries

theorem incompleteExpansionRejected (budget rowBudget : Nat) (ctx : Context)
    (intern : GroundCall → Option Nat) (env : Env) (kind : QuantifierKind)
    (source : SetExpr) (body : Expr) (metadata : TraceContext)
    (valuation : Nat → Bool) (report : QuantifiedReport)
    (incomplete : lower budget ctx intern env (quantify kind source body) = none) :
    checkQuantifiedTrace budget rowBudget ctx intern env kind source body metadata valuation report = false := by
  simp [checkQuantifiedTrace, makeReport, incomplete]

theorem acceptedTraceBudgets (budget rowBudget : Nat) (ctx : Context)
    (intern : GroundCall → Option Nat) (env : Env) (kind : QuantifierKind)
    (source : SetExpr) (body : Expr) (metadata : TraceContext)
    (valuation : Nat → Bool) (report : QuantifiedReport)
    (checked : checkQuantifiedTrace budget rowBudget ctx intern env kind source body
      metadata valuation report = true) :
    report.expansionCost ≤ budget ∧ report.rows.length ≤ rowBudget := by
  obtain ⟨expansion, lowered, equality, fits⟩ :=
    checkedReportExpansion budget rowBudget ctx intern env kind source body metadata valuation report checked
  refine ⟨?_, fits⟩
  rw [equality]
  exact Quantifiers.lowerCost budget expansion lowered

/-- Trace accounting is bound to the checked run, including unused capacity. -/
theorem acceptedTraceAccounting (budget rowBudget : Nat) (ctx : Context)
    (intern : GroundCall → Option Nat) (env : Env) (kind : QuantifierKind)
    (source : SetExpr) (body : Expr) (metadata : TraceContext)
    (valuation : Nat → Bool) (report : QuantifiedReport)
    (checked : checkQuantifiedTrace budget rowBudget ctx intern env kind source body
      metadata valuation report = true) :
    report.admittedBudget = budget ∧ report.remainingBudget ≤ budget ∧
      report.expansionCost + report.remainingBudget = budget := by
  obtain ⟨expansion, lowered, equality, _fits⟩ :=
    checkedReportExpansion budget rowBudget ctx intern env kind source body metadata valuation report checked
  rw [equality]
  exact ⟨rfl, Quantifiers.lowerRemaining budget expansion lowered,
    Quantifiers.lowerWorkConservation budget expansion lowered⟩

/-- Successful reports always expose a real local capture event/count. Imported
source claims remain scoped in that event, separate from distinct row coverage. -/
theorem acceptedTraceRawOccurrences (budget rowBudget : Nat) (ctx : Context)
    (intern : GroundCall → Option Nat) (env : Env) (kind : QuantifierKind)
    (source : SetExpr) (body : Expr) (metadata : TraceContext)
    (valuation : Nat → Bool) (report : QuantifiedReport)
    (checked : checkQuantifiedTrace budget rowBudget ctx intern env kind source body
      metadata valuation report = true) :
    ∃ capture, report.domainCapture = some capture ∧
      report.rawDomainOccurrences = some capture.observed.rawOccurrences ∧
      evalSet ctx env source = some report.domain := by
  obtain ⟨expansion, _lowered, equality, _fits⟩ :=
    checkedReportExpansion budget rowBudget ctx intern env kind source body metadata valuation report checked
  subst report
  let view := expansionView kind expansion.value
  obtain ⟨capture, present⟩ :=
    CaptureBudget.evalSetCapturePresent ctx env source view.domain view.captured
  refine ⟨capture, present, ?_, view.captured⟩
  change view.domain.rawOccurrences = some capture.observed.rawOccurrences
  simp [CapturedSet.rawOccurrences, present]

end Weft.Finite.Traces
