import Weft.Grounding.Model

namespace Weft.Grounding

open Weft.Logic

/-! L11–L12. A conservative canonical trace format for the mathematical checker.
It records each imported premise and the complete exhaustive-check request; it
claims no minimal derivation or raw-source span that the calculus did not receive.
All node IDs are local list positions, never external report handles. -/

/-- Public exhaustive-check rows, including the evaluation of each premise.
Rows are absent on invalid domains or insufficient budgets, not fabricated
partial witnesses. The trace retains all rows rather than claiming a minimal core. -/
structure EvaluationRow where
  values : List Bool
  premiseValues : List Bool
  queryValue : Bool
  deriving DecidableEq, Repr

def evaluationRows (r : Review) : List EvaluationRow :=
  if inputsInBounds r.atomCount (premises r) r.query = true then
    if r.budget < requiredBudget r.atomCount then []
    else (valuations r.atomCount).map fun values =>
      ⟨values, (premises r).map (evaluate (extend values)), evaluate (extend values) r.query⟩
  else []

theorem evaluationRowFaithful (r : Review) (row : EvaluationRow)
    (member : row ∈ evaluationRows r) :
    ∃ values ∈ valuations r.atomCount, row.values = values ∧
      row.premiseValues = (premises r).map (evaluate (extend values)) ∧
      row.queryValue = evaluate (extend values) r.query := by
  unfold evaluationRows at member
  split at member
  · split at member
    · simp at member
    · obtain ⟨values, present, equality⟩ := List.mem_map.mp member
      subst row
      exact ⟨values, present, rfl, rfl, rfl⟩
  · simp at member

/-- Completed trace accounting retains every selected valuation exactly in order. -/
theorem evaluationRowsComplete (r : Review)
    (inScope : inputsInBounds r.atomCount (premises r) r.query = true)
    (budget : ¬ r.budget < requiredBudget r.atomCount) :
    (evaluationRows r).map EvaluationRow.values = valuations r.atomCount := by
  simp [evaluationRows, inScope, budget, List.map_map, Function.comp_def]

inductive TracePayload where
  | input (captured : Input)
  | logicalEvaluation (request : Review) (outcome : Verdict) (rows : List EvaluationRow)
  | classification (outcome : Verdict) (grounded : Bool)
  deriving DecidableEq, Repr

structure TraceNode where
  inputs : List Nat
  payload : TracePayload
  deriving DecidableEq, Repr

structure Trace where
  nodes : List TraceNode
  roots : List Nat
  deriving DecidableEq, Repr

def outcome (r : Review) : Verdict :=
  classify r.atomCount (premises r) r.query r.budget

/-- Input origins contain the exact bindings, assessment dimensions, hypotheses,
rule qualification and external dependency edges. The evaluation node links every
captured input, even if the query is a constant. Its request records the complete
atom domain, budget, premises, explicit needs and conservative used inputs. -/
def canonicalTrace (r : Review) : Trace :=
  let n := r.captured.length
  ⟨r.captured.map (fun input => ⟨[], .input input⟩) ++
    [⟨List.range n, .logicalEvaluation r (outcome r) (evaluationRows r)⟩,
     ⟨[n], .classification (outcome r) (checkGrounding r)⟩], [n + 1]⟩

/-- Executable structural checks, independent of the result annotation. -/
def backwards (t : Trace) : Bool :=
  t.nodes.zipIdx.all fun entry => entry.1.inputs.all fun parent => decide (parent < entry.2)

def rootsPresent (t : Trace) : Bool :=
  t.roots.all fun root => decide (root < t.nodes.length)

/-- Every parent link denotes an existing earlier node: an earlier nonnegative
position is in bounds whenever its child is in bounds. -/
def TraceEdge (t : Trace) (child parent : Nat) : Prop :=
  ∃ node, (node, child) ∈ t.nodes.zipIdx ∧ parent ∈ node.inputs

theorem edgeDecreases (t : Trace) (h : backwards t = true)
    {child parent : Nat} (edge : TraceEdge t child parent) : parent < child := by
  obtain ⟨node, member, input⟩ := edge
  have allNodes := List.all_eq_true.mp h
  have allInputs := List.all_eq_true.mp (allNodes (node, child) member)
  exact of_decide_eq_true (allInputs parent input)

inductive TracePath (t : Trace) : Nat → Nat → Prop
  | edge {child parent} : TraceEdge t child parent → TracePath t child parent
  | trans {child middle parent} : TracePath t child middle →
      TracePath t middle parent → TracePath t child parent

theorem pathDecreases (t : Trace) (h : backwards t = true)
    {child parent : Nat} (path : TracePath t child parent) : parent < child := by
  induction path with
  | edge edge => exact edgeDecreases t h edge
  | trans _ _ first second => exact Nat.lt_trans second first

theorem traceAcyclic (t : Trace) (h : backwards t = true) (node : Nat) :
    ¬ TracePath t node node := by
  intro path
  exact Nat.lt_irrefl node (pathDecreases t h path)

/-- Canonical validation deliberately rejects unsupported alternative derivations.
Structural validity alone is insufficient: a DAG can still lie about its inputs
or final result. Recomputing the canonical payload validates those annotations. -/
def TraceAccepted (r : Review) (t : Trace) : Prop :=
  t = canonicalTrace r ∧ backwards t = true ∧ rootsPresent t = true

instance (r : Review) (t : Trace) : Decidable (TraceAccepted r t) := by
  unfold TraceAccepted
  infer_instance

def checkTrace (r : Review) (t : Trace) : Bool := decide (TraceAccepted r t)

def hypotheses (r : Review) : List Input :=
  r.captured.filter fun input => match input.origin with
    | .hypothesis _ => true
    | _ => false

structure ProjectedReport where
  scope : Scope
  result : Verdict
  grounded : Bool
  explicitNeeds : List Binding
  usedInputs : List Binding
  captured : List Input
  hypotheses : List Input
  trace : Trace
  executionPermission : Bool
  omitted : Bool
  deriving DecidableEq, Repr

/-- Only complete, non-authoritative projections are reusable in this calculus.
A truncated human rendering would need a separately marked, non-reusable type. -/
def reportFor (r : Review) (t : Trace) : ProjectedReport :=
  ⟨r.scope, outcome r, checkGrounding r, r.explicitNeeds, r.usedInputs,
    r.captured, hypotheses r, t, false, false⟩

/-- A caller-supplied projection is untrusted. No result strengthening, origin
stripping, hypothesis laundering, omission, or execution grant is accepted. -/
def project (r : Review) (t : Trace) (candidate : ProjectedReport) :
    Option ProjectedReport :=
  if checkTrace r t then
    if candidate = reportFor r t then some candidate else none
  else none

/-- Denotational content preservation, not equality to a Boolean checker output. -/
structure FaithfulProjection (r : Review) (t : Trace) (p : ProjectedReport) : Prop where
  scope : p.scope = r.scope
  result : p.result = classify r.atomCount (premises r) r.query r.budget
  grounding : p.grounded = checkGrounding r
  needs : p.explicitNeeds = r.explicitNeeds
  used : p.usedInputs = r.usedInputs
  originsAndDependencies : p.captured = r.captured
  assumptions : p.hypotheses = hypotheses r
  trace : p.trace = t
  canonical : t = canonicalTrace r
  backwardLinks : backwards t = true
  presentRoots : rootsPresent t = true
  acyclic : ∀ node, ¬ TracePath t node node
  noPermission : p.executionPermission = false
  noOmission : p.omitted = false

/-- L11. Acceptance preserves the checked result, complete original inputs and
all hypotheses; the retained trace is rooted, canonical and acyclic. -/
theorem traceFaithful (r : Review) (t : Trace) (candidate : ProjectedReport)
    (h : project r t candidate = some candidate) :
    FaithfulProjection r t candidate := by
  have accepted : checkTrace r t = true := by
    by_cases accept : checkTrace r t = true
    · exact accept
    · simp [project, accept] at h
  have equal : candidate = reportFor r t := by
    by_cases same : candidate = reportFor r t
    · exact same
    · simp [project, accepted, same] at h
  have valid : TraceAccepted r t := of_decide_eq_true accepted
  subst candidate
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, valid.1,
    valid.2.1, valid.2.2, traceAcyclic t valid.2.1, rfl, rfl⟩

/-- Authoritative data is deliberately separate from analysis history. These are
abstract owner-side contents, not a model of a Writfold API or filesystem. -/
structure AuthorityState where
  admittedCorpus : List Binding
  executionGrants : List Nat
  revision : Nat
  deriving DecidableEq, Repr

structure AnalysisState where
  authority : AuthorityState
  reports : List ProjectedReport
  deriving DecidableEq, Repr

structure AnalysisRequest where
  review : Review
  trace : Trace
  projection : ProjectedReport
  deriving DecidableEq, Repr

structure AnalysisResult where
  state : AnalysisState
  returnedReport : Option ProjectedReport
  issuedExecutionPermission : Option Nat
  deriving DecidableEq, Repr

def analysisStep (state : AnalysisState) (request : AnalysisRequest) : AnalysisResult :=
  match project request.review request.trace request.projection with
  | none => ⟨state, none, none⟩
  | some report =>
      ⟨⟨state.authority, state.reports ++ [report]⟩, some report, none⟩

/-- L12. Analysis may append a checked report but cannot change admission or
execution grants and cannot issue a permission. This is a pure transition-system
non-authority theorem, NOT an IO-containment or owner-API implementation proof. -/
theorem analysisNonAuthority (state : AnalysisState) (request : AnalysisRequest) :
    (analysisStep state request).state.authority = state.authority ∧
    (analysisStep state request).issuedExecutionPermission = none := by
  unfold analysisStep
  split <;> exact ⟨rfl, rfl⟩

def analyzeAll : AnalysisState → List AnalysisRequest → AnalysisState
  | state, [] => state
  | state, request :: rest => analyzeAll (analysisStep state request).state rest

theorem analysesPreserveAuthority (state : AnalysisState) (requests : List AnalysisRequest) :
    (analyzeAll state requests).authority = state.authority := by
  induction requests generalizing state with
  | nil => rfl
  | cons request rest ih =>
      exact (ih (analysisStep state request).state).trans
        (analysisNonAuthority state request).1

end Weft.Grounding
