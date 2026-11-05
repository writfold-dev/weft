import Weft.Grounding.ReportView
import Weft.Language.Semantics

namespace Weft.Grounding

open Weft.Logic Weft.Language

/-! Two checked layers: the existing exhaustive logical DAG, and annotations of
an actual successful typed elaboration of Review.query. The latter is a flat
subtrace with no foreign links: each entry names its exact surface occurrence or
captured premise, and all required entries must occur. Ordering and duplication
are harmless, so honest rich explanations are not rejected by core equality.

The supplied resolved AST/environment/profile are the boundary. No source spans,
byte parsing, variable-rule substitution, or real-world field truth are claimed.
Ground-rule notes describe imported qualified ground premises, not instantiation.
Mutation anchors: DetailValid comparisons and provenance; DetailedAccepted.query;
requiredDetails coverage; comparisonDetailFacts independent semantic bridge. -/

def surfaceParts : Surface → List Surface
  | s@(.boolean _) => [s]
  | s@(.equal _ _) => [s]
  | s@(.notEqual _ _) => [s]
  | s@(.predicate _ _) => [s]
  | s@(.neg inner) => s :: surfaceParts inner
  | s@(.conj left right) => s :: (surfaceParts left ++ surfaceParts right)
  | s@(.disj left right) => s :: (surfaceParts left ++ surfaceParts right)

def surfaceTerms : Surface → List Term
  | .boolean _ => []
  | .equal left right | .notEqual left right => [left, right]
  | .predicate _ arguments => arguments
  | .neg inner => surfaceTerms inner
  | .conj left right | .disj left right => surfaceTerms left ++ surfaceTerms right

inductive Detail where
  | term (source : Term) (value : Value)
  | comparison (negated : Bool) (left right : Term) (equalResult : Bool)
  | hypothesis (input : Input) (identity : Nat)
  | groundRule (input : Input) (assessment : Assessment)
  deriving DecidableEq, Repr

def comparisonSurface (negated : Bool) (left right : Term) : Surface :=
  if negated then .notEqual left right else .equal left right

/-- A comparison records equality truth; a not-equal occurrence negates it. -/
def comparisonResult (negated equalResult : Bool) : Bool :=
  if negated then !equalResult else equalResult

def DetailValid (env : Environment) (surface : Surface) (r : Review) : Detail → Prop
  | .term source value =>
      source ∈ surfaceTerms surface ∧ resolveTerm env source = some value
  | .comparison negated left right result =>
      comparisonSurface negated left right ∈ surfaceParts surface ∧
      compareTerms env left right = some result
  | .hypothesis input identity =>
      input ∈ r.captured ∧ input.origin = .hypothesis identity
  | .groundRule input assessment =>
      input ∈ r.captured ∧ input.origin = .rule assessment true

instance (env : Environment) (surface : Surface) (r : Review) (detail : Detail) :
    Decidable (DetailValid env surface r detail) := by
  cases detail <;> unfold DetailValid <;> infer_instance

def termDetails (env : Environment) (term : Term) : List Detail :=
  match resolveTerm env term with
  | none => []
  | some value => [.term term value]

def comparisonDetails (env : Environment) : Surface → List Detail
  | .equal left right =>
      match compareTerms env left right with
      | none => []
      | some result => [.comparison false left right result]
  | .notEqual left right =>
      match compareTerms env left right with
      | none => []
      | some result => [.comparison true left right result]
  | _ => []

def premiseDetails (input : Input) : List Detail :=
  match input.origin with
  | .hypothesis identity => [.hypothesis input identity]
  | .rule assessment true => [.groundRule input assessment]
  | _ => []

/-- Coverage preserves all occurrences conservatively, including short-circuited
branches and all captured hypotheses/qualified ground rules. The core layer also
retains every observation and every unqualified rule with its exact assessment. -/
def requiredDetails (env : Environment) (surface : Surface) (r : Review) : List Detail :=
  (surfaceTerms surface).flatMap (termDetails env) ++
    (surfaceParts surface).flatMap (comparisonDetails env) ++
    r.captured.flatMap premiseDetails

structure DetailedTrace where
  core : Trace
  details : List Detail
  deriving DecidableEq, Repr

structure DetailedAccepted (env : Environment) (profile : Profile)
    (intern : GroundCall → Option Nat) (surface : Surface) (r : Review)
    (trace : DetailedTrace) : Prop where
  query : elaborate env profile intern surface = some r.query
  core : TraceAccepted r trace.core
  annotations : ∀ detail ∈ trace.details, DetailValid env surface r detail
  coverage : ∀ detail ∈ requiredDetails env surface r, detail ∈ trace.details

instance (env : Environment) (profile : Profile) (intern : GroundCall → Option Nat)
    (surface : Surface) (r : Review) (trace : DetailedTrace) :
    Decidable (DetailedAccepted env profile intern surface r trace) :=
  decidable_of_iff
    (elaborate env profile intern surface = some r.query ∧
      TraceAccepted r trace.core ∧
      (∀ detail ∈ trace.details, DetailValid env surface r detail) ∧
      (∀ detail ∈ requiredDetails env surface r, detail ∈ trace.details))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩,
      fun h => ⟨h.query, h.core, h.annotations, h.coverage⟩⟩

def checkDetailedTrace (env : Environment) (profile : Profile)
    (intern : GroundCall → Option Nat) (surface : Surface) (r : Review)
    (trace : DetailedTrace) : Bool :=
  decide (DetailedAccepted env profile intern surface r trace)

/-- Independent denotational content for the rich annotation vocabulary. -/
def DetailMeaning (env : Environment) (surface : Surface) (r : Review) : Detail → Prop
  | .term source value => source ∈ surfaceTerms surface ∧ TermMeaning env source value
  | .comparison negated left right result =>
      comparisonSurface negated left right ∈ surfaceParts surface ∧
      ComparisonMeaning env left right result
  | .hypothesis input identity =>
      input ∈ r.captured ∧ input.origin = .hypothesis identity
  | .groundRule input assessment =>
      input ∈ r.captured ∧ input.origin = .rule assessment true

theorem detailMeaningSound (env : Environment) (surface : Surface) (r : Review)
    (detail : Detail) (valid : DetailValid env surface r detail) :
    DetailMeaning env surface r detail := by
  cases detail with
  | term source value =>
      exact ⟨valid.1, termMeaningSound env source value valid.2⟩
  | comparison negated left right result =>
      exact ⟨valid.1, comparisonMeaningSound env left right result valid.2⟩
  | hypothesis input identity => exact valid
  | groundRule input assessment => exact valid

/-- Every accepted field annotation gives both the actual lookup and its type. -/
theorem fieldDetailFacts (env : Environment) (surface : Surface) (r : Review)
    (path : Path) (value : Value)
    (valid : DetailValid env surface r (.term (.field path) value)) :
    env.fieldTypes path = some value.type ∧ env.fieldValues path = some value :=
  termEvaluationFacts env (.field path) value valid.2

/-- A comparison annotation is related to typed values independently of the
checker; no truth is inferred from the display text or from core trace equality. -/
theorem comparisonDetailFacts (env : Environment) (surface : Surface) (r : Review)
    (negated : Bool) (left right : Term) (result : Bool)
    (valid : DetailValid env surface r (.comparison negated left right result)) :
    ComparisonMeaning env left right result :=
  comparisonMeaningSound env left right result valid.2

theorem literalDetailFacts (env : Environment) (surface : Surface) (r : Review)
    (original value : Value)
    (valid : DetailValid env surface r (.term (.literal original) value)) :
    original = value := by
  exact Option.some.inj (termEvaluationFacts env (.literal original) value valid.2).2

/-- The annotation's operator determines the actual displayed Boolean, including
inequality; equality truth itself comes from the independent comparison relation. -/
theorem comparisonDetailOutput (env : Environment) (profile : Profile)
    (meaning : GroundCall → Bool) (surface : Surface) (r : Review)
    (negated : Bool) (left right : Term) (result : Bool)
    (valid : DetailValid env surface r (.comparison negated left right result)) :
    denote env profile meaning (comparisonSurface negated left right) =
      some (comparisonResult negated result) := by
  have checked := valid.2
  cases negated <;>
    simp [comparisonSurface, comparisonResult, denote, checked]

theorem hypothesisDetailProvenance (env : Environment) (surface : Surface) (r : Review)
    (input : Input) (identity : Nat)
    (valid : DetailValid env surface r (.hypothesis input identity)) :
    input.proposition ∈ premises r ∧ input.origin = .hypothesis identity :=
  ⟨List.mem_map.mpr ⟨input, valid.1, rfl⟩, valid.2⟩

theorem groundRuleDetailProvenance (env : Environment) (surface : Surface) (r : Review)
    (input : Input) (assessment : Assessment)
    (valid : DetailValid env surface r (.groundRule input assessment)) :
    input.proposition ∈ premises r ∧ input.origin = .rule assessment true :=
  ⟨List.mem_map.mpr ⟨input, valid.1, rfl⟩, valid.2⟩

structure DetailedFaithful (env : Environment) (profile : Profile)
    (intern : GroundCall → Option Nat) (meaning : GroundCall → Bool)
    (valuation : Nat → Bool) (surface : Surface) (r : Review)
    (trace : DetailedTrace) : Prop where
  elaboration : elaborate env profile intern surface = some r.query
  sourceMeaning : SurfaceMeaning env profile meaning surface (evaluate valuation r.query)
  core : TraceAccepted r trace.core
  annotations : ∀ detail ∈ trace.details, DetailMeaning env surface r detail
  coverage : ∀ detail ∈ requiredDetails env surface r, detail ∈ trace.details
  acyclic : ∀ node, ¬ TracePath trace.core node node
  logicalMeaning : VerdictMeaning r.atomCount (premises r) r.query (outcome r)
  noAuthority : (reportView r true).effectAuthority = false

/-- The profile/interner interpretation is explicit; this is source/IR fidelity,
not external-world evidence soundness or owner-side source-span verification. -/
theorem detailedTraceFaithful (env : Environment) (profile : Profile)
    (intern : GroundCall → Option Nat) (meaning : GroundCall → Bool)
    (valuation : Nat → Bool) (interpretation : Interpretation intern meaning valuation)
    (surface : Surface) (r : Review) (trace : DetailedTrace)
    (checked : checkDetailedTrace env profile intern surface r trace = true) :
    DetailedFaithful env profile intern meaning valuation surface r trace := by
  have accepted : DetailedAccepted env profile intern surface r trace :=
    of_decide_eq_true checked
  refine ⟨accepted.query, ?_, accepted.core, ?_, accepted.coverage,
    traceAcyclic trace.core accepted.core.2.1, ?_, rfl⟩
  · exact elaborationSemanticSound env profile intern meaning valuation interpretation
      surface r.query accepted.query
  · intro detail member
    exact detailMeaningSound env surface r detail (accepted.annotations detail member)
  · exact classificationSound r.atomCount (premises r) r.query r.budget

end Weft.Grounding
