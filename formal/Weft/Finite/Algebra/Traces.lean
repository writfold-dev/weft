import Weft.Finite.Algebra.Lowering
import Weft.Finite.TraceContext
import Weft.Finite.Bindings

/-!
# Algebra traces and capture accounting

A06: operation and comparison traces expose the actual operands, typed
membership, complete dependency closure (including removed members and empty
results), deterministic first-left subset counterexamples and honest
normalization input counts. Binding failure remains atomic.
-/

namespace Weft.Finite.Algebra

open Weft.Language Weft.Logic Weft.Finite.Syntax Weft.Finite.Sets
open Weft.Finite.Semantics Weft.Finite.Lowering Weft.Finite.Traces Weft.Finite.Bindings

inductive TraceKind where
  | union | intersection | difference
  deriving DecidableEq, Repr

structure OperationTrace where
  kind : TraceKind
  left : CapturedSet
  right : CapturedSet
  result : CapturedSet
  normalizationInput : Nat
  dependencies : List Weft.Grounding.Binding
  context : ContextView
  deriving DecidableEq, Repr

def operationOutcome : TraceKind → CapturedSet → CapturedSet → Option CapturedSet
  | .union, left, right => union left right
  | .intersection, left, right => intersection left right
  | .difference, left, right => difference left right

/-- The exact member list supplied to this result's normalization event. -/
def operationInput : TraceKind → CapturedSet → CapturedSet → List Member
  | .union, left, right => unionMembers left right
  | .intersection, left, right => intersectionMembers left right
  | .difference, left, right => differenceMembers left right

def makeOperationTrace (kind : TraceKind) (left right : CapturedSet)
    (metadata : TraceContext) : Option OperationTrace :=
  (operationOutcome kind left right).map fun result =>
    { kind := kind, left := left, right := right, result := result,
      normalizationInput := (operationInput kind left right).length,
      dependencies := (left.origins ++ right.origins) ++ contextOrigins metadata,
      context := contextView metadata }

def checkOperationTrace (kind : TraceKind) (left right : CapturedSet)
    (metadata : TraceContext) (trace : OperationTrace) : Bool :=
  decide (makeOperationTrace kind left right metadata = some trace)

/-- Membership characterization per operator, shared by the trace theorem. -/
def operationExpectation (kind : TraceKind) (left right : CapturedSet) (value : Value) : Prop :=
  match kind with
  | .union => value ∈ values left ∨ value ∈ values right
  | .intersection => value ∈ values left ∧ value ∈ values right
  | .difference => value ∈ values left ∧ value ∉ values right

theorem operationOutcomeMembership (kind : TraceKind) (left right result : CapturedSet)
    (success : operationOutcome kind left right = some result) (value : Value) :
    value ∈ values result ↔ operationExpectation kind left right value := by
  cases kind with
  | union => exact unionMembership success value
  | intersection => exact intersectionMembership success value
  | difference => exact differenceMembership success value

theorem operationOutcomeNormalized (kind : TraceKind) (left right result : CapturedSet)
    (success : operationOutcome kind left right = some result) :
    Sets.normalize left.elementType (operationInput kind left right)
      (left.origins ++ right.origins) = some result := by
  cases kind with
  | union => exact unionNormalized success (unionTypedResult success).1
  | intersection => exact intersectionNormalized success (intersectionTypedResult success).1
  | difference => exact differenceNormalized success (differenceTypedResult success).1

/-- A06: a checked operation trace is bound to the actual operands, the real
algebraic result with its exact membership, the complete dependency closure
including both whole operands — even for an empty result — and the untouched
report context. -/
theorem operationTraceFaithful (kind : TraceKind) (left right : CapturedSet)
    (metadata : TraceContext) (trace : OperationTrace)
    (checked : checkOperationTrace kind left right metadata trace = true) :
    operationOutcome kind left right = some trace.result ∧ trace.kind = kind ∧
      trace.left = left ∧ trace.right = right ∧
      (∀ value, value ∈ values trace.result ↔
        operationExpectation kind left right value) ∧
      trace.dependencies = (left.origins ++ right.origins) ++ contextOrigins metadata ∧
      trace.context = contextView metadata := by
  have accepted : makeOperationTrace kind left right metadata = some trace :=
    of_decide_eq_true checked
  cases made : operationOutcome kind left right with
  | none =>
      simp only [makeOperationTrace, made, Option.map_none] at accepted
      exact Option.noConfusion accepted
  | some result =>
      have built : makeOperationTrace kind left right metadata =
          some { kind := kind, left := left, right := right, result := result,
                 normalizationInput := (operationInput kind left right).length,
                 dependencies := (left.origins ++ right.origins) ++ contextOrigins metadata,
                 context := contextView metadata } := by
        simp only [makeOperationTrace, made, Option.map_some]
      rw [built] at accepted
      have fields := Option.some.inj accepted
      cases fields
      dsimp only
      refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
      exact fun value => operationOutcomeMembership kind left right result made value

/-- A06: capture accounting is honest — the recorded normalization input count
is exactly the count of the actual normalization event; for
intersection/difference it equals result cardinality on well-formed operands,
while union counts both normalized operand lists before cross-operand
deduplication. -/
theorem captureAccountingSound (kind : TraceKind) (left right : CapturedSet)
    (metadata : TraceContext) (trace : OperationTrace)
    (checked : checkOperationTrace kind left right metadata trace = true)
    (wellFormed : WellFormed left) :
    trace.result.rawOccurrences = some trace.normalizationInput ∧
      (kind = .intersection ∨ kind = .difference →
          trace.normalizationInput = trace.result.members.length) ∧
      (kind = .union → trace.normalizationInput =
        left.members.length + right.members.length) := by
  have accepted : makeOperationTrace kind left right metadata = some trace :=
    of_decide_eq_true checked
  cases made : operationOutcome kind left right with
  | none =>
      simp only [makeOperationTrace, made, Option.map_none] at accepted
      exact Option.noConfusion accepted
  | some result =>
      have built : makeOperationTrace kind left right metadata =
          some { kind := kind, left := left, right := right, result := result,
                 normalizationInput := (operationInput kind left right).length,
                 dependencies := (left.origins ++ right.origins) ++ contextOrigins metadata,
                 context := contextView metadata } := by
        simp only [makeOperationTrace, made, Option.map_some]
      rw [built] at accepted
      have fields := Option.some.inj accepted
      cases fields
      dsimp only
      have normalized : Sets.normalize left.elementType (operationInput kind left right)
          (left.origins ++ right.origins) = some result :=
        operationOutcomeNormalized kind left right result made
      have filteredNodup (predicate : Member → Bool) :
          ((left.members.filter predicate).map Member.value).Nodup :=
        List.Nodup.sublist (List.filter_sublist.map Member.value) wellFormed.2
      have representation := firstOccurrenceRepresentation left.elementType
        (operationInput kind left right) (left.origins ++ right.origins) result normalized
      have resultLength : result.members.length =
          (unique ((operationInput kind left right).map Member.value)).length := by
        simpa only [List.length_map] using congrArg List.length representation
      refine ⟨(Sets.normalizeRawOccurrences _ _ _ _ normalized).2, ?_, ?_⟩
      · intro algebraic
        rcases algebraic with rfl | rfl
        · have inputValues : (intersectionMembers left right).map Member.value =
              (left.members.filter (fun m => decide (m.value ∈ values right))).map Member.value := by
            simp only [intersectionMembers, List.map_map, Function.comp_def]
          show (operationInput TraceKind.intersection left right).length =
              result.members.length
          rw [resultLength, unique_of_nodup _
            (by simp only [operationInput]; rw [inputValues]; exact filteredNodup _),
            List.length_map]
        · show (operationInput TraceKind.difference left right).length =
              result.members.length
          rw [resultLength]
          simp only [operationInput, differenceMembers]
          rw [unique_of_nodup _
            (filteredNodup (fun m => decide (¬ m.value ∈ values right))),
            List.length_map]
      · intro isUnion
        subst isUnion
        show (operationInput TraceKind.union left right).length =
            left.members.length + right.members.length
        simp only [operationInput, unionMembers, List.length_append]

structure MembershipTrace where
  probe : Value
  set : CapturedSet
  outcome : Bool
  dependencies : List Weft.Grounding.Binding
  context : ContextView
  deriving DecidableEq, Repr

def makeMembershipTrace (value : Value) (set : CapturedSet)
    (metadata : TraceContext) : Option MembershipTrace :=
  (member value set).map fun outcome =>
    { probe := value, set := set, outcome := outcome,
      dependencies := set.origins ++ contextOrigins metadata,
      context := contextView metadata }

def checkMembershipTrace (value : Value) (set : CapturedSet) (metadata : TraceContext)
    (trace : MembershipTrace) : Bool :=
  decide (makeMembershipTrace value set metadata = some trace)

theorem membershipTraceFaithful (value : Value) (set : CapturedSet) (metadata : TraceContext)
    (trace : MembershipTrace)
    (checked : checkMembershipTrace value set metadata trace = true) :
    member value set = some trace.outcome ∧ trace.probe = value ∧ trace.set = set ∧
      (trace.outcome = true ↔ value ∈ values set) ∧
      trace.dependencies = set.origins ++ contextOrigins metadata ∧
      trace.context = contextView metadata := by
  have accepted : makeMembershipTrace value set metadata = some trace :=
    of_decide_eq_true checked
  by_cases typed : value.type = set.elementType
  · simp only [makeMembershipTrace, member, if_pos typed, Option.map_some] at accepted
    have fields := Option.some.inj accepted
    cases fields
    dsimp only
    refine ⟨by simp only [member, if_pos typed], rfl, rfl, ?_, rfl, rfl⟩
    exact decide_eq_true_iff (p := value ∈ values set)
  · simp only [makeMembershipTrace, member, if_neg typed, Option.bind_none] at accepted
    exact Option.noConfusion accepted

structure SubsetTrace where
  left : CapturedSet
  right : CapturedSet
  outcome : Bool
  counterexample : Option Member
  dependencies : List Weft.Grounding.Binding
  context : ContextView
  deriving DecidableEq, Repr

def makeSubsetTrace (left right : CapturedSet) (metadata : TraceContext) :
    Option SubsetTrace :=
  (subset left right).map fun outcome =>
    { left := left, right := right, outcome := outcome,
      counterexample := if outcome then none else firstCounterexample left right,
      dependencies := (left.origins ++ right.origins) ++ contextOrigins metadata,
      context := contextView metadata }

def checkSubsetTrace (left right : CapturedSet) (metadata : TraceContext)
    (trace : SubsetTrace) : Bool :=
  decide (makeSubsetTrace left right metadata = some trace)

/-- A06: a checked subset trace carries the true algebraic verdict, and a
false verdict's counterexample is exactly the deterministic first-left member
absent from the right operand — never a symbolic model-relative witness. -/
theorem subsetTraceFaithful (left right : CapturedSet) (metadata : TraceContext)
    (trace : SubsetTrace)
    (checked : checkSubsetTrace left right metadata trace = true) :
    subset left right = some trace.outcome ∧ trace.left = left ∧ trace.right = right ∧
      (trace.outcome = true ↔ ∀ m ∈ left.members, m.value ∈ values right) ∧
      (trace.outcome = false → ∃ witness, trace.counterexample = some witness ∧
        witness ∈ left.members ∧ witness.value ∉ values right) ∧
      trace.dependencies = (left.origins ++ right.origins) ++ contextOrigins metadata ∧
      trace.context = contextView metadata := by
  have accepted : makeSubsetTrace left right metadata = some trace :=
    of_decide_eq_true checked
  by_cases same : left.elementType = right.elementType
  · simp only [makeSubsetTrace, subset, if_pos same, Option.map_some] at accepted
    have fields := Option.some.inj accepted
    cases fields
    dsimp only
    have subsetDef : subset left right =
        some (left.members.all (fun m => decide (m.value ∈ values right))) := by
      simp only [subset, if_pos same]
    refine ⟨by rw [subsetDef], rfl, rfl,
      (subsetPredicateSound _ (by rw [subsetDef])).2, ?_, rfl, rfl⟩
    intro negative
    obtain ⟨witness, found, witnessIn, witnessAbsent⟩ :=
      subsetCounterexample _ (by rw [subsetDef]) negative
    exact ⟨witness, by simp only [negative, Bool.false_eq_true, if_false]; exact found,
      witnessIn, witnessAbsent⟩
  · simp only [makeSubsetTrace, subset, if_neg same, Option.bind_none] at accepted
    exact Option.noConfusion accepted

/-- A06 primary: operation, membership and subset traces are faithful, and an
algebra initializer that fails installs nothing while preserving every earlier
binding atomically. -/
theorem traceFaithful :
    (∀ (kind : TraceKind) (left right : CapturedSet) (metadata : TraceContext)
        (trace : OperationTrace), checkOperationTrace kind left right metadata trace = true →
        operationOutcome kind left right = some trace.result ∧
          (∀ value, value ∈ values trace.result ↔ operationExpectation kind left right value) ∧
          trace.dependencies = (left.origins ++ right.origins) ++ contextOrigins metadata ∧
          trace.context = contextView metadata) ∧
    (∀ (value : Value) (set : CapturedSet) (metadata : TraceContext)
        (trace : MembershipTrace), checkMembershipTrace value set metadata trace = true →
        member value set = some trace.outcome ∧
          (trace.outcome = true ↔ value ∈ values set) ∧
          trace.dependencies = set.origins ++ contextOrigins metadata) ∧
    (∀ (left right : CapturedSet) (metadata : TraceContext)
        (trace : SubsetTrace), checkSubsetTrace left right metadata trace = true →
        subset left right = some trace.outcome ∧
          (trace.outcome = false → ∃ witness, trace.counterexample = some witness ∧
            witness ∈ left.members ∧ witness.value ∉ values right)) :=
  ⟨fun kind left right metadata trace checked =>
      let faithful := operationTraceFaithful kind left right metadata trace checked
      ⟨faithful.1, faithful.2.2.2.2.1, faithful.2.2.2.2.2.1, faithful.2.2.2.2.2.2⟩,
    fun value set metadata trace checked =>
      let faithful := membershipTraceFaithful value set metadata trace checked
      ⟨faithful.1, faithful.2.2.2.1, faithful.2.2.2.2.1⟩,
    fun left right metadata trace checked =>
      let faithful := subsetTraceFaithful left right metadata trace checked
      ⟨faithful.1, faithful.2.2.2.2.1⟩⟩

/-- A06: a failed algebraic binding does not install a value or publish fake
zero cardinality; prior successful bindings stay faithful. -/
theorem bindingFailureAtomic (env : Bindings.Environment) (name : String)
    (kind : TraceKind) (left right : CapturedSet)
    (failure : operationOutcome kind left right = none) :
    declare env name (operationOutcome kind left right) = ⟨env, false⟩ ∧
      ∀ priorName value, lookup env priorName = some value →
        lookup (declare env name (operationOutcome kind left right)).environment priorName
          = some value := by
  rw [failure] at *
  refine ⟨failureAtomic env name none (missingInitializerFails env name), ?_⟩
  intro priorName value prior
  exact declarationPreservesPrior env name none priorName value prior

end Weft.Finite.Algebra
