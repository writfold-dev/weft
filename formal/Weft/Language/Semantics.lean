import Weft.Language.Elaboration

namespace Weft.Language

/-!
# Independent typed source meaning

These relations specify exact resolved-path lookup, nominal value equality,
profile signatures (including arity), and strict Boolean composition. None calls
resolveTerm, compareTerms, checkCall, denote, elaborate, or an IR evaluator.
The operational source denotation remains a useful bridge, not the definition
of semantic correctness. Profiles, environments and ground-call truth are
explicit mathematical inputs; external truth and raw parsing remain outside
this boundary. Naturals are unbounded, identities compare kind/realm/body.

`internerCoverage` is a mathematical existence theorem for partial collision-free
interning. Only captured calls must be realized; uncaptured calls need not have
an atom. Its proof uses classical choice to select a preimage for each occupied
index, and classical proposition decidability. No runtime is extracted from it.
Other proofs are constructive apart from Lean's ordinary equality/quotient
foundations; exact transitive axioms are determined by the integrated audit.
-/

inductive TermMeaning (env : Environment) : Term → Value → Prop where
  | literal (value : Value) : TermMeaning env (.literal value) value
  | field (path : Path) (value : Value)
      (typed : env.fieldTypes path = some value.type)
      (present : env.fieldValues path = some value) :
      TermMeaning env (.field path) value

def ComparisonMeaning (env : Environment) (left right : Term) (result : Bool) : Prop :=
  ∃ leftValue rightValue,
    TermMeaning env left leftValue ∧ TermMeaning env right rightValue ∧
    leftValue.type = rightValue.type ∧ result = decide (leftValue = rightValue)

inductive ArgumentsMeaning (env : Environment) : List Term → List Value → Prop where
  | nil : ArgumentsMeaning env [] []
  | cons {term : Term} {terms : List Term} {value : Value} {values : List Value}
      (first : TermMeaning env term value) (rest : ArgumentsMeaning env terms values) :
      ArgumentsMeaning env (term :: terms) (value :: values)

structure CallMeaning (env : Environment) (profile : Profile)
    (name : PredicateName) (arguments : List Term) (call : GroundCall) : Prop where
  predicate : call.predicate = name
  argumentsMeaning : ArgumentsMeaning env arguments call.arguments
  signature : profile.signature name = some (call.arguments.map Value.type)

inductive SurfaceMeaning (env : Environment) (profile : Profile)
    (meaning : GroundCall → Bool) : Surface → Bool → Prop where
  | boolean (value : Bool) : SurfaceMeaning env profile meaning (.boolean value) value
  | equal {left right : Term} {result : Bool}
      (comparison : ComparisonMeaning env left right result) :
      SurfaceMeaning env profile meaning (.equal left right) result
  | notEqual {left right : Term} {result : Bool}
      (comparison : ComparisonMeaning env left right result) :
      SurfaceMeaning env profile meaning (.notEqual left right) (!result)
  | predicate {name : PredicateName} {arguments : List Term} {call : GroundCall}
      (application : CallMeaning env profile name arguments call) :
      SurfaceMeaning env profile meaning (.predicate name arguments) (meaning call)
  | neg {inner : Surface} {result : Bool}
      (child : SurfaceMeaning env profile meaning inner result) :
      SurfaceMeaning env profile meaning (.neg inner) (!result)
  | conj {left right : Surface} {a b : Bool}
      (first : SurfaceMeaning env profile meaning left a)
      (second : SurfaceMeaning env profile meaning right b) :
      SurfaceMeaning env profile meaning (.conj left right) (a && b)
  | disj {left right : Surface} {a b : Bool}
      (first : SurfaceMeaning env profile meaning left a)
      (second : SurfaceMeaning env profile meaning right b) :
      SurfaceMeaning env profile meaning (.disj left right) (a || b)

theorem termMeaningSound (env : Environment) (term : Term) (value : Value)
    (success : resolveTerm env term = some value) : TermMeaning env term value := by
  obtain ⟨typed, present⟩ := termEvaluationFacts env term value success
  cases term with
  | literal actual =>
      have same : actual = value := Option.some.inj present
      subst value
      exact .literal actual
  | field path => exact .field path value typed present

theorem comparisonMeaningSound (env : Environment) (left right : Term) (result : Bool)
    (success : compareTerms env left right = some result) :
    ComparisonMeaning env left right result := by
  cases hl : resolveTerm env left with
  | none => simp [compareTerms, hl] at success
  | some a =>
      cases hr : resolveTerm env right with
      | none => simp [compareTerms, hl, hr] at success
      | some b =>
          by_cases typed : a.type = b.type
          · have truth : decide (a = b) = result := by
              simpa [compareTerms, hl, hr, typed] using success
            exact ⟨a, b, termMeaningSound env left a hl,
              termMeaningSound env right b hr, typed, truth.symm⟩
          · simp [compareTerms, hl, hr, typed] at success

theorem argumentsMeaningSound (env : Environment) (terms : List Term) (values : List Value)
    (success : resolveArguments env terms = some values) :
    ArgumentsMeaning env terms values := by
  induction terms generalizing values with
  | nil =>
      have same : ([] : List Value) = values := by simpa [resolveArguments] using success
      subst values
      exact .nil
  | cons term terms ih =>
      cases ht : resolveTerm env term with
      | none => simp [resolveArguments, ht] at success
      | some value =>
          cases hs : resolveArguments env terms with
          | none => simp [resolveArguments, ht, hs] at success
          | some rest =>
              have same : value :: rest = values := by
                simpa [resolveArguments, ht, hs] using success
              subst values
              exact .cons (termMeaningSound env term value ht) (ih rest hs)

theorem callMeaningSound (env : Environment) (profile : Profile)
    (name : PredicateName) (arguments : List Term) (call : GroundCall)
    (success : checkCall env profile name arguments = some call) :
    CallMeaning env profile name arguments call := by
  cases hp : profile.signature name with
  | none => simp [checkCall, hp] at success
  | some signature =>
      cases ha : resolveArguments env arguments with
      | none => simp [checkCall, hp, ha] at success
      | some values =>
          by_cases typed : values.map Value.type = signature
          · have same : (⟨name, values⟩ : GroundCall) = call := by
              simpa [checkCall, hp, ha, typed] using success
            subst call
            exact ⟨rfl, argumentsMeaningSound env arguments values ha,
              by simpa only [typed] using hp⟩
          · simp [checkCall, hp, ha, typed] at success

theorem denotationSound (env : Environment) (profile : Profile)
    (meaning : GroundCall → Bool) (surface : Surface) (result : Bool)
    (success : denote env profile meaning surface = some result) :
    SurfaceMeaning env profile meaning surface result := by
  induction surface generalizing result with
  | boolean value =>
      have same : value = result := by simpa [denote] using success
      subst result
      exact .boolean value
  | equal left right =>
      exact .equal (comparisonMeaningSound env left right result success)
  | notEqual left right =>
      cases hc : compareTerms env left right with
      | none => simp [denote, hc] at success
      | some value =>
          have same : (!value) = result := by simpa [denote, hc] using success
          subst result
          exact .notEqual (comparisonMeaningSound env left right value hc)
  | predicate name arguments =>
      cases hc : checkCall env profile name arguments with
      | none => simp [denote, hc] at success
      | some call =>
          have same : meaning call = result := by simpa [denote, hc] using success
          subst result
          exact .predicate (callMeaningSound env profile name arguments call hc)
  | neg inner ih =>
      cases hc : denote env profile meaning inner with
      | none => simp [denote, hc] at success
      | some value =>
          have same : (!value) = result := by simpa [denote, hc] using success
          subst result
          exact .neg (ih value hc)
  | conj left right ihLeft ihRight =>
      cases hl : denote env profile meaning left with
      | none => simp [denote, hl, combine] at success
      | some a =>
          cases hr : denote env profile meaning right with
          | none => simp [denote, hl, hr, combine] at success
          | some b =>
              have same : (a && b) = result := by
                simpa [denote, hl, hr, combine] using success
              subst result
              exact .conj (ihLeft a hl) (ihRight b hr)
  | disj left right ihLeft ihRight =>
      cases hl : denote env profile meaning left with
      | none => simp [denote, hl, combine] at success
      | some a =>
          cases hr : denote env profile meaning right with
          | none => simp [denote, hl, hr, combine] at success
          | some b =>
              have same : (a || b) = result := by
                simpa [denote, hl, hr, combine] using success
              subst result
              exact .disj (ihLeft a hl) (ihRight b hr)

/-- The existing operational L02 is a used bridge to independently specified meaning. -/
theorem elaborationSemanticSound (env : Environment) (profile : Profile)
    (intern : GroundCall → Option Nat) (meaning : GroundCall → Bool)
    (valuation : Nat → Bool) (interpretation : Interpretation intern meaning valuation)
    (surface : Surface) (formula : Weft.Logic.Formula)
    (success : elaborate env profile intern surface = some formula) :
    SurfaceMeaning env profile meaning surface (Weft.Logic.evaluate valuation formula) :=
  denotationSound env profile meaning surface (Weft.Logic.evaluate valuation formula)
    (elaborationSound env profile intern meaning valuation interpretation surface formula success)

/-- Every supplied meaning is realizable on all captured calls, with exact identity. -/
theorem internerCoverage (intern : GroundCall → Option Nat)
    (meaning : GroundCall → Bool)
    (exactCalls : ∀ a b index, intern a = some index → intern b = some index → a = b) :
    ∃ valuation, Interpretation intern meaning valuation := by
  classical
  let valuation : Nat → Bool := fun index =>
    if occupied : ∃ call, intern call = some index then
      meaning (Classical.choose occupied)
    else false
  refine ⟨valuation, exactCalls, ?_⟩
  intro call index captured
  have occupied : ∃ call, intern call = some index := ⟨call, captured⟩
  have same : Classical.choose occupied = call :=
    exactCalls _ call index (Classical.choose_spec occupied) captured
  simp only [valuation, dif_pos occupied, same]

/-- Exactness, unlike current truth agreement, licenses every reinterpretation. -/
theorem Interpretation.reinterpret {intern : GroundCall → Option Nat}
    {originalMeaning : GroundCall → Bool} {originalValuation : Nat → Bool}
    (interpretation : Interpretation intern originalMeaning originalValuation)
    (meaning : GroundCall → Bool) : ∃ valuation, Interpretation intern meaning valuation :=
  internerCoverage intern meaning interpretation.exactCalls

/-- Actual typed != lowering, not propositional equivalence sugar. The witnesses
include exact nominal types and value equality for every supported value kind. -/
theorem inequalitySugarSound (env : Environment) (profile : Profile)
    (intern : GroundCall → Option Nat) (valuation : Nat → Bool)
    (left right : Term) (formula : Weft.Logic.Formula)
    (success : elaborate env profile intern (.notEqual left right) = some formula) :
    ∃ result, ComparisonMeaning env left right result ∧
      formula = .neg (.literal result) ∧
      Weft.Logic.evaluate valuation formula = !result := by
  cases hc : compareTerms env left right with
  | none => simp [elaborate, hc] at success
  | some result =>
      have same : Weft.Logic.Formula.neg (.literal result) = formula := by
        simpa [elaborate, hc] using success
      subst formula
      exact ⟨result, comparisonMeaningSound env left right result hc, rfl, rfl⟩

end Weft.Language
