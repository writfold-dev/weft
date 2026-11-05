import Weft.Language.Semantics

namespace Weft.Language.Examples

/-!
Kernel-reducible positive/negative calibrations, not claims about raw parsing or
external data. Mutation targets: remove the field-type check (malformedField),
compare only identity bodies (identityKindRejected/identityNamespaceRejected),
check only zipped argument types (predicateArityRejected), short-circuit before
validating children (missingDisjunctRejected), or omit Interpretation.realizes
(mismatchedValuationChangesMeaning). Dropping exactCalls permits syntactically
different applications to alias even when their current truth happens to agree.
The mathematical theorem cannot validate a production parser; test source-to-AST
and source-to-IR correspondence separately against these constructor-level cases.
-/

def countPath : Path := ⟨0, ["count"]⟩
def malformedPath : Path := ⟨0, ["malformed"]⟩
def absentPath : Path := ⟨0, ["absent"]⟩
def unknownPath : Path := ⟨0, ["unregistered"]⟩

def env : Environment where
  fieldTypes path :=
    if path = countPath ∨ path = malformedPath ∨ path = absentPath then
      some .natural
    else none
  fieldValues path :=
    if path = countPath then some (.natural 7)
    else if path = malformedPath then some (.text "7")
    else if path = unknownPath then some (.natural 7)
    else none

def accepted : PredicateName := ⟨"pinned-profile", "accepted"⟩
def profile : Profile where
  signature name := if name = accepted then some [.natural] else none

def acceptedCall : GroundCall := ⟨accepted, [.natural 7]⟩
def internOnly (call : GroundCall) : Option Nat :=
  if call = acceptedCall then some 0 else none

def meaning (call : GroundCall) : Bool := decide (call.arguments = [.natural 7])
def valuation (_ : Nat) : Bool := true

theorem internOnlyCaptured (call : GroundCall) (index : Nat)
    (captured : internOnly call = some index) : call = acceptedCall := by
  by_cases same : call = acceptedCall
  · exact same
  · simp [internOnly, same] at captured

theorem interpretation : Interpretation internOnly meaning valuation := by
  constructor
  · intro a b index ha hb
    exact (internOnlyCaptured a index ha).trans (internOnlyCaptured b index hb).symm
  · intro call index captured
    have same := internOnlyCaptured call index captured
    subst call
    rfl

theorem successfulField : resolveTerm env (.field countPath) = some (.natural 7) := by
  decide

theorem successfulFieldType : Value.type (.natural 7) = Ty.natural :=
  termTypeSound env (.field countPath) (.natural 7) .natural (by decide) successfulField

theorem literalKinds :
    resolveTerm env (.literal (.boolean true)) = some (.boolean true) ∧
    resolveTerm env (.literal (.natural 18446744073709551616)) =
      some (.natural 18446744073709551616) ∧
    resolveTerm env (.literal (.text "seven")) = some (.text "seven") ∧
    resolveTerm env (.literal (.identity "claim" "realm-a" "same")) =
      some (.identity "claim" "realm-a" "same") := by
  decide

theorem malformedField : resolveTerm env (.field malformedPath) = none := by decide
theorem absentField : resolveTerm env (.field absentPath) = none := by decide
theorem unknownField : resolveTerm env (.field unknownPath) = none := by decide

theorem wrongComparisonType :
    elaborate env profile internOnly
      (.equal (.literal (.natural 7)) (.literal (.text "7"))) = none := by decide

theorem identityKindRejected :
    elaborate env profile internOnly
      (.equal (.literal (.identity "claim" "realm-a" "same"))
        (.literal (.identity "asset" "realm-a" "same"))) = none := by decide

theorem identityNamespaceRejected :
    elaborate env profile internOnly
      (.equal (.literal (.identity "claim" "realm-a" "same"))
        (.literal (.identity "claim" "realm-b" "same"))) = none := by decide

theorem identityTextRejected :
    elaborate env profile internOnly
      (.equal (.literal (.identity "claim" "realm-a" "same"))
        (.literal (.text "same"))) = none := by decide

theorem sameIdentityAccepted :
    elaborate env profile internOnly
      (.equal (.literal (.identity "claim" "realm-a" "same"))
        (.literal (.identity "claim" "realm-a" "same"))) =
      some (.literal true) := by decide

theorem differingIdentityBodies :
    elaborate env profile internOnly
      (.equal (.literal (.identity "claim" "realm-a" "first"))
        (.literal (.identity "claim" "realm-a" "second"))) =
      some (.literal false) := by decide

theorem predicateArityRejected :
    elaborate env profile internOnly (.predicate accepted []) = none ∧
    elaborate env profile internOnly
      (.predicate accepted [.literal (.natural 7), .literal (.natural 7)]) = none := by
  decide

theorem predicateTypeRejected :
    elaborate env profile internOnly
      (.predicate accepted [.literal (.text "7")]) = none := by decide

theorem unknownPredicateRejected :
    elaborate env profile internOnly
      (.predicate ⟨"pinned-profile", "missing"⟩ [.literal (.natural 7)]) = none := by decide

theorem uncapturedPredicateRejected :
    elaborate env profile internOnly
      (.predicate accepted [.literal (.natural 8)]) = none := by decide

theorem missingComparisonRejected :
    elaborate env profile internOnly
      (.equal (.field absentPath) (.literal (.natural 7))) = none := by decide

theorem malformedPredicateRejected :
    elaborate env profile internOnly (.predicate accepted [.field malformedPath]) = none := by
  decide

theorem missingDisjunctRejected :
    elaborate env profile internOnly
      (.disj (.boolean true) (.predicate accepted [.field absentPath])) = none ∧
    denote env profile meaning
      (.disj (.boolean true) (.predicate accepted [.field absentPath])) = none := by
  decide

def allConstructors : Surface :=
  .conj
    (.equal (.field countPath) (.literal (.natural 7)))
    (.disj
      (.neg (.notEqual (.literal (.text "same")) (.literal (.text "same"))))
      (.conj (.boolean true) (.predicate accepted [.field countPath])))

def allConstructorsIR : Weft.Logic.Formula :=
  .conj (.literal true)
    (.disj (.neg (.neg (.literal true))) (.conj (.literal true) (.atom 0)))

theorem successfulElaboration :
    elaborate env profile internOnly allConstructors = some allConstructorsIR := by decide

theorem successfulMeaning : denote env profile meaning allConstructors = some true := by decide

/-- Explicitly inhabits L02's external interpretation and success premises. -/
theorem successfulPreservation :
    denote env profile meaning allConstructors =
      some (Weft.Logic.evaluate valuation allConstructorsIR) :=
  elaborationSound env profile internOnly meaning valuation interpretation
    allConstructors allConstructorsIR successfulElaboration

theorem negativeComparisonMeaning :
    denote env profile meaning
      (.equal (.literal (.natural 7)) (.literal (.natural 8))) = some false ∧
    elaborate env profile internOnly
      (.equal (.literal (.natural 7)) (.literal (.natural 8))) =
      some (.literal false) := by decide

/-- Without the valuation agreement premise L02 is false, even with exact interning. -/
theorem mismatchedValuationChangesMeaning :
    denote env profile meaning (.predicate accepted [.field countPath]) = some true ∧
    elaborate env profile internOnly (.predicate accepted [.field countPath]) =
      some (.atom 0) ∧
    Weft.Logic.evaluate (fun _ => false) (.atom 0) = false := by decide

/-- The new relational conclusion is inhabited for all seven surface constructors. -/
theorem successfulIndependentPreservation :
    SurfaceMeaning env profile meaning allConstructors
      (Weft.Logic.evaluate valuation allConstructorsIR) :=
  elaborationSemanticSound env profile internOnly meaning valuation interpretation
    allConstructors allConstructorsIR successfulElaboration

/-- These witnesses use only the specification, not successful helper execution. -/
theorem independentFieldMeaning : TermMeaning env (.field countPath) (.natural 7) :=
  .field countPath (.natural 7) (by decide) (by decide)

theorem independentNaturalComparison :
    ComparisonMeaning env (.literal (.natural 7)) (.literal (.natural 8)) false :=
  ⟨_, _, .literal _, .literal _, rfl, by decide⟩

theorem independentTextComparison :
    ComparisonMeaning env (.literal (.text "a")) (.literal (.text "b")) false :=
  ⟨_, _, .literal _, .literal _, rfl, by decide⟩

theorem independentIdentityComparison :
    ComparisonMeaning env (.literal (.identity "claim" "realm-a" "first"))
      (.literal (.identity "claim" "realm-a" "second")) false :=
  ⟨_, _, .literal _, .literal _, rfl, by decide⟩

theorem independentCallMeaning :
    CallMeaning env profile accepted [.field countPath] acceptedCall :=
  ⟨rfl, .cons independentFieldMeaning .nil, by decide⟩

theorem independentPredicateMeaning :
    SurfaceMeaning env profile meaning (.predicate accepted [.field countPath]) true :=
  .predicate independentCallMeaning

theorem independentMalformedRejected :
    ¬ TermMeaning env (.field malformedPath) (.text "7") := by
  intro h
  cases h
  rename_i typed present
  have impossible : env.fieldTypes malformedPath ≠ some (Value.text "7").type := by decide
  exact impossible typed

theorem independentMissingRejected (value : Value) :
    ¬ TermMeaning env (.field absentPath) value := by
  intro h
  cases h
  rename_i typed present
  have absent : env.fieldValues absentPath = none := by decide
  rw [absent] at present
  cases present

theorem independentCrossTypeRejected (result : Bool) :
    ¬ ComparisonMeaning env (.literal (.natural 7)) (.literal (.text "7")) result := by
  rintro ⟨a, b, ha, hb, typed, truth⟩
  cases ha
  cases hb
  cases typed

theorem independentIdentityKindRejected (result : Bool) :
    ¬ ComparisonMeaning env (.literal (.identity "claim" "realm-a" "same"))
      (.literal (.identity "asset" "realm-a" "same")) result := by
  rintro ⟨a, b, ha, hb, typed, truth⟩
  cases ha
  cases hb
  have different : (Value.identity "claim" "realm-a" "same").type ≠
      (Value.identity "asset" "realm-a" "same").type := by decide
  exact different typed

theorem independentIdentityNamespaceRejected (result : Bool) :
    ¬ ComparisonMeaning env (.literal (.identity "claim" "realm-a" "same"))
      (.literal (.identity "claim" "realm-b" "same")) result := by
  rintro ⟨a, b, ha, hb, typed, truth⟩
  cases ha
  cases hb
  have different : (Value.identity "claim" "realm-a" "same").type ≠
      (Value.identity "claim" "realm-b" "same").type := by decide
  exact different typed

theorem independentArityRejected (call : GroundCall) :
    ¬ CallMeaning env profile accepted [] call := by
  rcases call with ⟨name, values⟩
  rintro ⟨predicate, arguments, signature⟩
  cases arguments
  have incompatible : profile.signature accepted ≠ some [] := by decide
  exact incompatible signature

theorem independentNaturalInequality :
    SurfaceMeaning env profile meaning
      (.notEqual (.literal (.natural 7)) (.literal (.natural 8))) true :=
  .notEqual independentNaturalComparison

theorem independentTextInequality :
    SurfaceMeaning env profile meaning
      (.notEqual (.literal (.text "a")) (.literal (.text "b"))) true :=
  .notEqual independentTextComparison

theorem independentIdentityInequality :
    SurfaceMeaning env profile meaning
      (.notEqual (.literal (.identity "claim" "realm-a" "first"))
        (.literal (.identity "claim" "realm-a" "second"))) true :=
  .notEqual independentIdentityComparison

/-- Every same-type literal pair, not only one selected example, inhabits != lowering. -/
theorem literalInequalityLowering (a b : Value) (typed : a.type = b.type) :
    ∃ result, ComparisonMeaning env (.literal a) (.literal b) result ∧
      Weft.Logic.Formula.neg (.literal (decide (a = b))) = .neg (.literal result) ∧
      Weft.Logic.evaluate valuation (.neg (.literal (decide (a = b)))) = !result :=
  inequalitySugarSound env profile internOnly valuation (.literal a) (.literal b)
    (.neg (.literal (decide (a = b))))
    (by simp [elaborate, compareTerms, resolveTerm, inferTerm, rawTerm, typed])

theorem naturalInequalityLowering :
    ∃ result, ComparisonMeaning env (.literal (.natural 7)) (.literal (.natural 8)) result ∧
      Weft.Logic.Formula.neg (.literal false) = .neg (.literal result) ∧
      Weft.Logic.evaluate valuation (.neg (.literal false)) = !result :=
  literalInequalityLowering (.natural 7) (.natural 8) rfl

theorem textInequalityLowering :
    ∃ result, ComparisonMeaning env (.literal (.text "a")) (.literal (.text "b")) result ∧
      Weft.Logic.Formula.neg (.literal false) = .neg (.literal result) ∧
      Weft.Logic.evaluate valuation (.neg (.literal false)) = !result :=
  literalInequalityLowering (.text "a") (.text "b") rfl

theorem identityInequalityLowering :
    ∃ result, ComparisonMeaning env
      (.literal (.identity "claim" "realm-a" "first"))
      (.literal (.identity "claim" "realm-a" "second")) result ∧
      Weft.Logic.Formula.neg (.literal false) = .neg (.literal result) ∧
      Weft.Logic.evaluate valuation (.neg (.literal false)) = !result :=
  literalInequalityLowering (.identity "claim" "realm-a" "first")
    (.identity "claim" "realm-a" "second") rfl

/-- Exactness is used to realize an arbitrary replacement, not merely today's truth. -/
theorem arbitraryMeaningCoverage (replacement : GroundCall → Bool) :
    ∃ replacementValuation, Interpretation internOnly replacement replacementValuation :=
  interpretation.reinterpret replacement

def otherCall : GroundCall := ⟨accepted, [.natural 8]⟩

theorem collidingInternerRejectedEvenWhenValuesAgree :
    ¬ Interpretation (fun _ => some 0) (fun _ => true) (fun _ => true) := by
  intro bad
  have same := bad.exactCalls acceptedCall otherCall 0 rfl rfl
  have distinct : acceptedCall ≠ otherCall := by decide
  exact distinct same

theorem collidingInternerCannotRealizeDisagreement :
    ¬ ∃ candidate : Nat → Bool,
      ∀ call index, (some 0 : Option Nat) = some index → candidate index = meaning call := by
  rintro ⟨candidate, realizes⟩
  have positive : candidate 0 = true := realizes acceptedCall 0 rfl
  have negative : candidate 0 = false := realizes otherCall 0 rfl
  rw [positive] at negative
  cases negative

theorem independentValuationMismatchRejected :
    ¬ Interpretation internOnly meaning (fun _ => false) := by
  intro bad
  have impossible : false = true := bad.realizes acceptedCall 0 (by decide)
  cases impossible

end Weft.Language.Examples
