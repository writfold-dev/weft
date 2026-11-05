import Weft.Finite.Quantifiers
import Weft.Finite.Substitution
import Weft.Finite.CaptureBudgetExamples

namespace Weft.Finite.QuantifierExamples
open Weft.Language Weft.Finite.Syntax Weft.Finite.Sets Weft.Finite.Lowering

/-- No root path is present: the legacy field path is independently captured. -/
def oldPath : Path := ⟨17, ["size"]⟩
def reference : Value := .identity "object" "pinned" "qualified-binding-17"
def context : Context where
  legacy := {
    fieldTypes := fun p => if p = oldPath then some .natural else none
    fieldValues := fun p => if p = oldPath then some (.natural 7) else none }
  profile := ⟨fun _ => some [.natural]⟩
  named := fun i => if i = 0 then some ⟨reference, []⟩ else none
  sets := fun _ => none
  fieldType := fun ty selector =>
    if ty = .identity "object" "pinned" ∧ selector = ["label"] then some .text else none
  field := fun value selector =>
    if value = reference ∧ selector = ["label"] then some ⟨.text "pinned", []⟩ else none
  collectionType := fun ty selector =>
    if ty = .natural ∧ selector = ["self"] then some .natural else none
  collection := fun value selector =>
    if selector = ["self"] then
      match value with
      | .natural n => normalize .natural [⟨.natural n, []⟩] []
      | _ => none
    else none
  globalOrigins := fun _ => []

def emptyEnv : Env := fun _ => none
def noAtoms : GroundCall → Option Nat := fun _ => none
def valuation : Nat → Bool := fun _ => false
def trueExpr : Expr := .atom (.legacy (.boolean true))
def falseExpr : Expr := .atom (.legacy (.boolean false))
def natural (n : Nat) : SetExpr := .singleton (.literal (.natural n))
def run (budget : Nat) (expr : Expr) : Option Bool :=
  (lower budget context noAtoms emptyEnv expr).map (fun e => Weft.Logic.evaluate valuation e.formula)

/-- Explicit structural admission profile; valuation and byte limits are separate. -/
def workProfile : Nat := 512

theorem emptyForall : run 3 (.all (.empty .natural) trueExpr) = some true := by decide
theorem emptyExists : run 3 (.any (.empty .natural) trueExpr) = some false := by decide

/-- Inner zero shadows the outer name; outer one still denotes seven. -/
def nestedShadow : Expr :=
  .all (natural 7) (.any (natural 8)
    (.conj (.atom (.equal (.bound 0) (.literal (.natural 8))))
      (.atom (.equal (.bound 1) (.literal (.natural 7))))))

theorem nestedShadowSuccess : run workProfile nestedShadow = some true := by decide

/-- The domain sees outer zero, while its body sees inner zero and outer one. -/
def dependentDomain : Expr :=
  .all (.union .natural (natural 3) (natural 9))
    (.any (.select .natural (.bound 0) ["self"])
      (.atom (.equal (.bound 0) (.bound 1))))

theorem dependentDomainSuccess : run workProfile dependentDomain = some true := by decide

def capturedSeven : Member := ⟨.natural 7, []⟩
def openBody : Expr := .all (.singleton (.bound 0))
  (.atom (.equal (.bound 0) (.bound 1)))

theorem captureAvoidanceShape :
    openBody.substitute (instantiate capturedSeven) =
      .all (.singleton (.captured capturedSeven))
        (.atom (.equal (.bound 0) (.captured capturedSeven))) := rfl

theorem captureAvoidanceSuccess :
    run workProfile (openBody.substitute (instantiate capturedSeven)) = some true := by decide

theorem witnessPresent :
    run workProfile (.any (.union .natural (natural 1) (natural 7))
      (.atom (.equal (.bound 0) (.literal (.natural 7))))) = some true := by decide

theorem counterexamplePresent :
    run workProfile (.all (.union .natural (natural 1) (natural 7))
      (.atom (.equal (.bound 0) (.literal (.natural 7))))) = some false := by decide

theorem mixedDomainRefused :
    run workProfile (.all (.union .natural (natural 1) (.singleton (.literal (.text "bad"))))
      trueExpr) = none := by decide

theorem unknownFieldInEmptyBodyRefused :
    run workProfile (.all (.empty .natural)
      (.atom (.equal (.field (.bound 0) ["missing"]) (.literal (.natural 0))))) = none := by decide

theorem illTypedEmptyBodyRefused :
    run workProfile (.any (.empty .natural)
      (.atom (.equal (.literal (.natural 1)) (.literal (.text "one"))))) = none := by decide

theorem unboundEmptyBodyRefused :
    run workProfile (.all (.empty .natural)
      (.atom (.equal (.bound 1) (.literal (.natural 0))))) = none := by decide

theorem unavailableBranchRefused :
    run workProfile (.disj trueExpr (.atom (.predicate ⟨"profile", "missing"⟩
      [.literal (.natural 0)]))) = none := by decide

theorem budgetExhausted : run 10 (.all (natural 7) (.neg falseExpr)) = none := by decide

theorem exactBudgetSucceeds : run 11 (.all (natural 7) (.neg falseExpr)) = some true := by decide

theorem missingRootDoesNotBreakLegacyPath :
    run workProfile (.atom (.legacy (.conj (.equal (.field oldPath) (.literal (.natural 7)))
      (.neg (.notEqual (.field oldPath) (.literal (.natural 7))))))) = some true := by decide

theorem boundReferenceSelection :
    run workProfile (.all (.singleton (.named 0))
      (.atom (.equal (.field (.bound 0) ["label"]) (.literal (.text "pinned"))))) = some true := by decide

theorem globalPathSelection :
    run workProfile (.atom (.equal (.global oldPath) (.literal (.natural 7)))) = some true := by decide

def boundSetContext : Context :=
  { context with sets := fun i =>
      if i = 0 then normalize .natural [⟨.natural 7, []⟩] [] else none }

theorem namedSetSpreadSuccess :
    ((lower workProfile boundSetContext noAtoms emptyEnv
      (.all (.union .natural (.named .natural 0) (natural 8))
        (.atom (.equal (.bound 0) (.bound 0))))).map
      (fun e => Weft.Logic.evaluate valuation e.formula)) = some true := by decide

theorem missingSetSpreadRefused :
    run workProfile (.all (.union .natural (.named .natural 99) (natural 8)) trueExpr) = none := by decide

theorem extensionalSetEquality :
    run workProfile (.atom (.setEqual (.union .natural (natural 1) (natural 2))
      (.union .natural (natural 2) (natural 1)))) = some true := by decide

set_option maxRecDepth 8192 in
/-- Integrated CB-M01: a tiny distinct domain cannot hide 4096 raw duplicates. -/
theorem duplicateCaptureRefused :
    lower 64 CaptureBudgetExamples.context noAtoms emptyEnv
      (.all (.named .natural 0) trueExpr) = none := rfl

theorem emptySpreadCaptureRefused :
    lower 32 CaptureBudgetExamples.context noAtoms emptyEnv
      (.all (.named .natural 1) trueExpr) = none := rfl

/-- Actual usage, not a recomputed formula-node estimate. -/
theorem exactUsageRetained :
    (lower 11 context noAtoms emptyEnv (.all (natural 7) (.neg falseExpr))).map
      (fun result => (result.used, result.remaining, result.value.cost)) =
      some (11, 0, 3) := by decide

theorem unusedCapacityRetained :
    (lower 20 context noAtoms emptyEnv (.all (natural 7) (.neg falseExpr))).map
      (fun result => (result.used, result.remaining)) = some (11, 9) := by decide

/-- Dependent domain and sibling instances consume the same admission state. -/
theorem dependentAggregateRefused : run 56 dependentDomain = none := by decide

theorem dependentExactUsage :
    (lower 57 context noAtoms emptyEnv dependentDomain).map
      (fun result => (Weft.Logic.evaluate valuation result.formula, result.used, result.remaining)) =
      some (true, 57, 0) := by decide

/-- Empty membership does not make repeated spread provenance free. -/
theorem repeatedEmptySpreadExactUsage :
    (lower 16 CaptureBudgetExamples.context noAtoms emptyEnv
      (.all CaptureBudgetExamples.repeatedSpread trueExpr)).map
      (fun result => (Weft.Logic.evaluate valuation result.formula, result.used, result.remaining)) =
      some (true, 16, 0) := by decide

theorem repeatedEmptySpreadInsufficient :
    (lower 15 CaptureBudgetExamples.context noAtoms emptyEnv
      (.all CaptureBudgetExamples.repeatedSpread trueExpr)).isNone = true := by decide

/-- An actual successful run inhabits both premises of Q09's prefix-refusal
theorem. Its zero remainder cannot pay the next sibling's body-node charge. -/
def completedBooleanPrefix : WorkExpansion context noAtoms emptyEnv trueExpr 3 :=
  (expand 3 context noAtoms emptyEnv trueExpr 3).get (by decide)

theorem completedBooleanPrefixSuccess :
    expand 3 context noAtoms emptyEnv trueExpr 3 = some completedBooleanPrefix := rfl

theorem completedBooleanPrefixExhausted : completedBooleanPrefix.remaining < 1 := by decide

theorem prefixThenNodeRefused :
    lower 4 context noAtoms emptyEnv (.conj trueExpr falseExpr) = none :=
  Quantifiers.budgetRefusesPartial 3 context noAtoms emptyEnv trueExpr falseExpr
    completedBooleanPrefix completedBooleanPrefixSuccess completedBooleanPrefixExhausted

theorem bothBooleanSiblingsComplete :
    run 7 (.conj trueExpr falseExpr) = some false := by decide

def twoMemberDomain : SetExpr := .union .natural (natural 1) (natural 2)

/-- At total budget 25, the quantifier node leaves 24; materialization actually
succeeds and leaves 6. This is not a refusal before any useful work was done. -/
theorem domainPrefixSucceeds :
    ((CaptureBudget.evalSet context emptyEnv twoMemberDomain).run 24).map
      (fun result => (result.1.members.length, result.2)) = some (2, 6) := by decide

/-- The actual instance gatherer finishes the first member and leaves 2 units. -/
theorem firstMemberPrefixSucceeds :
    (gather (ctx := context) (intern := noAtoms) (env := emptyEnv) (body := trueExpr)
      (fun inner => expand 24 context noAtoms inner trueExpr) [⟨.natural 1, []⟩] 6).map
      (fun result => result.remaining) = some 2 := by decide

/-- The next member-list node and body node consume those 2 units. Capture then
has zero, even though the first quantified instance was already completed. -/
theorem laterMemberCaptureExhausted :
    (CaptureBudget.resolveAtom context (push ⟨.natural 2, []⟩ emptyEnv)
      (.legacy (.boolean true))).run 0 = none := rfl

theorem laterMemberGatherRefused :
    (gather (ctx := context) (intern := noAtoms) (env := emptyEnv) (body := trueExpr)
      (fun inner => expand 24 context noAtoms inner trueExpr) [⟨.natural 2, []⟩] 2).isNone =
      true := by decide

theorem partialQuantifierRefusedAfterPrefix :
    (lower 25 context noAtoms emptyEnv (.all twoMemberDomain trueExpr)).isNone = true := by decide

theorem completeQuantifierAfterPrefix :
    (lower 27 context noAtoms emptyEnv (.all twoMemberDomain trueExpr)).map
      (fun result => (Weft.Logic.evaluate valuation result.formula, result.used, result.remaining)) =
      some (true, 27, 0) := by decide

end Weft.Finite.QuantifierExamples
