import Weft.Finite.Algebra.Conservation
import Weft.Finite.QuantifierExamples

/-!
# Inhabited algebra examples

Non-vacuous positive and negative vectors for A01-A08. These abstract bindings
are proof fixtures, not invented Writfold captures. Every refusal is an actual
refusal, and every origin identity is retained and checkable.
-/

namespace Weft.Finite.Algebra.Examples

open Weft.Language Weft.Grounding Weft.Finite.Sets Weft.Finite.Syntax Weft.Finite.Algebra
open Weft.Finite.CaptureBudget Weft.Finite.Lowering Weft.Finite.QuantifierExamples

def scope : Scope := ⟨1, 2, 3, 4, 5, 6⟩
def originLeft : Binding := ⟨scope, 1, 7, 8, 9, 10⟩
def originLeftAlias : Binding := ⟨scope, 1, 7, 11, 9, 10⟩
def originRight : Binding := ⟨scope, 2, 12, 13, 14, 15⟩
def originRightAlias : Binding := ⟨scope, 2, 12, 16, 14, 15⟩

/-- `{1, 2}` where 2 carries two distinct source origins. -/
def leftSet : CapturedSet :=
  ⟨.natural, [⟨.natural 1, [originLeft]⟩,
              ⟨.natural 2, [originLeft, originLeftAlias]⟩],
    [originLeft, originLeftAlias], some ⟨⟨.materialization, 3⟩, none⟩⟩

/-- `{2, 3}` with its own origins for 2. -/
def rightSet : CapturedSet :=
  ⟨.natural, [⟨.natural 2, [originRight]⟩, ⟨.natural 3, [originRightAlias]⟩],
    [originRight, originRightAlias], some ⟨⟨.materialization, 2⟩, none⟩⟩

def textSet : CapturedSet :=
  ⟨.text, [⟨.text "1", []⟩], [], some ⟨⟨.materialization, 1⟩, none⟩⟩

def natural (n : Nat) : SetExpr := .singleton (.literal (Value.natural n))

/-- A helper context binding one captured set at index 0. -/
def boundContext : Context :=
  { QuantifierExamples.context with
    sets := fun index => if index = 0 then some leftSet else none }

def evaluateWith (expr : Expr) : Option Bool :=
  (lower workProfile boundContext noAtoms emptyEnv expr).map
    (fun expansion => Weft.Logic.evaluate valuation expansion.formula)

/-! A01: exact memberships, duplicates, deterministic order. -/

theorem unionValuesAndCount :
    (union leftSet rightSet).map values =
      some [.natural 1, .natural 2, .natural 3] ∧
      (union leftSet rightSet).map CapturedSet.rawOccurrences = some (some 4) := by decide

theorem unionRetainsEveryOperandOrigin :
    (union leftSet rightSet).all (fun result =>
      originLeft ∈ result.origins ∧ originLeftAlias ∈ result.origins ∧
        originRight ∈ result.origins ∧ originRightAlias ∈ result.origins) := by decide

theorem intersectionValuesAndCount :
    (intersection leftSet rightSet).map values = some [.natural 2] ∧
      (intersection leftSet rightSet).map CapturedSet.rawOccurrences = some (some 1) := by decide

/-- The surviving 2 keeps its left aliases and gains the matching right
origin: contributing origins from both operands. -/
theorem intersectionMergesBothOrigins :
    (intersection leftSet rightSet).all (fun result =>
      result.members.any (fun m =>
        m.value = .natural 2 ∧
          originLeft ∈ m.origins ∧ originLeftAlias ∈ m.origins ∧
            originRight ∈ m.origins)) := by decide

theorem intersectionRetainsRemovedMemberEvidence :
    (intersection leftSet rightSet).all (fun result =>
      originRightAlias ∈ result.origins ∧ originLeft ∈ result.origins) := by decide

theorem differenceValuesAndCount :
    (difference leftSet rightSet).map values = some [.natural 1] ∧
      (difference leftSet rightSet).map CapturedSet.rawOccurrences = some (some 1) := by decide

/-- The right operand's whole closure survives a difference, including the
origins of the removed member 2. -/
theorem differenceRetainsRightClosure :
    (difference leftSet rightSet).all (fun result =>
      originRight ∈ result.origins ∧ originRightAlias ∈ result.origins ∧
        result.members.all (fun m => m.value ≠ .natural 2)) := by decide

theorem selfDifferenceTypedEmpty :
    (difference leftSet leftSet).all (fun result =>
      result.members = [] ∧ result.elementType = .natural ∧
        result.rawOccurrences = some 0) := by decide

theorem emptyIntersectionTyped :
    (intersection leftSet (empty .natural)).all (fun result =>
      result.members = [] ∧ result.elementType = .natural) := by decide

/-- Union agrees with spread materialization on membership and stable order. -/
theorem unionAgreesWithSpread :
    (materialize .natural [.spread (some leftSet), .spread (some rightSet)] []).map values =
      some [.natural 1, .natural 2, .natural 3] ∧
      (union leftSet rightSet).map values = some [.natural 1, .natural 2, .natural 3] := by decide

/-! A02: typed empties and refused mismatches. -/

theorem mixedOperandTypesRefused :
    (intersection leftSet textSet).isNone ∧ (difference leftSet textSet).isNone ∧
      (union leftSet textSet).isNone ∧ (subset leftSet textSet).isNone ∧
      (Sets.equal leftSet textSet).isNone := by decide

theorem wrongTypedMembershipRefused : member (.natural 1) textSet = none := by decide

/-! A03: predicates and counterexamples. -/

theorem membershipHitAndMiss :
    member (.natural 2) leftSet = some true ∧
      member (.natural 5) leftSet = some false ∧
      member (.text "2") leftSet = none := by decide

theorem subsetTrueFalseReflexive :
    subset leftSet leftSet = some true ∧
      subset leftSet ((union leftSet rightSet).getD leftSet) = some true ∧
      subset ((union leftSet rightSet).getD leftSet) leftSet = some false := by decide

theorem firstLeftCounterexampleDeterministic :
    firstCounterexample ((union leftSet rightSet).getD leftSet) leftSet =
      some ⟨.natural 3, [originRightAlias]⟩ := by decide

/-- Unavailable operands have no Boolean denotation. -/
theorem unavailableDomainRefuses :
    Syntax.evalSet QuantifierExamples.context QuantifierExamples.emptyEnv
        (.intersection .natural (.named .natural 99) (natural 1)) = none ∧
      Syntax.evalSet QuantifierExamples.context QuantifierExamples.emptyEnv
        (.difference .natural (natural 1) (.named .natural 99)) = none := by decide

theorem unavailableSubsetRefuses :
    (QuantifierExamples.run workProfile
      (.atom (.subset (.named .natural 99) (natural 1)))).isNone := by decide

theorem membershipAtomEvaluated :
    evaluateWith (.atom (.member (.literal (.natural 2)) (.named .natural 0))) = some true ∧
      evaluateWith (.atom (.member (.literal (.natural 5)) (.named .natural 0))) =
        some false := by decide

theorem subsetAtomEvaluated :
    evaluateWith (.atom (.subset (.named .natural 0)
        (.union .natural (natural 1) (natural 2)))) = some true ∧
      evaluateWith (.atom (.subset (.union .natural (natural 1) (natural 3))
        (.named .natural 0))) = some false := by decide

theorem differenceDomainQuantified :
    evaluateWith (.all (.difference .natural (.named .natural 0)
        (.union .natural (natural 1) (natural 2)))
      (.atom (.equal (.bound 0) (.literal (.natural 1))))) = some true := by decide

/-- Quantifying over the removed member's value fails: it is absent from the
derived domain. -/
theorem differenceDomainExcludesRemoved :
    evaluateWith (.any (.difference .natural (.named .natural 0)
        (.union .natural (natural 1) (natural 2)))
      (.atom (.equal (.bound 0) (.literal (.natural 2))))) = some false := by decide

/-! A05: substitution through the new constructors, including shadowing. -/

theorem algebraSubstitutionShape :
    (SetExpr.intersection .natural (.singleton (.bound 0)) (natural 2)).substitute
        (instantiate ⟨.natural 1, []⟩) =
      .intersection .natural (.singleton (.captured ⟨.natural 1, []⟩)) (natural 2) ∧
    (SetExpr.difference .natural (natural 2) (.singleton (.bound 0))).substitute
        (instantiate ⟨.natural 1, []⟩) =
      .difference .natural (natural 2) (.singleton (.captured ⟨.natural 1, []⟩)) ∧
    (Atom.subset (.singleton (.bound 0)) (natural 2)).substitute
        (instantiate ⟨.natural 1, []⟩) =
      .subset (.singleton (.captured ⟨.natural 1, []⟩)) (natural 2) := by decide

/-- An unbound domain binder refuses the whole quantifier: algebra never turns
an unavailable operand into an empty domain. -/
theorem unboundDomainBinderRefuses :
    (lower workProfile boundContext noAtoms emptyEnv
        (.all (.difference .natural (.named .natural 0) (.singleton (.bound 0)))
          (.atom (.equal (.bound 0) (.literal (.natural 1)))))).isNone := by decide

/-- The inner binder shadows the outer member: the body's `bound 0` is the
inner domain member (2), not the outer difference member (1), so the equality
fails without capture. -/
theorem shadowingNotCapture :
    evaluateWith (.any (.difference .natural (.named .natural 0) (natural 2))
      (.any (natural 2) (.atom (.equal (.bound 0) (.bound 1))))) = some false := by decide

/-! A06/A07: traces, accounting and budget refusal. -/

def metadata : Weft.Finite.Traces.TraceContext :=
  ⟨none, .declaredOnly, [originLeft], [], []⟩

def unionTrace : OperationTrace :=
  { kind := .union, left := leftSet, right := rightSet,
    result := (union leftSet rightSet).getD leftSet,
    normalizationInput := (unionMembers leftSet rightSet).length,
    dependencies := (leftSet.origins ++ rightSet.origins) ++
      Weft.Finite.Traces.contextOrigins metadata,
    context := Weft.Finite.Traces.contextView metadata }

theorem unionTraceChecked :
    checkOperationTrace .union leftSet rightSet metadata unionTrace = true := by decide

theorem subsetTraceChecked :
    checkSubsetTrace ((union leftSet rightSet).getD leftSet) leftSet metadata
        ((makeSubsetTrace ((union leftSet rightSet).getD leftSet) leftSet metadata).getD
          { left := (union leftSet rightSet).getD leftSet, right := leftSet, outcome := false,
            counterexample := none, dependencies := [],
            context := Weft.Finite.Traces.contextView metadata }) = true ∧
      ((makeSubsetTrace ((union leftSet rightSet).getD leftSet) leftSet metadata).getD
          { left := (union leftSet rightSet).getD leftSet, right := leftSet, outcome := false,
            counterexample := none, dependencies := [],
            context := Weft.Finite.Traces.contextView metadata }).counterexample =
        some ⟨.natural 3, [originRightAlias]⟩ := by decide

theorem zeroBudgetRefusesAlgebra :
    (CaptureBudget.evalSet boundContext emptyEnv
        (.intersection .natural (.named .natural 0) (natural 2))).run 0 = none ∧
      (CaptureBudget.resolveAtom boundContext emptyEnv
        (.subset (.named .natural 0) (natural 2))).run 0 = none := by
  constructor
  · rfl
  · rfl

/-- Real operand-scan cost is charged: a budget below the left operand's
complete admission (2 members with 1 and 2 origins, plus 2 set origins)
cannot reach any verdict. -/
theorem operandScanCostRefuses : (algebraSubset leftSet rightSet).run 6 = none := by decide

theorem enoughBudgetSucceeds : ((algebraSubset leftSet rightSet).run 14).isSome := by decide

/-! A08: local results stay non-grounded and non-authoritative. -/

theorem algebraContextNotAuthoritative :
    (Weft.Finite.Traces.contextView metadata).effectAuthority = false ∧
      (Weft.Finite.Traces.contextView metadata).writfoldGrounded = false ∧
      (Weft.Finite.Traces.contextView metadata).captured.inventory = .declaredOnly := by decide

end Weft.Finite.Algebra.Examples
