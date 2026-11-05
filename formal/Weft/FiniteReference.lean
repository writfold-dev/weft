import Lean
import Weft.Finite

namespace Weft.FiniteReference
open Lean Weft.Language Weft.Finite.Sets

structure Case where
  id : String
  passed : Bool

namespace S
export Weft.Finite.SetExamples
  (firstAlias secondAlias mergedAliases emptyCaptured firstOrigin secondOrigin
   malformedOrigins priorEnvironment)
end S

namespace Q
export Weft.Finite.QuantifierExamples
  (run workProfile trueExpr nestedShadow dependentDomain)
end Q

namespace T
export Weft.Finite.TraceExamples
  (universalReport refutingReport existentialReport absenceReport)
end T

namespace A
export Weft.Finite.Algebra.Examples
  (leftSet rightSet textSet natural boundContext evaluateWith unionTrace
   metadata originLeft originLeftAlias originRight originRightAlias)
end A

def cases : List Case :=
  [⟨"duplicate-values-retain-origins",
      decide (normalize .natural [S.firstAlias, S.secondAlias] [] = some S.mergedAliases)⟩,
   ⟨"raw-occurrences-not-distinct-count",
      decide (S.mergedAliases.rawOccurrences = some 2 ∧ S.mergedAliases.members.length = 1)⟩,
   ⟨"unavailable-member-is-not-deduplicated",
      (materialize .natural [.member (some S.firstAlias), .member none,
        .member (some S.secondAlias)] []).isNone⟩,
   ⟨"empty-spread-keeps-origins",
      decide (materialize .natural [.spread (some S.emptyCaptured)] [] = some S.emptyCaptured)⟩,
   ⟨"malformed-origin-closure-refused", (validate S.malformedOrigins).isNone⟩,
   ⟨"mixed-scalar-types-refused",
      (normalize .natural [⟨.natural 1, []⟩, ⟨.text "1", []⟩] []).isNone⟩,
   ⟨"nominal-kind-separation",
      (normalize (.identity "claim" "realm")
        [⟨.identity "claim" "realm" "same", []⟩,
         ⟨.identity "asset" "realm" "same", []⟩] []).isNone⟩,
   ⟨"duplicate-binding-refused",
      (Weft.Finite.Bindings.extend S.priorEnvironment "inputs" (some S.emptyCaptured)).isNone⟩,
   ⟨"empty-forall", decide (Q.run Q.workProfile (.all (.empty .natural) Q.trueExpr) = some true)⟩,
   ⟨"empty-exists", decide (Q.run Q.workProfile (.any (.empty .natural) Q.trueExpr) = some false)⟩,
   ⟨"hygienic-shadowing", decide (Q.run Q.workProfile Q.nestedShadow = some true)⟩,
   ⟨"dependent-finite-domains", decide (Q.run Q.workProfile Q.dependentDomain = some true)⟩,
   ⟨"zero-budget-refuses", (Q.run 0 Q.nestedShadow).isNone⟩,
   ⟨"universal-instance-coverage", T.universalReport.result &&
      decide (T.universalReport.domainSize = 2 ∧ T.universalReport.instantiatedCount = 2)⟩,
   ⟨"universal-counterexample-member", !T.refutingReport.result &&
      decide (T.refutingReport.counterexamples.map Member.value = [.natural 2])⟩,
   ⟨"existential-witness-member", T.existentialReport.result &&
      decide (T.existentialReport.witnesses.map Member.value = [.natural 1])⟩,
   ⟨"existential-complete-absence", !T.absenceReport.result && T.absenceReport.witnesses.isEmpty⟩,
   ⟨"algebra-union-membership-order",
      decide ((Weft.Finite.Algebra.union A.leftSet A.rightSet).map
        Weft.Finite.Algebra.values = some [.natural 1, .natural 2, .natural 3])⟩,
   ⟨"algebra-intersection-merges-origins",
      decide ((Weft.Finite.Algebra.intersection A.leftSet A.rightSet).map
        Weft.Finite.Algebra.values = some [.natural 2] ∧
        (Weft.Finite.Algebra.intersection A.leftSet A.rightSet).all (fun result =>
          result.members.any (fun m => m.value = .natural 2 ∧
            A.originLeft ∈ m.origins ∧ A.originRight ∈ m.origins)))⟩,
   ⟨"algebra-difference-retains-right-closure",
      decide ((Weft.Finite.Algebra.difference A.leftSet A.rightSet).map
        Weft.Finite.Algebra.values = some [.natural 1] ∧
        (Weft.Finite.Algebra.difference A.leftSet A.rightSet).all (fun result =>
          A.originRight ∈ result.origins ∧ A.originRightAlias ∈ result.origins))⟩,
   ⟨"algebra-typed-empty-results",
      decide ((Weft.Finite.Algebra.difference A.leftSet A.leftSet).all (fun result =>
        result.members = [] ∧ result.elementType = .natural) ∧
        (Weft.Finite.Algebra.intersection A.leftSet (Weft.Finite.Algebra.empty .natural)).all
          (fun result => result.members = [] ∧ result.elementType = .natural))⟩,
   ⟨"algebra-mixed-types-refused",
      decide ((Weft.Finite.Algebra.intersection A.leftSet A.textSet).isNone ∧
        (Weft.Finite.Algebra.difference A.leftSet A.textSet).isNone ∧
        (Weft.Finite.Algebra.subset A.leftSet A.textSet).isNone ∧
        (Weft.Finite.Algebra.member (.natural 1) A.textSet).isNone)⟩,
   ⟨"algebra-membership-hit-miss",
      decide (Weft.Finite.Algebra.member (.natural 2) A.leftSet = some true ∧
        Weft.Finite.Algebra.member (.natural 5) A.leftSet = some false)⟩,
   ⟨"algebra-subset-counterexample",
      decide (Weft.Finite.Algebra.subset
          ((Weft.Finite.Algebra.union A.leftSet A.rightSet).getD A.leftSet)
          A.leftSet = some false ∧
        Weft.Finite.Algebra.firstCounterexample
          ((Weft.Finite.Algebra.union A.leftSet A.rightSet).getD A.leftSet) A.leftSet =
          some ⟨.natural 3, [A.originRightAlias]⟩)⟩,
   ⟨"algebra-unavailable-operand-refused",
      (A.evaluateWith (.atom (.subset (.named .natural 99) (A.natural 1)))).isNone⟩,
   ⟨"algebra-shadowing-not-capture",
      decide (A.evaluateWith (.any
        (.difference .natural (.named .natural 0) (A.natural 2))
        (.any (A.natural 2) (.atom (.equal (.bound 0) (.bound 1))))) = some false)⟩,
   ⟨"algebra-zero-budget-refused",
      decide ((Weft.Finite.CaptureBudget.evalSet A.boundContext
          Weft.Finite.QuantifierExamples.emptyEnv
          (.intersection .natural (.named .natural 0) (A.natural 2))).run 0 = none)⟩]

def Case.json (item : Case) : Json := Json.mkObj
  [("id", .str item.id), ("passed", .bool item.passed),
   ("scope", .str "executed finite calculus case; no live Writfold or Rust refinement claim")]

end Weft.FiniteReference

def main : IO UInt32 := do
  let output ← IO.getStdout
  for item in Weft.FiniteReference.cases do
    output.putStrLn item.json.compress
  return if Weft.FiniteReference.cases.all (·.passed) then 0 else 1
