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
   ⟨"existential-complete-absence", !T.absenceReport.result && T.absenceReport.witnesses.isEmpty⟩]

def Case.json (item : Case) : Json := Json.mkObj
  [("id", .str item.id), ("passed", .bool item.passed),
   ("scope", .str "executed finite calculus case; no live Writfold or Rust refinement claim")]

end Weft.FiniteReference

def main : IO UInt32 := do
  let output ← IO.getStdout
  for item in Weft.FiniteReference.cases do
    output.putStrLn item.json.compress
  return if Weft.FiniteReference.cases.all (·.passed) then 0 else 1
