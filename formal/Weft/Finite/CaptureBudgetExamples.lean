import Weft.Finite.CaptureBudget

namespace Weft.Finite.CaptureBudgetExamples
open Weft.Language Weft.Grounding Weft.Finite.Syntax Weft.Finite.Sets
namespace CB
export Weft.Finite.CaptureBudget (evalSet resolveTerm resolveAtom spend)
end CB

/-!
Audit/mutation matrix (the names below are executable theorem declarations):
* CB-M01 `duplicateHeavyRefused`: remove the raw-member scan, or charge distinct
  output cardinality instead of raw input.
* CB-M02 `largeOriginsRefused`, `emptySpreadOriginsRefused`: skip member origins
  or skip global origins when the membership list is empty.
* CB-M03 `repeatedSpreadAggregateRefused`: reset fuel between union branches.
* CB-M04 `repeatedSpreadPreservesOrigin`: drop empty-spread provenance.
* CB-M05 `missingInputRefused`, `mixedInputRefused`, `malformedOriginsRefused`:
  replace absent/invalid external records with a successful empty set.
* CB-M06 `nestedDependentAggregateRefused`: reset capture work per quantified
  instance; `nestedDependentValues`: evaluate a dependent domain outside its
  pushed lexical environment.
* CB-M07 `argumentAggregateRefused`, `fieldOriginsAggregateRefused`: reset work
  between arguments or discard a field base's origins.
* CB-M08 `normalizationOperationCharged`: remove normalization invocation charging
  while retaining the raw-input scan.
* CB-M09 `bodyAndCaptureShareBudget`: give body expansion a fresh capture budget.
* CB-M10 `duplicateRawCountRetained`: substitute distinct cardinality for the
  actually checked raw imported-payload count.

These are source assertions, not a claim that Lean or mutation qualification has
run. Import this module in the qualification root; audit the six CB01–CB06
certificate families in CaptureBudget and every assertion in this matrix.
-/

def origin (n : Nat) : Binding := ⟨⟨0, 0, 0, 0, 0, 0⟩, 0, n, 0, 0, 0⟩
def member (n : Nat) : Member := ⟨.natural n, []⟩
def emptyEnv : Env := fun _ => none

def context : Context where
  legacy := { fieldTypes := fun _ => none, fieldValues := fun _ => none }
  profile := ⟨fun _ => some [.natural, .natural]⟩
  named := fun _ => none
  sets := fun index => match index with
    | 0 => some ⟨.natural, List.replicate 4096 (member 7), [], none⟩
    | 1 => some ⟨.natural, [], (List.range 256).map origin, none⟩
    | 2 => some ⟨.natural, [], [origin 1], none⟩
    | 3 => some ⟨.natural, [member 7, ⟨.text "mixed", []⟩], [], none⟩
    | 4 => some ⟨.natural, [⟨.natural 7, [origin 1]⟩], [], none⟩
    | 5 => some ⟨.natural, List.replicate 8 (member 7), [], none⟩
    | _ => none
  fieldType := fun ty selector =>
    if ty = .natural ∧ selector = ["next"] then some .natural else none
  field := fun value selector =>
    if selector = ["next"] then some ⟨value, [origin 2]⟩ else none
  collectionType := fun ty selector =>
    if ty = .natural ∧ selector = ["self"] then some .natural else none
  collection := fun value selector =>
    if selector = ["self"] then some ⟨value.type, [⟨value, []⟩], [], none⟩ else none
  globalOrigins := fun _ => []

set_option maxRecDepth 8192 in
theorem duplicateHeavyRefused :
    (CB.evalSet context emptyEnv (.named .natural 0)).run 64 = none := by decide

theorem largeOriginsRefused :
    (CB.resolveTerm context emptyEnv
      (.captured ⟨.natural 7, (List.range 256).map origin⟩)).run 32 = none := by decide

theorem emptySpreadOriginsRefused :
    (CB.evalSet context emptyEnv (.named .natural 1)).run 32 = none := by decide

def repeatedSpread : SetExpr := .union .natural (.named .natural 2) (.named .natural 2)

theorem repeatedSpreadAggregateRefused :
    (CB.evalSet context emptyEnv repeatedSpread).run 6 = none := by decide

theorem repeatedSpreadPreservesOrigin :
    ((CB.evalSet context emptyEnv repeatedSpread).run 1000).map
      (fun result => result.1.origins) = some [origin 1] := by decide

theorem missingInputRefused :
    (CB.evalSet context emptyEnv (.named .natural 99)).run 1000 = none := by decide

theorem mixedInputRefused :
    (CB.evalSet context emptyEnv (.named .natural 3)).run 10000 = none := by decide

theorem malformedOriginsRefused :
    (CB.evalSet context emptyEnv (.named .natural 4)).run 1000 = none := by decide

theorem normalizationOperationCharged :
    (CB.evalSet context emptyEnv (.named .natural 5)).run 10 = none := by decide

theorem duplicatesNormalizeWithEnoughWork :
    ((CB.evalSet context emptyEnv (.named .natural 5)).run 12000).map
      (fun result => result.1.members.map Member.value) = some [.natural 7] := by decide

theorem argumentAggregateRefused :
    (CB.resolveAtom context emptyEnv
      (.predicate ⟨"profile", "pair"⟩ [.literal (.natural 3), .literal (.natural 9)])).run 4 =
      none := rfl

theorem fieldOriginsAggregateRefused :
    (CB.resolveTerm context emptyEnv
      (.field (.captured ⟨.natural 7, [origin 1]⟩) ["next"])).run 8 = none := by decide

theorem fieldOriginsPreserved :
    ((CB.resolveTerm context emptyEnv
      (.field (.captured ⟨.natural 7, [origin 1]⟩) ["next"])).run 20).map
      (fun result => result.1.origins) = some [origin 1, origin 2] := by decide

/-- The same unit spent by a body node cannot be spent again by capture. -/
theorem bodyAndCaptureShareBudget :
    ((CB.spend 1).after (fun _ =>
      CB.resolveTerm context emptyEnv (.literal (.natural 7)))).run 1 = none := by decide

/-- Concrete integration harness: two nested dependent domains, followed by an
atom whose two local indices must denote the same captured outer value. Each
body node is charged from the same residual budget. No unbounded evaluator is
used to construct this result. This tests capture composition, not Lowering. -/
def nestedInstance (budget : Nat) (outer : Member) : Option (Value × Nat) := do
  let (_, r0) ← (CB.spend 1).run budget
  let env := push outer emptyEnv
  let (inner, r1) ← (CB.evalSet context env (.select .natural (.bound 0) ["self"])).run r0
  let innerMember ← inner.members.head?
  let (_, r2) ← (CB.spend 1).run r1
  let innerEnv := push innerMember env
  let (deep, r3) ← (CB.evalSet context innerEnv (.select .natural (.bound 0) ["self"])).run r2
  let deepMember ← deep.members.head?
  let (_, r4) ← (CB.spend 1).run r3
  let (_, rest) ← (CB.resolveAtom context (push deepMember innerEnv)
    (.equal (.bound 0) (.bound 1))).run r4
  some (deepMember.value, rest)

def nestedInstances : Nat → List Member → Option (List Value × Nat)
  | budget, [] => some ([], budget)
  | budget, outer :: rest => do
      let (value, r1) ← nestedInstance budget outer
      let (values, r2) ← nestedInstances r1 rest
      some (value :: values, r2)

def nestedDependent (budget : Nat) : Option (List Value × Nat) := do
  let (_, r0) ← (CB.spend 1).run budget
  let (outer, r1) ← (CB.evalSet context emptyEnv
    (.union .natural (.singleton (.literal (.natural 3)))
      (.singleton (.literal (.natural 9))))).run r0
  nestedInstances r1 outer.members

theorem nestedDependentValues :
    (nestedDependent 10000).map Prod.fst = some [.natural 3, .natural 9] := by decide

theorem dependentInstanceFits :
    (nestedInstance 1000 (member 3)).map Prod.fst = some (.natural 3) := by decide

theorem nestedDependentAggregateRefused : nestedDependent 50 = none := by decide

/-- CB-M10: replacing raw input count by distinct output count changes 8 to 1. -/
theorem duplicateRawCountRetained :
    ((CB.evalSet context emptyEnv (.named .natural 5)).run 100).map
      (fun result => (result.1.rawOccurrences, result.1.members.length, result.1.capture)) =
      some (some 8, 1, some ⟨⟨.importedPayload, 8⟩, none⟩) := by decide

end Weft.Finite.CaptureBudgetExamples
