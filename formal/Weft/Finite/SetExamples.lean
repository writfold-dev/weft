import Weft.Finite.Bindings
import Weft.Finite.Sets.Properties

namespace Weft.Finite.SetExamples

open Weft.Language Weft.Grounding Sets Bindings

/-! Executable positive and adverse examples for Q01–Q04. These abstract bindings
are proof fixtures, not invented Writfold captures or owner identity certificates.
Every success explicitly supplies a complete finite capture; refusal never means
an empty successful domain or a false predicate. -/

 def scope : Scope := ⟨1, 2, 3, 4, 5, 6⟩
 def firstOrigin : Binding := ⟨scope, 1, 7, 8, 9, 10⟩
 def secondOrigin : Binding := ⟨scope, 1, 7, 11, 9, 10⟩
 def emptySourceOrigin : Binding := ⟨scope, 2, 12, 13, 14, 15⟩

 def firstAlias : Member := ⟨.natural 7, [firstOrigin]⟩
 def secondAlias : Member := ⟨.natural 7, [secondOrigin]⟩
 def mergedAliases : CapturedSet :=
  ⟨.natural, [⟨.natural 7, [firstOrigin, secondOrigin]⟩], [firstOrigin, secondOrigin],
    some ⟨⟨.materialization, 2⟩, none⟩⟩

/-- Equal resolved values coalesce, but distinct revisions remain dependencies. -/
theorem duplicateAliases : normalize .natural [firstAlias, secondAlias] [] =
    some mergedAliases := by decide

 theorem duplicateAliasOrigins : firstOrigin ∈ mergedAliases.origins ∧
    secondOrigin ∈ mergedAliases.origins ∧ firstOrigin ≠ secondOrigin := by decide

 theorem duplicateAliasMemberOrigins : mergedAliases.members =
    [⟨.natural 7, [firstOrigin, secondOrigin]⟩] := rfl

 theorem firstOccurrenceOrder : normalize .natural
    [⟨.natural 2, []⟩, ⟨.natural 1, []⟩, ⟨.natural 2, []⟩] [] =
    some ⟨.natural, [⟨.natural 2, []⟩, ⟨.natural 1, []⟩], [],
      some ⟨⟨.materialization, 3⟩, none⟩⟩ := by decide

/-- Re-normalization preserves values and origins, but records a new local input
count: one already-distinct member, not the two original aliases. -/
theorem duplicateNormalizationIdempotent :
    (normalize mergedAliases.elementType mergedAliases.members mergedAliases.origins).map
      (fun set => (set.members, set.origins)) =
      some (mergedAliases.members, mergedAliases.origins) := by decide

theorem renormalizationHasNewCount :
    (normalize mergedAliases.elementType mergedAliases.members mergedAliases.origins).map
      CapturedSet.rawOccurrences = some (some 1) ∧ mergedAliases.rawOccurrences = some 2 := by decide

def emptyCaptured : CapturedSet :=
  ⟨.natural, [], [emptySourceOrigin], some ⟨⟨.materialization, 0⟩, none⟩⟩

 theorem emptySpreadOrigins : materialize .natural [.spread (some emptyCaptured)] [] =
    some emptyCaptured := by decide

 theorem repeatedEmptySpreadOrigins : materialize .natural
    [.spread (some emptyCaptured), .spread (some emptyCaptured)] [] =
    some emptyCaptured := by decide

 theorem mixedLiteralAndSpread : materialize .natural
    [.member (some firstAlias), .spread (some emptyCaptured), .member (some secondAlias)] [] =
    some ⟨.natural, [⟨.natural 7, [firstOrigin, secondOrigin]⟩],
      [firstOrigin, emptySourceOrigin, secondOrigin], some ⟨⟨.materialization, 2⟩, none⟩⟩ := by decide

def diamondLeft : CapturedSet := ⟨.natural, [firstAlias], [firstOrigin, secondOrigin], none⟩
def diamondRight : CapturedSet := ⟨.natural, [firstAlias], [firstOrigin, emptySourceOrigin], none⟩

theorem diamondSpreadOrigins : materialize .natural
    [.spread (some diamondLeft), .spread (some diamondRight)] [] =
    some ⟨.natural, [firstAlias], [firstOrigin, secondOrigin, emptySourceOrigin],
      some ⟨⟨.materialization, 2⟩, none⟩⟩ := by decide

def malformedOrigins : CapturedSet := ⟨.natural, [firstAlias], [], none⟩
def malformedType : CapturedSet := ⟨.text, [firstAlias], [firstOrigin], none⟩

 theorem missingOriginRejected : validate malformedOrigins = none := by decide
 theorem wrongMemberTypeRejected : validate malformedType = none := by decide

 theorem malformedSpreadRejected : materialize .natural
    [.member (some secondAlias), .spread (some malformedOrigins)] [] = none := by decide

 theorem unavailableLateMemberRejected : materialize .natural
    [.member (some firstAlias), .member none] [] = none := by decide

 theorem unavailableSpreadRejected : materialize .natural
    [.member (some firstAlias), .spread none] [] = none := by decide

 theorem unavailableAliasNotDeduplicatedAway : materialize .natural
    [.member (some firstAlias), .member none, .member (some secondAlias)] [] = none := by decide

 theorem wrongEmptySpreadTypeRejected : materialize .text
    [.spread (some emptyCaptured)] [] = none := by decide

 theorem mixedMemberTypesRejected : normalize .natural
    [⟨.natural 1, []⟩, ⟨.text "1", []⟩] [] = none := by decide

 theorem sameBytesDifferentKinds : normalize (.identity "citation" "realm")
    [⟨.identity "citation" "realm" "bytes", []⟩,
      ⟨.identity "asset" "realm" "bytes", []⟩] [] = none := by decide

 theorem sameBytesDifferentRealms : normalize (.identity "citation" "first")
    [⟨.identity "citation" "first" "bytes", []⟩,
      ⟨.identity "citation" "second" "bytes", []⟩] [] = none := by decide

 theorem extensionalOrderIgnored : Sets.compare
    ⟨.natural, [⟨.natural 1, []⟩, ⟨.natural 2, []⟩], [], none⟩
    ⟨.natural, [⟨.natural 2, []⟩, ⟨.natural 1, []⟩], [], none⟩ = some true := by decide

 theorem extensionalOriginsIgnored : Sets.compare
    ⟨.natural, [⟨.natural 7, [firstOrigin]⟩], [firstOrigin], none⟩
    ⟨.natural, [⟨.natural 7, [secondOrigin]⟩], [secondOrigin], none⟩ = some true := by decide

 theorem extensionalDifferentMembers : Sets.compare
    ⟨.natural, [⟨.natural 1, []⟩], [], none⟩
    ⟨.natural, [⟨.natural 2, []⟩], [], none⟩ = some false := by decide

 theorem extensionalMalformedRefused : Sets.compare malformedOrigins mergedAliases = none := by decide

 theorem emptyNominalKindsStillDiffer : Sets.compare
    ⟨.identity "citation" "realm", [], [], none⟩
    ⟨.identity "asset" "realm", [], [], none⟩ = none := by decide

def installedAliases : CapturedSet :=
  { mergedAliases with capture := some (importedStatistics mergedAliases) }

def installedEmpty : CapturedSet :=
  { emptyCaptured with capture := some (importedStatistics emptyCaptured) }

def priorEnvironment : Bindings.Environment := [("inputs", installedAliases)]

 theorem firstBindingInstalled : extend [] "inputs" (some mergedAliases) =
    some priorEnvironment := by decide

 theorem duplicateBindingRejected : extend priorEnvironment "inputs" (some emptyCaptured) =
    none := by decide

 theorem duplicateBindingAtomic : declare priorEnvironment "inputs" (some emptyCaptured) =
    ⟨priorEnvironment, false⟩ := by decide

 theorem missingInitializerRejected : extend priorEnvironment "later" none = none := by decide

 theorem malformedInitializerRejected : extend priorEnvironment "later" (some malformedType) =
    none := by decide

 theorem appendPreservesDeclarationOrder : extend priorEnvironment "later" (some emptyCaptured) =
    some [("inputs", installedAliases), ("later", installedEmpty)] := by decide

 theorem priorLookupPreserved : lookup
    [("inputs", installedAliases), ("later", installedEmpty)] "inputs" = some installedAliases := by decide

 theorem forwardReferenceRejected : declarePrior priorEnvironment "later" "future" =
    ⟨priorEnvironment, false⟩ := by decide

 theorem selfReferenceRejected : declarePrior priorEnvironment "later" "later" =
    ⟨priorEnvironment, false⟩ := by decide

 theorem priorSetInitializer : declarePrior priorEnvironment "copy" "inputs" =
    ⟨[("inputs", installedAliases), ("copy", installedAliases)], true⟩ := by decide

/-- The binding observes one validated payload member and retains the original
two-input materialization as imported provenance. No evidence timestamp changes. -/
theorem bindingPreservesSourceCount :
    installedAliases.rawOccurrences = some 1 ∧
      installedAliases.capture = some
        ⟨⟨.importedPayload, 1⟩, some ⟨.materialization, 2⟩⟩ ∧
      installedAliases.origins = mergedAliases.origins := by decide

theorem extensionalCountsIgnored :
    Sets.compare mergedAliases { mergedAliases with capture := none } = some true := by decide

/-- This materialization receives two normalized spread members, not four
transitive source aliases. Both distinct source-origin identities survive. -/
theorem localCountNotTransitiveText :
    (materialize .natural [.spread (some mergedAliases), .spread (some mergedAliases)] []).map
      (fun set => (set.rawOccurrences, set.members.length, set.origins)) =
      some (some 2, 1, [firstOrigin, secondOrigin]) := by decide

end Weft.Finite.SetExamples
