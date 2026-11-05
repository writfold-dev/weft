import Weft.Finite.Algebra.Predicates

/-!
# Complete operand closure

A04: successful algebra and predicates retain the complete operation-level
dependency closure of both operands — including eliminated members and the
entire right operand of a difference, even for empty results — while per-member
origin attribution stays faithful. Either operand's failure prevents success,
and successful complete inputs have a successful semantic result.
-/

namespace Weft.Finite.Algebra

open Weft.Language Weft.Grounding Weft.Finite.Syntax Weft.Finite.Sets Weft.Finite.Semantics

section OperationClosure

variable {left right result : CapturedSet}

theorem unionClosure (success : union left right = some result) (origin : Binding)
    (fromLeft : origin ∈ left.origins) : origin ∈ result.origins := by
  by_cases same : left.elementType = right.elementType
  · exact (normalizeOrigins _ _ _ _ (unionNormalized success same) origin).mpr
      (Or.inl (List.mem_append_left _ fromLeft))
  · simp [union, same] at success

theorem unionRightClosure (success : union left right = some result) (origin : Binding)
    (fromRight : origin ∈ right.origins) : origin ∈ result.origins := by
  by_cases same : left.elementType = right.elementType
  · exact (normalizeOrigins _ _ _ _ (unionNormalized success same) origin).mpr
      (Or.inl (List.mem_append_right _ fromRight))
  · simp [union, same] at success

theorem intersectionClosure (success : intersection left right = some result)
    (origin : Binding) (fromEither : origin ∈ left.origins ∨ origin ∈ right.origins) :
    origin ∈ result.origins := by
  by_cases same : left.elementType = right.elementType
  · exact (normalizeOrigins _ _ _ _ (intersectionNormalized success same) origin).mpr
      (Or.inl (match fromEither with
        | Or.inl h => List.mem_append_left _ h
        | Or.inr h => List.mem_append_right _ h))
  · simp [intersection, same] at success

theorem differenceClosure (success : difference left right = some result)
    (origin : Binding) (fromEither : origin ∈ left.origins ∨ origin ∈ right.origins) :
    origin ∈ result.origins := by
  by_cases same : left.elementType = right.elementType
  · exact (normalizeOrigins _ _ _ _ (differenceNormalized success same) origin).mpr
      (Or.inl (match fromEither with
        | Or.inl h => List.mem_append_left _ h
        | Or.inr h => List.mem_append_right _ h))
  · simp [difference, same] at success

/-- Intersection retains, for each surviving identity, the contributing left
alias origins of the operand pair. -/
theorem intersectionLeftAliasOrigins (success : intersection left right = some result)
    (value : Value) (inRight : value ∈ values right)
    (leftAlias : Member) (leftIn : leftAlias ∈ left.members) (leftEq : leftAlias.value = value)
    (origin : Binding) (originIn : origin ∈ leftAlias.origins) :
    ∃ survivor ∈ result.members, survivor.value = value ∧ origin ∈ survivor.origins := by
  by_cases same : left.elementType = right.elementType
  · have inputIn : ⟨leftAlias.value, unique (leftAlias.origins ++
          (rightContributors leftAlias.value right).flatMap Member.origins)⟩ ∈
        intersectionMembers left right := by
      refine List.mem_map.mpr ⟨leftAlias, ?_, rfl⟩
      refine List.mem_filter.mpr ⟨leftIn, ?_⟩
      simpa only [decide_eq_true_eq, leftEq] using inRight
    have survived : value ∈ values result :=
      (intersectionMembership success value).mpr
        ⟨List.mem_map.mpr ⟨leftAlias, leftIn, leftEq⟩, inRight⟩
    obtain ⟨survivor, survivorIn, survivorEq⟩ := List.mem_map.mp survived
    refine ⟨survivor, survivorIn, survivorEq, ?_⟩
    exact (normalizeMemberOrigins _ _ _ _ (intersectionNormalized success same) survivor
      survivorIn origin).mpr
      ⟨⟨leftAlias.value, unique (leftAlias.origins ++
          (rightContributors leftAlias.value right).flatMap Member.origins)⟩, inputIn, by
        refine ⟨by rw [leftEq, survivorEq], ?_⟩
        exact (Sets.mem_unique origin _).mpr (List.mem_append_left _ originIn)⟩
  · simp [intersection, same] at success

/-- Intersection retains the contributing right alias origins for surviving
identities: matching right members' origins are merged into the survivor. -/
theorem intersectionRightAliasOrigins (success : intersection left right = some result)
    (value : Value) (inLeft : value ∈ values left)
    (rightAlias : Member) (rightIn : rightAlias ∈ right.members)
    (rightEq : rightAlias.value = value)
    (origin : Binding) (originIn : origin ∈ rightAlias.origins) :
    ∃ survivor ∈ result.members, survivor.value = value ∧ origin ∈ survivor.origins := by
  by_cases same : left.elementType = right.elementType
  · obtain ⟨leftAlias, leftIn, leftEq⟩ := List.mem_map.mp inLeft
    have inputIn : ⟨leftAlias.value, unique (leftAlias.origins ++
          (rightContributors leftAlias.value right).flatMap Member.origins)⟩ ∈
        intersectionMembers left right := by
      refine List.mem_map.mpr ⟨leftAlias, ?_, rfl⟩
      refine List.mem_filter.mpr ⟨leftIn, ?_⟩
      simpa only [decide_eq_true_eq, leftEq] using
        (List.mem_map.mpr ⟨rightAlias, rightIn, rightEq⟩)
    have survived : value ∈ values result :=
      (intersectionMembership success value).mpr
        ⟨inLeft, List.mem_map.mpr ⟨rightAlias, rightIn, rightEq⟩⟩
    obtain ⟨survivor, survivorIn, survivorEq⟩ := List.mem_map.mp survived
    refine ⟨survivor, survivorIn, survivorEq, ?_⟩
    have rightContributorMembership : rightAlias ∈ rightContributors leftAlias.value right := by
      simp only [rightContributors]
      refine List.mem_filter.mpr ⟨rightIn, ?_⟩
      simp [leftEq, rightEq]
    refine (normalizeMemberOrigins _ _ _ _ (intersectionNormalized success same) survivor
      survivorIn origin).mpr
      ⟨⟨leftAlias.value, unique (leftAlias.origins ++
          (rightContributors leftAlias.value right).flatMap Member.origins)⟩, inputIn, by
        refine ⟨by rw [leftEq, survivorEq], ?_⟩
        refine (Sets.mem_unique origin _).mpr (List.mem_append_right _ ?_)
        exact List.mem_flatMap.mpr ⟨rightAlias, rightContributorMembership, originIn⟩⟩
  · simp [intersection, same] at success

/-- Eliminated members and their origins stay reachable as operand evidence:
with closed operands, a removed member's origins remain in the result's
operation-level closure even though the member itself is gone. -/
theorem removedMemberEvidenceRetained (success : difference left right = some result)
    (closedLeft : Closed left) (removed : Member) (removedIn : removed ∈ left.members)
    (origin : Binding) (viaRemoved : origin ∈ removed.origins) :
    origin ∈ result.origins := by
  have inMemberOrigins : origin ∈ memberOrigins left.members :=
    List.mem_flatMap.mpr ⟨removed, removedIn, viaRemoved⟩
  exact differenceClosure success origin (Or.inl (closedLeft origin inMemberOrigins))

/-- A difference never relabels the right operand's provenance onto a
surviving value: survivors come from the left, removed values from the right. -/
theorem differenceSurvivorsAreLeft (success : difference left right = some result)
    (survivor : Member) (survivorIn : survivor ∈ result.members)
    (rightAlias : Member) (rightIn : rightAlias ∈ right.members) :
    survivor.value ≠ rightAlias.value := by
  have survived := (differenceMembership success survivor.value).mp
    (List.mem_map.mpr ⟨survivor, survivorIn, rfl⟩)
  intro sameValue
  exact survived.2 (List.mem_map.mpr ⟨rightAlias, rightIn, sameValue.symm⟩)

/-- A04 primary: successful operations preserve complete operand closure —
both operands' whole origin lists survive in the result even when the result is
empty, per-member attribution stays faithful, and eliminated members stay
reachable as operand evidence. -/
theorem operandClosurePreserved (unionResult intersectionResult differenceResult : CapturedSet)
    (unionSuccess : union left right = some unionResult)
    (intersectionSuccess : intersection left right = some intersectionResult)
    (differenceSuccess : difference left right = some differenceResult) :
    (∀ origin ∈ left.origins, origin ∈ unionResult.origins ∧
        origin ∈ intersectionResult.origins ∧ origin ∈ differenceResult.origins) ∧
      (∀ origin ∈ right.origins, origin ∈ unionResult.origins ∧
        origin ∈ intersectionResult.origins ∧ origin ∈ differenceResult.origins) ∧
      (∀ value, value ∈ values left ∧ value ∈ values right →
        ∃ survivor ∈ intersectionResult.members, survivor.value = value) ∧
      (∀ survivor ∈ differenceResult.members, ∀ rightAlias ∈ right.members,
        survivor.value ≠ rightAlias.value) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro origin inLeft
    exact ⟨unionClosure unionSuccess origin inLeft,
      intersectionClosure intersectionSuccess origin (Or.inl inLeft),
      differenceClosure differenceSuccess origin (Or.inl inLeft)⟩
  · intro origin inRight
    exact ⟨unionRightClosure unionSuccess origin inRight,
      intersectionClosure intersectionSuccess origin (Or.inr inRight),
      differenceClosure differenceSuccess origin (Or.inr inRight)⟩
  · intro value inBoth
    obtain ⟨survivor, survivorIn, survivorEq⟩ :=
      List.mem_map.mp ((intersectionMembership intersectionSuccess value).mpr inBoth)
    exact ⟨survivor, survivorIn, survivorEq⟩
  · intro survivor survivorIn rightAlias rightAliasIn
    exact differenceSurvivorsAreLeft differenceSuccess survivor survivorIn rightAlias rightAliasIn

end OperationClosure

section Availability

/-- Either operand's failure prevents any successful semantic result: missing,
malformed or wrong-typed sources cannot be hidden by an algebraic operator, by
a vacuous subset, or by an early membership probe. -/
theorem failedOperandRefusesResult (ctx : Context) (env : Env) (elementType : Ty)
    (left right : SetExpr)
    (failed : evalSet ctx env left = none ∨ evalSet ctx env right = none) :
    evalSet ctx env (.intersection elementType left right) = none ∧
      evalSet ctx env (.difference elementType left right) = none ∧
      (∀ resolved : ResolvedAtom, resolveAtom ctx env (.subset left right) ≠ some resolved) ∧
      (∀ failedSet : SetExpr, evalSet ctx env failedSet = none →
          ∀ resolved : ResolvedAtom, ∀ term : Syntax.Term,
            resolveAtom ctx env (.member term failedSet) ≠ some resolved) := by
  rcases failed with leftFailed | rightFailed
  · refine ⟨by simp [evalSet, leftFailed], by simp [evalSet, leftFailed], ?_, ?_⟩
    · intro resolved success
      rw [predicatesSound.2.2.2 ctx env left right (Or.inl leftFailed)] at success
      exact Option.noConfusion success
    · intro failedSet failedEval resolved term success
      rw [predicatesSound.2.2.1 ctx env term failedSet (Or.inr failedEval)] at success
      exact Option.noConfusion success
  · refine ⟨by simp [evalSet, rightFailed], by simp [evalSet, rightFailed], ?_, ?_⟩
    · intro resolved success
      rw [predicatesSound.2.2.2 ctx env left right (Or.inr rightFailed)] at success
      exact Option.noConfusion success
    · intro failedSet failedEval resolved term success
      rw [predicatesSound.2.2.1 ctx env term failedSet (Or.inr failedEval)] at success
      exact Option.noConfusion success

/-- Successful complete inputs have a successful semantic result: the
operations are usable on valid finite inputs, not only safe on failure. -/
theorem operationsComplete (left right : CapturedSet) (same : left.elementType = right.elementType)
    (wellFormed : WellFormed left) (rightWellFormed : WellFormed right) :
    (∃ unionResult, union left right = some unionResult) ∧
      (∃ intersectionResult, intersection left right = some intersectionResult) ∧
      (∃ differenceResult, difference left right = some differenceResult) ∧
      (∃ outcome, subset left right = some outcome) ∧
      (∀ value, value.type = left.elementType →
          ∃ probe, member value left = some probe) := by
  refine ⟨⟨_, (unionSuccessExactly same wellFormed rightWellFormed).choose_spec.1⟩,
    ⟨_, (intersectionSuccessExactly same wellFormed).choose_spec.1⟩,
    ⟨_, (differenceSuccessExactly same wellFormed).choose_spec.1⟩,
    ⟨left.members.all (fun m => decide (m.value ∈ values right)),
      by simp only [subset, if_pos same]⟩, ?_⟩
  intro value typed
  exact ⟨decide (value ∈ values left), by simp only [member, if_pos typed]⟩

end Availability

end Weft.Finite.Algebra
