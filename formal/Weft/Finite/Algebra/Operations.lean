import Weft.Finite.Sets

/-!
# Finite set algebra operations

Revision-3 set algebra on captured sets: union `|`, intersection `&`, left
difference `-`, typed membership `in` and inclusive subset `<=`. These are the
single authoritative operations; `Syntax.evalSet`/`Semantics.resolveAtom` and
the budgeted `CaptureBudget` programs delegate here. Provenance survives
completely: every operation retains both operands' full origin closure at
operation level, and surviving members keep faithful per-member origins.
Algebraic laws are extensional: swapping operands can change display order and
source provenance, and that distinction is preserved, never canonicalized away.
-/

namespace Weft.Finite.Algebra

open Weft.Finite.Sets Weft.Language Weft.Grounding

/-- Values of a captured set in its stable representation order. -/
def values (set : CapturedSet) : List Value := set.members.map Member.value

/-- A set whose members are typed and already duplicate-free: the shape of any
`Sets.normalize` result, and therefore a lawful operand/result of the algebra. -/
def WellFormed (set : CapturedSet) : Prop :=
  Typed set.elementType set.members ∧ (values set).Nodup

theorem normalizeWellFormed (elementType : Ty) (members : List Member)
    (extraOrigins : List Binding) (result : CapturedSet)
    (success : normalize elementType members extraOrigins = some result) :
    WellFormed result := by
  have typed := normalizeTyped elementType members extraOrigins result success
  exact ⟨fun member present => (typed.2 member present).trans typed.1.symm,
    normalizeNoDuplicates elementType members extraOrigins result success⟩

/-- A parametric explicit empty at one element type. -/
def empty (elementType : Ty) : CapturedSet :=
  ⟨elementType, [], [], none⟩

theorem empty_elementType (elementType : Ty) :
    (empty elementType).elementType = elementType := rfl

theorem emptyWellFormed (elementType : Ty) : WellFormed (empty elementType) := by
  refine ⟨?_, by simp [values, empty]⟩
  intro member absent
  cases absent

/-- Union input: both normalized operand lists, left order first. The
normalization input count is therefore the cardinality sum before
cross-operand deduplication. -/
def unionMembers (left right : CapturedSet) : List Member :=
  left.members ++ right.members

def rightContributors (value : Value) (right : CapturedSet) : List Member :=
  right.members.filter (fun m => decide (m.value = value))

/-- Intersection input: each qualifying left member once, in left order, with
the contributing origins of every matching right alias merged into it. -/
def intersectionMembers (left right : CapturedSet) : List Member :=
  (left.members.filter (fun m => decide (m.value ∈ values right))).map
    (fun m => ⟨m.value,
      unique (m.origins ++ (rightContributors m.value right).flatMap Member.origins)⟩)

/-- Difference input: each surviving left member once, in left order, keeping
its own left origins. The right operand's closure is retained at operation
level, never relabelled onto surviving values. -/
def differenceMembers (left right : CapturedSet) : List Member :=
  left.members.filter (fun m => decide (¬ m.value ∈ values right))

/-- Incompatible nominal kinds/realms refuse; a typed empty result keeps its
element type instead of erasing the mismatch. -/
def union (left right : CapturedSet) : Option CapturedSet :=
  if left.elementType = right.elementType then
    normalize left.elementType (unionMembers left right) (left.origins ++ right.origins)
  else none

def intersection (left right : CapturedSet) : Option CapturedSet :=
  if left.elementType = right.elementType then
    normalize left.elementType (intersectionMembers left right) (left.origins ++ right.origins)
  else none

def difference (left right : CapturedSet) : Option CapturedSet :=
  if left.elementType = right.elementType then
    normalize left.elementType (differenceMembers left right) (left.origins ++ right.origins)
  else none

section Inputs

variable (left right : CapturedSet)

theorem mem_unionInputs (value : Value) :
    value ∈ (unionMembers left right).map Member.value ↔
      value ∈ values left ∨ value ∈ values right := by
  simp [unionMembers, values, List.mem_append, List.mem_map]

theorem mem_intersectionInputs (value : Value) :
    value ∈ (intersectionMembers left right).map Member.value ↔
      value ∈ values left ∧ value ∈ values right := by
  constructor
  · intro present
    simp only [intersectionMembers, List.map_map, Function.comp_def] at present
    obtain ⟨member, inFiltered, equality⟩ := List.mem_map.mp present
    have qualifying := (List.mem_filter.mp inFiltered).2
    simp only [decide_eq_true_eq] at qualifying
    refine ⟨List.mem_map.mpr ⟨member, (List.mem_filter.mp inFiltered).1, equality⟩, ?_⟩
    rw [← equality]
    exact qualifying
  · intro present
    obtain ⟨member, memberLeft, equality⟩ := List.mem_map.mp present.1
    have qualifying : decide (member.value ∈ values right) = true := by
      simp only [decide_eq_true_eq, equality]; exact present.2
    have rebuilt : (⟨member.value, unique (member.origins ++
          (rightContributors member.value right).flatMap Member.origins)⟩ : Member) ∈
        intersectionMembers left right := by
      simp only [intersectionMembers]
      exact List.mem_map.mpr ⟨member, List.mem_filter.mpr ⟨memberLeft, qualifying⟩, rfl⟩
    exact List.mem_map.mpr ⟨_, rebuilt, equality⟩

theorem mem_differenceInputs (value : Value) :
    value ∈ (differenceMembers left right).map Member.value ↔
      value ∈ values left ∧ value ∉ values right := by
  constructor
  · intro present
    obtain ⟨member, inFiltered, equality⟩ := List.mem_map.mp present
    have excluding := (List.mem_filter.mp inFiltered).2
    simp only [decide_eq_true_eq] at excluding
    refine ⟨List.mem_map.mpr ⟨member, (List.mem_filter.mp inFiltered).1, equality⟩, ?_⟩
    rw [← equality]
    exact excluding
  · intro present
    obtain ⟨member, memberLeft, equality⟩ := List.mem_map.mp present.1
    have excluding : decide (¬ member.value ∈ values right) = true := by
      simp only [decide_eq_true_eq]; rw [equality]; exact present.2
    refine List.mem_map.mpr ⟨member, ?_, ?_⟩
    · simp only [differenceMembers]
      exact List.mem_filter.mpr ⟨memberLeft, excluding⟩
    · exact equality

theorem typedUnionInputs (same : left.elementType = right.elementType)
    (wellFormed : WellFormed left) (rightWellFormed : WellFormed right) :
    Typed left.elementType (unionMembers left right) := by
  intro member present
  rcases List.mem_append.mp present with here | there
  · exact wellFormed.1 member here
  · rw [rightWellFormed.1 member there]; exact same.symm

theorem typedIntersectionInputs (wellFormed : WellFormed left) :
    Typed left.elementType (intersectionMembers left right) := by
  intro member present
  have inValues : member.value ∈ (intersectionMembers left right).map Member.value :=
    List.mem_map.mpr ⟨member, present, rfl⟩
  have inLeft := ((mem_intersectionInputs left right member.value).mp inValues).1
  obtain ⟨source, sourceLeft, valueEq⟩ := List.mem_map.mp inLeft
  rw [← valueEq]
  exact wellFormed.1 source sourceLeft

theorem typedDifferenceInputs (wellFormed : WellFormed left) :
    Typed left.elementType (differenceMembers left right) := by
  intro member present
  have inValues : member.value ∈ (differenceMembers left right).map Member.value :=
    List.mem_map.mpr ⟨member, present, rfl⟩
  have inLeft := ((mem_differenceInputs left right member.value).mp inValues).1
  obtain ⟨source, sourceLeft, valueEq⟩ := List.mem_map.mp inLeft
  rw [← valueEq]
  exact wellFormed.1 source sourceLeft

end Inputs

section Membership

variable {left right result : CapturedSet}

theorem unionNormalized (success : union left right = some result)
    (same : left.elementType = right.elementType) :
    Sets.normalize left.elementType (unionMembers left right)
      (left.origins ++ right.origins) = some result := by
  simpa [union, same] using success

theorem intersectionNormalized (success : intersection left right = some result)
    (same : left.elementType = right.elementType) :
    Sets.normalize left.elementType (intersectionMembers left right)
      (left.origins ++ right.origins) = some result := by
  simpa [intersection, same] using success

theorem differenceNormalized (success : difference left right = some result)
    (same : left.elementType = right.elementType) :
    Sets.normalize left.elementType (differenceMembers left right)
      (left.origins ++ right.origins) = some result := by
  simpa [difference, same] using success

/-- A01: successful union has exactly the specified extensional membership. -/
theorem unionMembership (success : union left right = some result) (value : Value) :
    value ∈ values result ↔ value ∈ values left ∨ value ∈ values right := by
  by_cases same : left.elementType = right.elementType
  · exact (normalizeMembership _ _ _ _ (unionNormalized success same) value).trans
      (mem_unionInputs left right value)
  · simp [union, same] at success

/-- A01: successful intersection has exactly the specified extensional
membership, computed before any empty result could hide a type mismatch. -/
theorem intersectionMembership (success : intersection left right = some result)
    (value : Value) :
    value ∈ values result ↔ value ∈ values left ∧ value ∈ values right := by
  by_cases same : left.elementType = right.elementType
  · exact (normalizeMembership _ _ _ _ (intersectionNormalized success same) value).trans
      (mem_intersectionInputs left right value)
  · simp [intersection, same] at success

/-- A01: successful difference keeps exactly the left members absent from the
right operand; the direction is never swapped. -/
theorem differenceMembership (success : difference left right = some result)
    (value : Value) :
    value ∈ values result ↔ value ∈ values left ∧ value ∉ values right := by
  by_cases same : left.elementType = right.elementType
  · exact (normalizeMembership _ _ _ _ (differenceNormalized success same) value).trans
      (mem_differenceInputs left right value)
  · simp [difference, same] at success

/-- A01: deterministic first-occurrence display order follows from the actual
operations for all three operators: union keeps left order then unseen right
members; intersection and difference keep qualifying left order. -/
theorem displayOrderSound (intersectionResult differenceResult : CapturedSet)
    (unionSuccess : union left right = some result)
    (intersectionSuccess : intersection left right = some intersectionResult)
    (differenceSuccess : difference left right = some differenceResult)
    (wellFormed : WellFormed left) :
    values result = unique (values left ++ values right) ∧
      values intersectionResult =
        (left.members.filter (fun m => decide (m.value ∈ values right))).map Member.value ∧
      values differenceResult =
        (left.members.filter (fun m => decide (¬ m.value ∈ values right))).map Member.value := by
  by_cases same : left.elementType = right.elementType
  · have filteredSublist (predicate : Member → Bool) :
        ((left.members.filter predicate).map Member.value).Sublist (values left) :=
      List.filter_sublist.map Member.value
    constructor
    · simp only [values]
      rw [firstOccurrenceRepresentation _ _ _ _ (unionNormalized unionSuccess same)]
      simp [unionMembers, values, List.map_append]
    constructor
    · simp only [values]
      rw [firstOccurrenceRepresentation _ _ _ _
          (intersectionNormalized intersectionSuccess same)]
      simp only [intersectionMembers, List.map_map, Function.comp_def]
      rw [unique_of_nodup _ (List.Nodup.sublist (filteredSublist _) wellFormed.2)]
      rfl
    · simp only [values]
      rw [firstOccurrenceRepresentation _ _ _ _ (differenceNormalized differenceSuccess same)]
      simp only [differenceMembers]
      rw [unique_of_nodup _ (List.Nodup.sublist (filteredSublist _) wellFormed.2)]
      rfl
  · simp [union, same] at unionSuccess

end Membership

section Typed

variable {left right result : CapturedSet}

theorem unionTypedResult (success : union left right = some result) :
    left.elementType = right.elementType ∧ result.elementType = left.elementType ∧
      Typed left.elementType result.members := by
  by_cases same : left.elementType = right.elementType
  · have typed := normalizeTyped _ _ _ _ (unionNormalized success same)
    exact ⟨same, typed.1, typed.2⟩
  · simp [union, same] at success

theorem intersectionTypedResult (success : intersection left right = some result) :
    left.elementType = right.elementType ∧ result.elementType = left.elementType ∧
      Typed left.elementType result.members := by
  by_cases same : left.elementType = right.elementType
  · have typed := normalizeTyped _ _ _ _ (intersectionNormalized success same)
    exact ⟨same, typed.1, typed.2⟩
  · simp [intersection, same] at success

theorem differenceTypedResult (success : difference left right = some result) :
    left.elementType = right.elementType ∧ result.elementType = left.elementType ∧
      Typed left.elementType result.members := by
  by_cases same : left.elementType = right.elementType
  · have typed := normalizeTyped _ _ _ _ (differenceNormalized success same)
    exact ⟨same, typed.1, typed.2⟩
  · simp [difference, same] at success

/-- A02: successful operations preserve the unified homogeneous element type,
including typed empty results. -/
theorem operationsTyped (unionResult intersectionResult differenceResult : CapturedSet)
    (unionSuccess : union left right = some unionResult)
    (intersectionSuccess : intersection left right = some intersectionResult)
    (differenceSuccess : difference left right = some differenceResult) :
    (left.elementType = right.elementType ∧ unionResult.elementType = left.elementType ∧
        Typed left.elementType unionResult.members) ∧
      (left.elementType = right.elementType ∧
        intersectionResult.elementType = left.elementType ∧
        Typed left.elementType intersectionResult.members) ∧
      (left.elementType = right.elementType ∧
        differenceResult.elementType = left.elementType ∧
        Typed left.elementType differenceResult.members) :=
  ⟨unionTypedResult unionSuccess, intersectionTypedResult intersectionSuccess,
    differenceTypedResult differenceSuccess⟩

/-- A02: an empty intersection result retains its exact element type; the
emptiness that came from filtering does not erase typing obligations. -/
theorem emptyResultRetainsType (result : CapturedSet) (vacuous : result.members = [])
    (intersectionCase : intersection left right = some result) :
    left.elementType = right.elementType ∧ result.elementType = left.elementType ∧
      Typed left.elementType result.members ∧ values result = [] := by
  have typed := intersectionTypedResult intersectionCase
  exact ⟨typed.1, typed.2.1, typed.2.2, by simp [values, vacuous]⟩

/-- A02: incompatible nominal kinds/realms cannot succeed for any operator or
extensional comparison; scalar/set misuse and emptiness cannot launder it. -/
theorem mixedTypesRefused (mismatch : left.elementType ≠ right.elementType) :
    union left right = none ∧ intersection left right = none ∧
      difference left right = none ∧ equal left right = none := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [union, intersection, difference, equal, mismatch]

end Typed

section Laws

variable {left : CapturedSet}

theorem unionSuccessExactly {right : CapturedSet} (same : left.elementType = right.elementType)
    (wellFormed : WellFormed left) (rightWellFormed : WellFormed right) :
    ∃ result, union left right = some result ∧ WellFormed result := by
  have typed := typedUnionInputs left right same wellFormed rightWellFormed
  have normalized : Sets.normalize left.elementType (unionMembers left right)
      (left.origins ++ right.origins) =
      some (build left.elementType (unionMembers left right) (left.origins ++ right.origins)) :=
    if_pos typed
  exact ⟨_, by rw [union, if_pos same]; exact normalized,
    normalizeWellFormed _ _ _ _ normalized⟩

theorem intersectionSuccessExactly {right : CapturedSet}
    (same : left.elementType = right.elementType) (wellFormed : WellFormed left) :
    ∃ result, intersection left right = some result ∧ WellFormed result := by
  have typed := typedIntersectionInputs left right wellFormed
  have normalized : Sets.normalize left.elementType (intersectionMembers left right)
      (left.origins ++ right.origins) =
      some (build left.elementType (intersectionMembers left right)
        (left.origins ++ right.origins)) :=
    if_pos typed
  exact ⟨_, by rw [intersection, if_pos same]; exact normalized,
    normalizeWellFormed _ _ _ _ normalized⟩

theorem differenceSuccessExactly {right : CapturedSet}
    (same : left.elementType = right.elementType) (wellFormed : WellFormed left) :
    ∃ result, difference left right = some result ∧ WellFormed result := by
  have typed := typedDifferenceInputs left right wellFormed
  have normalized : Sets.normalize left.elementType (differenceMembers left right)
      (left.origins ++ right.origins) =
      some (build left.elementType (differenceMembers left right)
        (left.origins ++ right.origins)) :=
    if_pos typed
  exact ⟨_, by rw [difference, if_pos same]; exact normalized,
    normalizeWellFormed _ _ _ _ normalized⟩

/-- A01: union idempotence, commutativity, associativity and identity,
extensionally, on valid finite inputs. -/
theorem unionLaws (wellFormed : WellFormed left) :
    (∃ result, union left left = some result ∧ ExtensionalEqual result left) ∧
      (∀ right : CapturedSet, right.elementType = left.elementType → WellFormed right →
        ∃ first second, union left right = some first ∧ union right left = some second ∧
          ExtensionalEqual first second) ∧
      (∀ right third : CapturedSet, right.elementType = left.elementType →
        third.elementType = right.elementType → WellFormed right → WellFormed third →
        ∃ leftAssociated rightAssociated firstInner rightInner,
          union right third = some rightInner ∧ union left rightInner = some leftAssociated ∧
          union left right = some firstInner ∧ union firstInner third = some rightAssociated ∧
          ExtensionalEqual leftAssociated rightAssociated) ∧
      (∃ result, union left (empty left.elementType) = some result ∧
        ExtensionalEqual result left ∧
        ∃ other, union (empty left.elementType) left = some other ∧
          ExtensionalEqual other left) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨result, success, _⟩ := unionSuccessExactly rfl wellFormed wellFormed
    exact ⟨result, success, ⟨(unionTypedResult success).2.1, fun value => by
      simpa [values] using unionMembership success value⟩⟩
  · intro right same rightWellFormed
    obtain ⟨first, firstSuccess, _⟩ :=
      unionSuccessExactly same.symm wellFormed rightWellFormed
    obtain ⟨second, secondSuccess, _⟩ :=
      unionSuccessExactly same rightWellFormed wellFormed
    refine ⟨first, second, firstSuccess, secondSuccess, ⟨?_, fun value => ?_⟩⟩
    · exact (unionTypedResult firstSuccess).2.1.trans
        (same.symm.trans (unionTypedResult secondSuccess).2.1.symm)
    · exact (unionMembership firstSuccess value).trans
        (or_comm.trans (unionMembership secondSuccess value).symm)
  · intro right third sameRight sameThird rightWellFormed thirdWellFormed
    obtain ⟨rightInner, rightSuccess, rightInnerWellFormed⟩ :=
      unionSuccessExactly sameThird.symm rightWellFormed thirdWellFormed
    have rightInnerType : rightInner.elementType = right.elementType :=
      (unionTypedResult rightSuccess).2.1
    obtain ⟨leftAssociated, leftSuccess, _⟩ :=
      unionSuccessExactly (sameRight.symm.trans rightInnerType.symm) wellFormed
        rightInnerWellFormed
    obtain ⟨firstInner, firstSuccess, firstInnerWellFormed⟩ :=
      unionSuccessExactly sameRight.symm wellFormed rightWellFormed
    have firstInnerType : firstInner.elementType = left.elementType :=
      (unionTypedResult firstSuccess).2.1
    obtain ⟨rightAssociated, associatedSuccess, _⟩ :=
      unionSuccessExactly (firstInnerType.trans (sameRight.symm.trans sameThird.symm))
        firstInnerWellFormed thirdWellFormed
    refine ⟨leftAssociated, rightAssociated, firstInner, rightInner, rightSuccess, leftSuccess,
      firstSuccess, associatedSuccess, ⟨?_, fun value => ?_⟩⟩
    · rw [(unionTypedResult leftSuccess).2.1, (unionTypedResult associatedSuccess).2.1,
        firstInnerType.symm]
    · show value ∈ values leftAssociated ↔ value ∈ values rightAssociated
      rw [unionMembership leftSuccess value, unionMembership associatedSuccess value,
        unionMembership rightSuccess value, unionMembership firstSuccess value]
      exact or_assoc.symm
  · have emptyFormed := emptyWellFormed left.elementType
    obtain ⟨result, success, _⟩ :=
      unionSuccessExactly (empty_elementType left.elementType).symm wellFormed emptyFormed
    obtain ⟨other, otherSuccess, _⟩ :=
      unionSuccessExactly (empty_elementType left.elementType) emptyFormed wellFormed
    refine ⟨result, success, ⟨(unionTypedResult success).2.1, fun value => by
        simpa [values, empty] using unionMembership success value⟩,
      other, otherSuccess, ⟨(unionTypedResult otherSuccess).2.1, fun value => by
        simpa [values, empty] using unionMembership otherSuccess value⟩⟩

/-- A01: intersection idempotence, commutativity, associativity and empty
identity, extensionally, on valid finite inputs. -/
theorem intersectionLaws (wellFormed : WellFormed left) :
    (∃ result, intersection left left = some result ∧ ExtensionalEqual result left) ∧
      (∀ right : CapturedSet, right.elementType = left.elementType → WellFormed right →
        ∃ first second, intersection left right = some first ∧
          intersection right left = some second ∧ ExtensionalEqual first second) ∧
      (∀ right third : CapturedSet, right.elementType = left.elementType →
        third.elementType = right.elementType → WellFormed right → WellFormed third →
        ∃ leftAssociated rightAssociated firstInner rightInner,
          intersection right third = some rightInner ∧
          intersection left rightInner = some leftAssociated ∧
          intersection left right = some firstInner ∧
          intersection firstInner third = some rightAssociated ∧
          ExtensionalEqual leftAssociated rightAssociated) ∧
      (∃ first, intersection left (empty left.elementType) = some first ∧
          ExtensionalEqual first (empty left.elementType)) ∧
      (∃ second, intersection (empty left.elementType) left = some second ∧
        ExtensionalEqual second (empty left.elementType)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨result, success, _⟩ := intersectionSuccessExactly rfl wellFormed
    exact ⟨result, success, ⟨(intersectionTypedResult success).2.1, fun value => by
      simpa [values] using intersectionMembership success value⟩⟩
  · intro right same rightWellFormed
    obtain ⟨first, firstSuccess, _⟩ :=
      intersectionSuccessExactly same.symm wellFormed
    obtain ⟨second, secondSuccess, _⟩ :=
      intersectionSuccessExactly same rightWellFormed
    refine ⟨first, second, firstSuccess, secondSuccess, ⟨?_, fun value => ?_⟩⟩
    · exact (intersectionTypedResult firstSuccess).2.1.trans
        (same.symm.trans (intersectionTypedResult secondSuccess).2.1.symm)
    · exact (intersectionMembership firstSuccess value).trans
        (and_comm.trans (intersectionMembership secondSuccess value).symm)
  · intro right third sameRight sameThird rightWellFormed thirdWellFormed
    obtain ⟨rightInner, rightSuccess, _⟩ :=
      intersectionSuccessExactly sameThird.symm rightWellFormed
    have rightInnerType : rightInner.elementType = right.elementType :=
      (intersectionTypedResult rightSuccess).2.1
    obtain ⟨leftAssociated, leftSuccess, _⟩ :=
      intersectionSuccessExactly (sameRight.symm.trans rightInnerType.symm) wellFormed
    obtain ⟨firstInner, firstSuccess, firstInnerWellFormed⟩ :=
      intersectionSuccessExactly sameRight.symm wellFormed
    have firstInnerType : firstInner.elementType = left.elementType :=
      (intersectionTypedResult firstSuccess).2.1
    obtain ⟨rightAssociated, associatedSuccess, _⟩ :=
      intersectionSuccessExactly (firstInnerType.trans (sameRight.symm.trans sameThird.symm))
        firstInnerWellFormed
    refine ⟨leftAssociated, rightAssociated, firstInner, rightInner, rightSuccess, leftSuccess,
      firstSuccess, associatedSuccess, ⟨?_, fun value => ?_⟩⟩
    · rw [(intersectionTypedResult leftSuccess).2.1, (intersectionTypedResult associatedSuccess).2.1,
        firstInnerType.symm]
    · show value ∈ values leftAssociated ↔ value ∈ values rightAssociated
      rw [intersectionMembership leftSuccess value, intersectionMembership associatedSuccess value,
        intersectionMembership rightSuccess value, intersectionMembership firstSuccess value]
      exact and_assoc.symm
  · obtain ⟨result, success, _⟩ :=
      intersectionSuccessExactly (empty_elementType left.elementType).symm wellFormed
    exact ⟨result, success, ⟨(intersectionTypedResult success).2.1, fun value => by
      simpa [values, empty] using intersectionMembership success value⟩⟩
  · have emptyFormed := emptyWellFormed left.elementType
    obtain ⟨result, success, _⟩ :=
      intersectionSuccessExactly (empty_elementType left.elementType) emptyFormed
    exact ⟨result, success, ⟨(intersectionTypedResult success).2.1, fun value => by
      simpa [values, empty] using intersectionMembership success value⟩⟩

/-- A01: self/empty difference laws: `a - a` is the typed empty, `a - ∅ = a`
and `∅ - a = ∅`, extensionally, on valid finite inputs. -/
theorem differenceLaws (wellFormed : WellFormed left) :
    (∃ result, difference left left = some result ∧
        ExtensionalEqual result (empty left.elementType)) ∧
      (∃ result, difference left (empty left.elementType) = some result ∧
        ExtensionalEqual result left) ∧
      (∀ right : CapturedSet, right.elementType = left.elementType →
        ∃ result, difference (empty left.elementType) right = some result ∧
          ExtensionalEqual result (empty left.elementType)) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨result, success, _⟩ := differenceSuccessExactly rfl wellFormed
    refine ⟨result, success, ⟨(differenceTypedResult success).2.1, fun value => ?_⟩⟩
    constructor
    · intro present
      have both := (differenceMembership success value).mp present
      exact (both.2 both.1).elim
    · intro impossible
      simp [values, empty] at impossible
  · obtain ⟨result, success, _⟩ :=
      differenceSuccessExactly (empty_elementType left.elementType).symm wellFormed
    exact ⟨result, success, ⟨(differenceTypedResult success).2.1, fun value => by
      simpa [values, empty] using differenceMembership success value⟩⟩
  · intro right same
    have emptyFormed := emptyWellFormed left.elementType
    obtain ⟨result, success, _⟩ :=
      differenceSuccessExactly ((empty_elementType left.elementType).trans same.symm)
        emptyFormed
    refine ⟨result, success, ⟨(differenceTypedResult success).2.1, fun value => ?_⟩⟩
    constructor
    · intro present
      exact ((differenceMembership success value).mp present).1
    · intro impossible
      simp [values, empty] at impossible

/-- A01 primary: successful union/intersection/difference have exactly the
specified extensional memberships, duplicate-free results and deterministic
display order, from the actual operations above. -/
theorem operationsSound {right : CapturedSet} (unionResult intersectionResult
    differenceResult : CapturedSet)
    (unionSuccess : union left right = some unionResult)
    (intersectionSuccess : intersection left right = some intersectionResult)
    (differenceSuccess : difference left right = some differenceResult)
    (wellFormed : WellFormed left) :
    (values unionResult).Nodup ∧ (values intersectionResult).Nodup ∧
      (values differenceResult).Nodup ∧
      (∀ value, value ∈ values unionResult ↔ value ∈ values left ∨ value ∈ values right) ∧
      (∀ value, value ∈ values intersectionResult ↔
        value ∈ values left ∧ value ∈ values right) ∧
      (∀ value, value ∈ values differenceResult ↔
        value ∈ values left ∧ value ∉ values right) ∧
      values unionResult = unique (values left ++ values right) ∧
      values intersectionResult =
        (left.members.filter (fun m => decide (m.value ∈ values right))).map Member.value ∧
      values differenceResult =
        (left.members.filter (fun m => decide (¬ m.value ∈ values right))).map Member.value := by
  have order := displayOrderSound (left := left) (right := right) intersectionResult
    differenceResult unionSuccess intersectionSuccess differenceSuccess wellFormed
  refine ⟨?_, ?_, ?_, fun value => unionMembership unionSuccess value,
    fun value => intersectionMembership intersectionSuccess value,
    fun value => differenceMembership differenceSuccess value, order.1, order.2.1, order.2.2⟩
  · simp only [values]
    rw [firstOccurrenceRepresentation _ _ _ _
      (unionNormalized unionSuccess (unionTypedResult unionSuccess).1)]
    exact unique_nodup _
  · simp only [values]
    rw [firstOccurrenceRepresentation _ _ _ _
      (intersectionNormalized intersectionSuccess (intersectionTypedResult intersectionSuccess).1)]
    exact unique_nodup _
  · simp only [values]
    rw [firstOccurrenceRepresentation _ _ _ _
      (differenceNormalized differenceSuccess (differenceTypedResult differenceSuccess).1)]
    exact unique_nodup _

end Laws

section Predicates

/-- Typed scalar/reference membership: an ill-typed probe has no Boolean
denotation; a well-typed probe is decided extensionally, exactly. -/
def member (value : Value) (set : CapturedSet) : Option Bool :=
  if value.type = set.elementType then some (decide (value ∈ values set)) else none

/-- Inclusive subset, including equality: refused — never false — when the
operand element types differ. -/
def subset (left right : CapturedSet) : Option Bool :=
  if left.elementType = right.elementType then
    some (left.members.all (fun m => decide (m.value ∈ values right)))
  else none

end Predicates

end Weft.Finite.Algebra
