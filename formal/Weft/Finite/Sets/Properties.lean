import Weft.Finite.Sets

namespace Weft.Finite.Sets

open Weft.Language Weft.Grounding

/-! Total success for completely available typed segments, exact expansion
membership, and stability of repeated normalization. These complement the public
refusal and dependency-preservation contracts without assuming well-formed input. -/

 theorem resolveSegmentTyped (elementType : Ty) (segment : Segment) (set : CapturedSet)
    (success : resolveSegment elementType segment = some set) :
    set.elementType = elementType ∧ Typed elementType set.members := by
  cases segment with
  | member capture =>
      cases capture with
      | none => simp [resolveSegment] at success
      | some member => exact normalizeTyped _ _ _ _ success
  | spread capture =>
      cases capture with
      | none => simp [resolveSegment] at success
      | some source =>
          by_cases typed : source.elementType = elementType
          · have valid : validate source = some set := by
              simpa [resolveSegment, typed] using success
            simpa [typed] using validateTyped source set valid
          · simp [resolveSegment, typed] at success

 theorem expandTyped (elementType : Ty) (segments : List Segment)
    (members : List Member) (origins : List Binding)
    (success : expand elementType segments = some (members, origins)) : Typed elementType members := by
  induction segments generalizing members origins with
  | nil =>
      have same : ([], []) = (members, origins) := by simpa [expand] using success
      have empty : members = [] := (congrArg Prod.fst same).symm
      simp [empty, Typed]
  | cons segment rest ih =>
      obtain ⟨set, tailMembers, tailOrigins, hs, ht, rfl, _⟩ :=
        expandCons _ _ _ _ _ success
      have headTyped := (resolveSegmentTyped _ _ _ hs).2
      have tailTyped := ih _ _ ht
      intro member present
      exact (List.mem_append.mp present).elim (headTyped member) (tailTyped member)

 theorem expandComplete (elementType : Ty) (segments : List Segment)
    (available : ∀ segment ∈ segments, ∃ set, resolveSegment elementType segment = some set) :
    ∃ members origins, expand elementType segments = some (members, origins) := by
  induction segments with
  | nil => exact ⟨[], [], rfl⟩
  | cons segment rest ih =>
      obtain ⟨set, hs⟩ := available segment (by simp)
      obtain ⟨members, origins, ht⟩ := ih (fun part present =>
        available part (List.mem_cons_of_mem _ present))
      exact ⟨set.members ++ members, set.origins ++ origins, by simp [expand, hs, ht]⟩

/-- Every entirely resolved and well-typed finite literal has a complete result;
refusal is not an arbitrary implementation choice on these inputs. -/
theorem materializeComplete (elementType : Ty) (segments : List Segment)
    (extraOrigins : List Binding)
    (available : ∀ segment ∈ segments, ∃ set, resolveSegment elementType segment = some set) :
    ∃ result, materialize elementType segments extraOrigins = some result := by
  obtain ⟨members, origins, expanded⟩ := expandComplete _ _ available
  have typed := expandTyped _ _ _ _ expanded
  exact ⟨build elementType members (extraOrigins ++ origins),
    by simp [materialize, expanded, normalize, typed]⟩

 theorem expandMembership (elementType : Ty) (segments : List Segment)
    (members : List Member) (origins : List Binding)
    (success : expand elementType segments = some (members, origins)) (value : Value) :
    value ∈ members.map Member.value ↔ ∃ segment ∈ segments, ∃ set,
      resolveSegment elementType segment = some set ∧ value ∈ set.members.map Member.value := by
  induction segments generalizing members origins with
  | nil =>
      have same : ([], []) = (members, origins) := by simpa [expand] using success
      have empty : members = [] := (congrArg Prod.fst same).symm
      simp [empty]
  | cons first rest ih =>
      obtain ⟨head, tailMembers, tailOrigins, hh, ht, hm, _⟩ :=
        expandCons _ _ _ _ _ success
      rw [hm, List.map_append, List.mem_append, ih _ _ ht]
      constructor
      · intro present
        rcases present with here | ⟨segment, later, set, resolved, member⟩
        · exact ⟨first, by simp, head, hh, here⟩
        · exact ⟨segment, List.mem_cons_of_mem _ later, set, resolved, member⟩
      · rintro ⟨segment, present, set, resolved, member⟩
        rcases List.mem_cons.mp present with same | later
        · subst segment
          rw [hh] at resolved
          cases Option.some.inj resolved
          exact Or.inl member
        · exact Or.inr ⟨segment, later, set, resolved, member⟩

/-- Exact finite membership includes every resolved source segment and nothing
else; normalization does not permit a successful subset of the declared literal. -/
theorem materializeMembership (elementType : Ty) (segments : List Segment)
    (extraOrigins : List Binding) (result : CapturedSet)
    (success : materialize elementType segments extraOrigins = some result) (value : Value) :
    value ∈ result.members.map Member.value ↔ ∃ segment ∈ segments, ∃ set,
      resolveSegment elementType segment = some set ∧ value ∈ set.members.map Member.value := by
  cases expanded : expand elementType segments with
  | none => simp [materialize, expanded] at success
  | some pair =>
      rcases pair with ⟨members, origins⟩
      have normalized : normalize elementType members (extraOrigins ++ origins) = some result := by
        simpa [materialize, expanded] using success
      exact (normalizeMembership _ _ _ _ normalized value).trans
        (expandMembership _ _ _ _ expanded value)

 theorem normalizeStableOrigins (first second : CapturedSet) (closed : Closed first)
    (success : normalize first.elementType first.members first.origins = some second)
    (origin : Binding) : origin ∈ second.origins ↔ origin ∈ first.origins := by
  rw [normalizeOrigins _ _ _ _ success]
  exact ⟨fun present => present.elim id (closed origin), Or.inl⟩

/-- Renormalization is total for a normalized result, preserves its precise
representation order, and neither gains nor loses any global origin identity. -/
theorem renormalizationStable (elementType : Ty) (members : List Member)
    (extraOrigins : List Binding) (first : CapturedSet)
    (success : normalize elementType members extraOrigins = some first) :
    ∃ second, normalize first.elementType first.members first.origins = some second ∧
      ExtensionalEqual second first ∧
      second.members.map Member.value = first.members.map Member.value ∧
      ∀ origin, origin ∈ second.origins ↔ origin ∈ first.origins := by
  have typeFacts := normalizeTyped _ _ _ _ success
  have typed : Typed first.elementType first.members := by
    rw [typeFacts.1]
    exact typeFacts.2
  let second := build first.elementType first.members first.origins
  have again : normalize first.elementType first.members first.origins = some second := by
    simp [normalize, typed, second]
  refine ⟨second, again, normalizeIdempotent first second again, ?_, ?_⟩
  · rw [firstOccurrenceRepresentation _ _ _ _ again]
    exact unique_of_nodup _ (normalizeNoDuplicates _ _ _ _ success)
  · exact normalizeStableOrigins first second (normalizeClosed _ _ _ _ success) again

end Weft.Finite.Sets
