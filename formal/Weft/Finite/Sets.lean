import Weft.Language.Core
import Weft.Grounding.Model

namespace Weft.Finite.Sets

open Weft.Language Weft.Grounding

/-! Finite captured sets use full resolved values, never source aliases. Origins
are exact abstract Binding identities. The owner must preserve all distinctions
when interpreting reference bodies; equal display text is not such a premise.
Availability is represented by Option before normalization, not by filtering. -/

structure Member where
  value : Value
  origins : List Binding
  deriving DecidableEq, Repr

/-- Scope of an observed input count, not a count of transitive textual syntax. -/
inductive CaptureScope where
  | materialization
  | importedPayload
  deriving DecidableEq, Repr

structure CaptureObservation where
  scope : CaptureScope
  rawOccurrences : Nat
  deriving DecidableEq, Repr

/-- `observed` describes this materialization/validation accounting event, never
an evidence observation or freshness refresh. `importedSource` is supplied
provenance, NOT an assertion that its source was available or re-observed.
There are at most two fixed-arity count/scope records: no recursive history,
history copying, or unmetered metadata-list traversal is introduced. -/
structure CaptureStatistics where
  observed : CaptureObservation
  importedSource : Option CaptureObservation
  deriving DecidableEq, Repr

def CaptureStatistics.sourceClaim (capture : CaptureStatistics) : CaptureObservation :=
  capture.importedSource.getD capture.observed

structure CapturedSet where
  elementType : Ty
  members : List Member
  origins : List Binding
  /-- External raw records explicitly use `none` when no history was supplied. -/
  capture : Option CaptureStatistics
  deriving DecidableEq, Repr

def CapturedSet.rawOccurrences (set : CapturedSet) : Option Nat :=
  set.capture.map (fun capture => capture.observed.rawOccurrences)

def importedStatistics (set : CapturedSet) : CaptureStatistics :=
  ⟨⟨.importedPayload, set.members.length⟩, set.capture.map CaptureStatistics.sourceClaim⟩

/-- Stable duplicate removal: the head wins, and later equal values disappear. -/
def unique {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => x :: (unique xs).filter (fun y => decide (y ≠ x))

@[simp] theorem mem_unique {α : Type} [DecidableEq α] (a : α) (xs : List α) :
    a ∈ unique xs ↔ a ∈ xs := by
  induction xs with
  | nil => simp [unique]
  | cons x xs ih =>
      by_cases h : a = x <;> simp [unique, ih, h]

 theorem unique_nodup {α : Type} [DecidableEq α] (xs : List α) :
    (unique xs).Nodup := by
  induction xs with
  | nil => simp [unique]
  | cons x xs ih =>
      apply List.nodup_cons.mpr
      constructor
      · simp
      · exact List.Pairwise.filter _ ih

 theorem unique_of_nodup {α : Type} [DecidableEq α] (xs : List α)
    (h : xs.Nodup) : unique xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have facts := List.nodup_cons.mp h
      rw [unique, ih facts.2]
      congr 1
      apply List.filter_eq_self.mpr
      intro y hy
      simp only [decide_eq_true_eq]
      intro same
      subst y
      exact facts.1 hy

 theorem unique_idempotent {α : Type} [DecidableEq α] (xs : List α) :
    unique (unique xs) = unique xs := unique_of_nodup _ (unique_nodup xs)

 def memberOrigins (members : List Member) : List Binding :=
  members.flatMap Member.origins

 def originsFor (value : Value) : List Member → List Binding
  | [] => []
  | member :: rest =>
      (if member.value = value then member.origins else []) ++ originsFor value rest

@[simp] theorem mem_originsFor (value : Value) (origin : Binding)
    (members : List Member) :
    origin ∈ originsFor value members ↔
      ∃ member ∈ members, member.value = value ∧ origin ∈ member.origins := by
  induction members with
  | nil => simp [originsFor]
  | cons member rest ih =>
      by_cases same : member.value = value <;>
        simp [originsFor, same, ih]

/-- Representation order follows first occurrences; every alias contributes its
origins to the surviving value, independently of that representation choice. -/
def normalizedMembers (members : List Member) : List Member :=
  (unique (members.map Member.value)).map
    (fun value => ⟨value, unique (originsFor value members)⟩)

 def Typed (elementType : Ty) (members : List Member) : Prop :=
  ∀ member ∈ members, member.value.type = elementType

instance (elementType : Ty) (members : List Member) :
    Decidable (Typed elementType members) :=
  inferInstanceAs (Decidable (∀ member ∈ members, member.value.type = elementType))

 def build (elementType : Ty) (members : List Member)
    (extraOrigins : List Binding) : CapturedSet :=
  ⟨elementType, normalizedMembers members, unique (extraOrigins ++ memberOrigins members),
    some ⟨⟨.materialization, members.length⟩, none⟩⟩

/-- No successful prefix: all input members must have the declared type. -/
def normalize (elementType : Ty) (members : List Member)
    (extraOrigins : List Binding) : Option CapturedSet :=
  if Typed elementType members then some (build elementType members extraOrigins) else none

 theorem normalizeSuccess (elementType : Ty) (members : List Member)
    (extraOrigins : List Binding) (result : CapturedSet)
    (success : normalize elementType members extraOrigins = some result) :
    Typed elementType members ∧ result = build elementType members extraOrigins := by
  by_cases typed : Typed elementType members
  · simp [normalize, typed] at success
    exact ⟨typed, success.symm⟩
  · simp [normalize, typed] at success

/-- The count is taken before duplicate removal in this exact normalization
event, not from the output membership and not from recursively expanded syntax. -/
theorem normalizeRawOccurrences (elementType : Ty) (members : List Member)
    (extraOrigins : List Binding) (result : CapturedSet)
    (success : normalize elementType members extraOrigins = some result) :
    result.capture = some ⟨⟨.materialization, members.length⟩, none⟩ ∧
      result.rawOccurrences = some members.length := by
  rcases normalizeSuccess _ _ _ _ success with ⟨_, rfl⟩
  exact ⟨rfl, rfl⟩

@[simp] theorem normalizedMembership (value : Value) (members : List Member) :
    value ∈ (normalizedMembers members).map Member.value ↔
      value ∈ members.map Member.value := by
  simp [normalizedMembers, List.map_map, Function.comp_def]

/-- Q01: exact extensional membership, in both directions, for every value. -/
theorem normalizeMembership (elementType : Ty) (members : List Member)
    (extraOrigins : List Binding) (result : CapturedSet)
    (success : normalize elementType members extraOrigins = some result) (value : Value) :
    value ∈ result.members.map Member.value ↔ value ∈ members.map Member.value := by
  rcases normalizeSuccess _ _ _ _ success with ⟨_, rfl⟩
  exact normalizedMembership value members

/-- Q02: all output members have the stated type, including nominal kind/realm. -/
theorem normalizeTyped (elementType : Ty) (members : List Member)
    (extraOrigins : List Binding) (result : CapturedSet)
    (success : normalize elementType members extraOrigins = some result) :
    result.elementType = elementType ∧ Typed elementType result.members := by
  rcases normalizeSuccess _ _ _ _ success with ⟨typed, rfl⟩
  refine ⟨rfl, ?_⟩
  intro member hm
  have hv : member.value ∈ members.map Member.value :=
    (normalizedMembership member.value members).mp (List.mem_map.mpr ⟨member, hm, rfl⟩)
  obtain ⟨source, hs, equal⟩ := List.mem_map.mp hv
  rw [← equal]
  exact typed source hs

 theorem normalizeOrigins (elementType : Ty) (members : List Member)
    (extraOrigins : List Binding) (result : CapturedSet)
    (success : normalize elementType members extraOrigins = some result) (origin : Binding) :
    origin ∈ result.origins ↔ origin ∈ extraOrigins ∨ origin ∈ memberOrigins members := by
  rcases normalizeSuccess _ _ _ _ success with ⟨_, rfl⟩
  simp [build]

 theorem normalizeMemberOrigins (elementType : Ty) (members : List Member)
    (extraOrigins : List Binding) (result : CapturedSet)
    (success : normalize elementType members extraOrigins = some result)
    (member : Member) (present : member ∈ result.members) (origin : Binding) :
    origin ∈ member.origins ↔
      ∃ source ∈ members, source.value = member.value ∧ origin ∈ source.origins := by
  rcases normalizeSuccess _ _ _ _ success with ⟨_, rfl⟩
  obtain ⟨value, _, equal⟩ := List.mem_map.mp present
  subst member
  simp

 theorem normalizeNoDuplicates (elementType : Ty) (members : List Member)
    (extraOrigins : List Binding) (result : CapturedSet)
    (success : normalize elementType members extraOrigins = some result) :
    (result.members.map Member.value).Nodup := by
  rcases normalizeSuccess _ _ _ _ success with ⟨_, rfl⟩
  simpa [build, normalizedMembers, List.map_map, Function.comp_def] using
    unique_nodup (members.map Member.value)

/-- Extensional equality is typed, order-independent, and provenance-independent.
It does not imply equal assessments or equal dependency closures. -/
def ExtensionalEqual (left right : CapturedSet) : Prop :=
  left.elementType = right.elementType ∧
    ∀ value, value ∈ left.members.map Member.value ↔ value ∈ right.members.map Member.value

/-- Internal finite comparison; public `compare` validates external inputs first. -/
def equal (left right : CapturedSet) : Option Bool :=
  if left.elementType = right.elementType then
    some ((left.members.all fun m => decide (m.value ∈ right.members.map Member.value)) &&
      (right.members.all fun m => decide (m.value ∈ left.members.map Member.value)))
  else none

theorem equalCorrect (left right : CapturedSet) :
    equal left right = some true ↔ ExtensionalEqual left right := by
  by_cases typed : left.elementType = right.elementType
  · simp only [equal, typed, ↓reduceIte, Option.some.injEq, Bool.and_eq_true,
      List.all_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨forward, backward⟩
      refine ⟨typed, fun value => ⟨?_, ?_⟩⟩
      · intro present
        obtain ⟨member, hm, rfl⟩ := List.mem_map.mp present
        exact forward member hm
      · intro present
        obtain ⟨member, hm, rfl⟩ := List.mem_map.mp present
        exact backward member hm
    · intro equivalent
      constructor
      · intro member present
        exact (equivalent.2 member.value).mp (List.mem_map.mpr ⟨member, present, rfl⟩)
      · intro member present
        exact (equivalent.2 member.value).mpr (List.mem_map.mpr ⟨member, present, rfl⟩)
  · simp [equal, typed, ExtensionalEqual]

 theorem extensionalRefl (set : CapturedSet) : ExtensionalEqual set set :=
  ⟨rfl, fun _ => Iff.rfl⟩

 theorem extensionalSymm (left right : CapturedSet) (h : ExtensionalEqual left right) :
    ExtensionalEqual right left := ⟨h.1.symm, fun value => (h.2 value).symm⟩

 theorem extensionalTrans (a b c : CapturedSet)
    (ab : ExtensionalEqual a b) (bc : ExtensionalEqual b c) : ExtensionalEqual a c :=
  ⟨ab.1.trans bc.1, fun value => (ab.2 value).trans (bc.2 value)⟩

 theorem normalizeExtensional (elementType : Ty) (members : List Member)
    (origins : List Binding) (result : CapturedSet)
    (success : normalize elementType members origins = some result) :
    ExtensionalEqual result ⟨elementType, members, origins, none⟩ :=
  ⟨(normalizeTyped _ _ _ _ success).1, normalizeMembership _ _ _ _ success⟩

 theorem normalizeIdempotent (first second : CapturedSet)
    (success : normalize first.elementType first.members first.origins = some second) :
    ExtensionalEqual second first := normalizeExtensional _ _ _ _ success

 theorem mixedTypeFails (elementType : Ty) (members : List Member)
    (origins : List Binding) (member : Member) (present : member ∈ members)
    (wrong : member.value.type ≠ elementType) : normalize elementType members origins = none := by
  have invalid : ¬ Typed elementType members := fun typed => wrong (typed member present)
  simp [normalize, invalid]

 theorem nominalKindSeparation (kind other realm body : String) (h : kind ≠ other) :
    Value.identity kind realm body ≠ Value.identity other realm body := by
  intro same
  cases same
  exact h rfl

 theorem nominalRealmSeparation (kind realm other body : String) (h : realm ≠ other) :
    Value.identity kind realm body ≠ Value.identity kind other body := by
  intro same
  cases same
  exact h rfl

/-- Validate external records before accepting them. Global origins must already
contain every member dependency; missing provenance is malformed, not repaired. -/
def Closed (set : CapturedSet) : Prop :=
  ∀ origin ∈ memberOrigins set.members, origin ∈ set.origins

instance (set : CapturedSet) : Decidable (Closed set) :=
  inferInstanceAs (Decidable (∀ origin ∈ memberOrigins set.members, origin ∈ set.origins))

def validate (set : CapturedSet) : Option CapturedSet :=
  if Closed set then
    (normalize set.elementType set.members set.origins).map
      (fun value => { value with capture := some (importedStatistics set) })
  else none

theorem validateSuccess (set result : CapturedSet) (success : validate set = some result) :
    Closed set ∧ ∃ normalized,
      normalize set.elementType set.members set.origins = some normalized ∧
      result = { normalized with capture := some (importedStatistics set) } := by
  by_cases closed : Closed set
  · cases normalized : normalize set.elementType set.members set.origins with
    | none => simp [validate, closed, normalized] at success
    | some value =>
      have same : { value with capture := some (importedStatistics set) } = result := by
        simpa [validate, closed, normalized] using success
      exact ⟨closed, value, rfl, same.symm⟩
  · simp [validate, closed] at success

theorem validateOrigins (set result : CapturedSet) (success : validate set = some result)
    (origin : Binding) : origin ∈ result.origins ↔ origin ∈ set.origins := by
  obtain ⟨closed, normalized, checked, rfl⟩ := validateSuccess set result success
  change origin ∈ normalized.origins ↔ origin ∈ set.origins
  rw [normalizeOrigins _ _ _ _ checked]
  exact ⟨fun h => h.elim id (closed origin), Or.inl⟩

theorem validateTyped (set result : CapturedSet) (success : validate set = some result) :
    result.elementType = set.elementType ∧ Typed set.elementType result.members := by
  obtain ⟨_, normalized, checked, rfl⟩ := validateSuccess set result success
  exact normalizeTyped set.elementType set.members set.origins normalized checked

/-- Imported statistics count the payload actually checked. Prior source counts
remain explicitly imported provenance, never a fabricated observation. -/
theorem validateRawOccurrences (set result : CapturedSet)
    (success : validate set = some result) :
    result.capture = some (importedStatistics set) ∧
      result.rawOccurrences = some set.members.length := by
  obtain ⟨_, _, _, rfl⟩ := validateSuccess set result success
  exact ⟨rfl, rfl⟩

theorem normalizeClosed (elementType : Ty) (members : List Member)
    (extraOrigins : List Binding) (result : CapturedSet)
    (success : normalize elementType members extraOrigins = some result) : Closed result := by
  intro origin present
  obtain ⟨member, hm, ho⟩ := List.mem_flatMap.mp present
  obtain ⟨source, hs, _, required⟩ :=
    (normalizeMemberOrigins _ _ _ _ success member hm origin).mp ho
  exact (normalizeOrigins _ _ _ _ success origin).mpr
    (Or.inr (List.mem_flatMap.mpr ⟨source, hs, required⟩))

theorem validateExtensional (set result : CapturedSet) (success : validate set = some result) :
    ExtensionalEqual result set := by
  obtain ⟨_, normalized, checked, rfl⟩ := validateSuccess set result success
  exact normalizeExtensional set.elementType set.members set.origins normalized checked

/-- Public extensional comparison refuses malformed records on either side. -/
def compare (left right : CapturedSet) : Option Bool :=
  match validate left, validate right with
  | some a, some b => equal a b
  | _, _ => none

theorem compareSound (left right : CapturedSet) (success : compare left right = some true) :
    ExtensionalEqual left right := by
  cases hl : validate left with
  | none => simp [compare, hl] at success
  | some a =>
      cases hr : validate right with
      | none => simp [compare, hl, hr] at success
      | some b =>
          have equalAB : equal a b = some true := by simpa [compare, hl, hr] using success
          exact extensionalTrans left a right
            (extensionalSymm a left (validateExtensional left a hl))
            (extensionalTrans a b right ((equalCorrect a b).mp equalAB)
              (validateExtensional right b hr))

theorem firstOccurrenceRepresentation (elementType : Ty) (members : List Member)
    (extraOrigins : List Binding) (result : CapturedSet)
    (success : normalize elementType members extraOrigins = some result) :
    result.members.map Member.value = unique (members.map Member.value) := by
  rcases normalizeSuccess _ _ _ _ success with ⟨_, rfl⟩
  simp [build, normalizedMembers, List.map_map, Function.comp_def]

theorem duplicateMembership (elementType : Ty) (member : Member) (rest : List Member)
    (extraOrigins : List Binding) (once twice : CapturedSet)
    (single : normalize elementType (member :: rest) extraOrigins = some once)
    (duplicate : normalize elementType (member :: member :: rest) extraOrigins = some twice) :
    ExtensionalEqual twice once := by
  refine ⟨(normalizeTyped _ _ _ _ duplicate).1.trans
    (normalizeTyped _ _ _ _ single).1.symm, ?_⟩
  intro value
  rw [normalizeMembership _ _ _ _ duplicate, normalizeMembership _ _ _ _ single]
  simp

 theorem malformedOriginsFail (set : CapturedSet) (malformed : ¬ Closed set) :
    validate set = none := by simp [validate, malformed]

/-- Captures explicitly retain failure; a spread is a set, never a scalar. The
expected type is checked even when the spread has no members. -/
inductive Segment where
  | member (capture : Option Member)
  | spread (capture : Option CapturedSet)
  deriving DecidableEq, Repr

def resolveSegment (elementType : Ty) : Segment → Option CapturedSet
  | .member none => none
  | .member (some member) => normalize elementType [member] []
  | .spread none => none
  | .spread (some set) =>
      if set.elementType = elementType then validate set else none

/-- Every segment must resolve before any successful materialization exists. -/
def expand (elementType : Ty) : List Segment → Option (List Member × List Binding)
  | [] => some ([], [])
  | segment :: rest =>
      match resolveSegment elementType segment, expand elementType rest with
      | some set, some (members, origins) => some (set.members ++ members, set.origins ++ origins)
      | _, _ => none

def materialize (elementType : Ty) (segments : List Segment)
    (extraOrigins : List Binding) : Option CapturedSet :=
  match expand elementType segments with
  | none => none
  | some (members, origins) => normalize elementType members (extraOrigins ++ origins)

theorem expandCons (elementType : Ty) (segment : Segment) (rest : List Segment)
    (members : List Member) (origins : List Binding)
    (success : expand elementType (segment :: rest) = some (members, origins)) :
    ∃ set tailMembers tailOrigins,
      resolveSegment elementType segment = some set ∧
      expand elementType rest = some (tailMembers, tailOrigins) ∧
      members = set.members ++ tailMembers ∧ origins = set.origins ++ tailOrigins := by
  cases hs : resolveSegment elementType segment with
  | none => simp [expand, hs] at success
  | some set =>
      cases ht : expand elementType rest with
      | none => simp [expand, hs, ht] at success
      | some tail =>
          rcases tail with ⟨tailMembers, tailOrigins⟩
          have same : (set.members ++ tailMembers, set.origins ++ tailOrigins) =
              (members, origins) := by simpa [expand, hs, ht] using success
          exact ⟨set, tailMembers, tailOrigins, rfl, rfl,
            (congrArg Prod.fst same).symm, (congrArg Prod.snd same).symm⟩

theorem expandSegmentOrigins (elementType : Ty) (segments : List Segment)
    (members : List Member) (origins : List Binding)
    (success : expand elementType segments = some (members, origins))
    (segment : Segment) (present : segment ∈ segments) (set : CapturedSet)
    (resolved : resolveSegment elementType segment = some set)
    (origin : Binding) (required : origin ∈ set.origins) : origin ∈ origins := by
  induction segments generalizing members origins with
  | nil => simp at present
  | cons first rest ih =>
      obtain ⟨head, tailMembers, tailOrigins, hh, ht, _, ho⟩ :=
        expandCons _ _ _ _ _ success
      rw [ho]
      rcases List.mem_cons.mp present with same | later
      · subst first
        rw [resolved] at hh
        cases Option.some.inj hh
        exact List.mem_append_left _ required
      · exact List.mem_append_right _ (ih _ _ ht later)

/-- An unavailable, malformed or wrong-type source refuses the whole expression. -/
theorem expansionFailureAtomic (elementType : Ty) (segments : List Segment)
    (segment : Segment) (present : segment ∈ segments)
    (failed : resolveSegment elementType segment = none) :
    expand elementType segments = none := by
  induction segments with
  | nil => simp at present
  | cons first rest ih =>
      rcases List.mem_cons.mp present with same | later
      · subst first
        simp [expand, failed]
      · have tailFailed := ih later
        cases resolved : resolveSegment elementType first <;>
          simp [expand, tailFailed, resolved]

theorem materializationFailureAtomic (elementType : Ty) (segments : List Segment)
    (extraOrigins : List Binding) (segment : Segment) (present : segment ∈ segments)
    (failed : resolveSegment elementType segment = none) :
    materialize elementType segments extraOrigins = none := by
  simp [materialize, expansionFailureAtomic _ _ _ present failed]

/-- Q03: every captured spread edge survives, including an empty spread's origin.
The theorem ranges over any position in a successful literal, not just singleton
or nonempty spreads. -/
theorem spreadPreservesOrigins (elementType : Ty) (segments : List Segment)
    (extraOrigins : List Binding) (result source : CapturedSet)
    (success : materialize elementType segments extraOrigins = some result)
    (present : Segment.spread (some source) ∈ segments)
    (origin : Binding) (required : origin ∈ source.origins) : origin ∈ result.origins := by
  cases expanded : expand elementType segments with
  | none => simp [materialize, expanded] at success
  | some pair =>
      rcases pair with ⟨members, origins⟩
      have normalized : normalize elementType members (extraOrigins ++ origins) =
          some result := by simpa [materialize, expanded] using success
      have resolvedExists : ∃ set,
          resolveSegment elementType (.spread (some source)) = some set := by
        cases resolved : resolveSegment elementType (.spread (some source)) with
        | none =>
            have impossible := expansionFailureAtomic _ _ _ present resolved
            rw [impossible] at expanded
            contradiction
        | some set => exact ⟨set, rfl⟩
      obtain ⟨set, resolved⟩ := resolvedExists
      have validated : validate source = some set := by
        by_cases typed : source.elementType = elementType
        · simpa [resolveSegment, typed] using resolved
        · simp [resolveSegment, typed] at resolved
      have kept := (validateOrigins source set validated origin).mpr required
      have inOrigins := expandSegmentOrigins _ _ _ _ expanded _ present _ resolved _ kept
      exact (normalizeOrigins _ _ _ _ normalized origin).mpr
        (Or.inl (List.mem_append_right _ inOrigins))

theorem materializeExtraOrigins (elementType : Ty) (segments : List Segment)
    (extraOrigins : List Binding) (result : CapturedSet)
    (success : materialize elementType segments extraOrigins = some result)
    (origin : Binding) (required : origin ∈ extraOrigins) : origin ∈ result.origins := by
  cases expanded : expand elementType segments with
  | none => simp [materialize, expanded] at success
  | some pair =>
      rcases pair with ⟨members, origins⟩
      have normalized : normalize elementType members (extraOrigins ++ origins) =
          some result := by simpa [materialize, expanded] using success
      exact (normalizeOrigins _ _ _ _ normalized origin).mpr
        (Or.inl (List.mem_append_left _ required))

theorem materializeTyped (elementType : Ty) (segments : List Segment)
    (extraOrigins : List Binding) (result : CapturedSet)
    (success : materialize elementType segments extraOrigins = some result) :
    result.elementType = elementType ∧ Typed elementType result.members := by
  cases expanded : expand elementType segments with
  | none => simp [materialize, expanded] at success
  | some pair =>
      rcases pair with ⟨members, origins⟩
      exact normalizeTyped _ _ _ _ (by simpa [materialize, expanded] using success)

/-- Raw occurrences are the actual concatenated segment inputs to this event.
A spread contributes its checked members, not unavailable transitive source text. -/
theorem materializeRawOccurrences (elementType : Ty) (segments : List Segment)
    (extraOrigins : List Binding) (result : CapturedSet)
    (success : materialize elementType segments extraOrigins = some result) :
    ∃ members origins, expand elementType segments = some (members, origins) ∧
      result.rawOccurrences = some members.length := by
  cases expanded : expand elementType segments with
  | none => simp [materialize, expanded] at success
  | some pair =>
    obtain ⟨members, origins⟩ := pair
    exact ⟨members, origins, rfl,
      (normalizeRawOccurrences elementType members (extraOrigins ++ origins) result
        (by simpa [materialize, expanded] using success)).2⟩

theorem extensionalCaptureIndependent (left right : CapturedSet)
    (a b : Option CaptureStatistics) :
    equal { left with capture := a } { right with capture := b } = equal left right := rfl

end Weft.Finite.Sets
