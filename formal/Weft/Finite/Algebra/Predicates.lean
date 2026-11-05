import Weft.Finite.Semantics

/-!
# Membership and subset predicates

A03: `in` is true exactly for typed membership and `<=` is true exactly for
inclusive subset, decided by the single authoritative `Weft.Finite.Algebra`
operations. Unavailable or ill-typed operands have no Boolean denotation: a
refusal never becomes `false`. A false subset retains a deterministic
first-left counterexample tied to the exact finite operands.
-/

namespace Weft.Finite.Algebra

open Weft.Language Weft.Finite.Syntax Weft.Finite.Sets Weft.Finite.Semantics

section PredicateLaws

variable {left right : CapturedSet}

/-- A03: `in` is true exactly for typed membership; the probe type must equal
the set's element type, including for empty sets. -/
theorem membershipPredicateSound (value : Value) (outcome : Bool)
    (success : member value left = some outcome) :
    value.type = left.elementType ∧ (outcome = true ↔ value ∈ values left) := by
  by_cases typed : value.type = left.elementType
  · have decided : decide (value ∈ values left) = outcome := Option.some.inj
      (by simpa [member, typed] using success)
    exact ⟨typed, by rw [← decided]; simp [decide_eq_true_eq]⟩
  · simp [member, typed] at success

/-- A03: `<=` is true exactly for inclusive subset over the whole left set. -/
theorem subsetPredicateSound (outcome : Bool) (success : subset left right = some outcome) :
    left.elementType = right.elementType ∧
      (outcome = true ↔ ∀ m ∈ left.members, m.value ∈ values right) := by
  by_cases same : left.elementType = right.elementType
  · have decided : left.members.all (fun m => decide (m.value ∈ values right)) = outcome :=
      Option.some.inj (by simpa [subset, same] using success)
    exact ⟨same, by rw [← decided]; simp [List.all_eq_true, decide_eq_true_eq]⟩
  · simp [subset, same] at success

/-- A03: empty and reflexive subset laws, antisymmetry with extensional
equality, and agreement of subset with extensional equality. -/
theorem subsetLaws :
    (∀ set : CapturedSet, subset set set = some true) ∧
      (∀ set : CapturedSet, subset (empty set.elementType) set = some true) ∧
      (∀ a b : CapturedSet, subset a b = some true ∧ subset b a = some true →
        ExtensionalEqual a b) ∧
      (∀ a b : CapturedSet, a.elementType = b.elementType → ExtensionalEqual a b →
        subset a b = some true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro set
    have decision : set.members.all (fun m => decide (m.value ∈ values set)) = true := by
      rw [List.all_eq_true]
      intro member present
      exact decide_eq_true_eq.mpr (List.mem_map.mpr ⟨member, present, rfl⟩)
    show (if set.elementType = set.elementType then
        some (set.members.all (fun m => decide (m.value ∈ values set))) else none) = some true
    rw [if_pos rfl, decision]
  · intro set
    simp only [empty_elementType, subset, if_pos rfl, Option.some.injEq]
    rfl
  · intro a b bothQualify
    obtain ⟨forward, backward⟩ := bothQualify
    have forwardFact := subsetPredicateSound true forward
    have backwardFact := subsetPredicateSound true backward
    refine ⟨forwardFact.1, fun value => ⟨?_, ?_⟩⟩
    · intro present
      obtain ⟨member, memberLeft, rfl⟩ := List.mem_map.mp present
      exact forwardFact.2.mp rfl member memberLeft
    · intro present
      obtain ⟨member, memberRight, rfl⟩ := List.mem_map.mp present
      exact backwardFact.2.mp rfl member memberRight
  · intro a b same equivalent
    have membersQualify : a.members.all (fun m => decide (m.value ∈ values b)) = true := by
      rw [List.all_eq_true]
      intro member present
      exact decide_eq_true_eq.mpr
        ((equivalent.2 member.value).mp (List.mem_map.mpr ⟨member, present, rfl⟩))
    show (if a.elementType = b.elementType then
        some (a.members.all (fun m => decide (m.value ∈ values b))) else none) = some true
    rw [if_pos same, membersQualify]

/-- First member of a list absent from `right`, scanning from the head: the
deterministic first-left counterexample search. -/
def firstAbsent (right : CapturedSet) : List Member → Option Member
  | [] => none
  | m :: rest => if decide (m.value ∈ values right) then firstAbsent right rest else some m

/-- The deterministic first-left member of `left` absent from `right`, or none
when every left member is present. -/
def firstCounterexample (left right : CapturedSet) : Option Member :=
  firstAbsent right left.members

theorem firstAbsent_some (right : CapturedSet) : ∀ members : List Member,
    (∃ m ∈ members, m.value ∉ values right) →
    ∃ w, firstAbsent right members = some w ∧ w ∈ members ∧ w.value ∉ values right := by
  intro members
  induction members with
  | nil =>
      intro failing
      obtain ⟨_m, membership, _⟩ := failing
      simp at membership
  | cons head rest ih =>
      intro failing
      by_cases probe : decide (head.value ∈ values right) = true
      · have headQualifies : head.value ∈ values right := by
          simpa only [decide_eq_true_eq] using probe
        have restFailing : ∃ m ∈ rest, m.value ∉ values right := by
          obtain ⟨m, present, absent⟩ := failing
          rcases List.mem_cons.mp present with rfl | later
          · exact absurd headQualifies absent
          · exact ⟨m, later, absent⟩
        obtain ⟨w, found, wIn, wAbsent⟩ := ih restFailing
        exact ⟨w, by simp [firstAbsent, probe, found],
          List.mem_cons.mpr (Or.inr wIn), wAbsent⟩
      · refine ⟨head, by simp [firstAbsent, probe], List.mem_cons.mpr (Or.inl rfl), ?_⟩
        intro membership
        have trueProbe : decide (head.value ∈ values right) = true := by
          simp [membership]
        rw [trueProbe] at probe
        exact absurd rfl probe

/-- A03: a false subset yields a deterministic first-left counterexample: a
concrete member of `left`, absent from `right`, tied to those exact operands. -/
theorem subsetCounterexample (outcome : Bool) (success : subset left right = some outcome)
    (negative : outcome = false) :
    ∃ witness, firstCounterexample left right = some witness ∧
      witness ∈ left.members ∧ witness.value ∉ values right := by
  by_cases same : left.elementType = right.elementType
  · have decided : left.members.all (fun m => decide (m.value ∈ values right)) = outcome :=
      Option.some.inj (by simpa [subset, same] using success)
    have failing : ∃ m ∈ left.members, m.value ∉ values right := by
      apply Classical.byContradiction
      intro noFailing
      have allTrue : left.members.all (fun m => decide (m.value ∈ values right)) = true := by
        rw [List.all_eq_true]
        intro m mIn
        exact decide_eq_true_eq.mpr
          (Classical.byContradiction (fun absent => noFailing ⟨m, mIn, absent⟩))
      rw [allTrue] at decided
      rw [negative] at decided
      exact Bool.noConfusion decided
    obtain ⟨w, found, wIn, wAbsent⟩ := firstAbsent_some right left.members failing
    exact ⟨w, by rw [firstCounterexample, found], wIn, wAbsent⟩
  · have refused : subset left right = none := by simp [subset, same]
    rw [refused] at success
    exact Option.noConfusion success

end PredicateLaws

section AtomResolution

private theorem bindSome' {α β : Type} (first : Option α) (next : α → Option β)
    (value : β) (success : first.bind next = some value) :
    ∃ a, first = some a ∧ next a = some value := by
  cases first with
  | none => simp at success
  | some a => exact ⟨a, rfl, success⟩

/-- A03 primary: membership and subset atoms resolve to exactly the typed
Boolean facts of the single authoritative operations, carrying both operands'
complete origins; unavailable operands have no Boolean denotation. -/
theorem predicatesSound :
    (∀ (ctx : Context) (env : Env) (term : Syntax.Term) (set : SetExpr) (resolved : ResolvedAtom),
        resolveAtom ctx env (.member term set) = some resolved →
        ∃ x captured outcome, resolveTerm ctx env term = some x ∧
          evalSet ctx env set = some captured ∧ member x.value captured = some outcome ∧
          resolved.surface = .boolean outcome ∧
          resolved.origins = x.origins ++ captured.origins) ∧
    (∀ (ctx : Context) (env : Env) (left right : SetExpr) (resolved : ResolvedAtom),
        resolveAtom ctx env (.subset left right) = some resolved →
        ∃ x y outcome, evalSet ctx env left = some x ∧ evalSet ctx env right = some y ∧
          subset x y = some outcome ∧ resolved.surface = .boolean outcome ∧
          resolved.origins = x.origins ++ y.origins) ∧
    (∀ (ctx : Context) (env : Env) (term : Syntax.Term) (set : SetExpr),
        resolveTerm ctx env term = none ∨ evalSet ctx env set = none →
        resolveAtom ctx env (.member term set) = none) ∧
    (∀ (ctx : Context) (env : Env) (left right : SetExpr),
        evalSet ctx env left = none ∨ evalSet ctx env right = none →
        resolveAtom ctx env (.subset left right) = none) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ctx env term set resolved success
    simp only [resolveAtom] at success
    obtain ⟨x, xOk, afterX⟩ := bindSome' _ _ _ success
    obtain ⟨captured, capturedOk, afterCaptured⟩ := bindSome' _ _ _ afterX
    obtain ⟨outcome, outcomeOk, finished⟩ := bindSome' _ _ _ afterCaptured
    have recordEq : (⟨Surface.boolean outcome,
        x.origins ++ captured.origins⟩ : ResolvedAtom) = resolved := Option.some.inj finished
    cases recordEq
    exact ⟨x, captured, outcome, xOk, capturedOk, outcomeOk, rfl, rfl⟩
  · intro ctx env left right resolved success
    simp only [resolveAtom] at success
    obtain ⟨x, xOk, afterX⟩ := bindSome' _ _ _ success
    obtain ⟨y, yOk, afterY⟩ := bindSome' _ _ _ afterX
    obtain ⟨outcome, outcomeOk, finished⟩ := bindSome' _ _ _ afterY
    have recordEq : (⟨Surface.boolean outcome,
        x.origins ++ y.origins⟩ : ResolvedAtom) = resolved := Option.some.inj finished
    cases recordEq
    exact ⟨x, y, outcome, xOk, yOk, outcomeOk, rfl, rfl⟩
  · intro ctx env term set unavailable
    rcases unavailable with scalar | domain
    · simp [resolveAtom, scalar]
    · simp [resolveAtom, domain]
  · intro ctx env left right unavailable
    rcases unavailable with leftUnavailable | rightUnavailable
    · simp [resolveAtom, leftUnavailable]
    · simp [resolveAtom, rightUnavailable]

end AtomResolution

end Weft.Finite.Algebra
