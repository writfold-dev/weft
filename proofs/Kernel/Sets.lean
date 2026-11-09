import Extracted.WeftCore
import Kernel.Spec

/-!
# Finite set algebra over value identities (A01, A03)

Theorems over the Aeneas translation of `weft_core::sets`
(`Extracted/WeftCore.lean`), the decisions `weft_domain`'s set operations
call. They restate, at the level of value identities, the calculus's
set-algebra claims:

- A01 (exact membership and deterministic display order): normalization is
  `unique` (first occurrence), union is `unique (left ++ right)`,
  intersection and difference are the qualifying left values in left order;
  each has exactly the specified extensional membership
  (`normalize_spec`, `union_spec`, `intersection_spec`, `difference_spec`).
- A03 (predicates and faithful counterexamples): membership is `∈`; subset
  answers `none` iff every left value is on the right, otherwise the first
  left position that is not (`contains_spec`, `subset_spec`); extensional
  equality is mutual inclusion (`same_members_spec`).

Typing, budget charging and origin closure (A02, A04–A08) stay in
`weft_domain` and remain covered by the calculus, tests and differential
checks, not by these theorems.

Every theorem is a total-correctness Hoare triple `f args ⦃ r => P r ⦄`: the
call terminates without failure and its result satisfies `P`.
-/

open Aeneas Aeneas.Std Result
open weft_core
open Weft.Core.Spec

namespace Weft.Core

/-- `Vec::deref` exposes the vector's own list. -/
@[simp] theorem deref_val {α : Type} (v : alloc.vec.Vec α) :
    (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref, Slice.from_val]

/-- The answer of `position_of`: the first position holding `value`, or
`none` when no position does. -/
def FirstPosition (values : List Usize) (value : Usize) : Option Usize → Prop
  | none => value ∉ values
  | some p => ∃ h : p.val < values.length, values[p.val] = value ∧
      ∀ j (hj : j < p.val), values[j]'(Nat.lt_trans hj h) ≠ value

/-- The search loop from position `i`, knowing `value` is not before `i`. -/
theorem position_of_loop_spec (values : Slice Usize) (value : Usize) (i : Usize)
    (hi : i.val ≤ values.val.length)
    (hprefix : ∀ j (h : j < values.val.length), j < i.val → values.val[j] ≠ value) :
    sets.position_of_loop values value i ⦃ r => FirstPosition values.val value r ⦄ := by
  unfold sets.position_of_loop
  apply loop.spec_decr_nat (fun i : Usize => values.val.length - i.val)
    (fun i : Usize => i.val ≤ values.val.length ∧
      ∀ j (h : j < values.val.length), j < i.val → values.val[j] ≠ value)
  · intro i ⟨hi, hprefix⟩
    unfold sets.position_of_loop.body
    try dsimp only
    split_ifs with hlt
    · have hlt' : i.val < values.val.length := by scalar_tac
      step as ⟨ x, hx ⟩
      split_ifs with heq
      · simp only [WP.spec_ok, FirstPosition]
        refine ⟨hlt', ?_, ?_⟩
        · rw [← hx, heq]
        · intro j hj
          exact hprefix j _ hj
      · apply WP.spec_bind (Usize.add_spec (by scalar_tac))
        intro i' hi'
        simp only [WP.spec_ok]
        and_intros
        all_goals try scalar_tac
        intro j hj hji
        by_cases hlt'' : j < i.val
        · exact hprefix j hj hlt''
        · have : j = i.val := by scalar_tac
          subst this
          rw [← hx]
          exact heq
    · simp only [WP.spec_ok, FirstPosition]
      intro hmem
      obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hmem
      exact hprefix j hj (by scalar_tac) hjeq
  · exact ⟨hi, hprefix⟩

/-- `position_of` answers the first position holding `value`. -/
theorem position_of_spec (values : Slice Usize) (value : Usize) :
    sets.position_of values value ⦃ r => FirstPosition values.val value r ⦄ := by
  unfold sets.position_of
  apply position_of_loop_spec
  · simp
  · intro j _ hj; simp at hj

/-- `contains` is membership. -/
theorem contains_spec (values : Slice Usize) (value : Usize) :
    sets.contains values value ⦃ r => r ↔ value ∈ values.val ⦄ := by
  unfold sets.contains
  apply WP.spec_bind (position_of_spec values value)
  intro o ho
  cases o with
  | none => simpa [FirstPosition] using ho
  | some p =>
    obtain ⟨h, hp, _⟩ := ho
    simp only [core.option.Option.is_some, Option.isSome_some, WP.spec_ok, true_iff]
    rw [← hp]
    exact List.getElem_mem h

theorem foldl_extendStep_length (base xs : List Usize) :
    (xs.foldl extendStep base).length ≤ base.length + xs.length := by
  induction xs generalizing base with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons]
    have := ih (extendStep base x)
    have hstep : (extendStep base x).length ≤ base.length + 1 := by
      unfold extendStep; split_ifs <;> simp
    omega

/-- The `extend_unique` loop from position `i`: the vector so far is the
first `i` raw values folded into `base` one at a time. -/
theorem extend_unique_loop_spec (raw : Slice Usize) (extended : alloc.vec.Vec Usize)
    (i : Usize) (base : List Usize)
    (hbound : base.length + raw.val.length ≤ Usize.max)
    (hi : i.val ≤ raw.val.length)
    (hext : extended.val = (raw.val.take i.val).foldl extendStep base) :
    sets.extend_unique_loop raw extended i ⦃ v => v.val = raw.val.foldl extendStep base ⦄ := by
  unfold sets.extend_unique_loop
  apply loop.spec_decr_nat
    (fun s : alloc.vec.Vec Usize × Usize => raw.val.length - s.2.val)
    (fun s : alloc.vec.Vec Usize × Usize => s.2.val ≤ raw.val.length ∧
      s.1.val = (raw.val.take s.2.val).foldl extendStep base)
  · rintro ⟨extended, i⟩ ⟨hi, hext⟩
    dsimp only at hi hext
    unfold sets.extend_unique_loop.body
    try dsimp only
    split_ifs with hlt
    · have hlt' : i.val < raw.val.length := by scalar_tac
      step as ⟨ x, hx ⟩
      apply WP.spec_bind (contains_spec _ x)
      intro b hb
      rw [deref_val] at hb
      have htake : raw.val.take (i.val + 1) = raw.val.take i.val ++ [x] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt', hx]
        rfl
      have hlen : extended.val.length < Usize.max := by
        have := foldl_extendStep_length base (raw.val.take i.val)
        rw [hext]
        simp only [List.length_take] at this
        omega
      split_ifs with hin
      · try simp only [bind_ok]
        apply WP.spec_bind (Usize.add_spec (by scalar_tac))
        intro i' hi'
        have hi'' : i'.val = i.val + 1 := by scalar_tac
        simp only [WP.spec_ok]
        and_intros
        all_goals try scalar_tac
        rw [hi'', htake, List.foldl_append, ← hext]
        simp [extendStep, hb.mp hin]
      · apply WP.spec_bind (alloc.vec.Vec.push_spec extended x hlen)
        intro extended' hextended'
        apply WP.spec_bind (Usize.add_spec (by scalar_tac))
        intro i' hi'
        have hi'' : i'.val = i.val + 1 := by scalar_tac
        simp only [WP.spec_ok]
        and_intros
        all_goals try scalar_tac
        rw [hi'', htake, List.foldl_append, ← hext, hextended']
        have : x ∉ extended.val := fun h => hin (hb.mpr h)
        simp [extendStep, this]
    · simp only [WP.spec_ok]
      have : i.val = raw.val.length := by scalar_tac
      rw [hext, this, List.take_length]
  · exact ⟨hi, hext⟩

/-- `extend_unique` folds every raw value into the given members. -/
theorem extend_unique_spec (members : alloc.vec.Vec Usize) (raw : Slice Usize)
    (hbound : members.val.length + raw.val.length ≤ Usize.max) :
    sets.extend_unique members raw ⦃ v => v.val = raw.val.foldl extendStep members.val ⦄ := by
  unfold sets.extend_unique
  exact extend_unique_loop_spec raw members 0#usize members.val hbound (by simp) (by simp)

theorem unique_length_le {α : Type} [DecidableEq α] (xs : List α) :
    (unique xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [unique]
  | cons x xs ih =>
    simp only [unique, List.length_cons]
    have := List.length_filter_le (fun y => decide (y ≠ x)) (unique xs)
    omega

/-- A01 normalization: the distinct values in first-occurrence order —
exactly the calculus's `unique`, so duplicate-free with the same members. -/
theorem normalize_spec (raw : Slice Usize) :
    sets.normalize raw ⦃ v =>
      v.val = unique raw.val ∧ v.val.Nodup ∧ ∀ x, x ∈ v.val ↔ x ∈ raw.val ⦄ := by
  unfold sets.normalize
  apply WP.spec_mono (extend_unique_spec _ raw (by simp))
  intro v hv
  have hu : v.val = unique raw.val := by
    rw [hv]
    have := foldl_extendStep_unique ([] : List Usize) raw.val
    simpa [unique] using this
  exact ⟨hu, hu ▸ unique_nodup _, fun x => by rw [hu, mem_unique]⟩

/-- A01 union: left order first, then the right's unseen values — the
calculus's `unique (left ++ right)` — with exactly the members of either
side. The precondition is that the two operands fit one `usize` length,
which any pair of in-memory slices of `usize` does. -/
theorem union_spec (left right : Slice Usize)
    (hbound : left.val.length + right.val.length ≤ Usize.max) :
    sets.union left right ⦃ v =>
      v.val = unique (left.val ++ right.val) ∧ v.val.Nodup ∧
      ∀ x, x ∈ v.val ↔ x ∈ left.val ∨ x ∈ right.val ⦄ := by
  unfold sets.union
  apply WP.spec_bind (normalize_spec left)
  intro n ⟨hn, _, _⟩
  have hb : n.val.length + right.val.length ≤ Usize.max := by
    have := unique_length_le left.val
    rw [hn]; omega
  apply WP.spec_mono (extend_unique_spec n right hb)
  intro v hv
  have hu : v.val = unique (left.val ++ right.val) := by
    rw [hv, hn, foldl_extendStep_unique]
  exact ⟨hu, hu ▸ unique_nodup _, fun x => by rw [hu, mem_unique, List.mem_append]⟩

/-- The selection loop from position `i`: kept so far are the first `i`
left values whose membership on the right equals `present`. -/
theorem select_loop_spec (left right : Slice Usize) (present : Bool)
    (kept : alloc.vec.Vec Usize) (i : Usize)
    (hi : i.val ≤ left.val.length)
    (hkept : kept.val = (left.val.take i.val).filter
      (fun x => decide (decide (x ∈ right.val) = present))) :
    sets.select_loop left right present kept i ⦃ v =>
      v.val = left.val.filter (fun x => decide (decide (x ∈ right.val) = present)) ⦄ := by
  unfold sets.select_loop
  apply loop.spec_decr_nat
    (fun s : alloc.vec.Vec Usize × Usize => left.val.length - s.2.val)
    (fun s : alloc.vec.Vec Usize × Usize => s.2.val ≤ left.val.length ∧
      s.1.val = (left.val.take s.2.val).filter
        (fun x => decide (decide (x ∈ right.val) = present)))
  · rintro ⟨kept, i⟩ ⟨hi, hkept⟩
    dsimp only at hi hkept
    unfold sets.select_loop.body
    try dsimp only
    split_ifs with hlt
    · have hlt' : i.val < left.val.length := by scalar_tac
      step as ⟨ x, hx ⟩
      apply WP.spec_bind (contains_spec right x)
      intro b hb
      have hbd : b = decide (x ∈ right.val) := by
        cases b <;> simp_all
      have htake : left.val.take (i.val + 1) = left.val.take i.val ++ [x] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt', hx]
        rfl
      have hlen : kept.val.length < Usize.max := by
        have := List.length_filter_le (fun x => decide (decide (x ∈ right.val) = present))
          (left.val.take i.val)
        have := left.property
        rw [hkept]
        simp only [List.length_take] at *
        scalar_tac
      split_ifs with hsel
      · apply WP.spec_bind (alloc.vec.Vec.push_spec kept x hlen)
        intro kept' hkept'
        apply WP.spec_bind (Usize.add_spec (by scalar_tac))
        intro i' hi'
        have hi'' : i'.val = i.val + 1 := by scalar_tac
        simp only [WP.spec_ok]
        and_intros
        all_goals try scalar_tac
        rw [hi'', htake, List.filter_append, hkept', hkept]
        simp [← hbd, hsel]
      · try simp only [bind_ok]
        apply WP.spec_bind (Usize.add_spec (by scalar_tac))
        intro i' hi'
        have hi'' : i'.val = i.val + 1 := by scalar_tac
        simp only [WP.spec_ok]
        and_intros
        all_goals try scalar_tac
        rw [hi'', htake, List.filter_append, hkept]
        simp [← hbd, hsel]
    · simp only [WP.spec_ok]
      have : i.val = left.val.length := by scalar_tac
      rw [hkept, this, List.take_length]
  · exact ⟨hi, hkept⟩

theorem select_spec (left right : Slice Usize) (present : Bool) :
    sets.select left right present ⦃ v =>
      v.val = left.val.filter (fun x => decide (decide (x ∈ right.val) = present)) ⦄ := by
  unfold sets.select
  exact select_loop_spec left right present _ 0#usize (by simp) (by simp)

/-- A01 intersection: the left values also on the right, in left order;
membership is exactly "in both", and a normalized left stays duplicate-free. -/
theorem intersection_spec (left right : Slice Usize) :
    sets.intersection left right ⦃ v =>
      v.val = left.val.filter (fun x => decide (x ∈ right.val)) ∧
      (∀ x, x ∈ v.val ↔ x ∈ left.val ∧ x ∈ right.val) ∧
      (left.val.Nodup → v.val.Nodup) ⦄ := by
  unfold sets.intersection
  apply WP.spec_mono (select_spec left right true)
  intro v hv
  have h : v.val = left.val.filter (fun x => decide (x ∈ right.val)) := by
    rw [hv]; simp
  refine ⟨h, fun x => by rw [h, List.mem_filter]; simp, fun hn => h ▸ hn.filter _⟩

/-- A01 difference: the left values not on the right, in left order;
membership is exactly "left and not right" — a removed value never survives. -/
theorem difference_spec (left right : Slice Usize) :
    sets.difference left right ⦃ v =>
      v.val = left.val.filter (fun x => decide (x ∉ right.val)) ∧
      (∀ x, x ∈ v.val ↔ x ∈ left.val ∧ x ∉ right.val) ∧
      (left.val.Nodup → v.val.Nodup) ⦄ := by
  unfold sets.difference
  apply WP.spec_mono (select_spec left right false)
  intro v hv
  have h : v.val = left.val.filter (fun x => decide (x ∉ right.val)) := by
    rw [hv]; simp
  refine ⟨h, fun x => by rw [h, List.mem_filter]; simp, fun hn => h ▸ hn.filter _⟩

/-- The answer of `subset`: `none` when every left value is on the right,
otherwise the first left position whose value is not. -/
def FirstMissing (left right : List Usize) : Option Usize → Prop
  | none => ∀ x ∈ left, x ∈ right
  | some p => ∃ h : p.val < left.length, left[p.val] ∉ right ∧
      ∀ j (hj : j < p.val), left[j]'(Nat.lt_trans hj h) ∈ right

/-- The subset loop from position `i`, knowing every earlier left value is
on the right. -/
theorem subset_loop_spec (left right : Slice Usize) (i : Usize)
    (hi : i.val ≤ left.val.length)
    (hprefix : ∀ j (h : j < left.val.length), j < i.val → left.val[j] ∈ right.val) :
    sets.subset_loop left right i ⦃ r => FirstMissing left.val right.val r ⦄ := by
  unfold sets.subset_loop
  apply loop.spec_decr_nat (fun i : Usize => left.val.length - i.val)
    (fun i : Usize => i.val ≤ left.val.length ∧
      ∀ j (h : j < left.val.length), j < i.val → left.val[j] ∈ right.val)
  · intro i ⟨hi, hprefix⟩
    unfold sets.subset_loop.body
    try dsimp only
    split_ifs with hlt
    · have hlt' : i.val < left.val.length := by scalar_tac
      step as ⟨ x, hx ⟩
      apply WP.spec_bind (contains_spec right x)
      intro b hb
      split_ifs with hin
      · apply WP.spec_bind (Usize.add_spec (by scalar_tac))
        intro i' hi'
        simp only [WP.spec_ok]
        and_intros
        all_goals try scalar_tac
        intro j hj hji
        by_cases hlt'' : j < i.val
        · exact hprefix j hj hlt''
        · have : j = i.val := by scalar_tac
          subst this
          rw [← hx]
          exact hb.mp hin
      · simp only [WP.spec_ok, FirstMissing]
        refine ⟨hlt', ?_, fun j hj => hprefix j _ hj⟩
        rw [← hx]
        exact fun h => hin (hb.mpr h)
    · simp only [WP.spec_ok, FirstMissing]
      intro x hmem
      obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hmem
      rw [← hjeq]
      exact hprefix j hj (by scalar_tac)
  · exact ⟨hi, hprefix⟩

/-- A03 inclusive subset with its faithful counterexample: `none` iff every
left value is on the right; otherwise the first left position that is not. -/
theorem subset_spec (left right : Slice Usize) :
    sets.subset left right ⦃ r => FirstMissing left.val right.val r ⦄ := by
  unfold sets.subset
  apply subset_loop_spec
  · simp
  · intro j _ hj; simp at hj

theorem firstMissing_none_iff (left right : List Usize) (r : Option Usize)
    (h : FirstMissing left right r) : r = none ↔ ∀ x ∈ left, x ∈ right := by
  cases r with
  | none => simpa [FirstMissing] using h
  | some p =>
    obtain ⟨hp, hmiss, _⟩ := h
    simp only [reduceCtorEq, false_iff]
    intro hall
    exact hmiss (hall _ (List.getElem_mem hp))

/-- Extensional equality: exactly the same members on both sides, whatever
the order. -/
theorem same_members_spec (left right : Slice Usize) :
    sets.same_members left right ⦃ r => r ↔ ∀ x, x ∈ left.val ↔ x ∈ right.val ⦄ := by
  unfold sets.same_members
  apply WP.spec_bind (subset_spec left right)
  intro o ho
  have hlr := firstMissing_none_iff _ _ _ ho
  cases o with
  | some p =>
    simp only [core.option.Option.is_none, Option.isNone_some, Bool.false_eq_true,
      ↓reduceIte, WP.spec_ok, false_iff]
    intro hall
    have := hlr.mpr (fun x hx => (hall x).mp hx)
    cases this
  | none =>
    simp only [core.option.Option.is_none, Option.isNone_none, ↓reduceIte]
    apply WP.spec_bind (subset_spec right left)
    intro o' ho'
    have hrl := firstMissing_none_iff _ _ _ ho'
    have hl := hlr.mp rfl
    cases o' with
    | some p =>
      simp only [Option.isNone_some, WP.spec_ok,
        Bool.false_eq_true, false_iff]
      intro hall
      have := hrl.mpr (fun x hx => (hall x).mpr hx)
      cases this
    | none =>
      simp only [Option.isNone_none, WP.spec_ok, true_iff]
      have hr := hrl.mp rfl
      exact fun x => ⟨hl x, hr x⟩

end Weft.Core
