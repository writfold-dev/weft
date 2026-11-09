import Extracted.WeftCore

/-!
# Reuse scope equality

Theorems over the Aeneas translation of `weft_core::scope`
(`Extracted/WeftCore.lean`), the decision `weft reuse` calls. The wire layer
builds one comparison per recorded scope field (source digest, evaluator
profile, report kind, each evaluation bound) and refuses with a named
difference for every position `refusals` returns. Proved here:

- byte equality is exact, length included (`same_bytes_spec`);
- `refusals` returns exactly the unsatisfied positions, ascending
  (`refusals_spec`);
- reuse is admitted iff every comparison is satisfied (`reusable_iff`), so
  any difference in a field that must be equal is refused
  (`refuses_any_difference`).

Which fields are compared, and their byte encodings, are the wire layer's
(tests and CLI scenarios), not a theorem here.
-/

open Aeneas Aeneas.Std Result
open weft_core

namespace Weft.Core

/-- The byte loop of `same_bytes` from position `i`: equality of two
equal-length slices, given the bytes before `i` agree. -/
theorem same_bytes_loop_spec (a b : Slice U8) (i : Usize)
    (hlen : a.val.length = b.val.length) (hi : i.val ≤ a.val.length)
    (hprefix : ∀ j, j < i.val → a.val[j]? = b.val[j]?) :
    scope.same_bytes_loop a b i ⦃ r => r ↔ a.val = b.val ⦄ := by
  unfold scope.same_bytes_loop
  apply loop.spec_decr_nat (fun i : Usize => a.val.length - i.val)
    (fun i : Usize => i.val ≤ a.val.length ∧ ∀ j, j < i.val → a.val[j]? = b.val[j]?)
  · intro i ⟨hi, hprefix⟩
    unfold scope.same_bytes_loop.body
    try dsimp only
    split_ifs with hlt
    · have hlt' : i.val < a.val.length := by scalar_tac
      step as ⟨ x, hx ⟩
      step as ⟨ y, hy ⟩
      split_ifs with hne
      · simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
        intro heq
        rw [bne_iff_ne] at hne
        apply hne
        rw [hx, hy]
        exact List.getElem_of_eq heq _
      · rw [bne_iff_ne, not_not] at hne
        apply WP.spec_bind (Usize.add_spec (by scalar_tac))
        intro i' hi'
        simp only [WP.spec_ok]
        and_intros
        all_goals try scalar_tac
        intro j hj
        by_cases hji : j < i.val
        · exact hprefix j hji
        · have : j = i.val := by scalar_tac
          subst this
          rw [List.getElem?_eq_getElem (by scalar_tac), List.getElem?_eq_getElem (by scalar_tac),
            ← hx, ← hy, hne]
    · simp only [WP.spec_ok, true_iff]
      apply List.ext_getElem?
      intro j
      by_cases hj : j < a.val.length
      · exact hprefix j (by scalar_tac)
      · rw [List.getElem?_eq_none (by scalar_tac), List.getElem?_eq_none (by scalar_tac)]
  · exact ⟨hi, hprefix⟩

/-- `same_bytes` is byte-exact equality, length included: no prefix, no
truncation. -/
theorem same_bytes_spec (a b : Slice U8) :
    scope.same_bytes a b ⦃ r => r ↔ a.val = b.val ⦄ := by
  unfold scope.same_bytes
  dsimp only
  split_ifs with hne
  · simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    intro h
    rw [bne_iff_ne] at hne
    apply hne
    apply UScalar.eq_of_val_eq
    simp [h]
  · apply same_bytes_loop_spec
    · rw [bne_iff_ne, not_not] at hne
      have := congrArg UScalar.val hne
      simpa [Slice.len_val] using this
    · simp
    · intro j hj; simp at hj

/-- When one comparison holds: equal bytes for `Equal`, different bytes for
`Unequal`. -/
def Satisfied (c : scope.Comparison) : Prop :=
  match c.requirement with
  | .Equal => c.recorded.val = c.required.val
  | .Unequal => c.recorded.val ≠ c.required.val

instance : DecidablePred Satisfied := fun c => by
  unfold Satisfied; cases c.requirement <;> infer_instance

/-- `satisfied` decides `Satisfied`. -/
theorem satisfied_spec (c : scope.Comparison) :
    scope.satisfied c ⦃ r => r ↔ Satisfied c ⦄ := by
  unfold scope.satisfied
  apply WP.spec_bind (same_bytes_spec _ _)
  intro equal hequal
  simp only [alloc.vec.Vec.deref, Slice.from_val] at hequal
  rcases c with ⟨requirement, recorded, required⟩
  cases requirement <;> simp_all [Satisfied]

/-- The positions below `n` whose comparison is not satisfied, ascending. -/
def refusedBelow (cs : List scope.Comparison) (n : Nat) : List Nat :=
  (List.range n).filter (fun j => decide (∃ c, cs[j]? = some c ∧ ¬ Satisfied c))

/-- The refusal loop from position `i`: the refusals so far are exactly the
unsatisfied positions below `i`. -/
theorem refusals_loop_spec (cs : Slice scope.Comparison) (refused : alloc.vec.Vec Usize)
    (i : Usize) (hi : i.val ≤ cs.val.length)
    (hrefused : refused.val.map (·.val) = refusedBelow cs.val i.val) :
    scope.refusals_loop cs refused i ⦃ v =>
      v.val.map (·.val) = refusedBelow cs.val cs.val.length ⦄ := by
  unfold scope.refusals_loop
  apply loop.spec_decr_nat
    (fun s : alloc.vec.Vec Usize × Usize => cs.val.length - s.2.val)
    (fun s : alloc.vec.Vec Usize × Usize => s.2.val ≤ cs.val.length ∧
      s.1.val.map (·.val) = refusedBelow cs.val s.2.val)
  · rintro ⟨refused, i⟩ ⟨hi, hrefused⟩
    dsimp only at hi hrefused
    unfold scope.refusals_loop.body
    try dsimp only
    split_ifs with hlt
    · have hlt' : i.val < cs.val.length := by scalar_tac
      step as ⟨ c, hc ⟩
      apply WP.spec_bind (satisfied_spec c)
      intro b hb
      have hci : cs.val[i.val]? = some c := by
        rw [List.getElem?_eq_getElem hlt', hc]
      have hstep : refusedBelow cs.val (i.val + 1) =
          refusedBelow cs.val i.val ++ (if Satisfied c then [] else [i.val]) := by
        unfold refusedBelow
        rw [List.range_succ, List.filter_append]
        congr 1
        by_cases hs : Satisfied c <;> simp [hci, hs]
      have hlen : refused.val.length < Usize.max := by
        have h1 := congrArg List.length hrefused
        have h2 : (refusedBelow cs.val i.val).length ≤ i.val := by
          unfold refusedBelow
          exact (List.length_filter_le _ _).trans (by simp)
        have := cs.property
        simp only [List.length_map] at h1
        scalar_tac
      split_ifs with hsat
      · try simp only [bind_ok]
        apply WP.spec_bind (Usize.add_spec (by scalar_tac))
        intro i' hi'
        have hi'' : i'.val = i.val + 1 := by scalar_tac
        simp only [WP.spec_ok]
        and_intros
        -- `scalar_tac`'s simp preprocessing closes the list equation from
        -- `hstep`, `hrefused` and `hb`/`hsat`.
        all_goals try scalar_tac
      · apply WP.spec_bind (alloc.vec.Vec.push_spec refused i hlen)
        intro refused' hrefused'
        apply WP.spec_bind (Usize.add_spec (by scalar_tac))
        intro i' hi'
        have hi'' : i'.val = i.val + 1 := by scalar_tac
        simp only [WP.spec_ok]
        and_intros
        all_goals try scalar_tac
        rw [hi'', hstep, ← hrefused, hrefused']
        have : ¬ Satisfied c := fun h => hsat (hb.mpr h)
        simp [this]
    · simp only [WP.spec_ok]
      have : i.val = cs.val.length := by scalar_tac
      rw [hrefused, this]
  · exact ⟨hi, hrefused⟩

/-- `refusals` returns exactly the unsatisfied positions, ascending. -/
theorem refusals_spec (cs : Slice scope.Comparison) :
    scope.refusals cs ⦃ v => v.val.map (·.val) = refusedBelow cs.val cs.val.length ⦄ := by
  unfold scope.refusals
  apply refusals_loop_spec
  · simp
  · simp [refusedBelow]

/-- Reuse is admitted (no refusal) iff every comparison is satisfied. -/
theorem reusable_iff (cs : Slice scope.Comparison) :
    scope.refusals cs ⦃ v => v.val = [] ↔ ∀ c ∈ cs.val, Satisfied c ⦄ := by
  apply WP.spec_mono (refusals_spec cs)
  intro v hv
  rw [← List.map_eq_nil_iff (f := (·.val)), hv, refusedBelow, List.filter_eq_nil_iff]
  constructor
  · intro h c hc
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    have := h j (List.mem_range.mpr hj)
    by_contra hns
    exact this (by simp only [decide_eq_true_eq]; exact ⟨_, List.getElem?_eq_getElem hj, hns⟩)
  · intro h j _
    simp only [decide_eq_true_eq, not_exists, not_and, not_not]
    intro c hc
    exact h c (List.mem_of_getElem? hc)

/-- Reuse refuses any difference in a field that must be equal: one
differing byte, or a differing length, anywhere in the scope is a refusal. -/
theorem refuses_any_difference (cs : Slice scope.Comparison)
    (hdiff : ∃ c ∈ cs.val, c.requirement = .Equal ∧ c.recorded.val ≠ c.required.val) :
    scope.refusals cs ⦃ v => v.val ≠ [] ⦄ := by
  apply WP.spec_mono (reusable_iff cs)
  intro v hv hnil
  obtain ⟨c, hc, hreq, hne⟩ := hdiff
  have := hv.mp hnil c hc
  simp only [Satisfied, hreq] at this
  exact hne this

end Weft.Core
