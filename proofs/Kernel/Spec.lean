import Aeneas

/-!
# Restated calculus specifications

The Weft calculus in `formal/` is pinned to Lean v4.21.0; this proof project
is pinned to the Aeneas toolchain (Lean v4.35.0), so it cannot import the
calculus. The definitions the kernel theorems are stated against are restated
here, verbatim in meaning, and named after their originals:

- `unique` is `Weft.Finite.Sets.unique` (`formal/Weft/Finite/Sets.lean`):
  first-occurrence deduplication, the normalization every captured set and
  every algebra result passes through (A01 display order).
- `verdictOf` is `Weft.Logic.verdictOf` (`formal/Weft/Logic/Classification.lean`):
  the verdict from the positive and negative polarity flags.

No theorem here is imported from, or claimed to refine, the calculus: the
restatement is reviewed, not machine-linked.
-/

namespace Weft.Core.Spec

/-- `Weft.Finite.Sets.unique`, restated. -/
def unique {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => x :: (unique xs).filter (fun y => decide (y ≠ x))

@[simp] theorem mem_unique {α : Type} [DecidableEq α] (a : α) (xs : List α) :
    a ∈ unique xs ↔ a ∈ xs := by
  induction xs with
  | nil => simp [unique]
  | cons x xs ih =>
    simp only [unique, List.mem_cons, List.mem_filter, ih, decide_eq_true_eq]
    by_cases h : a = x <;> simp [h]

theorem unique_nodup {α : Type} [DecidableEq α] (xs : List α) : (unique xs).Nodup := by
  induction xs with
  | nil => simp [unique]
  | cons x xs ih =>
    simp only [unique, List.nodup_cons, List.mem_filter, decide_eq_true_eq]
    exact ⟨by simp, ih.filter _⟩

/-- Appending one value to the input appends it to the normalization exactly
when it is new. This is the step the kernel's loop takes. -/
theorem unique_append_singleton {α : Type} [DecidableEq α] (xs : List α) (x : α) :
    unique (xs ++ [x]) = if x ∈ xs then unique xs else unique xs ++ [x] := by
  induction xs with
  | nil => simp [unique]
  | cons y ys ih =>
    simp only [List.cons_append, unique, ih, List.mem_cons]
    by_cases hx : x ∈ ys
    · simp [hx]
    · by_cases hxy : x = y
      · subst hxy
        simp [hx, List.filter_append]
      · simp [hx, hxy, List.filter_append]

/-- One step of the kernel's `extend_unique` loop. -/
def extendStep {α : Type} [DecidableEq α] (acc : List α) (x : α) : List α :=
  if x ∈ acc then acc else acc ++ [x]

/-- Extending a normalization with more input is the normalization of the
concatenation. -/
theorem foldl_extendStep_unique {α : Type} [DecidableEq α] (l xs : List α) :
    xs.foldl extendStep (unique l) = unique (l ++ xs) := by
  induction xs generalizing l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have : extendStep (unique l) x = unique (l ++ [x]) := by
      rw [unique_append_singleton]
      simp only [extendStep, mem_unique]
    rw [this, ih]
    simp

/-- `Weft.Logic.Verdict` restricted to complete evaluations. -/
inductive Verdict where
  | entailed | refuted | undetermined | inconsistent
  deriving DecidableEq

/-- `Weft.Logic.verdictOf`, restated. -/
def verdictOf : Bool → Bool → Verdict
  | false, false => .inconsistent
  | true, false => .entailed
  | false, true => .refuted
  | true, true => .undetermined

end Weft.Core.Spec
