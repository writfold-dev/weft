import Weft.Logic.Syntax

namespace Weft.Logic

/-- A finite valuation is valid exactly when it assigns every declared atom once. -/
def ValidValuation (atomCount : Nat) (values : List Bool) : Prop :=
  values.length = atomCount

/-- The arbitrary outside-domain extension is used only after scope validation.
`evaluate_agrees` proves that its outside-domain values cannot affect meaning. -/
def extend : List Bool → Nat → Bool
  | [], _ => false
  | value :: _, 0 => value
  | _ :: values, id + 1 => extend values id

/-- One recursive enumeration is shared by the two disjoint Boolean extensions. -/
def valuations : Nat → List (List Bool)
  | 0 => [[]]
  | atomCount + 1 =>
      let smaller := valuations atomCount
      smaller.map (false :: ·) ++ smaller.map (true :: ·)

theorem valuation_mem_iff (atomCount : Nat) (values : List Bool) :
    values ∈ valuations atomCount ↔ ValidValuation atomCount values := by
  induction atomCount generalizing values with
  | zero =>
      cases values <;> simp [valuations, ValidValuation]
  | succ atomCount ih =>
      cases values with
      | nil => simp [valuations, ValidValuation]
      | cons value values =>
          cases value <;>
            simp [valuations, List.mem_map, ih, ValidValuation]

/-- L05: every length-n Boolean valuation appears, with no completeness assumption. -/
theorem valuationsComplete (atomCount : Nat) (values : List Bool)
    (valid : ValidValuation atomCount values) : values ∈ valuations atomCount :=
  (valuation_mem_iff atomCount values).mpr valid

/-- Budget units are complete valuation checks, including the unique empty valuation. -/
def requiredBudget : Nat → Nat
  | 0 => 1
  | atomCount + 1 => 2 * requiredBudget atomCount

theorem valuationsLength (atomCount : Nat) :
    (valuations atomCount).length = requiredBudget atomCount := by
  induction atomCount with
  | zero => rfl
  | succ atomCount ih =>
      simp [valuations, requiredBudget, ih, Nat.two_mul]

theorem requiredBudget_pow (atomCount : Nat) : requiredBudget atomCount = 2 ^ atomCount := by
  induction atomCount with
  | zero => rfl
  | succ atomCount ih => simp [requiredBudget, ih, Nat.pow_succ, Nat.mul_comm]

/-- Capture an arbitrary mathematical valuation, not just an enumerated one. -/
def capture (valuation : Nat → Bool) : Nat → List Bool
  | 0 => []
  | atomCount + 1 => valuation 0 :: capture (fun id => valuation (id + 1)) atomCount

theorem capture_valid (valuation : Nat → Bool) (atomCount : Nat) :
    ValidValuation atomCount (capture valuation atomCount) := by
  induction atomCount generalizing valuation with
  | zero => rfl
  | succ atomCount ih =>
      simpa [ValidValuation, capture] using congrArg Nat.succ (ih (fun id => valuation (id + 1)))

theorem capture_agrees (valuation : Nat → Bool) (atomCount id : Nat)
    (bound : id < atomCount) : extend (capture valuation atomCount) id = valuation id := by
  induction atomCount generalizing valuation id with
  | zero => exact False.elim (Nat.not_lt_zero id bound)
  | succ atomCount ih =>
      cases id with
      | zero => rfl
      | succ id =>
          exact ih (fun i => valuation (i + 1)) id (Nat.lt_of_succ_lt_succ bound)

theorem capture_evaluate (valuation : Nat → Bool) (atomCount : Nat) (formula : Formula)
    (inScope : inBounds atomCount formula = true) :
    evaluate (extend (capture valuation atomCount)) formula = evaluate valuation formula :=
  evaluate_agrees atomCount formula _ _ inScope (capture_agrees valuation atomCount)

/-- Every unrestricted mathematical valuation has an enumerated representative. -/
theorem valuationsRepresent (atomCount : Nat) (valuation : Nat → Bool) :
    ∃ values ∈ valuations atomCount,
      ∀ formula, inBounds atomCount formula = true →
        evaluate (extend values) formula = evaluate valuation formula := by
  exact ⟨capture valuation atomCount, valuationsComplete _ _ (capture_valid _ _),
    capture_evaluate valuation atomCount⟩

end Weft.Logic
