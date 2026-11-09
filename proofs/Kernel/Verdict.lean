import Extracted.WeftCore
import Kernel.Spec

/-!
# Check classification over a complete finite trace

Theorems over the Aeneas translation of `weft_core::verdict`
(`Extracted/WeftCore.lean`), the verdict `weft_kernel`'s evaluator returns.
`verdict_of` is the calculus's `verdictOf`, and `classify` computes the two
polarity flags over the trace, so each verdict means what the calculus's
`VerdictMeaning` says, read over the rows:

- entailed iff some row is a premise model and the query holds in every one;
- refuted iff some row is a premise model and the query fails in every one;
- undetermined iff premise models of both polarities exist;
- inconsistent premises iff no row is a premise model.

That the rows are exactly every valuation of the active atoms, and that each
row's two Booleans are the premises' and query's values there, is the
evaluator's obligation (tests and the Lean/Rust differential), not a theorem
here.
-/

open Aeneas Aeneas.Std Result
open weft_core

namespace Weft.Core

/-- A premise model where the query holds. -/
def Supports (row : verdict.TraceRow) : Prop := row.premises_hold ∧ row.query

instance : DecidablePred Supports := fun row => by unfold Supports; infer_instance

/-- A premise model where the query fails. -/
def Refutes (row : verdict.TraceRow) : Prop := row.premises_hold ∧ ¬ row.query

instance : DecidablePred Refutes := fun row => by unfold Refutes; infer_instance

/-- The kernel verdict for each calculus verdict. -/
def ofSpec : Spec.Verdict → verdict.LogicalVerdict
  | .entailed => .Entailed
  | .refuted => .Refuted
  | .undetermined => .Undetermined
  | .inconsistent => .InconsistentPremises

/-- Each row has exactly one role: supporting, refuting or excluded. -/
theorem role_spec (row : verdict.TraceRow) :
    verdict.role row ⦃ r =>
      (r = .Supporting ↔ Supports row) ∧
      (r = .Refuting ↔ Refutes row) ∧
      (r = .Excluded ↔ ¬ row.premises_hold) ⦄ := by
  unfold verdict.role
  rcases row with ⟨valuation, premises, query⟩
  cases premises <;> cases query <;> simp [Supports, Refutes]

/-- `verdict_of` is the calculus's `verdictOf`. -/
theorem verdict_of_spec (supporting refuting : Bool) :
    verdict.verdict_of supporting refuting ⦃ v =>
      v = ofSpec (Spec.verdictOf supporting refuting) ⦄ := by
  unfold verdict.verdict_of
  cases supporting <;> cases refuting <;> simp [Spec.verdictOf, ofSpec]

/-- The classification loop from position `i`: the flags record whether a
supporting / refuting row occurs before `i`. -/
theorem classify_loop_spec (rows : Slice verdict.TraceRow) (supporting refuting : Bool)
    (i : Usize) (hi : i.val ≤ rows.val.length)
    (hs : supporting = true ↔ ∃ (j : Nat) (h : j < rows.val.length), j < i.val ∧ Supports rows.val[j])
    (hr : refuting = true ↔ ∃ (j : Nat) (h : j < rows.val.length), j < i.val ∧ Refutes rows.val[j]) :
    verdict.classify_loop rows supporting refuting i ⦃ flags =>
      (flags.1 = true ↔ ∃ row ∈ rows.val, Supports row) ∧
      (flags.2 = true ↔ ∃ row ∈ rows.val, Refutes row) ⦄ := by
  unfold verdict.classify_loop
  apply loop.spec_decr_nat
    (fun s : Bool × Bool × Usize => rows.val.length - s.2.2.val)
    (fun s : Bool × Bool × Usize => s.2.2.val ≤ rows.val.length ∧
      (s.1 = true ↔ ∃ (j : Nat) (h : j < rows.val.length), j < s.2.2.val ∧ Supports rows.val[j]) ∧
      (s.2.1 = true ↔ ∃ (j : Nat) (h : j < rows.val.length), j < s.2.2.val ∧ Refutes rows.val[j]))
  · rintro ⟨supporting, refuting, i⟩ ⟨hi, hs, hr⟩
    dsimp only at hi hs hr
    unfold verdict.classify_loop.body
    try dsimp only
    split_ifs with hlt
    · have hlt' : i.val < rows.val.length := by scalar_tac
      step as ⟨ row, hrow ⟩
      apply WP.spec_bind (role_spec row)
      intro role ⟨hsup, href, hexc⟩
      -- Extending the prefix by position `i` adds exactly that row.
      have hext : ∀ P : verdict.TraceRow → Prop,
          (∃ (j : Nat) (h : j < rows.val.length), j < i.val + 1 ∧ P rows.val[j]) ↔
          ((∃ (j : Nat) (h : j < rows.val.length), j < i.val ∧ P rows.val[j]) ∨ P row) := by
        intro P
        constructor
        · rintro ⟨j, hj, hji, hp⟩
          by_cases hlt'' : j < i.val
          · exact Or.inl ⟨j, hj, hlt'', hp⟩
          · have : j = i.val := by omega
            subst this
            exact Or.inr (hrow ▸ hp)
        · rintro (⟨j, hj, hji, hp⟩ | hp)
          · exact ⟨j, hj, by omega, hp⟩
          · exact ⟨i.val, hlt', by omega, hrow ▸ hp⟩
      cases role
      all_goals
        simp only [bind_ok]
        step as ⟨ i', hi' ⟩
        have hi'' : i'.val = i.val + 1 := by scalar_tac
        and_intros
        all_goals try scalar_tac
        all_goals rw [hi'', hext]
      · -- Supporting: the supporting flag is set
        have hS : Supports row := hsup.mp rfl
        simp [hS]
      · -- Supporting: the refuting flag is unchanged
        have hR : ¬ Refutes row := fun h => by
          have := hsup.mp rfl; simp [Supports, Refutes] at this h; simp_all
        simp [hR, hr]
      · -- Refuting: the supporting flag is unchanged
        have hS : ¬ Supports row := fun h => by
          have := href.mp rfl; simp [Supports, Refutes] at this h; simp_all
        simp [hS, hs]
      · -- Refuting: the refuting flag is set
        have hR : Refutes row := href.mp rfl
        simp [hR]
      · -- Excluded: neither flag changes
        have hS : ¬ Supports row := fun h => (hexc.mp rfl) h.1
        simp [hS, hs]
      · have hR : ¬ Refutes row := fun h => (hexc.mp rfl) h.1
        simp [hR, hr]
    · simp only [WP.spec_ok]
      have : i.val = rows.val.length := by scalar_tac
      rw [this] at hs hr
      refine ⟨hs.trans ?_, hr.trans ?_⟩
      all_goals
        constructor
        · rintro ⟨j, hj, _, hp⟩; exact ⟨_, List.getElem_mem hj, hp⟩
        · rintro ⟨row, hmem, hp⟩
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
          exact ⟨j, hj, hj, hp⟩
  · exact ⟨hi, hs, hr⟩

/-- `classify` is `verdictOf` over the two polarity flags of the trace. -/
theorem classify_spec (rows : Slice verdict.TraceRow) :
    verdict.classify rows ⦃ v =>
      v = ofSpec (Spec.verdictOf (decide (∃ row ∈ rows.val, Supports row))
        (decide (∃ row ∈ rows.val, Refutes row))) ⦄ := by
  unfold verdict.classify
  apply WP.spec_bind (classify_loop_spec rows false false 0#usize (by simp) (by simp) (by simp))
  rintro ⟨s, r⟩ ⟨hs, hr⟩
  apply WP.spec_mono (verdict_of_spec s r)
  intro v hv
  rw [hv]
  congr
  · cases s <;> simp_all
  · cases r <;> simp_all

/-- Classification by cases on the two polarities. -/
theorem classify_cases (rows : Slice verdict.TraceRow) :
    verdict.classify rows ⦃ v =>
      (v = .Entailed ↔ (∃ row ∈ rows.val, Supports row) ∧ ¬ ∃ row ∈ rows.val, Refutes row) ∧
      (v = .Refuted ↔ (¬ ∃ row ∈ rows.val, Supports row) ∧ ∃ row ∈ rows.val, Refutes row) ∧
      (v = .Undetermined ↔ (∃ row ∈ rows.val, Supports row) ∧ ∃ row ∈ rows.val, Refutes row) ∧
      (v = .InconsistentPremises ↔
        (¬ ∃ row ∈ rows.val, Supports row) ∧ ¬ ∃ row ∈ rows.val, Refutes row) ⦄ := by
  apply WP.spec_mono (classify_spec rows)
  intro v hv
  subst hv
  by_cases hS : ∃ row ∈ rows.val, Supports row <;>
    by_cases hR : ∃ row ∈ rows.val, Refutes row <;>
    simp [hS, hR, Spec.verdictOf, ofSpec]

/-- Entailed iff some row is a premise model and the query holds in every
premise model (`VerdictMeaning .entailed`, over the trace). -/
theorem classify_entailed_iff (rows : Slice verdict.TraceRow) :
    verdict.classify rows ⦃ v =>
      v = .Entailed ↔ (∃ row ∈ rows.val, row.premises_hold) ∧
        ∀ row ∈ rows.val, row.premises_hold → row.query ⦄ := by
  apply WP.spec_mono (classify_cases rows)
  rintro v ⟨h, -, -, -⟩
  rw [h]
  simp only [Supports, Refutes]
  constructor
  · rintro ⟨⟨row, hm, hp, _⟩, hn⟩
    exact ⟨⟨row, hm, hp⟩, fun r hr hp => by
      by_contra hq; exact hn ⟨r, hr, hp, by simpa using hq⟩⟩
  · rintro ⟨⟨row, hm, hp⟩, hall⟩
    exact ⟨⟨row, hm, hp, hall row hm hp⟩, fun ⟨r, hr, hp, hq⟩ => by
      have := hall r hr hp; simp_all⟩

/-- Refuted iff some row is a premise model and the query fails in every
premise model (`VerdictMeaning .refuted`, over the trace). -/
theorem classify_refuted_iff (rows : Slice verdict.TraceRow) :
    verdict.classify rows ⦃ v =>
      v = .Refuted ↔ (∃ row ∈ rows.val, row.premises_hold) ∧
        ∀ row ∈ rows.val, row.premises_hold → ¬ row.query ⦄ := by
  apply WP.spec_mono (classify_cases rows)
  rintro v ⟨-, h, -, -⟩
  rw [h]
  simp only [Supports, Refutes]
  constructor
  · rintro ⟨hn, ⟨row, hm, hp, _⟩⟩
    exact ⟨⟨row, hm, hp⟩, fun r hr hp hq => hn ⟨r, hr, hp, hq⟩⟩
  · rintro ⟨⟨row, hm, hp⟩, hall⟩
    exact ⟨fun ⟨r, hr, hp, hq⟩ => hall r hr hp hq, ⟨row, hm, hp, hall row hm hp⟩⟩

/-- Undetermined iff premise models of both polarities exist
(`VerdictMeaning .undetermined`, over the trace). -/
theorem classify_undetermined_iff (rows : Slice verdict.TraceRow) :
    verdict.classify rows ⦃ v =>
      v = .Undetermined ↔ (∃ row ∈ rows.val, row.premises_hold ∧ row.query) ∧
        ∃ row ∈ rows.val, row.premises_hold ∧ ¬ row.query ⦄ := by
  apply WP.spec_mono (classify_cases rows)
  rintro v ⟨-, -, h, -⟩
  rw [h]
  rfl

/-- Inconsistent premises iff no row is a premise model
(`VerdictMeaning .inconsistent`, over the trace): an empty or premise-free
trace is never entailed. -/
theorem classify_inconsistent_iff (rows : Slice verdict.TraceRow) :
    verdict.classify rows ⦃ v =>
      v = .InconsistentPremises ↔ ∀ row ∈ rows.val, ¬ row.premises_hold ⦄ := by
  apply WP.spec_mono (classify_cases rows)
  rintro v ⟨-, -, -, h⟩
  rw [h]
  simp only [Supports, Refutes]
  constructor
  · rintro ⟨hs, hr⟩ row hm hp
    by_cases hq : row.query
    · exact hs ⟨row, hm, hp, hq⟩
    · exact hr ⟨row, hm, hp, hq⟩
  · intro hall
    exact ⟨fun ⟨r, hr, hp, _⟩ => hall r hr hp, fun ⟨r, hr, hp, _⟩ => hall r hr hp⟩

end Weft.Core
