import Weft.Logic
import Weft.Language.Core

namespace Weft.Language

/-!
# Surface-to-formula preservation (L02)

The only imports are the core-only Weft logical calculus and typed surface AST.
A pinned profile supplies signatures and an independent denotational meaning.
The theorem does NOT establish that this meaning is true of the external world,
that a citation is authorized/current, or that a profile was registered correctly.
Those are acquisition/profile/evidence obligations, not syntactic consequences.

An interner is partial: exhaustion or an uncaptured call fails elaboration. Its
contract distinguishes exact ground calls and explicitly relates their assigned
indices to the chosen valuation. No default atom or false value is synthesized.
L02 is conditional on this contract; a mismatching external valuation is not
silently accepted. All successful children are required, including Boolean
short-circuit cases, so missing fields cannot disappear behind `true or ...`.
-/

structure Interpretation (intern : GroundCall → Option Nat)
    (meaning : GroundCall → Bool) (valuation : Nat → Bool) : Prop where
  exactCalls : ∀ a b index, intern a = some index → intern b = some index → a = b
  realizes : ∀ call index, intern call = some index → valuation index = meaning call

def elaborate (env : Environment) (profile : Profile)
    (intern : GroundCall → Option Nat) : Surface → Option Weft.Logic.Formula
  | .boolean value => some (.literal value)
  | .equal left right => (compareTerms env left right).map Weft.Logic.Formula.literal
  | .notEqual left right =>
      (compareTerms env left right).map (fun value => .neg (.literal value))
  | .predicate name arguments =>
      match checkCall env profile name arguments with
      | none => none
      | some call => (intern call).map Weft.Logic.Formula.atom
  | .neg inner => (elaborate env profile intern inner).map Weft.Logic.Formula.neg
  | .conj left right => combine Weft.Logic.Formula.conj
      (elaborate env profile intern left) (elaborate env profile intern right)
  | .disj left right => combine Weft.Logic.Formula.disj
      (elaborate env profile intern left) (elaborate env profile intern right)

/-- L02: every successful elaboration has the independently defined source
meaning under every valuation realizing the explicit ground interpretation.
There is no checker/classifier premise, nor a definition of meaning via IR. -/
theorem elaborationSound (env : Environment) (profile : Profile)
    (intern : GroundCall → Option Nat) (meaning : GroundCall → Bool)
    (valuation : Nat → Bool) (interpretation : Interpretation intern meaning valuation)
    (surface : Surface) (formula : Weft.Logic.Formula)
    (success : elaborate env profile intern surface = some formula) :
    denote env profile meaning surface = some (Weft.Logic.evaluate valuation formula) := by
  induction surface generalizing formula with
  | boolean value =>
      have same : Weft.Logic.Formula.literal value = formula := by
        simpa [elaborate] using success
      subst formula
      rfl
  | equal left right =>
      cases checked : compareTerms env left right with
      | none => simp [elaborate, checked] at success
      | some value =>
          have same : Weft.Logic.Formula.literal value = formula := by
            simpa [elaborate, checked] using success
          subst formula
          simp [denote, checked, Weft.Logic.evaluate]
  | notEqual left right =>
      cases checked : compareTerms env left right with
      | none => simp [elaborate, checked] at success
      | some value =>
          have same : Weft.Logic.Formula.neg (.literal value) = formula := by
            simpa [elaborate, checked] using success
          subst formula
          simp [denote, checked, Weft.Logic.evaluate]
  | predicate name arguments =>
      cases checked : checkCall env profile name arguments with
      | none => simp [elaborate, checked] at success
      | some call =>
          cases captured : intern call with
          | none => simp [elaborate, checked, captured] at success
          | some index =>
              have same : Weft.Logic.Formula.atom index = formula := by
                simpa [elaborate, checked, captured] using success
              subst formula
              simp [denote, checked, Weft.Logic.evaluate,
                interpretation.realizes call index captured]
  | neg inner ih =>
      cases checked : elaborate env profile intern inner with
      | none => simp [elaborate, checked] at success
      | some child =>
          have same : Weft.Logic.Formula.neg child = formula := by
            simpa [elaborate, checked] using success
          subst formula
          simp [denote, ih child checked, Weft.Logic.evaluate]
  | conj left right ihLeft ihRight =>
      cases checkedLeft : elaborate env profile intern left with
      | none => simp [elaborate, checkedLeft, combine] at success
      | some leftFormula =>
          cases checkedRight : elaborate env profile intern right with
          | none => simp [elaborate, checkedLeft, checkedRight, combine] at success
          | some rightFormula =>
              have same : Weft.Logic.Formula.conj leftFormula rightFormula = formula := by
                simpa [elaborate, checkedLeft, checkedRight, combine] using success
              subst formula
              simp [denote, ihLeft leftFormula checkedLeft,
                ihRight rightFormula checkedRight, combine, Weft.Logic.evaluate]
  | disj left right ihLeft ihRight =>
      cases checkedLeft : elaborate env profile intern left with
      | none => simp [elaborate, checkedLeft, combine] at success
      | some leftFormula =>
          cases checkedRight : elaborate env profile intern right with
          | none => simp [elaborate, checkedLeft, checkedRight, combine] at success
          | some rightFormula =>
              have same : Weft.Logic.Formula.disj leftFormula rightFormula = formula := by
                simpa [elaborate, checkedLeft, checkedRight, combine] using success
              subst formula
              simp [denote, ihLeft leftFormula checkedLeft,
                ihRight rightFormula checkedRight, combine, Weft.Logic.evaluate]

/-- In particular, successful elaboration is never a missing source denotation. -/
theorem successfulElaborationDefined (env : Environment) (profile : Profile)
    (intern : GroundCall → Option Nat) (meaning : GroundCall → Bool)
    (valuation : Nat → Bool) (interpretation : Interpretation intern meaning valuation)
    (surface : Surface) (formula : Weft.Logic.Formula)
    (success : elaborate env profile intern surface = some formula) :
    denote env profile meaning surface ≠ none := by
  rw [elaborationSound env profile intern meaning valuation interpretation surface formula success]
  simp

end Weft.Language
