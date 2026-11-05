import Std

namespace Weft.Logic

inductive Formula where
  | atom (id : Nat)
  | literal (value : Bool)
  | neg (inner : Formula)
  | conj (left right : Formula)
  | disj (left right : Formula)
  deriving DecidableEq, Repr

def evaluate (valuation : Nat → Bool) : Formula → Bool
  | .atom id => valuation id
  | .literal value => value
  | .neg inner => !(evaluate valuation inner)
  | .conj left right => evaluate valuation left && evaluate valuation right
  | .disj left right => evaluate valuation left || evaluate valuation right

def substitute (replacement : Nat → Formula) : Formula → Formula
  | .atom id => replacement id
  | .literal value => .literal value
  | .neg inner => .neg (substitute replacement inner)
  | .conj left right => .conj (substitute replacement left) (substitute replacement right)
  | .disj left right => .disj (substitute replacement left) (substitute replacement right)

/-- L03: simultaneous substitution changes the valuation, not formula meaning. -/
theorem substitutionSound (replacement : Nat → Formula) (valuation : Nat → Bool)
    (formula : Formula) :
    evaluate valuation (substitute replacement formula) =
      evaluate (fun id => evaluate valuation (replacement id)) formula := by
  induction formula with
  | atom id => rfl
  | literal value => rfl
  | neg inner ih => simp only [substitute, evaluate, ih]
  | conj left right ihl ihr => simp only [substitute, evaluate, ihl, ihr]
  | disj left right ihl ihr => simp only [substitute, evaluate, ihl, ihr]

def rename (renamingFn : Nat → Nat) (formula : Formula) : Formula :=
  substitute (fun id => .atom (renamingFn id)) formula

theorem renamingSound (renamingFn : Nat → Nat) (valuation : Nat → Bool)
    (formula : Formula) :
    evaluate valuation (rename renamingFn formula) =
      evaluate (fun id => valuation (renamingFn id)) formula :=
  substitutionSound _ _ _

def implication (left right : Formula) : Formula := .disj (.neg left) right

/-- L04's rule implication sugar. Actual typed equality/inequality lowering is
specified independently by Language.comparisonMeaningSound/inequalitySugarSound;
there is no unused second equality language in the logical IR. -/
theorem sugarSound (valuation : Nat → Bool) (left right : Formula) :
    evaluate valuation (implication left right) = true ↔
      (evaluate valuation left = true → evaluate valuation right = true) := by
  cases hl : evaluate valuation left <;> cases hr : evaluate valuation right <;>
    simp [implication, evaluate, hl, hr]

def inBounds (atomCount : Nat) : Formula → Bool
  | .atom id => decide (id < atomCount)
  | .literal _ => true
  | .neg inner => inBounds atomCount inner
  | .conj left right => inBounds atomCount left && inBounds atomCount right
  | .disj left right => inBounds atomCount left && inBounds atomCount right

def inputsInBounds (atomCount : Nat) (premises : List Formula) (query : Formula) : Bool :=
  premises.all (inBounds atomCount) && inBounds atomCount query

def InputsScoped (atomCount : Nat) (premises : List Formula) (query : Formula) : Prop :=
  inputsInBounds atomCount premises query = true

/-- Formula meaning depends only on the captured domain, never on its extension. -/
theorem evaluate_agrees (atomCount : Nat) (formula : Formula)
    (left right : Nat → Bool) (inScope : inBounds atomCount formula = true)
    (agree : ∀ id, id < atomCount → left id = right id) :
    evaluate left formula = evaluate right formula := by
  induction formula with
  | atom id =>
      exact agree id (of_decide_eq_true inScope)
  | literal value => rfl
  | neg inner ih =>
      simp only [evaluate, ih inScope]
  | conj lhs rhs ihl ihr =>
      have hs : inBounds atomCount lhs = true ∧ inBounds atomCount rhs = true := by
        simpa only [inBounds, Bool.and_eq_true] using inScope
      simp only [evaluate, ihl hs.1, ihr hs.2]
  | disj lhs rhs ihl ihr =>
      have hs : inBounds atomCount lhs = true ∧ inBounds atomCount rhs = true := by
        simpa only [inBounds, Bool.and_eq_true] using inScope
      simp only [evaluate, ihl hs.1, ihr hs.2]

/-- Denotation of premises, independent of enumeration and the checker. -/
def PremisesHold (premises : List Formula) (valuation : Nat → Bool) : Prop :=
  ∀ formula ∈ premises, evaluate valuation formula = true

inductive Verdict where
  | entailed | refuted | undetermined | inconsistent | unknown
  deriving DecidableEq, Repr

end Weft.Logic
