import Weft.Finite.CaptureBudget
import Weft.Finite.Semantics

namespace Weft.Finite.Lowering
open Weft.Language Weft.Logic Weft.Finite.Syntax Weft.Finite.Sets Weft.Finite.Semantics

mutual
  /-- Checked derivation: no arbitrary list of answers can inhabit this interface.
  The atom proof records actual old-calculus elaboration; every quantified child
  is indexed by the exact body and its hygienically extended environment. -/
  inductive Expansion (ctx : Context) (intern : GroundCall → Option Nat) : Env → Expr → Type where
    | atom {env atom} (resolved : ResolvedAtom) (formula : Formula)
        (captured : resolveAtom ctx env atom = some resolved)
        (checked : Typing.checkAtom ctx (types env) atom = true)
        (lowered : Language.elaborate ctx.legacy ctx.profile intern resolved.surface = some formula) :
        Expansion ctx intern env (.atom atom)
    | neg {env body} (child : Expansion ctx intern env body) : Expansion ctx intern env (.neg body)
    | conj {env a b} (left : Expansion ctx intern env a) (right : Expansion ctx intern env b) :
        Expansion ctx intern env (.conj a b)
    | disj {env a b} (left : Expansion ctx intern env a) (right : Expansion ctx intern env b) :
        Expansion ctx intern env (.disj a b)
    | all {env domain body} (set : CapturedSet)
        (captured : evalSet ctx env domain = some set)
        (checked : Typing.check ctx (types env) (.all domain body) = true)
        (children : Instances ctx intern env body set.members) :
        Expansion ctx intern env (.all domain body)
    | any {env domain body} (set : CapturedSet)
        (captured : evalSet ctx env domain = some set)
        (checked : Typing.check ctx (types env) (.any domain body) = true)
        (children : Instances ctx intern env body set.members) :
        Expansion ctx intern env (.any domain body)
  inductive Instances (ctx : Context) (intern : GroundCall → Option Nat) :
      Env → Expr → List Member → Type where
    | nil {env : Env} {body : Expr} : Instances ctx intern env body []
    | cons {env : Env} {body : Expr} {rest : List Member} (member : Member)
        (child : Expansion ctx intern (push member env) body)
        (tail : Instances ctx intern env body rest) : Instances ctx intern env body (member :: rest)
end

mutual
  def Expansion.formula {ctx intern env expr} : Expansion ctx intern env expr → Formula
    | .atom _ formula _ _ _ => formula
    | .neg child => .neg child.formula
    | .conj left right => .conj left.formula right.formula
    | .disj left right => .disj left.formula right.formula
    | .all _ _ _ children => children.allFormula
    | .any _ _ _ children => children.anyFormula
  def Instances.allFormula {ctx intern env body members} : Instances ctx intern env body members → Formula
    | .nil => .literal true
    | .cons _ child tail => .conj child.formula tail.allFormula
  def Instances.anyFormula {ctx intern env body members} : Instances ctx intern env body members → Formula
    | .nil => .literal false
    | .cons _ child tail => .disj child.formula tail.anyFormula
end

mutual
  def Expansion.origins {ctx intern env expr} : Expansion ctx intern env expr → List Weft.Grounding.Binding
    | .atom resolved _ _ _ _ => resolved.origins
    | .neg child => child.origins
    | .conj left right | .disj left right => left.origins ++ right.origins
    | .all set _ _ children | .any set _ _ children => set.origins ++ children.origins
  def Instances.origins {ctx intern env body members} : Instances ctx intern env body members → List Weft.Grounding.Binding
    | .nil => []
    | .cons member child tail => member.origins ++ child.origins ++ tail.origins
end

mutual
  def Expansion.cost {ctx intern env expr} : Expansion ctx intern env expr → Nat
    | .atom _ _ _ _ _ => 1
    | .neg child => 1 + child.cost
    | .conj left right | .disj left right => 1 + left.cost + right.cost
    | .all _ _ _ children | .any _ _ _ children => 1 + children.cost
  def Instances.cost {ctx intern env body members} : Instances ctx intern env body members → Nat
    | .nil => 0
    | .cons _ child tail => child.cost + tail.cost
end

/-- A complete result and the actual residual admission budget. The proof is
erased; `remaining` is the state threaded by the executable computation. -/
structure WorkResult (α : Type) (budget : Nat) where
  value : α
  remaining : Nat
  decreasing : remaining ≤ budget

def WorkResult.used {α : Type} {budget : Nat} (result : WorkResult α budget) : Nat :=
  budget - result.remaining

/-- Structural admission accounting, not valuation fuel, serialized byte limits,
or a primitive-step/wall-clock bound for normalization and scalar elaboration. -/
abbrev Work (α : Type) := (budget : Nat) → Option (WorkResult α budget)

namespace Work
variable {α β : Type}

def pure (value : α) : Work α := fun budget => some ⟨value, budget, Nat.le_refl _⟩

/-- Destructure successful records before threading state. Keeping the whole
proof-carrying record behind each value/remainder projection duplicates that
record's unreduced computation during kernel reduction of nested binds. The
certificates are still retained, but only their proof fields are composed. -/
def bind (first : Work α) (next : α → Work β) : Work β := fun budget =>
  match first budget with
  | none => none
  | some ⟨value, remaining, decreasing⟩ =>
      match next value remaining with
      | none => none
      | some ⟨result, rest, decreases⟩ =>
          some ⟨result, rest, Nat.le_trans decreases decreasing⟩

def fail : Work α := fun _ => none

/-- The semantic equation is a proof-only field, never an evaluator replay. -/
def capture {meaning : Option α} (program : CaptureBudget.Program meaning) :
    Work {value : α // meaning = some value} := fun budget =>
  match success : program.run budget with
  | none => none
  | some (value, remaining) =>
      some ⟨⟨value, program.sound success⟩, remaining, program.decreasing success⟩

def spend (amount : Nat) : Work Unit :=
  bind (capture (CaptureBudget.spend amount)) (fun _ => pure ())

/-- Executable sequencing passes exactly the first result's remainder, not the
original budget or a cost inferred from the resulting formula. -/
theorem bindThreaded (first : Work α) (next : α → Work β) (budget : Nat)
    (result : WorkResult β budget) (success : bind first next budget = some result) :
    ∃ a : WorkResult α budget, first budget = some a ∧
      ∃ b : WorkResult β a.remaining, next a.value a.remaining = some b ∧
        result.value = b.value ∧ result.remaining = b.remaining := by
  cases ha : first budget with
  | none => simp [bind, ha] at success
  | some a =>
    cases hb : next a.value a.remaining with
    | none => simp [bind, ha, hb] at success
    | some b =>
      have same :
          (⟨b.value, b.remaining, Nat.le_trans b.decreasing a.decreasing⟩ :
            WorkResult β budget) = result := by
        simpa [bind, ha, hb] using success
      exact ⟨a, rfl, b, hb, congrArg WorkResult.value same.symm,
        congrArg WorkResult.remaining same.symm⟩

theorem captureUsage {meaning : Option α} (program : CaptureBudget.Program meaning)
    (budget : Nat) (result : WorkResult {value : α // meaning = some value} budget)
    (success : capture program budget = some result) :
    program.run budget = some (result.value.val, result.remaining) := by
  unfold capture at success
  split at success <;> simp_all
  cases success
  exact ⟨rfl, rfl⟩

end Work

instance : Monad Work where
  pure := Work.pure
  bind := Work.bind

abbrev WorkExpansion (ctx : Context) (intern : GroundCall → Option Nat)
    (env : Env) (expr : Expr) (budget : Nat) :=
  WorkResult (Expansion ctx intern env expr) budget

def WorkExpansion.formula {ctx intern env expr budget}
    (result : WorkExpansion ctx intern env expr budget) : Formula := result.value.formula

def WorkExpansion.origins {ctx intern env expr budget}
    (result : WorkExpansion ctx intern env expr budget) : List Weft.Grounding.Binding :=
  result.value.origins

/-- Each instance consumes one list-node admission unit, then its complete body
and capture work. The tail receives the child's actual residual state. -/
def gather {ctx intern env body}
    (child : (inner : Env) → Work (Expansion ctx intern inner body)) :
    (members : List Member) → Work (Instances ctx intern env body members)
  | [] => pure .nil
  | member :: rest => do
      Work.spend 1
      let head ← child (push member env)
      let tail ← gather child rest
      pure (.cons member head tail)

/-- Charge a body node before capture, then thread one aggregate state through
every capture, Boolean sibling, dependent domain and member. Type validation
still visits the body even when the captured domain is empty. -/
def expand (depth : Nat) (ctx : Context) (intern : GroundCall → Option Nat)
    (env : Env) (expr : Expr) : Work (Expansion ctx intern env expr) :=
  match depth with
  | 0 => Work.fail
  | fuel + 1 => do
    Work.spend 1
    match expr with
    | .atom atom =>
        let resolved ← Work.capture (CaptureBudget.resolveAtom ctx env atom)
        if checked : Typing.checkAtom ctx (types env) atom = true then
          match lowered : Language.elaborate ctx.legacy ctx.profile intern resolved.val.surface with
          | none => Work.fail
          | some formula => pure (.atom resolved.val formula resolved.property checked lowered)
        else Work.fail
    | .neg body => do
        let child ← expand fuel ctx intern env body
        pure (.neg child)
    | .conj a b => do
        let left ← expand fuel ctx intern env a
        let right ← expand fuel ctx intern env b
        pure (.conj left right)
    | .disj a b => do
        let left ← expand fuel ctx intern env a
        let right ← expand fuel ctx intern env b
        pure (.disj left right)
    | .all domain body =>
        let set ← Work.capture (CaptureBudget.evalSet ctx env domain)
        if checked : Typing.check ctx (types env) (.all domain body) = true then
          let children ← gather (fun inner => expand fuel ctx intern inner body) set.val.members
          pure (.all set.val set.property checked children)
        else Work.fail
    | .any domain body =>
        let set ← Work.capture (CaptureBudget.evalSet ctx env domain)
        if checked : Typing.check ctx (types env) (.any domain body) = true then
          let children ← gather (fun inner => expand fuel ctx intern inner body) set.val.members
          pure (.any set.val set.property checked children)
        else Work.fail
termination_by structural expr

/-- The only public lowering boundary retains actual usage and the complete
semantic derivation. Failure returns neither a partial expansion nor a budget. -/
def lower (budget : Nat) (ctx : Context) (intern : GroundCall → Option Nat)
    (env : Env) (expr : Expr) : Option (WorkExpansion ctx intern env expr budget) :=
  expand budget ctx intern env expr budget

theorem workConservation {α : Type} {budget : Nat} (result : WorkResult α budget) :
    result.used + result.remaining = budget :=
  Nat.sub_add_cancel result.decreasing

theorem captureRefuses {α : Type} {meaning : Option α}
    (program : CaptureBudget.Program meaning) (budget : Nat)
    (refused : program.run budget = none) : Work.capture program budget = none := by
  unfold Work.capture
  split <;> simp_all

theorem spendRefuses (amount budget : Nat) (insufficient : budget < amount) :
    Work.spend amount budget = none := by
  have refused := captureRefuses (CaptureBudget.spend amount) budget
    (CaptureBudget.spend_insufficient amount budget insufficient)
  simp [Work.spend, Work.bind, refused]

theorem Work.spendOneSucc (budget : Nat) :
    Work.spend 1 (budget + 1) =
      some (⟨(), budget, Nat.le_succ budget⟩ : WorkResult Unit (budget + 1)) := by
  have fits : 1 ≤ budget + 1 := Nat.succ_le_succ (Nat.zero_le budget)
  cases captured : Work.capture (CaptureBudget.spend 1) (budget + 1) with
  | none =>
      unfold Work.capture at captured
      split at captured
      · rename_i refused
        simp [CaptureBudget.spend, fits] at refused
      · contradiction
  | some result =>
      have usage := Work.captureUsage (CaptureBudget.spend 1) (budget + 1) result captured
      have same : budget = result.remaining := by
        simpa [CaptureBudget.spend, fits] using congrArg (Option.map Prod.snd) usage
      rcases result with ⟨value, remaining, decreasing⟩
      dsimp at same
      subst remaining
      simp [Work.spend, Work.bind, captured, Work.pure]

/-- An inhabited completed prefix is discarded when the next charge cannot be
paid from its actual remainder. No statement about a result's baked-in bounds
substitutes for this executable refusal equation. -/
theorem Work.prefixChargeRefuses {α β : Type} (first : Work α)
    (next : α → Work β) (budget amount : Nat) (prefixRun : WorkResult α budget)
    (completed : first budget = some prefixRun) (insufficient : prefixRun.remaining < amount) :
    Work.bind first (fun value =>
      Work.bind (Work.spend amount) (fun _ => next value)) budget = none := by
  have refused := spendRefuses amount prefixRun.remaining insufficient
  simp [Work.bind, completed, refused]

theorem expandZero (depth : Nat) (ctx : Context) (intern : GroundCall → Option Nat)
    (env : Env) (expr : Expr) : expand depth ctx intern env expr 0 = none := by
  cases depth <;> cases expr <;> rfl

end Weft.Finite.Lowering
