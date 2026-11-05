import Weft.Finite.Lowering

namespace Weft.Finite.Quantifiers
open Weft.Language Weft.Logic Weft.Finite.Syntax Weft.Finite.Sets
open Weft.Finite.Semantics Weft.Finite.Lowering

private theorem instancesFromBodySound (ctx : Context) (intern : GroundCall → Option Nat)
    (interpret : GroundCall → Bool) (valuation : Nat → Bool) (env : Env) (body : Expr)
    (bodySound : ∀ {inner : Env} (child : Expansion ctx intern inner body),
      evaluate valuation child.formula = true ↔ meaning ctx interpret inner body)
    (members : List Member) :
    ∀ children : Instances ctx intern env body members,
      (evaluate valuation children.allFormula = true ↔
        ∀ member ∈ members, meaning ctx interpret (push member env) body) ∧
      (evaluate valuation children.anyFormula = true ↔
        ∃ member ∈ members, meaning ctx interpret (push member env) body) := by
  induction members with
  | nil =>
      intro children
      cases children
      simp [Instances.allFormula, Instances.anyFormula, evaluate]
  | cons member rest ih =>
      intro children
      cases children with
      | cons actual child tail =>
          have headSound := bodySound child
          have tailSound := ih tail
          constructor
          · simp [Instances.allFormula, evaluate, headSound, tailSound.1]
          · simp [Instances.anyFormula, evaluate, headSound, tailSound.2]

/-- Induction is on finite source syntax; member traversal uses the independent
list induction above. No guessed size of a dependent derivation is required. -/
theorem sound (ctx : Context) (intern : GroundCall → Option Nat)
    (interpret : GroundCall → Bool) (valuation : Nat → Bool)
    (coherent : Interpretation intern interpret valuation)
    {env : Env} {expr : Expr} (expansion : Expansion ctx intern env expr) :
    evaluate valuation expansion.formula = true ↔ meaning ctx interpret env expr := by
  induction expr generalizing env with
  | atom atom =>
      cases expansion with
      | atom resolved formula captured checked lowered =>
          have scalar := Language.elaborationSound ctx.legacy ctx.profile intern interpret
            valuation coherent resolved.surface formula lowered
          simp [Expansion.formula, meaning, captured, scalar]
  | neg body ih =>
      cases expansion with
      | neg child =>
          simpa [Expansion.formula, evaluate, meaning] using not_congr (ih child)
  | conj a b ihLeft ihRight =>
      cases expansion with
      | conj left right =>
          simp [Expansion.formula, evaluate, meaning, ihLeft left, ihRight right]
  | disj a b ihLeft ihRight =>
      cases expansion with
      | disj left right =>
          simp [Expansion.formula, evaluate, meaning, ihLeft left, ihRight right]
  | all domain body ih =>
      cases expansion with
      | all set captured checked children =>
          have folded := instancesFromBodySound ctx intern interpret valuation env body
            (fun child => ih child) set.members children
          simpa [Expansion.formula, meaning, captured] using folded.1
  | any domain body ih =>
      cases expansion with
      | any set captured checked children =>
          have folded := instancesFromBodySound ctx intern interpret valuation env body
            (fun child => ih child) set.members children
          simpa [Expansion.formula, meaning, captured] using folded.2

theorem instancesSound (ctx : Context) (intern : GroundCall → Option Nat)
    (interpret : GroundCall → Bool) (valuation : Nat → Bool)
    (coherent : Interpretation intern interpret valuation)
    {env : Env} {body : Expr} {members : List Member}
    (children : Instances ctx intern env body members) :
    (evaluate valuation children.allFormula = true ↔
      ∀ member ∈ members, meaning ctx interpret (push member env) body) ∧
    (evaluate valuation children.anyFormula = true ↔
      ∃ member ∈ members, meaning ctx interpret (push member env) body) :=
  instancesFromBodySound ctx intern interpret valuation env body
    (fun child => sound ctx intern interpret valuation coherent child) members children

/-- Q06: universal lowering covers every actual member of the exact captured
set, not an arbitrary list of substituted Boolean answers. -/
theorem forallSound (ctx : Context) (intern : GroundCall → Option Nat)
    (interpret : GroundCall → Bool) (valuation : Nat → Bool)
    (coherent : Interpretation intern interpret valuation)
    (env : Env) (domain : SetExpr) (body : Expr) (set : CapturedSet)
    (captured : evalSet ctx env domain = some set)
    (expansion : Expansion ctx intern env (.all domain body)) :
    evaluate valuation expansion.formula = true ↔
      ∀ member ∈ set.members, meaning ctx interpret (push member env) body := by
  simpa [meaning, captured] using sound ctx intern interpret valuation coherent expansion

/-- Q07: an existential witness must be a member of the evaluated domain. -/
theorem existsSound (ctx : Context) (intern : GroundCall → Option Nat)
    (interpret : GroundCall → Bool) (valuation : Nat → Bool)
    (coherent : Interpretation intern interpret valuation)
    (env : Env) (domain : SetExpr) (body : Expr) (set : CapturedSet)
    (captured : evalSet ctx env domain = some set)
    (expansion : Expansion ctx intern env (.any domain body)) :
    evaluate valuation expansion.formula = true ↔
      ∃ member ∈ set.members, meaning ctx interpret (push member env) body := by
  simpa [meaning, captured] using sound ctx intern interpret valuation coherent expansion

private theorem instancesFromBodyAvailable (ctx : Context) (intern : GroundCall → Option Nat)
    (interpret : GroundCall → Bool) (env : Env) (body : Expr)
    (bodyAvailable : ∀ {inner : Env} (_child : Expansion ctx intern inner body),
      available ctx interpret inner body)
    (members : List Member) :
    ∀ _children : Instances ctx intern env body members,
      ∀ member ∈ members, available ctx interpret (push member env) body := by
  induction members with
  | nil =>
      intro children
      simp
  | cons member rest ih =>
      intro children
      cases children with
      | cons actual child tail =>
          intro item memberOf
          simp only [List.mem_cons] at memberOf
          rcases memberOf with rfl | memberOf
          · exact bodyAvailable child
          · exact ih tail item memberOf

theorem availableExpansion (ctx : Context) (intern : GroundCall → Option Nat)
    (interpret : GroundCall → Bool) (valuation : Nat → Bool)
    (coherent : Interpretation intern interpret valuation)
    {env : Env} {expr : Expr} (expansion : Expansion ctx intern env expr) :
    available ctx interpret env expr := by
  induction expr generalizing env with
  | atom atom =>
      cases expansion with
      | atom resolved formula captured checked lowered =>
          exact ⟨resolved, evaluate valuation formula, captured,
            Language.elaborationSound ctx.legacy ctx.profile intern interpret valuation
              coherent resolved.surface formula lowered⟩
  | neg body ih =>
      cases expansion with
      | neg child => exact ih child
  | conj a b ihLeft ihRight =>
      cases expansion with
      | conj left right => exact ⟨ihLeft left, ihRight right⟩
  | disj a b ihLeft ihRight =>
      cases expansion with
      | disj left right => exact ⟨ihLeft left, ihRight right⟩
  | all domain body ih =>
      cases expansion with
      | all set captured checked children =>
          exact ⟨set, captured, checked,
            instancesFromBodyAvailable ctx intern interpret env body
              (fun child => ih child) set.members children⟩
  | any domain body ih =>
      cases expansion with
      | any set captured checked children =>
          exact ⟨set, captured, checked,
            instancesFromBodyAvailable ctx intern interpret env body
              (fun child => ih child) set.members children⟩

theorem availableInstances (ctx : Context) (intern : GroundCall → Option Nat)
    (interpret : GroundCall → Bool) (valuation : Nat → Bool)
    (coherent : Interpretation intern interpret valuation)
    {env : Env} {body : Expr} {members : List Member}
    (children : Instances ctx intern env body members) :
    ∀ member ∈ members, available ctx interpret (push member env) body :=
  instancesFromBodyAvailable ctx intern interpret env body
    (fun child => availableExpansion ctx intern interpret valuation coherent child) members children

theorem denotationSound (ctx : Context) (intern : GroundCall → Option Nat)
    (interpret : GroundCall → Bool) (valuation : Nat → Bool)
    (coherent : Interpretation intern interpret valuation)
    {env : Env} {expr : Expr} (expansion : Expansion ctx intern env expr) :
    Denotes ctx interpret env expr (evaluate valuation expansion.formula) :=
  ⟨availableExpansion ctx intern interpret valuation coherent expansion,
    sound ctx intern interpret valuation coherent expansion⟩

/-- Accepted-run accounting identities. These are not themselves executable
refusal proofs; Q09's refusal statement below uses a completed prefix and an
inhabitable insufficient next-node charge. -/
theorem lowerCost {ctx : Context} {intern : GroundCall → Option Nat}
    {env : Env} {expr : Expr} (budget : Nat)
    (candidate : WorkExpansion ctx intern env expr budget)
    (_success : lower budget ctx intern env expr = some candidate) :
    candidate.used ≤ budget := Nat.sub_le _ _

theorem lowerRemaining {ctx : Context} {intern : GroundCall → Option Nat}
    {env : Env} {expr : Expr} (budget : Nat)
    (candidate : WorkExpansion ctx intern env expr budget)
    (_success : lower budget ctx intern env expr = some candidate) :
    candidate.remaining ≤ budget := candidate.decreasing

theorem lowerWorkConservation {ctx : Context} {intern : GroundCall → Option Nat}
    {env : Env} {expr : Expr} (budget : Nat)
    (candidate : WorkExpansion ctx intern env expr budget)
    (_success : lower budget ctx intern env expr = some candidate) :
    candidate.used + candidate.remaining = budget := workConservation candidate

/-- Q09 at the public lowerer: a successful left prefix may consume the remaining
capacity, but it cannot be published as a successful conjunction when the next
body-node charge is unaffordable. The premise is executable and inhabited by
`QuantifierExamples.completedBooleanPrefix`, unlike `budget < budget - rest`. -/
theorem budgetRefusesPartial (budget : Nat) (ctx : Context)
    (intern : GroundCall → Option Nat) (env : Env) (left right : Expr)
    (prefixRun : WorkExpansion ctx intern env left budget)
    (completed : expand budget ctx intern env left budget = some prefixRun)
    (insufficient : prefixRun.remaining < 1) :
    lower (budget + 1) ctx intern env (.conj left right) = none := by
  have empty : prefixRun.remaining = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ insufficient)
  have refused : expand budget ctx intern env right prefixRun.remaining = none := by
    rw [empty]
    exact expandZero budget ctx intern env right
  change Work.bind (Work.spend 1) (fun _ =>
    Work.bind (expand budget ctx intern env left) (fun a =>
      Work.bind (expand budget ctx intern env right) (fun b =>
        Work.pure (Expansion.conj a b)))) (budget + 1) = none
  simp [Work.bind, Work.spendOneSucc, Work.pure, completed, refused]

theorem zeroBudgetRefuses (ctx : Context) (intern : GroundCall → Option Nat)
    (env : Env) (expr : Expr) : lower 0 ctx intern env expr = none :=
  expandZero 0 ctx intern env expr

/-- Refusal at the actual integrated atom branch, before scalar elaboration. -/
theorem atomCaptureRefuses (budget : Nat) (ctx : Context)
    (intern : GroundCall → Option Nat) (env : Env) (atom : Atom)
    (refused : (CaptureBudget.resolveAtom ctx env atom).run budget = none) :
    lower (budget + 1) ctx intern env (.atom atom) = none := by
  simp [lower, Lowering.expand, Bind.bind, Work.bind, Work.spendOneSucc,
    captureRefuses _ _ refused]

/-- Domain refusal never publishes a vacuous or prefix quantifier result. -/
theorem forallCaptureRefuses (budget : Nat) (ctx : Context)
    (intern : GroundCall → Option Nat) (env : Env) (domain : SetExpr) (body : Expr)
    (refused : (CaptureBudget.evalSet ctx env domain).run budget = none) :
    lower (budget + 1) ctx intern env (.all domain body) = none := by
  simp [lower, Lowering.expand, Bind.bind, Work.bind, Work.spendOneSucc,
    captureRefuses _ _ refused]

theorem existsCaptureRefuses (budget : Nat) (ctx : Context)
    (intern : GroundCall → Option Nat) (env : Env) (domain : SetExpr) (body : Expr)
    (refused : (CaptureBudget.evalSet ctx env domain).run budget = none) :
    lower (budget + 1) ctx intern env (.any domain body) = none := by
  simp [lower, Lowering.expand, Bind.bind, Work.bind, Work.spendOneSucc,
    captureRefuses _ _ refused]

/-- Truth conservation for the full earlier scalar AST. -/
theorem scalarTruthConservation (ctx : Context) (interpret : GroundCall → Bool)
    (env : Env) (surface : Surface) :
    meaning ctx interpret env (.atom (.legacy surface)) ↔
      Language.denote ctx.legacy ctx.profile interpret surface = some true := by
  simp [meaning, resolveAtom]

theorem scalarAvailabilityConservation (ctx : Context) (interpret : GroundCall → Bool)
    (env : Env) (surface : Surface) :
    available ctx interpret env (.atom (.legacy surface)) ↔
      ∃ value, Language.denote ctx.legacy ctx.profile interpret surface = some value := by
  simp [available, resolveAtom]

/-- Q10: both Boolean results and strict definedness of the full earlier AST,
including all global field paths, predicates and Boolean nesting. A separately
captured root value is NOT required for an existing global path. -/
theorem scalarConservation (ctx : Context) (interpret : GroundCall → Bool)
    (env : Env) (surface : Surface) (value : Bool) :
    Denotes ctx interpret env (.atom (.legacy surface)) value ↔
      Language.denote ctx.legacy ctx.profile interpret surface = some value := by
  rw [Denotes, scalarAvailabilityConservation, scalarTruthConservation]
  cases result : Language.denote ctx.legacy ctx.profile interpret surface with
  | none => simp
  | some actual => cases actual <;> cases value <;> simp

end Weft.Finite.Quantifiers
