import Weft.Finite.Semantics

namespace Weft.Finite.Syntax
open Weft.Language Weft.Finite.Sets

theorem termTypeRename (ctx : Context) (source target : TypeEnv) (renameFn : Nat → Nat)
    (compatible : ∀ i, target (renameFn i) = source i) (term : Term) :
    termType ctx target (term.rename renameFn) = termType ctx source term := by
  induction term with
  | literal value => rfl
  | captured member => rfl
  | named index => rfl
  | bound index => exact compatible index
  | global path => rfl
  | field base selector ih => simp only [Term.rename, termType, ih]

theorem termTypeSubstitution (ctx : Context) (source target : TypeEnv)
    (replacement : Nat → Term)
    (compatible : ∀ i, termType ctx target (replacement i) = source i) (term : Term) :
    termType ctx target (term.substitute replacement) = termType ctx source term := by
  induction term with
  | literal value => rfl
  | captured member => rfl
  | named index => rfl
  | bound index => exact compatible index
  | global path => rfl
  | field base selector ih => simp only [Term.substitute, termType, ih]

theorem liftedTypeSubstitution (ctx : Context) (source target : TypeEnv)
    (replacement : Nat → Term)
    (compatible : ∀ i, termType ctx target (replacement i) = source i) (ty : Ty) :
    ∀ i, termType ctx (push ty target) (liftSubstitution replacement i) = push ty source i := by
  intro i
  cases i with
  | zero => rfl
  | succ i =>
      exact (termTypeRename ctx target (push ty target) Nat.succ (fun _ => rfl)
        (replacement i)).trans (compatible i)

theorem setTypeSubstitution (ctx : Context) (source target : TypeEnv)
    (replacement : Nat → Term)
    (compatible : ∀ i, termType ctx target (replacement i) = source i) (set : SetExpr) :
    SetExpr.elementType ctx target (set.substitute replacement) = SetExpr.elementType ctx source set := by
  cases set with
  | empty ty => rfl
  | singleton term => exact termTypeSubstitution ctx source target replacement compatible term
  | union ty a b => rfl
  | named ty index => rfl
  | select ty base selector => rfl

theorem checkSetSubstitution (ctx : Context) (source target : TypeEnv)
    (replacement : Nat → Term)
    (compatible : ∀ i, termType ctx target (replacement i) = source i) (set : SetExpr) :
    Typing.checkSet ctx target (set.substitute replacement) = Typing.checkSet ctx source set := by
  induction set with
  | empty ty => rfl
  | singleton term =>
      simp only [SetExpr.substitute, Typing.checkSet,
        termTypeSubstitution ctx source target replacement compatible]
  | union ty a b ihA ihB =>
      simp only [SetExpr.substitute, Typing.checkSet, ihA, ihB,
        setTypeSubstitution ctx source target replacement compatible]
  | named ty index => rfl
  | select ty base selector =>
      simp only [SetExpr.substitute, Typing.checkSet,
        termTypeSubstitution ctx source target replacement compatible]

theorem checkAtomSubstitution (ctx : Context) (source target : TypeEnv)
    (replacement : Nat → Term)
    (compatible : ∀ i, termType ctx target (replacement i) = source i) (atom : Atom) :
    Typing.checkAtom ctx target (atom.substitute replacement) = Typing.checkAtom ctx source atom := by
  cases atom <;> simp [Atom.substitute, Typing.checkAtom,
    termTypeSubstitution ctx source target replacement compatible,
    setTypeSubstitution ctx source target replacement compatible,
    checkSetSubstitution ctx source target replacement compatible, List.map_map, Function.comp_def]

theorem checkSubstitution (ctx : Context) (source target : TypeEnv)
    (replacement : Nat → Term)
    (compatible : ∀ i, termType ctx target (replacement i) = source i) (expr : Expr) :
    Typing.check ctx target (expr.substitute replacement) = Typing.check ctx source expr := by
  induction expr generalizing source target replacement with
  | atom atom => exact checkAtomSubstitution ctx source target replacement compatible atom
  | neg body ih => exact ih source target replacement compatible
  | conj a b ihA ihB | disj a b ihA ihB =>
      simp only [Expr.substitute, Typing.check,
        ihA source target replacement compatible, ihB source target replacement compatible]
  | all domain body ih | any domain body ih =>
      simp only [Expr.substitute, Typing.check,
        setTypeSubstitution ctx source target replacement compatible]
      cases assigned : SetExpr.elementType ctx source domain with
      | none => rfl
      | some ty =>
          simp only [checkSetSubstitution ctx source target replacement compatible,
            ih (push ty source) (push ty target) (liftSubstitution replacement)
              (liftedTypeSubstitution ctx source target replacement compatible ty)]

theorem typesPush (env : Env) (member : Member) :
    types (push member env) = push member.value.type (types env) := by
  funext index
  cases index <;> rfl

end Weft.Finite.Syntax
