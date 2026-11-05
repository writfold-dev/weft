import Weft.Finite.SubstitutionTyping
import Init.Data.List.Monadic

namespace Weft.Finite.Syntax
open Weft.Language Weft.Finite.Sets Weft.Finite.Semantics

/-- Arbitrary index renaming preserves meaning when environments commute with
that renaming. In particular successor shifts cannot capture the newest binder. -/
theorem renameMeaning (ctx : Context) (source target : Env) (renameFn : Nat → Nat)
    (compatible : ∀ i, target (renameFn i) = source i) (term : Term) :
    resolveTerm ctx target (term.rename renameFn) = resolveTerm ctx source term := by
  induction term with
  | literal value => rfl
  | captured member => rfl
  | named index => rfl
  | bound index => exact compatible index
  | global path => rfl
  | field base selector ih => simp only [Term.rename, resolveTerm, ih]

theorem shiftMeaning (ctx : Context) (env : Env) (member : Member) (term : Term) :
    resolveTerm ctx (push member env) (term.rename Nat.succ) = resolveTerm ctx env term :=
  renameMeaning ctx env (push member env) Nat.succ (fun _ => rfl) term

theorem termSubstitutionMeaning (ctx : Context) (source target : Env)
    (replacement : Nat → Term)
    (compatible : ∀ i, resolveTerm ctx target (replacement i) = source i) (term : Term) :
    resolveTerm ctx target (term.substitute replacement) = resolveTerm ctx source term := by
  induction term with
  | literal value => rfl
  | captured member => rfl
  | named index => rfl
  | bound index => exact compatible index
  | global path => rfl
  | field base selector ih => simp only [Term.substitute, resolveTerm, ih]

theorem liftedSubstitutionMeaning (ctx : Context) (source target : Env)
    (replacement : Nat → Term)
    (compatible : ∀ i, resolveTerm ctx target (replacement i) = source i) (member : Member) :
    ∀ i, resolveTerm ctx (push member target) (liftSubstitution replacement i) =
      push member source i := by
  intro i
  cases i with
  | zero => rfl
  | succ i =>
      exact (shiftMeaning ctx target member (replacement i)).trans (compatible i)

theorem setSubstitutionMeaning (ctx : Context) (source target : Env)
    (replacement : Nat → Term)
    (compatible : ∀ i, resolveTerm ctx target (replacement i) = source i) (set : SetExpr) :
    evalSet ctx target (set.substitute replacement) = evalSet ctx source set := by
  induction set with
  | empty ty => rfl
  | singleton term =>
      simp only [SetExpr.substitute, evalSet, termSubstitutionMeaning ctx source target replacement compatible]
  | union ty a b ihA ihB => simp only [SetExpr.substitute, evalSet, ihA, ihB]
  | named ty index => rfl
  | select ty base selector =>
      simp only [SetExpr.substitute, evalSet, termSubstitutionMeaning ctx source target replacement compatible]

theorem argumentsSubstitutionMeaning (ctx : Context) (source target : Env)
    (replacement : Nat → Term)
    (compatible : ∀ i, resolveTerm ctx target (replacement i) = source i) (args : List Term) :
    (args.map (Term.substitute replacement)).mapM (resolveTerm ctx target) =
      args.mapM (resolveTerm ctx source) := by
  induction args with
  | nil => rfl
  | cons term rest ih =>
      -- Use the lawful cons equation for the actual accumulator-based mapM.
      simp only [List.map_cons, List.mapM_cons,
        termSubstitutionMeaning ctx source target replacement compatible, ih]

theorem atomSubstitutionMeaning (ctx : Context) (source target : Env)
    (replacement : Nat → Term)
    (compatible : ∀ i, resolveTerm ctx target (replacement i) = source i) (atom : Atom) :
    resolveAtom ctx target (atom.substitute replacement) = resolveAtom ctx source atom := by
  cases atom with
  | legacy surface => rfl
  | equal a b =>
      simp only [Atom.substitute, resolveAtom,
        termSubstitutionMeaning ctx source target replacement compatible]
  | notEqual a b =>
      simp only [Atom.substitute, resolveAtom,
        termSubstitutionMeaning ctx source target replacement compatible]
  | predicate name args =>
      simp only [Atom.substitute, resolveAtom,
        argumentsSubstitutionMeaning ctx source target replacement compatible]
  | setEqual a b =>
      simp only [Atom.substitute, resolveAtom,
        setSubstitutionMeaning ctx source target replacement compatible]

/-- Q05: capture-avoiding substitution preserves the entire explicit expression
meaning, including nested quantifiers and domains depending on outer binders.
The compatibility premise is about resolved values and their complete origins,
not equality of display names. -/
theorem truthSubstitutionMeaning (ctx : Context) (interpret : GroundCall → Bool)
    (expr : Expr) (source target : Env) (replacement : Nat → Term)
    (compatible : ∀ i, resolveTerm ctx target (replacement i) = source i) :
    meaning ctx interpret target (expr.substitute replacement) ↔
      meaning ctx interpret source expr := by
  induction expr generalizing source target replacement with
  | atom atom =>
      simp only [Expr.substitute, meaning,
        atomSubstitutionMeaning ctx source target replacement compatible]
  | neg body ih =>
      exact not_congr (ih source target replacement compatible)
  | conj a b ihA ihB =>
      exact and_congr (ihA source target replacement compatible) (ihB source target replacement compatible)
  | disj a b ihA ihB =>
      exact or_congr (ihA source target replacement compatible) (ihB source target replacement compatible)
  | all domain body ih =>
      simp only [Expr.substitute, meaning,
        setSubstitutionMeaning ctx source target replacement compatible]
      apply exists_congr
      intro set
      apply and_congr Iff.rfl
      apply forall_congr'
      intro member
      apply forall_congr'
      intro _
      exact ih (push member source) (push member target) (liftSubstitution replacement)
        (liftedSubstitutionMeaning ctx source target replacement compatible member)
  | any domain body ih =>
      simp only [Expr.substitute, meaning,
        setSubstitutionMeaning ctx source target replacement compatible]
      apply exists_congr
      intro set
      apply and_congr Iff.rfl
      apply exists_congr
      intro member
      apply and_congr Iff.rfl
      exact ih (push member source) (push member target) (liftSubstitution replacement)
        (liftedSubstitutionMeaning ctx source target replacement compatible member)

theorem availableSubstitutionMeaning (ctx : Context) (interpret : GroundCall → Bool)
    (expr : Expr) (source target : Env) (replacement : Nat → Term)
    (compatible : ∀ i, resolveTerm ctx target (replacement i) = source i)
    (typed : ∀ i, termType ctx (types target) (replacement i) = types source i) :
    available ctx interpret target (expr.substitute replacement) ↔
      available ctx interpret source expr := by
  induction expr generalizing source target replacement with
  | atom atom =>
      simp only [Expr.substitute, available,
        atomSubstitutionMeaning ctx source target replacement compatible]
  | neg body ih => exact ih source target replacement compatible typed
  | conj a b ihA ihB | disj a b ihA ihB =>
      exact and_congr (ihA source target replacement compatible typed)
        (ihB source target replacement compatible typed)
  | all domain body ih | any domain body ih =>
      -- Availability checks the original quantifier constructor, including any.
      have checked := checkSubstitution ctx (types source) (types target)
        replacement typed (.all domain body)
      have checkedAny := checkSubstitution ctx (types source) (types target)
        replacement typed (.any domain body)
      simp only [Expr.substitute] at checked checkedAny
      simp only [Expr.substitute, available,
        setSubstitutionMeaning ctx source target replacement compatible, checked, checkedAny]
      apply exists_congr
      intro set
      apply and_congr Iff.rfl
      apply and_congr Iff.rfl
      apply forall_congr'
      intro member
      apply forall_congr'
      intro _
      have liftedTyped :
          ∀ i, termType ctx (types (push member target)) (liftSubstitution replacement i) =
            types (push member source) i := by
        simpa only [typesPush] using
          liftedTypeSubstitution ctx (types source) (types target) replacement typed member.value.type
      exact ih (push member source) (push member target) (liftSubstitution replacement)
        (liftedSubstitutionMeaning ctx source target replacement compatible member) liftedTyped

/-- Q05 includes strict definedness and both Boolean values, not merely truth.
Typed substitution must commute with both value and type environments; preserving
values alone would not preserve static checking of an empty quantified body. -/
theorem substitutionMeaning (ctx : Context) (interpret : GroundCall → Bool)
    (expr : Expr) (source target : Env) (replacement : Nat → Term)
    (compatible : ∀ i, resolveTerm ctx target (replacement i) = source i)
    (typed : ∀ i, termType ctx (types target) (replacement i) = types source i)
    (value : Bool) :
    Denotes ctx interpret target (expr.substitute replacement) value ↔
      Denotes ctx interpret source expr value := by
  unfold Denotes
  rw [availableSubstitutionMeaning ctx interpret expr source target replacement compatible typed,
    truthSubstitutionMeaning ctx interpret expr source target replacement compatible]

/-- Closing the nearest binder retains every captured origin and decrements the
remaining outer indices. The recursively lifted substitution protects inner zero. -/
def instantiate (member : Member) : Nat → Term
  | 0 => .captured member
  | n + 1 => .bound n

theorem instantiateMeaning (ctx : Context) (interpret : GroundCall → Bool)
    (env : Env) (member : Member) (body : Expr) :
    meaning ctx interpret env (body.substitute (instantiate member)) ↔
      meaning ctx interpret (push member env) body := by
  apply truthSubstitutionMeaning
  intro i
  cases i <;> rfl

theorem extensionPreservesOuter (env : Env) (member : Member) (index : Nat) :
    push member env (index + 1) = env index := rfl

theorem instantiateDenotation (ctx : Context) (interpret : GroundCall → Bool)
    (env : Env) (member : Member) (body : Expr) (value : Bool) :
    Denotes ctx interpret env (body.substitute (instantiate member)) value ↔
      Denotes ctx interpret (push member env) body value := by
  apply substitutionMeaning
  · intro i
    cases i <;> rfl
  · intro i
    cases i <;> rfl

end Weft.Finite.Syntax
