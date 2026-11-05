import Weft.Finite.Quantifiers
import Weft.Finite.Substitution
import Weft.Finite.Algebra.Closure

/-!
# Extended substitution, typing and lowering agreement

A05: capture-avoiding substitution, typing preservation and lowering agreement
extend to the algebra constructors, including expressions inside quantified
domains and bodies. Membership/subset lower to checked Boolean literals of the
algebraic verdict — exactly like set equality — never to uninterpreted atoms or
raw-name substitution.
-/

namespace Weft.Finite.Algebra

open Weft.Language Weft.Logic Weft.Finite.Syntax Weft.Finite.Sets
open Weft.Finite.Semantics Weft.Finite.Lowering Weft.Finite.Quantifiers

/-- A05: substitution commutes with the new set constructors and the new
atoms; inherited Q05 coverage extends to them. -/
theorem substitutionMeaning (ctx : Context) (source target : Env)
    (replacement : Nat → Syntax.Term)
    (compatible : ∀ i, resolveTerm ctx target (replacement i) = source i) :
    (∀ (elementType : Ty) (left right : SetExpr), evalSet ctx target
          ((SetExpr.intersection elementType left right).substitute replacement) =
        evalSet ctx source (.intersection elementType left right)) ∧
    (∀ (elementType : Ty) (left right : SetExpr), evalSet ctx target
          ((SetExpr.difference elementType left right).substitute replacement) =
        evalSet ctx source (.difference elementType left right)) ∧
    (∀ (term : Syntax.Term) (set : SetExpr), resolveAtom ctx target
          ((Atom.member term set).substitute replacement) =
        resolveAtom ctx source (.member term set)) ∧
    (∀ left right : SetExpr, resolveAtom ctx target
          ((Atom.subset left right).substitute replacement) =
        resolveAtom ctx source (.subset left right)) :=
  ⟨fun _elementType left right => by
      simp only [SetExpr.substitute, evalSet,
        setSubstitutionMeaning ctx source target replacement compatible left,
        setSubstitutionMeaning ctx source target replacement compatible right],
    fun _elementType left right => by
      simp only [SetExpr.substitute, evalSet,
        setSubstitutionMeaning ctx source target replacement compatible left,
        setSubstitutionMeaning ctx source target replacement compatible right],
    fun term set => by
      simp only [Atom.substitute, resolveAtom,
        termSubstitutionMeaning ctx source target replacement compatible term,
        setSubstitutionMeaning ctx source target replacement compatible set],
    fun left right => by
      simp only [Atom.substitute, resolveAtom,
        setSubstitutionMeaning ctx source target replacement compatible left,
        setSubstitutionMeaning ctx source target replacement compatible right]⟩

/-- A05: static checking is preserved by substitution for the new constructors,
so typing obligations survive substitution, including in empty quantified
bodies over algebraic domains. -/
theorem substitutionTyped (ctx : Context) (source target : TypeEnv)
    (replacement : Nat → Syntax.Term)
    (compatible : ∀ i, termType ctx target (replacement i) = source i) :
    (∀ (elementType : Ty) (left right : SetExpr),
        Typing.checkSet ctx target
            ((SetExpr.intersection elementType left right).substitute replacement) =
          Typing.checkSet ctx source (.intersection elementType left right)) ∧
    (∀ (elementType : Ty) (left right : SetExpr),
        Typing.checkSet ctx target
            ((SetExpr.difference elementType left right).substitute replacement) =
          Typing.checkSet ctx source (.difference elementType left right)) ∧
    (∀ (term : Syntax.Term) (set : SetExpr),
        Typing.checkAtom ctx target ((Atom.member term set).substitute replacement) =
          Typing.checkAtom ctx source (.member term set)) ∧
    (∀ left right : SetExpr,
        Typing.checkAtom ctx target ((Atom.subset left right).substitute replacement) =
          Typing.checkAtom ctx source (.subset left right)) :=
  ⟨fun _elementType _left _right =>
      checkSetSubstitution ctx source target replacement compatible _,
    fun _elementType _left _right =>
      checkSetSubstitution ctx source target replacement compatible _,
    fun _term _set => checkAtomSubstitution ctx source target replacement compatible _,
    fun _left _right => checkAtomSubstitution ctx source target replacement compatible _⟩

/-- Membership atoms lower to the checked literal of the algebraic verdict,
with both operands' complete origins; the resolved surface is the Boolean fact
itself, not a free predicate atom. -/
theorem memberAtomLiteral (ctx : Context) (intern : GroundCall → Option Nat)
    (env : Env) (term : Syntax.Term) (set : SetExpr)
    (resolved : ResolvedAtom) (formula : Formula)
    (captured : resolveAtom ctx env (.member term set) = some resolved)
    (lowered : Language.elaborate ctx.legacy ctx.profile intern resolved.surface = some formula) :
    ∃ x capturedSet outcome, resolveTerm ctx env term = some x ∧
      evalSet ctx env set = some capturedSet ∧ member x.value capturedSet = some outcome ∧
      resolved.surface = .boolean outcome ∧ resolved.origins = x.origins ++ capturedSet.origins ∧
      formula = .literal outcome := by
  obtain ⟨x, capturedSet, outcome, termOk, setOk, memberOk, surfaceEq, originsEq⟩ :=
    predicatesSound.1 ctx env term set resolved captured
  refine ⟨x, capturedSet, outcome, termOk, setOk, memberOk, surfaceEq, originsEq, ?_⟩
  rw [surfaceEq] at lowered
  exact (Option.some.inj (by simpa [Language.elaborate] using lowered)).symm

theorem subsetAtomLiteral (ctx : Context) (intern : GroundCall → Option Nat)
    (env : Env) (left right : SetExpr)
    (resolved : ResolvedAtom) (formula : Formula)
    (captured : resolveAtom ctx env (.subset left right) = some resolved)
    (lowered : Language.elaborate ctx.legacy ctx.profile intern resolved.surface = some formula) :
    ∃ x y outcome, evalSet ctx env left = some x ∧ evalSet ctx env right = some y ∧
      subset x y = some outcome ∧ resolved.surface = .boolean outcome ∧
      resolved.origins = x.origins ++ y.origins ∧ formula = .literal outcome := by
  obtain ⟨x, y, outcome, leftOk, rightOk, subsetOk, surfaceEq, originsEq⟩ :=
    predicatesSound.2.1 ctx env left right resolved captured
  refine ⟨x, y, outcome, leftOk, rightOk, subsetOk, surfaceEq, originsEq, ?_⟩
  rw [surfaceEq] at lowered
  exact (Option.some.inj (by simpa [Language.elaborate] using lowered)).symm

/-- A05 primary: every algebra atom lowers to the checked literal of its
algebraic verdict, and evaluation of any lowered formula containing them
agrees with independent meaning, including inside quantified domains/bodies. -/
theorem loweringSound (ctx : Context) (intern : GroundCall → Option Nat)
    (interpret : GroundCall → Bool) (valuation : Nat → Bool)
    (coherent : Interpretation intern interpret valuation) :
    (∀ (env : Env) (term : Syntax.Term) (set : SetExpr)
        (expansion : Expansion ctx intern env (.atom (.member term set))), ∃ outcome,
          expansion.formula = .literal outcome ∧
            (evaluate valuation (.literal outcome) = true ↔
              meaning ctx interpret env (.atom (.member term set)))) ∧
    (∀ (env : Env) (left right : SetExpr)
        (expansion : Expansion ctx intern env (.atom (.subset left right))), ∃ outcome,
          expansion.formula = .literal outcome ∧
            (evaluate valuation (.literal outcome) = true ↔
              meaning ctx interpret env (.atom (.subset left right)))) ∧
    (∀ (env : Env) (expr : Expr)
        (expansion : Expansion ctx intern env expr),
        evaluate valuation expansion.formula = true ↔
          meaning ctx interpret env expr) := by
  refine ⟨?_, ?_, fun _env _expr expansion =>
    Quantifiers.sound ctx intern interpret valuation coherent expansion⟩
  · intro env term set expansion
    cases expansion with
    | atom resolved formula captured checked lowered =>
        obtain ⟨x, capturedSet, outcome, _termOk, _setOk, _memberOk, surfaceEq, _originsEq,
            formulaEq⟩ :=
          memberAtomLiteral ctx intern env term set resolved formula captured lowered
        refine ⟨outcome, ⟨formulaEq, ?_⟩⟩
        constructor
        · intro evaluated
          exact ⟨resolved, captured, by rw [surfaceEq]; simpa [Language.denote] using evaluated⟩
        · intro meaningWitness
          obtain ⟨resolved', captured', denoted⟩ := meaningWitness
          have same : resolved' = resolved := Option.some.inj (captured'.symm.trans captured)
          rw [same, surfaceEq] at denoted
          simpa [Language.denote] using denoted
  · intro env left right expansion
    cases expansion with
    | atom resolved formula captured checked lowered =>
        obtain ⟨x, y, outcome, _leftOk, _rightOk, _subsetOk, surfaceEq, _originsEq,
            formulaEq⟩ :=
          subsetAtomLiteral ctx intern env left right resolved formula captured lowered
        refine ⟨outcome, ⟨formulaEq, ?_⟩⟩
        constructor
        · intro evaluated
          exact ⟨resolved, captured, by rw [surfaceEq]; simpa [Language.denote] using evaluated⟩
        · intro meaningWitness
          obtain ⟨resolved', captured', denoted⟩ := meaningWitness
          have same : resolved' = resolved := Option.some.inj (captured'.symm.trans captured)
          rw [same, surfaceEq] at denoted
          simpa [Language.denote] using denoted

end Weft.Finite.Algebra
