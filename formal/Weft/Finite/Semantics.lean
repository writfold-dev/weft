import Weft.Finite.Typing

namespace Weft.Finite.Semantics
open Weft.Language Weft.Finite.Syntax Weft.Finite.Sets

structure ResolvedAtom where
  surface : Surface
  origins : List Weft.Grounding.Binding

def legacyTermOrigins (ctx : Context) : Language.Term → List Weft.Grounding.Binding
  | .literal _ => []
  | .field path => ctx.globalOrigins path

def legacyOrigins (ctx : Context) : Surface → List Weft.Grounding.Binding
  | .boolean _ => []
  | .equal a b | .notEqual a b => legacyTermOrigins ctx a ++ legacyTermOrigins ctx b
  | .predicate _ args => args.flatMap (legacyTermOrigins ctx)
  | .neg body => legacyOrigins ctx body
  | .conj a b | .disj a b => legacyOrigins ctx a ++ legacyOrigins ctx b

def resolveAtom (ctx : Context) (env : Env) : Atom → Option ResolvedAtom
  | .legacy surface => some ⟨surface, legacyOrigins ctx surface⟩
  | .equal a b => do
      let x ← resolveTerm ctx env a
      let y ← resolveTerm ctx env b
      some ⟨.equal (.literal x.value) (.literal y.value), x.origins ++ y.origins⟩
  | .notEqual a b => do
      let x ← resolveTerm ctx env a
      let y ← resolveTerm ctx env b
      some ⟨.notEqual (.literal x.value) (.literal y.value), x.origins ++ y.origins⟩
  | .predicate name args => do
      let members ← args.mapM (resolveTerm ctx env)
      some ⟨.predicate name (members.map (fun m => .literal m.value)),
        members.flatMap Member.origins⟩
  | .setEqual a b => do
      let x ← evalSet ctx env a
      let y ← evalSet ctx env b
      let equal ← Sets.equal x y
      some ⟨.boolean equal, x.origins ++ y.origins⟩

/-- Independent source meaning. Quantification is directly over actual captured
membership, with domains evaluated outside and bodies inside the new scope.
Availability is a separate strict obligation supplied by successful lowering;
false is not used by lowering as a fallback for absent denotations. -/
def meaning (ctx : Context) (interpret : GroundCall → Bool) (env : Env) : Expr → Prop
  | .atom atom => ∃ resolved, resolveAtom ctx env atom = some resolved ∧
      Language.denote ctx.legacy ctx.profile interpret resolved.surface = some true
  | .neg body => ¬ meaning ctx interpret env body
  | .conj a b => meaning ctx interpret env a ∧ meaning ctx interpret env b
  | .disj a b => meaning ctx interpret env a ∨ meaning ctx interpret env b
  | .all domain body => ∃ set, evalSet ctx env domain = some set ∧
      ∀ member ∈ set.members, meaning ctx interpret (push member env) body
  | .any domain body => ∃ set, evalSet ctx env domain = some set ∧
      ∃ member ∈ set.members, meaning ctx interpret (push member env) body

/-- Strict availability does not short-circuit either Boolean branch or any
quantified instance, even an irrelevant existential or universal branch. -/
def available (ctx : Context) (interpret : GroundCall → Bool) (env : Env) : Expr → Prop
  | .atom atom => ∃ resolved value, resolveAtom ctx env atom = some resolved ∧
      Language.denote ctx.legacy ctx.profile interpret resolved.surface = some value
  | .neg body => available ctx interpret env body
  | .conj a b | .disj a b => available ctx interpret env a ∧ available ctx interpret env b
  | .all domain body => ∃ set, evalSet ctx env domain = some set ∧
      Typing.check ctx (types env) (.all domain body) = true ∧
      ∀ member ∈ set.members, available ctx interpret (push member env) body
  | .any domain body => ∃ set, evalSet ctx env domain = some set ∧
      Typing.check ctx (types env) (.any domain body) = true ∧
      ∀ member ∈ set.members, available ctx interpret (push member env) body

/-- Partial Boolean denotation: unavailable syntax denotes neither Boolean.
The truth component above is only used together with strict availability. -/
def Denotes (ctx : Context) (interpret : GroundCall → Bool) (env : Env)
    (expr : Expr) (value : Bool) : Prop :=
  available ctx interpret env expr ∧ (value = true ↔ meaning ctx interpret env expr)

end Weft.Finite.Semantics
