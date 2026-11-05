import Weft.Finite.Syntax

namespace Weft.Finite.Typing
open Weft.Language Weft.Finite.Syntax

def sameType : Option Ty → Option Ty → Bool
  | some a, some b => decide (a = b)
  | _, _ => false

def legacyTerm (ctx : Context) : Language.Term → Option Ty := Language.inferTerm ctx.legacy

def legacyCheck (ctx : Context) : Surface → Bool
  | .boolean _ => true
  | .equal a b | .notEqual a b => sameType (legacyTerm ctx a) (legacyTerm ctx b)
  | .predicate name args =>
      match ctx.profile.signature name with
      | none => false
      | some signature => decide (args.map (legacyTerm ctx) = signature.map some)
  | .neg e => legacyCheck ctx e
  | .conj a b | .disj a b => legacyCheck ctx a && legacyCheck ctx b

def checkSet (ctx : Context) (env : TypeEnv) : SetExpr → Bool
  | .empty _ => true
  | .singleton term => (termType ctx env term).isSome
  | .union ty a b => checkSet ctx env a && checkSet ctx env b &&
      sameType (a.elementType ctx env) (some ty) && sameType (b.elementType ctx env) (some ty)
  | .named ty i => match ctx.sets i with
      | none => false
      | some set => decide (set.elementType = ty)
  | .select ty base selector =>
      sameType ((termType ctx env base).bind (fun t => ctx.collectionType t selector)) (some ty)

def checkAtom (ctx : Context) (env : TypeEnv) : Atom → Bool
  | .legacy surface => legacyCheck ctx surface
  | .equal a b | .notEqual a b => sameType (termType ctx env a) (termType ctx env b)
  | .predicate name args =>
      match ctx.profile.signature name with
      | none => false
      | some signature => decide (args.map (termType ctx env) = signature.map some)
  | .setEqual a b => checkSet ctx env a && checkSet ctx env b &&
      sameType (a.elementType ctx env) (b.elementType ctx env)

/-- Validation descends into the body before inspecting domain cardinality.
In particular empty domains never excuse unknown names or mixed comparisons. -/
def check (ctx : Context) (env : TypeEnv) : Expr → Bool
  | .atom atom => checkAtom ctx env atom
  | .neg body => check ctx env body
  | .conj a b | .disj a b => check ctx env a && check ctx env b
  | .all domain body | .any domain body =>
      match domain.elementType ctx env with
      | none => false
      | some ty => checkSet ctx env domain && check ctx (push ty env) body

end Weft.Finite.Typing
