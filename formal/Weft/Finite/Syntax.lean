import Weft.Finite.Sets
import Weft.Language.Elaboration

namespace Weft.Finite.Syntax
open Weft.Language Weft.Finite.Sets

/-- Resolved lexical indices, not textual aliases. Global paths retain their old
exact-path semantics, independently of reference-valued local bindings. -/
inductive Term where
  | literal (value : Value)
  | captured (member : Member)
  | named (index : Nat)
  | bound (index : Nat)
  | global (path : Path)
  | field (base : Term) (selector : List String)
  deriving DecidableEq, Repr

inductive SetExpr where
  | empty (elementType : Ty)
  | singleton (term : Term)
  /-- Resolved literal/spread concatenation: `{x, ...s}` is the union of a
  singleton and the captured set expression, never a scalar text coercion. -/
  | union (elementType : Ty) (left right : SetExpr)
  | named (elementType : Ty) (index : Nat)
  | select (elementType : Ty) (base : Term) (selector : List String)
  deriving DecidableEq, Repr

inductive Atom where
  | legacy (surface : Surface)
  | equal (left right : Term)
  | notEqual (left right : Term)
  | predicate (name : PredicateName) (arguments : List Term)
  | setEqual (left right : SetExpr)
  deriving DecidableEq, Repr

inductive Expr where
  | atom (atom : Atom)
  | neg (body : Expr)
  | conj (left right : Expr)
  | disj (left right : Expr)
  | all (domain : SetExpr) (body : Expr)
  | any (domain : SetExpr) (body : Expr)
  deriving DecidableEq, Repr

abbrev Env := Nat → Option Member
abbrev TypeEnv := Nat → Option Ty

def push {α : Type} (value : α) (env : Nat → Option α) : Nat → Option α
  | 0 => some value
  | n + 1 => env n

def types (env : Env) : TypeEnv := fun i => (env i).map (fun m => m.value.type)

/-- A context is one pinned profile/capture. Reference selectors use the full
resolved Value; equal display labels are never a reference-coherence premise.
A host claiming correspondence must supply coherent value/profile interpretations. -/
structure Context where
  legacy : Environment
  profile : Profile
  named : Nat → Option Member
  sets : Nat → Option CapturedSet
  fieldType : Ty → List String → Option Ty
  field : Value → List String → Option Member
  collectionType : Ty → List String → Option Ty
  collection : Value → List String → Option CapturedSet
  globalOrigins : Path → List Weft.Grounding.Binding

def termType (ctx : Context) (env : TypeEnv) : Term → Option Ty
  | .literal v => some v.type
  | .captured m => some m.value.type
  | .named i => (ctx.named i).map (fun m => m.value.type)
  | .bound i => env i
  | .global p => ctx.legacy.fieldTypes p
  | .field base selector => (termType ctx env base).bind (fun ty => ctx.fieldType ty selector)

/-- Explicit finite mathematical empty sets carry a type. Inferring it from raw
source is a separate frontend obligation, not a default external profile. -/
def SetExpr.elementType (ctx : Context) (env : TypeEnv) : SetExpr → Option Ty
  | .empty ty => some ty
  | .singleton term => termType ctx env term
  | .union ty _ _ | .named ty _ | .select ty _ _ => some ty

def resolveTerm (ctx : Context) (env : Env) : Term → Option Member
  | .literal v => some ⟨v, []⟩
  | .captured m => some m
  | .named i => ctx.named i
  | .bound i => env i
  | .global p => (Language.resolveTerm ctx.legacy (.field p)).map
      (fun v => ⟨v, ctx.globalOrigins p⟩)
  | .field base selector => do
      let m ← resolveTerm ctx env base
      let ty ← ctx.fieldType m.value.type selector
      let result ← ctx.field m.value selector
      if result.value.type = ty then
        some ⟨result.value, m.origins ++ result.origins⟩
      else none

def evalSet (ctx : Context) (env : Env) : SetExpr → Option CapturedSet
  | .empty ty => normalize ty [] []
  | .singleton term => do
      let member ← resolveTerm ctx env term
      normalize member.value.type [member] []
  | .union ty left right => do
      let a ← evalSet ctx env left
      let b ← evalSet ctx env right
      if a.elementType = ty ∧ b.elementType = ty then
        normalize ty (a.members ++ b.members) (a.origins ++ b.origins)
      else none
  | .named ty index => do
      let raw ← ctx.sets index
      if raw.elementType = ty then validate raw else none
  | .select ty base selector => do
      let member ← resolveTerm ctx env base
      let declared ← ctx.collectionType member.value.type selector
      let raw ← ctx.collection member.value selector
      if declared = ty ∧ raw.elementType = ty then
        let checked ← validate raw
        normalize ty checked.members (member.origins ++ checked.origins)
      else none

def liftRename (renameFn : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => renameFn n + 1

def Term.rename (renameFn : Nat → Nat) : Term → Term
  | .bound i => .bound (renameFn i)
  | .field base selector => .field (base.rename renameFn) selector
  | other => other

def Term.substitute (replacement : Nat → Term) : Term → Term
  | .bound i => replacement i
  | .field base selector => .field (base.substitute replacement) selector
  | other => other

def liftSubstitution (replacement : Nat → Term) : Nat → Term
  | 0 => .bound 0
  | n + 1 => (replacement n).rename Nat.succ

def SetExpr.substitute (replacement : Nat → Term) : SetExpr → SetExpr
  | .empty ty => .empty ty
  | .singleton term => .singleton (term.substitute replacement)
  | .union ty a b => .union ty (a.substitute replacement) (b.substitute replacement)
  | .named ty i => .named ty i
  | .select ty base selector => .select ty (base.substitute replacement) selector

def Atom.substitute (replacement : Nat → Term) : Atom → Atom
  | .legacy s => .legacy s
  | .equal a b => .equal (a.substitute replacement) (b.substitute replacement)
  | .notEqual a b => .notEqual (a.substitute replacement) (b.substitute replacement)
  | .predicate n args => .predicate n (args.map (Term.substitute replacement))
  | .setEqual a b => .setEqual (a.substitute replacement) (b.substitute replacement)

def Expr.substitute (replacement : Nat → Term) : Expr → Expr
  | .atom a => .atom (a.substitute replacement)
  | .neg e => .neg (e.substitute replacement)
  | .conj a b => .conj (a.substitute replacement) (b.substitute replacement)
  | .disj a b => .disj (a.substitute replacement) (b.substitute replacement)
  | .all domain body => .all (domain.substitute replacement)
      (body.substitute (liftSubstitution replacement))
  | .any domain body => .any (domain.substitute replacement)
      (body.substitute (liftSubstitution replacement))

end Weft.Finite.Syntax
