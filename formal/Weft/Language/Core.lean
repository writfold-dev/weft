namespace Weft.Language

universe u v w

/-!
# Typed mathematical surface AST (L01)

This module starts after name resolution. A path contains a nominal local binding
and the complete sequence of field selections; lookup is exact, not a search or
fallback. Parsing bytes, escape decoding, declaration-order name resolution,
source spans and production Rust correspondence are outside these theorems.

Types and values are explicit profile inputs. In particular a nominal identity's
kind AND namespace participate in its type; its body is not a text coercion.
`Nat` is mathematical, unbounded natural arithmetic. An environment may be partial
or malformed: resolution checks its declared type against its actual value on
every lookup, so no global well-formedness axiom is hidden in L01.
-/

inductive Ty where
  | boolean
  | natural
  | text
  | identity (kind realm : String)
  deriving DecidableEq, Repr

inductive Value where
  | boolean (value : Bool)
  | natural (value : Nat)
  | text (value : String)
  | identity (kind realm body : String)
  deriving DecidableEq, Repr

def Value.type : Value → Ty
  | .boolean _ => .boolean
  | .natural _ => .natural
  | .text _ => .text
  | .identity kind realm _ => .identity kind realm

structure Path where
  binding : Nat
  fields : List String
  deriving DecidableEq, Repr

inductive Term where
  | literal (value : Value)
  | field (path : Path)
  deriving DecidableEq, Repr

structure Environment where
  fieldTypes : Path → Option Ty
  fieldValues : Path → Option Value

def inferTerm (env : Environment) : Term → Option Ty
  | .literal value => some value.type
  | .field path => env.fieldTypes path

/-- Raw mathematical lookup, not a public successfully typed evaluation. -/
def rawTerm (env : Environment) : Term → Option Value
  | .literal value => some value
  | .field path => env.fieldValues path

/-- Unknown type, absent value and malformed value all fail, never become false. -/
def resolveTerm (env : Environment) (term : Term) : Option Value :=
  match inferTerm env term, rawTerm env term with
  | some expected, some value =>
      if value.type = expected then some value else none
  | _, _ => none

theorem termEvaluationFacts (env : Environment) (term : Term) (value : Value)
    (success : resolveTerm env term = some value) :
    inferTerm env term = some value.type ∧ rawTerm env term = some value := by
  cases ht : inferTerm env term with
  | none => simp [resolveTerm, ht] at success
  | some expected =>
      cases hv : rawTerm env term with
      | none => simp [resolveTerm, ht, hv] at success
      | some actual =>
          by_cases typed : actual.type = expected
          · have same : actual = value := by
              simpa [resolveTerm, ht, hv, typed] using success
            subst value
            simp_all
          · simp [resolveTerm, ht, hv, typed] at success

/-- L01: successful evaluation preserves the independently assigned term type. -/
theorem termTypeSound (env : Environment) (term : Term) (value : Value)
    (expected : Ty) (assigned : inferTerm env term = some expected)
    (success : resolveTerm env term = some value) : value.type = expected := by
  have typed := (termEvaluationFacts env term value success).1
  rw [assigned] at typed
  exact (Option.some.inj typed).symm

theorem missingFieldFails (env : Environment) (path : Path)
    (missing : env.fieldValues path = none) :
    resolveTerm env (.field path) = none := by
  cases ht : env.fieldTypes path <;>
    simp [resolveTerm, inferTerm, rawTerm, missing, ht]

theorem unknownFieldFails (env : Environment) (path : Path)
    (unknown : env.fieldTypes path = none) :
    resolveTerm env (.field path) = none := by
  simp [resolveTerm, inferTerm, unknown]

structure PredicateName where
  realm : String
  name : String
  deriving DecidableEq, Repr

structure Profile where
  signature : PredicateName → Option (List Ty)

structure GroundCall where
  predicate : PredicateName
  arguments : List Value
  deriving DecidableEq, Repr

/-- Every expression constructor in spec/grammar.ebnf, after resolving names.
Parentheses/precedence determine this tree; they are not extra semantic nodes. -/
inductive Surface where
  | boolean (value : Bool)
  | equal (left right : Term)
  | notEqual (left right : Term)
  | predicate (name : PredicateName) (arguments : List Term)
  | neg (inner : Surface)
  | conj (left right : Surface)
  | disj (left right : Surface)
  deriving DecidableEq, Repr

def resolveArguments (env : Environment) : List Term → Option (List Value)
  | [] => some []
  | term :: rest =>
      match resolveTerm env term, resolveArguments env rest with
      | some value, some values => some (value :: values)
      | _, _ => none

/-- Exact list equality checks both arity and every argument's nominal type. -/
def checkCall (env : Environment) (profile : Profile)
    (name : PredicateName) (arguments : List Term) : Option GroundCall :=
  match profile.signature name, resolveArguments env arguments with
  | some signature, some values =>
      if values.map Value.type = signature then some ⟨name, values⟩ else none
  | _, _ => none

def compareTerms (env : Environment) (left right : Term) : Option Bool :=
  match resolveTerm env left, resolveTerm env right with
  | some a, some b =>
      if a.type = b.type then some (decide (a = b)) else none
  | _, _ => none

/-- Strict combination: even a logically irrelevant missing operand is an error. -/
def combine {α : Type u} {β : Type v} {γ : Type w}
    (operation : α → β → γ) : Option α → Option β → Option γ
  | some left, some right => some (operation left right)
  | _, _ => none

/-- Independent source denotation: does not call elaborate, intern, or the IR
checker. The profile's ground-predicate meaning is an explicit mathematical
interpretation, not authority granted to a host callback by its name. -/
def denote (env : Environment) (profile : Profile) (meaning : GroundCall → Bool) :
    Surface → Option Bool
  | .boolean value => some value
  | .equal left right => compareTerms env left right
  | .notEqual left right => (compareTerms env left right).map Bool.not
  | .predicate name arguments => (checkCall env profile name arguments).map meaning
  | .neg inner => (denote env profile meaning inner).map Bool.not
  | .conj left right => combine Bool.and
      (denote env profile meaning left) (denote env profile meaning right)
  | .disj left right => combine Bool.or
      (denote env profile meaning left) (denote env profile meaning right)

end Weft.Language
