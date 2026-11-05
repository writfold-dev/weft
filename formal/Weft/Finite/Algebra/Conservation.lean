import Weft.Finite.Algebra.Budget
import Weft.Finite.Quantifiers

/-!
# Conservation of the previous finite language

A08: embedding the previous finite language preserves meaning and typing, and
the new comparisons cannot promote inventory completeness, hypotheses or
authoritative state. Every algebra result remains non-grounded and
non-authoritative, and absence is relative only to the exact supplied finite
operands.
-/

namespace Weft.Finite.Algebra

open Weft.Language Weft.Finite.Syntax Weft.Finite.Sets Weft.Finite.Semantics
open Weft.Finite.Quantifiers Weft.Finite.Traces

/-- A08: the full earlier scalar AST keeps its exact denotation under the
extended calculus, including all global field paths, predicates and Boolean
nesting — the algebra adds constructors without redefining any old meaning. -/
theorem legacyDenotationConserved (ctx : Context) (interpret : GroundCall → Bool)
    (env : Env) (surface : Surface) (value : Bool) :
    Denotes ctx interpret env (.atom (.legacy surface)) value ↔
      Language.denote ctx.legacy ctx.profile interpret surface = some value :=
  scalarConservation ctx interpret env surface value

/-- A08: quantified meaning over algebraic domains is exactly the previous
finite clause — for every actual member of the exact captured domain set. -/
theorem quantifiedMeaningConserved (ctx : Context) (interpret : GroundCall → Bool)
    (env : Env) (domain : SetExpr) (body : Expr) (set : CapturedSet)
    (captured : evalSet ctx env domain = some set) :
    (Semantics.meaning ctx interpret env (.all domain body) ↔
        ∀ member ∈ set.members, Semantics.meaning ctx interpret (push member env) body) ∧
      (Semantics.meaning ctx interpret env (.any domain body) ↔
        ∃ member ∈ set.members, Semantics.meaning ctx interpret (push member env) body) := by
  constructor <;> simp [Semantics.meaning, captured]

/-- A08: no algebra trace invents authority — every local result keeps
`effect_authority: false` and `writfold_grounded: false`. -/
theorem reportNoAuthority (metadata : TraceContext) :
    (contextView metadata).effectAuthority = false ∧
      (contextView metadata).writfoldGrounded = false :=
  ⟨rfl, rfl⟩

/-- A08: an algebra result never upgrades the captured inventory claim, the
required gaps or the hypothetical status of the inputs. -/
theorem inventoryNotUpgraded (metadata : TraceContext) :
    (contextView metadata).captured.inventory = metadata.inventory ∧
      (contextView metadata).captured.requiredGaps = metadata.requiredGaps ∧
      (contextView metadata).hypothetical =
        metadata.inputs.any (fun input =>
          match input.origin with
          | .hypothesis _ => true
          | _ => false) :=
  ⟨rfl, rfl, rfl⟩

/-- A08 primary: the algebra extension conserves the earlier calculus —
legacy denotation, quantified meaning over algebraic domains, relative-only
absence and non-authority — and cannot promote inventory completeness,
hypotheses or authoritative state. -/
theorem finiteConservation (ctx : Context) (interpret : GroundCall → Bool) (env : Env) :
    (∀ surface : Surface, ∀ value : Bool,
        Denotes ctx interpret env (.atom (.legacy surface)) value ↔
          Language.denote ctx.legacy ctx.profile interpret surface = some value) ∧
      (∀ (domain : SetExpr) (body : Expr) (set : CapturedSet),
          evalSet ctx env domain = some set →
            (Semantics.meaning ctx interpret env (.all domain body) ↔
                ∀ member ∈ set.members,
                  Semantics.meaning ctx interpret (push member env) body) ∧
            (Semantics.meaning ctx interpret env (.any domain body) ↔
                ∃ member ∈ set.members,
                  Semantics.meaning ctx interpret (push member env) body)) ∧
      (∀ (left right result : CapturedSet) (_success : difference left right = some result)
          (value : Value), value ∈ values result ↔
            value ∈ values left ∧ value ∉ values right) ∧
      (∀ metadata : TraceContext,
          (contextView metadata).effectAuthority = false ∧
            (contextView metadata).writfoldGrounded = false ∧
            (contextView metadata).captured.inventory = metadata.inventory) :=
  ⟨fun surface value => legacyDenotationConserved ctx interpret env surface value,
    fun _ _ _ captured => quantifiedMeaningConserved ctx interpret env _ _ _ captured,
    fun left right result _success value => differenceMembership (left := left) (right := right) (result := result) _success value,
    fun metadata => let authority := reportNoAuthority metadata
      ⟨authority.1, authority.2, (inventoryNotUpgraded metadata).1⟩⟩

end Weft.Finite.Algebra
