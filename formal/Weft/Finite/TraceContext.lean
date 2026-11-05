import Weft.Grounding.Model

namespace Weft.Finite.Traces

open Weft.Grounding

/-! Captured reporting metadata, not acquisition or authority. An inventory claim
is copied verbatim from the request; finite-domain coverage cannot improve it.
Hypotheses and observations retain their complete original Input records, including
assessment and exact Binding identity. No source locations or live IO are modeled.
Mutation anchors: contextOrigins includes input binding AND dependency edges;
contextView retains inventory, requirements, gaps and the original input list. -/

inductive Inventory where
  | declaredOnly
  | incomplete (omissions : List Binding)
  | claimedComplete (inventory : Binding)
  deriving DecidableEq, Repr

structure TraceContext where
  intendedDomain : Option Binding
  inventory : Inventory
  explicitNeeds : List Binding
  requiredGaps : List Binding
  inputs : List Input
  deriving DecidableEq, Repr

/-- Conservative provenance includes every captured premise, even unused ones. -/
def contextOrigins (context : TraceContext) : List Binding :=
  ((context.intendedDomain.toList ++ context.explicitNeeds) ++ context.requiredGaps) ++
    context.inputs.flatMap (fun input => input.binding :: input.dependencies)

structure ContextView where
  captured : TraceContext
  hypothetical : Bool
  effectAuthority : Bool
  writfoldGrounded : Bool
  deriving DecidableEq, Repr

/-- Valuation-relative reports do not mint world grounding or effect authority. -/
def contextView (context : TraceContext) : ContextView :=
  ⟨context, context.inputs.any (fun input => match input.origin with
    | .hypothesis _ => true
    | _ => false), false, false⟩

theorem explicitNeedRetained (context : TraceContext) (binding : Binding)
    (member : binding ∈ context.explicitNeeds) : binding ∈ contextOrigins context := by
  simp only [contextOrigins, List.mem_append]
  exact Or.inl (Or.inl (Or.inr member))

theorem gapRetained (context : TraceContext) (binding : Binding)
    (member : binding ∈ context.requiredGaps) : binding ∈ contextOrigins context := by
  simp only [contextOrigins, List.mem_append]
  exact Or.inl (Or.inr member)

theorem inputBindingRetained (context : TraceContext) (input : Input)
    (member : input ∈ context.inputs) : input.binding ∈ contextOrigins context := by
  unfold contextOrigins
  apply List.mem_append.mpr
  right
  exact List.mem_flatMap.mpr ⟨input, member, List.mem_cons_self⟩

theorem inputDependencyRetained (context : TraceContext) (input : Input)
    (member : input ∈ context.inputs) (binding : Binding)
    (edge : binding ∈ input.dependencies) : binding ∈ contextOrigins context := by
  unfold contextOrigins
  apply List.mem_append.mpr
  right
  exact List.mem_flatMap.mpr ⟨input, member, List.mem_cons.mpr (Or.inr edge)⟩

theorem hypothesisNotLaundered (context : TraceContext) (input : Input)
    (member : input ∈ context.inputs) (identity : Nat)
    (origin : input.origin = .hypothesis identity) :
    input ∈ (contextView context).captured.inputs ∧
      input.origin = .hypothesis identity ∧
      (contextView context).hypothetical = true := by
  refine ⟨member, origin, ?_⟩
  change context.inputs.any _ = true
  exact List.any_eq_true.mpr ⟨input, member, by simp [origin]⟩

theorem observationNotRefreshed (context : TraceContext) (input : Input)
    (member : input ∈ context.inputs) (assessment : Assessment)
    (origin : input.origin = .observation assessment) :
    input ∈ (contextView context).captured.inputs ∧
      input.origin = .observation assessment := ⟨member, origin⟩

theorem inventoryNotUpgraded (context : TraceContext) :
    (contextView context).captured.inventory = context.inventory := rfl

theorem reportNoAuthority (context : TraceContext) :
    (contextView context).effectAuthority = false ∧
      (contextView context).writfoldGrounded = false := ⟨rfl, rfl⟩

end Weft.Finite.Traces
