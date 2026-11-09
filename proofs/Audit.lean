import Lean
import Kernel

/-!
# Axiom audit

Every theorem under `Weft.Core` is audited: its transitive axioms must be a
subset of Lean's standard three. Anything else — `sorryAx`, a project axiom,
an Aeneas `axiom` standing in for an unmodelled external — fails the build.
The headline claims are also required to exist, so a deleted or renamed
theorem cannot pass silently.
-/
open Lean Elab Command

/-- Lean's standard axioms. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The headline claims: set algebra (A01/A03 over value identities), check
classification, and reuse scope equality. -/
def claims : List Name := [
  ``Weft.Core.position_of_spec,
  ``Weft.Core.contains_spec,
  ``Weft.Core.normalize_spec,
  ``Weft.Core.union_spec,
  ``Weft.Core.intersection_spec,
  ``Weft.Core.difference_spec,
  ``Weft.Core.subset_spec,
  ``Weft.Core.same_members_spec,
  ``Weft.Core.role_spec,
  ``Weft.Core.verdict_of_spec,
  ``Weft.Core.classify_spec,
  ``Weft.Core.classify_entailed_iff,
  ``Weft.Core.classify_refuted_iff,
  ``Weft.Core.classify_undetermined_iff,
  ``Weft.Core.classify_inconsistent_iff,
  ``Weft.Core.same_bytes_spec,
  ``Weft.Core.satisfied_spec,
  ``Weft.Core.refusals_spec,
  ``Weft.Core.reusable_iff,
  ``Weft.Core.refuses_any_difference,
]

/-- Every theorem under `Weft.Core`, sorted by name. -/
def coreTheorems (env : Environment) : Array Name :=
  let audited : Name := `Weft.Core
  (env.constants.fold (init := (#[] : Array Name)) fun acc decl info =>
    if audited.isPrefixOf decl && decl.isInternal = false && info.isThm then acc.push decl
    else acc).qsort (fun a b => a.toString < b.toString)

-- `name` is a reserved token once the Aeneas library is imported (its attribute
-- syntax), so declarations are called `decl` here.
def auditAxioms : CommandElabM Unit := do
  let env ← getEnv
  let sorted := coreTheorems env
  if sorted.isEmpty then
    throwError "axiom audit: no theorems under Weft.Core"
  for decl in sorted do
    let axioms := (← collectAxioms decl).qsort (fun a b => a.toString < b.toString)
    logInfo m!"AXIOMS {decl}: {axioms.toList}"
    for ax in axioms do
      unless allowedAxioms.contains ax do
        throwError "axiom audit: {decl} depends on {ax}, which is not a standard Lean axiom"
  for claim in claims do
    unless sorted.contains claim do
      throwError "axiom audit: required claim {claim} is missing or is not a theorem"
  logInfo m!"AXIOM_AUDIT ok: {sorted.size} theorems, {claims.length} required claims, axioms ⊆ {allowedAxioms}"

run_cmd auditAxioms
