# Weft revision 3 — finite set algebra

Authority: Tarek's 5 November 2026 request for a handover implementing the selected
set-algebra design with Lean proofs first, followed by implementation and quality
qualification. This is a requirements supplement, **not an implementation or a
pass receipt**. At handover creation, revision 2 remains the active qualification
authority; no current status or adoption record is changed by this package.

## Deliverable and boundary

Implement native union `|`, intersection `&`, left difference `-`, scalar membership
`in`, and inclusive subset `<=`, end to end: language contract, Lean semantics and
proofs, executable reference, Rust frontend/lowering, dependency-preserving reports,
actual CLI behavior, and exact-source qualification evidence.

Keep homogeneous immutable finite sets, exact typed identity, lexical quantifiers,
complete operand materialization and every origin/required dependency. Removing a
member must not remove the evidence needed to compute the result. Failed inputs
are not empty sets or Boolean false. No `+` alias, complement, symmetric-difference
operator, arithmetic/bitwise overloading, comprehensions, mutation or general loops.

Work only in Weft. Revision 1 and revision 2 remain inherited contracts, pinned by
[base.json](base.json). Do not edit those packages or this frozen package after
landing; requirement corrections need an explicit new revision. Preserve historical
receipts and failed attempts. Writfold work remains owner-side and proposal-only;
P05/P06/P07/P09 remain required and blocked unless independently satisfied. A local
set-algebra component pass is not the final composed product or effect authority.

## Read in this order

1. [Language and semantic decisions](plan/01-language-and-semantics.md).
2. [Proof obligations and proof-first checkpoint](plan/02-proofs-and-reference.md).
3. [Implementation milestones, scenarios and gates](plan/03-implementation-and-gates.md).
4. [Theorem registry](registries/theorems.json) and [gate registry](registries/gates.json).
5. The [revision-2 entrypoint](../../revision-2/weft/AGENT_START_HERE.md) and its
   plans, then the [revision-1 entrypoint](../../revision-1/weft/AGENT_START_HERE.md)
   and its six plans. Their unchanged architecture, evidence and integration rules
   still apply.
6. Current mutable records: [adoption](../../../qualification/handover-adoption.json),
   [status](../../../qualification/status.json), [proof checkpoint](../../../qualification/finite-calculus.json),
   [reference checkpoint](../../../qualification/reference-calibration.json),
   [engineering adoption](../../../qualification/engineering-adoption.json),
   [runtime evidence](../../../qualification/local-runtime.json), and
   [traceability](../../../qualification/traceability.json).

Read these as different things: a requirement is mandatory; a historic pass applies
only to its captured inputs; a new implementation is unqualified until its actual
producers complete. Never copy old counts, hashes or status strings into new evidence.

## Stop/go order

- **M0 — Adopt the exact contract:** preserve revision-2 evidence, select this
  supplement explicitly, freeze source semantics, and prepare the expanded audit
  and scenario inventories. No production Rust changes for this feature.
- **M1 — Prove and qualify:** satisfy A01–A08 plus all inherited L/Q families;
  pass the complete P01A/WEFT01A Lean gate with substantive mutation controls and
  an executable reference. Record the source-bound checkpoint. This unlocks Rust.
- **M2 — Implement:** update every selected syntax position, type/binder/lowering
  path and caller. No parallel legacy evaluator or compatibility shim.
- **M3 — Exercise:** pass S45–S60 and inherited cases using real source inputs,
  full reports and the actual Lean/Rust executables, including refusal/budget paths.
- **M4 — Qualify and land:** run the existing quality/runtime/traceability producers,
  retain the exact musl artifact, update documentation and mutable status honestly,
  and deliver the extension with external blockers still explicit.

The complete registry has 30 theorem families (L01–L12, Q01–Q10, A01–A08), 12
required stages/gates, and 60 required scenarios (S01–S60). These are inventory
requirements, not claimed results. P01A is inserted after P01S and before P02;
the existing `scripts/gate lean` producer must cover it. Do not invent a new CLI
subcommand that merely prints a gate label.

## Completion report

Report implemented syntax; proof and reference receipt paths/hashes; actual runtime
and traceability receipts; the exact binary identity; passing/refused scenarios;
remaining external blockers; and any disclosed assurance limits. Source-AST proofs
and executable agreement are not a parser/Rust refinement theorem. If a prerequisite
is unavailable, finish reachable work, name the missing input and stop at that gate
without weakening it or calling the extension complete.
