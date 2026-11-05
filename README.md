# Weft

Grounded reasoning about proposed changes, using knowledge retained in Writfold.

**Status: proof-first implementation under the
[revision-2 finite-language supplement](handovers/revision-2/weft/AGENT_START_HERE.md).**
The original calculus and the native-set/bounded-quantifier extension are
[qualified in their exact recorded scopes](docs/calculus-assurance.md).
Rust implementation follows those proof gates. Current completion belongs in
[the status ledger](qualification/status.json), not the immutable plan.
No final end-to-end release or shipping-Rust refinement theorem is claimed.

## The question

> Given this exact proposed change, this knowledge snapshot and this intended
> use, which obligations are justified, contradicted, conditional or unresolved?

The first proposed deliverable is a **grounded-plan verification report**, not an
executable plan, an authorization token or an assertion that arbitrary code is
correct. A report explains its dependencies and gaps as carefully as its positive
findings.

## Decisions from the discussion

- Weft is an ordinary Writfold client, using the same structured stdio interface
  as an agent. No Weft-specific Writfold opcodes, bytecode VM, recipe ingestion
  endpoint or second execution engine.
- Weft owns its language, semantic analysis, local evaluation and explanations.
  Any future proof backend has its own explicitly qualified boundary.
- Writfold remains responsible for knowledge identity, admission, context-specific
  assessment, freshness and authorized operations. Weft cannot override a refusal.
- Start with read-only assessment and a report. Retention, execution-history
  attachment and promotion of findings are separate, later admission decisions.
- Language and report contracts are selected under the handover. Actual Writfold
  service mappings remain owner-side proposals; a grammar alone proves nothing.

## Read visually first

[Visual guide](docs/visual-guide.md): system boundary, assessment flow, a report
mockup and the proposed relationship to execution/learning history.

## Design materials

- [Grounded-plan semantics](docs/grounded-plans.md): what grounding can and cannot
  establish, including hypothetical versus established premises.
- [Report proposal](docs/verification-report.md): independent evidence dimensions,
  findings, dependencies and adversarial cases.
- [Language notes](spec/language.md) and [EBNF](spec/grammar.ebnf):
  syntax separated from lexical, static and evaluation rules.
- [Examples](examples/README.md): a declared plan/contract mismatch and conditional
  reasoning, with no invented live citations or production output.
- [Decisions and open questions](docs/decisions.md).
- [Sources and status](docs/references.md).
- [Design checks](docs/design-checks.md): exercised syntax, document and visual
  checks, with explicit limits on what they establish.
- [Finite language direction](docs/finite-language-direction.md): `:=`, sets,
  lexical quantifiers, provenance and model-scoped witnesses.
- [Concrete report contract](spec/report-v1.md).
- [Finite collection request for Writfold](docs/writfold-finite-collections-request.md):
  proposal-only shared reader prerequisites for its owning agent.

## First question to work through

A plan proposes changing pagination from stable to unspecified ordering. The
retained API contract requires stable ordering. Can Weft identify that conflict,
show the exact contract and plan fields, and separately explain whether the
contract is admitted, applicable, fresh and validated for this assessment?

This checks the **declared plan against a contract**. It does not prove that an
implementation behaves like its declaration. That requires separately captured
implementation evidence under a suitable validation profile.

The initial examples and mockup remain illustrative. The
[Writfold integration request](handovers/revision-1/weft/plan/06-writfold-handoff.md)
is proposal-only for its owning agent; this repository does not modify Writfold.
The complete planning, grounding, execution and learning flow remains required,
including any currently blocked external prerequisites.
