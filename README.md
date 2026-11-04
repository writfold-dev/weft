# Weft

Grounded reasoning about proposed changes, using knowledge retained in Writfold.

**Status: design exploration, not an implemented language or verifier.** This
repository contains a proposed first use case, semantic boundaries, an illustrative
EBNF grammar, synthetic examples and visuals. None is an executed verification
report, an admitted Writfold profile or a promise that the required production
APIs already exist.

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
- Syntax, logical fragment, report schema and exact service mappings remain
  proposals. A grammar does not settle their semantics.

## Read visually first

[Visual guide](docs/visual-guide.md): system boundary, assessment flow, a report
mockup and the proposed relationship to execution/learning history.

## Design materials

- [Grounded-plan semantics](docs/grounded-plans.md): what grounding can and cannot
  establish, including hypothetical versus established premises.
- [Report proposal](docs/verification-report.md): independent evidence dimensions,
  findings, dependencies and adversarial cases.
- [Language notes](spec/language.md) and [illustrative EBNF](spec/grammar.ebnf):
  syntax separated from lexical, static and evaluation rules.
- [Examples](examples/README.md): a declared plan/contract mismatch and conditional
  reasoning, with no invented live citations or production output.
- [Decisions and open questions](docs/decisions.md).
- [Sources and status](docs/references.md).
- [Design checks](docs/design-checks.md): exercised syntax, document and visual
  checks, with explicit limits on what they establish.

## First question to work through

A plan proposes changing pagination from stable to unspecified ordering. The
retained API contract requires stable ordering. Can Weft identify that conflict,
show the exact contract and plan fields, and separately explain whether the
contract is admitted, applicable, fresh and validated for this assessment?

This checks the **declared plan against a contract**. It does not prove that an
implementation behaves like its declaration. That requires separately captured
implementation evidence under a suitable validation profile.

There is no build, executable, parser, solver integration or live Writfold
assessment in this repository yet. The deliverable here is a reviewed design
proposal; implementation requires resolving the decisions listed above.
