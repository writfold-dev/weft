# Weft

Grounded reasoning about proposed changes, using knowledge retained in Writfold.

**Status: qualified local symbolic development binary with a live control client.**
The original and finite-set Lean calculus passed before Rust implementation.
The Rust frontend, finite evaluator and source-linked reports are exercised
under [revision 3](handovers/revision-3/weft/AGENT_START_HERE.md), which adds
native set algebra: union `|`, intersection `&`, left difference `-`, scalar
membership `in` and inclusive subset `<=`, proved first (A01-A08) and then
implemented through the same evaluator and report paths. The local
`weft reuse` surface refuses any prior-report reuse across changed scope, and
`weft control` drives the owner-pinned `writfold.agent/1` transport-control
contract through a real stdio session with the vendored owner artifact under
`contracts/writfold-agent-1/`.
[Runtime assurance](docs/runtime-assurance.md) records the exact boundary.
Real Writfold data integration and the final composed release remain blocked;
no shipping-Rust refinement theorem or effect authority is claimed.

## Try the actual binary

Download the Linux x86_64 musl archive from the
[private development release](https://github.com/writfold-dev/weft/releases/tag/v0.1.0-dev.1).
No Rust, Lean, Python or companion is needed for these local commands.
From this checkout, point `WEFT` at the unpacked executable:

```sh
WEFT=/path/to/unpacked/weft
"$WEFT" --version
"$WEFT" analyze examples/sets.weft
"$WEFT" prove examples/sets.weft --human
"$WEFT" prove examples/set-algebra.weft --human
"$WEFT" prove examples/sets.weft > report.json && "$WEFT" reuse report.json examples/sets.weft
"$WEFT" control /path/to/pinned/writfold --expect-sha256 70b0d07b18e2f1bd70fc34fce4cc5335fccdd5c6307c014f55abf81ecd97fcca
```

JSON is the default; `--json` and `--human` select the view. Analysis exits 0 on
local structural success. A complete hypothetical proof result exits 1—even
when entailed. Reuse exits 0 only on exact report-recorded scope equality and
1 on any named difference; control exits 0 only on a complete pinned-identity
session. Malformed, unresolved or incomplete work exits 2. Read the finding
categories, not an exit code as an approval token.

The set example entails the checks over assumed SDK support, but extending the
domain with an unsupported SDK remains undetermined. Every result retains
`writfold_grounded: false` and `effect_authority: false`.

## The question

> Given this exact proposed change, this knowledge snapshot and this intended
> use, which obligations are justified, contradicted, conditional or unresolved?

The current deliverable is a **local verification report**: outcomes, explanations,
source/assumption links, complete finite traces and explicit unresolved inputs.
It is not an executable plan, an authorization token or a claim that arbitrary code
is correct. The full grounded-plan workflow remains the required integration goal.

## Decisions from the discussion

- Weft is designed to drive Writfold through the same structured stdio interface
  as an agent. The production client is blocked on owner-landed services/contracts;
  no Weft-specific opcodes, bytecode VM, recipe endpoint or second effect engine.
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
- [Examples](examples/README.md): five executed local theories and two external
  contract proposals that correctly refuse without real Writfold inputs.
- [Decisions and open questions](docs/decisions.md).
- [Sources and status](docs/references.md).
- [Design checks](docs/design-checks.md): exercised syntax, document and visual
  checks, with explicit limits on what they establish.
- [Finite language direction](docs/finite-language-direction.md): `:=`, sets,
  lexical quantifiers, provenance and model-scoped witnesses.
- [Concrete report contract](spec/report-v1.md).
- [Shared control-protocol model](model/README.md): TLA+ seed, TLC mutant
  checks and executed TLAPS proofs for the pinned `writfold.agent/1`
  transport contract (P10); protocol model only, no grounding claimed.
- [Finite collection request for Writfold](docs/writfold-finite-collections-request.md):
  proposal-only shared reader prerequisites for its owning agent.
- [Build and qualification](docs/build-and-qualification.md): exact local producer
  commands, resource boundaries and the static runtime package.
- [Rust implementation](docs/rust-implementation.md): crate dependencies,
  bounded passes, trace representation and calibrated source policies.
- [Complete traceability](qualification/traceability.json): all 22 theorem
  families, 11 gates and 44 scenarios, including explicit external blockers.
- [Set-algebra implementation handover](handovers/revision-3/weft/AGENT_START_HERE.md):
  selected `|`, `&`, `-`, `in`, `<=` semantics, Lean-first milestones and mandatory
  gates. Requirements only; revision 2 remains the active qualified scope.

## First question to work through

A plan proposes changing pagination from stable to unspecified ordering. The
retained API contract requires stable ordering. Can Weft identify that conflict,
show the exact contract and plan fields, and separately explain whether the
contract is admitted, applicable, fresh and validated for this assessment?

This checks the **declared plan against a contract**. It does not prove that an
implementation behaves like its declaration. That requires separately captured
implementation evidence under a suitable validation profile.

The external examples and original report mockup remain illustrative. The
[Writfold integration request](handovers/revision-1/weft/plan/06-writfold-handoff.md)
is proposal-only for its owning agent; this work does not modify Writfold.
The complete planning, grounding, execution and learning flow remains required.
Current completion belongs in [the status ledger](qualification/status.json),
not the immutable plan.
