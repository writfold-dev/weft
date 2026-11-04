# Weft, visually

Design diagrams, not implemented services. Solid arrows describe the proposed
assessment boundary; the final diagram explicitly describes possible later
integration. No graph edge grants authority.

## One client interface, not a new VM

```mermaid
flowchart LR
    A[Agent or human] --> E["Weft<br/>Language and semantic checks<br/>Local evaluation"]
    E <-->|ordinary requests and responses| I["Writfold<br/>Shared stdio interface<br/>Scoped evidence and assessments"]
    E --> R[Read-only verification report]
    A -.->|same interface| I
```

The local evaluator is not a remote instruction set. A later proof backend would
be selected and qualified separately; no solver is required by this diagram.

## From a proposed change to honest findings

```mermaid
flowchart TD
    P[Proposal and declared obligations] --> B[Capture exact inputs and profile]
    B -->|read or decoding failure| F[Typed failure; no verdict]
    B -->|inputs captured| U{Knowledge usable?}
    U -->|No| G[Expose stale or conflicting basis]
    U -->|Yes| C[Check obligations and dependencies]
    C -->|incomplete evaluation| N[Unknown or not evaluated]
    C -->|evaluation complete| H{Hypotheses needed?}
    H -->|Yes| Q[Conditional findings]
    H -->|No| D[Grounded satisfied or violated findings]
    F --> R[Report with coverage limits]
    G --> R
    N --> R
    Q --> R
    D --> R
```

Mixed outcomes stay visible. An unusable premise can explain a historical
comparison but cannot justify a current grounded finding. A pure logical
inconsistency or incomplete search, if such a profile is selected, stays a
separate result rather than entering an ordinary satisfied/violated branch.

## Report surface

![Synthetic report showing a grounded declared-order violation and an unmet stale SDK dependency; not an executed result](report-mockup.svg)

This is a discussion artifact, not an application screenshot. The
[report proposal](verification-report.md) defines the independent information
that the presentation must preserve.

## How a report could later enrich execution history

```mermaid
flowchart TD
    R[Weft report and full dependency closure] -->|separate authorized retention| O[Retained evidence object]
    O -->|validated reference through Writfold| J[Plan or run history in EngineeringLedger]
    J -->|derived projection| X[Execution activity view]
    O -->|optional new proposal| L[Learning candidate]
    L --> E[Evaluation and review]
    E --> A[Existing corpus admission and publication]
    A --> K[New admitted knowledge revision]
```

This is **future integration**, not an existing Weft attachment API. A report may
be useful for review without being a trusted execution-gate receipt. Ledger
references and activity rows cannot publish knowledge; admission and current
effect authorization remain distinct.

The Context, Execution and Learning graphs are semantic views in Writfold's
revision-5 design. Weft adds an explanation/dependency artifact, not a fourth
knowledge database or another operational state owner.
