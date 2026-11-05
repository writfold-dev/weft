# Execution-graph integration: required, not implemented

This clarifies the full P06/P07/P09 acceptance scope. It does not add a Weft VM,
modify Writfold or claim its production services exist. The Writfold-owning agent
receives the actual interface proposals in handover plan/06-writfold-handoff.md.

## Three distinct graphs

1. The **Weft derivation graph** explains which observations, hypotheses, rules
   and logical checks support a report. It carries no execution capability.
2. A **Writfold procedure/control graph** describes typed steps, calls, branches,
   joins, effects, budgets and gate floors. Its definition is admitted knowledge,
   not something obtained by treating a proof trace as executable instructions.
3. A **Writfold run/invocation graph** records actual activations, attempts,
   effects and receipts selected by validated ledger heads. Activity is a derived
   view, never the authoritative writer of those events.

## Required real flow

- The agent authors an exact prospective change and its declared obligations.
- It selects an admitted Writfold procedure and supplies exact typed inputs, or
  proposes a new/changed procedure graph through Writfold's existing authoring,
  validation, review and admission path. Weft does not invent that schema.
- Weft assesses the declared obligations against exact scoped knowledge and
  emits the complete report/derivation and dependency closure.
- Writfold validates any graph/procedure proposal's types, closed dependency
  references, effect ceilings, required gate floors, resource bounds, call/join
  correctness and current authority before admission. A positive Weft report
  does not replace those checks or authorize the graph.
- Through WR6, retain the exact report and link its subject/procedure/repository
  vector to the admitted plan and run. Activation instantiates the actual run
  graph from the selected procedure, not from an arbitrary Weft trace.
- Through WR7, recheck live guards and execute actual qualified effects, retaining
  receipts and reconciling unknown outcomes without blind replay.
- Through WR8, propose learning/knowledge changes from retained observations;
  evaluate and review them against a fixed protocol before ordinary admission.

## Additional details needed from the owning agent

WR6 must include the exact supported **procedure/graph proposal and run-start
input schemas**, their validation/admission operations, producer/gate profiles,
expected predecessor and idempotency semantics. Reuse the same agent-facing
services; there is no Weft-only graph import or second normal writer.

The composed smoke must observe a real instantiated run graph and its ledger
references, not merely create JSON that resembles a graph. Include a rejected
wrong-kind/invalid graph proposal, stale subject/report binding, weakened gate
floor, insufficient authority and lost-acknowledgement recovery where those
operations are supported by the qualified Writfold contract.

These acceptance obligations remain externally blocked. A local Weft binary can
exercise its calculus and reports now but cannot manufacture these observations
or count an unavailable graph/admission/effect path as passed.
