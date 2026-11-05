# Shared control-protocol qualification

`Control.tla` is a *seed* for TLC, not a complete model of the pinned
`writfold.agent/1` transport-control contract. Terminal session states
(committed shutdown, encoding failure, EOF) close the process and stutter;
deadlock checking is disabled for this seed only. Run TLC on `Control.cfg`,
run TLC on each mutant in `mutants/` against its target invariant listed in
`mutants.json`, and run `tlapm ControlSafety.tla` with the pinned tools in an
isolated writable build tree. `scripts/gate model` performs exactly this and
retains all outputs, including every mutant counterexample trace.

Ground truth is the pinned self-contained contract archive retained by the
Writfold owner (archive sha256
`1971ed3fb84a210eee6e53a9af3fb331affb3ad931e7717adb8926b641bba842`; embedded
`contract.json` sha256
`b673d10f7c14c73d8f5778cfb9b2e84a98a159f1553d5c008054402ee85e7be2`) plus its
stateful vectors, per
[plans/writfold-agent-control-contract-ready.md](../plans/writfold-agent-control-contract-ready.md).
This is a model of that shared boundary, not evidence of any running Writfold
service and not a Weft client implementation.

## What is established at seed scope

- TLC explores the finite seed (`MaxGen = 3`) and finds no violation of the
  eleven invariants: type safety, generation/admission accounting,
  once-only initialize and shutdown, shutdown-after-initialize, the
  phase/count agreement, reply-cited commits (encode-before-commit),
  authority isolation, null-id/correlation discipline and the frozen
  post-shutdown generation.
- Seven single-deviation mutants (`mutants.json`) each violate exactly their
  targeted invariant, with retained counterexample traces.
- TLAPS proves `Init => Strong`, `Strong /\ [Next]_vars => Strong'` action by
  action, and `Spec => []Safety` by induction; every obligation is executed
  by `tlapm`, with none deferred.

## Seed abstractions and required expansion

The seed abstracts one request-id spelling, byte bounds as action classes,
JSON structure, process identity and exit codes. Expanding to a full model
before any P05/P06/P07 work closes requires at least: both directions of the
65,536-byte LF-inclusive bound as arithmetic over concrete frame encodings;
the distinct string/integer/null id grammar with lexical integer rules and
-0 normalization; drain-and-continue after oversize frames and the exact
null-id/null-generation error content; generation exhaustion refusing and
closing; notifications interleaved with requests; a final non-newline frame
evaluated at EOF; exit-code classes 0/1/130; and the concrete client
obligations (initialize before use, owned-child reaping, no method invention).
A byte-accurate client/server refinement with an implementation-action bridge
remains separate TLAPS work; liveness is not claimed and any fairness argument
must be designed separately.

No model here exercises corpus, citation, assessment, retention or effect
services: the control profile has none, and a successful handshake must never
be relabelled as grounding. `writfold_grounded: false` discipline is unchanged
by this model.
