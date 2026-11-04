# Grounded plans

Status: proposed semantics for discussion. No Weft checker or Writfold integration
has been implemented or admitted by this document.

## What Weft would produce

A report answering: **what follows about this proposed change from these exact,
authorized knowledge inputs, under this interpretation and these assumptions?**

The report has three useful products:

1. An evidence inventory: what the assessment actually depended on, with durable
   identities and Writfold's context-specific assessments.
2. Findings: satisfied or violated declared obligations, conditional derivations,
   conflicting support and unresolved questions, each with its explanation.
3. A dependency structure: which evidence and rules justify each finding and what
   must be reassessed when a relevant dependency changes.

The third item is a derivation/dependency graph **inside the report**. It is not a
second Writfold execution graph. Retaining it or attaching it to a run is a
separate operation; see the [visual guide](visual-guide.md).

## Three things that must not become one

- **Prospective subject:** the exact plan, patch or design being reviewed. It may
  be unadmitted; otherwise evaluating a new proposal would require accepting it
  first. Its retained identity establishes what was inspected, not its truth.
- **Grounding evidence:** admitted claims, assets, validation receipts and
  registered interpretations whose applicability and usability are checked for
  the specific context and intended use.
- **Hypotheses:** explicit premises used to explore a possible conclusion. Merely
  storing or admitting a statement that someone assumes P does not establish P.

In the proposed strict grounding profile, an unresolved hypothesis cannot
satisfy a required obligation. A conditional analysis remains useful, but cannot
be labelled fully grounded. This applies even when the hypothesis itself has an
admitted record: admission of the record and discharge of its proposition differ.

## Proposed grounding condition

Let S be the exact subject, K the authorized context/release/read cut, U the
intended use, T the explicit assessment time, and P the pinned interpretation and
assessment profile. The report should claim grounding only for a **declared
obligation set and captured transitive dependency closure** D.

A positive grounded assessment would require all of the following:

- Each required obligation has an applicable checked justification under P.
- Each supporting knowledge dependency resolves to its exact retained binding
  in K and satisfies the applicable Writfold admission/usability requirements
  for U at T. An unrelated positive witness is not enough.
- Dependencies on interpretations, rules, validation receipts, selectors and
  completeness evidence are included, not just the final cited claims.
- All required assessments and evaluations completed; no missing, unauthorized,
  stale, contested, unsupported or unvalidated dependency is hidden.
- No unresolved hypothesis is needed by a required derivation. A dependency may
  be called unused only when that fact is established by the selected checker;
  otherwise dependency accounting is conservative.
- Coverage is adequate for the declared task. Any finite universal claim names
  an exact domain and evidence that it is complete for that claim.

This is a proposed conjunction of obligations, not a new Writfold admission
predicate and not yet a proved judgment. Individual results must retain their
independent status even when the conjunction fails.

### What full grounding cannot mean

Weft cannot infer everything an agent privately read, remembered or assumed.
Initially it can assess the declared plan obligations and the reads actually
captured through its evaluation. A complete captured read-set is not proof that
the plan contains every real requirement or every external dependency.

Enforcing that *all* agent reads/effects pass through a controlled boundary would
require separate execution containment and coverage contracts. A query language
alone does not provide that guarantee. Do not inspect or depend on hidden model
chain-of-thought to claim it.

Nor can Writfold admission guarantee universal factual truth. It establishes the
accepted evidence and policy conditions under the system's stated assumptions.
Freshness is profile/time-relative, not a guarantee that an unobserved remote
system has not changed.

## Knowledge support is not classical proof status

Writfold's existing support values are NONE, POSITIVE, NEGATIVE and BOTH. Preserve
them, along with applicability, freshness, validation, contestation, availability
and the resulting policy judgment. BOTH is a representable conflict; NONE is not
false. A positive witness does not make a stale claim usable.

For assets, report the assessments applicable to that asset kind. Do not invent
a four-valued claim judgment or a universal freshness field for opaque bytes.
Associated claims/receipts must be bound to the exact asset and intended use.

Weft's own finite computations or logical derivations are a separate layer.
Importing a Writfold claim as a logical premise requires an explicit checked
bridge from that claim's formula and usability assessment to the selected theory.
Do not treat prose, an admission flag or an LLM interpretation as that bridge.
Contrary evidence must be included according to the profile; a chosen citation
list is not permission to ignore a known conflict.

If a future classical proof profile is selected, it must distinguish entailment,
refutation, two-sided models, inconsistent premises and incomplete search. Check
premise consistency before reporting classical consequences. Do not flatten
Writfold's BOTH into a classical refutation or let inconsistency prove everything.
The first report does not require SAT, SMT or Lean as its implementation choice.

## A small first example

A captured proposal declares pagination ordering `unspecified`. An admitted,
applicable contract requires `stable`. A registered interpretation reads those
fields from exact structured inputs; an associated claim/receipt identifies the
contract's scope and current usability.

The finite obligation is equality of two nominal ordering values. It is violated
under that interpretation. The report should show both fields, their bindings and
the comparison rule. This is more precise than "the plan makes no sense."

If the contract's validation is stale, the report can still describe the historical
field mismatch, but cannot promote it to a currently grounded violation. If the
field cannot be decoded, that is an interpretation failure, not inequality. If
the plan says stable, equality only establishes agreement of the declarations;
it does not prove implementation behavior, performance or test adequacy.

This gives us a bounded first question without selecting a general theorem prover.
Later inference can compose qualified rules with those observations and preserve
the resulting derivation tree and inherited assumptions.

## Transport and execution boundary

Weft uses the ordinary structured stdio interface as an agent would. It may have
an internal typed AST/IR, but that representation is local to Weft. There is no
Writfold opcode set, VM or Weft recipe endpoint.

Pin the scope for an assessment. Each response must match the request/session
and retained bindings. Reconnecting cannot silently switch the context or use a
newer release. A refusal or an unavailable required service is an explicit
execution finding; do not substitute a local filesystem or direct-database read.

Read-only assessment does not implicitly admit evidence, apply a plan, start an
effectful procedure or refresh the world. Any future requested jobs must preserve
Writfold's ownership/cancellation rules. A stopped UI is not proof that its child
processes stopped.

A REPL would share evaluation semantics with batch mode. Successful cells bind
immutable values; failed/interrupted cells cannot introduce successful findings.
Refreshing evidence creates a new assessment. Replay of captured evidence,
rechecking a proof and observing the current world are distinct operations.

## What enriching the execution graph could mean

The revision-5 Execution X view spans admitted procedure definitions, immutable
operational ledger records and derived activity projections. It is not a graph
that Weft writes directly.

A future admitted integration could retain an exact report and its dependency
closure, then reference it from a plan/run/attempt through a suitable existing
or explicitly extended typed Writfold contract. The producer/checker identity and
assurance scope must be recorded; Weft cannot self-issue a trusted gate receipt.
A report can inform review without satisfying an execution gate.

A reusable lesson would be a separate candidate: evaluate, review, admit against
the expected predecessor, retain its justification, then publish through the
ordinary corpus path. None of this happens merely because Weft printed a positive
result. New effects still recheck current authority, policy and dependencies.

Exact attachment APIs and report-envelope mappings are unresolved. Existing
calculus proofs and codec components do not imply those production services exist.
