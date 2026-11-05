# `weft.report/1` machine contract

This is Weft's report envelope, not a Writfold receipt or a new Writfold wire
namespace. JSON stdout contains one complete object. Human output is a projection
of the same values. Local development commands never set `writfold_grounded` or
`effect_authority` to true.

## Envelope

Required fields:

- `schema`: exact string `weft.report/1`.
- `kind`: `analysis`, `assessment` or `diagnostics`.
- `scope`: `local-analysis` or `local-symbolic` for the implemented development
  paths. A future grounded path requires its own admitted input/producer contract;
  merely changing this string cannot establish grounding.
- `source`: `{ kind: "loaded", path, sha256, bytes, content }` for bytes actually
  read, or `{ kind: "unavailable", reason, path? }` when no source could be read.
  Content is `{ encoding: "utf-8", text }` for valid source, or
  `{ encoding: "hex", hex }` for rejected non-UTF-8 bytes. This preserves the
  exact local query for replay; missing files/arguments never receive an invented
  empty-source digest.
- `execution`: `complete`, `incomplete` or `failed`.
- `writfold_grounded`: Boolean, false for all local commands.
- `effect_authority`: false; reports never carry effect permission.
- `diagnostics`: ordered diagnostic array, never discarded on a negative outcome.
- `review`: present only after a review header was actually parsed.
- `checks`: ordered findings, empty when source cannot be elaborated.
- `trace`: ordered DAG nodes with backward-only local references.
- `budgets`: the selected source/token/depth/construction/member/instance/atom/
  valuation/evaluation-step/trace/output bounds and actual construction accounting.
- `origins`: present for compiled theories; a separate backward-only provenance
  DAG. Origin IDs and logical trace IDs are distinct local domains.

No invented placeholder contexts, artifact hashes or producer identities. The
source digest is an ordinary named SHA256 field, not a Writfold fingerprint kind.
Offsets/counts are nonnegative bounded JSON integers; semantic natural literals
are typed decimal strings to preserve arbitrary precision.

## Parsed review

`review` carries `name`, `profile`, `requested_context`, `requested_snapshot`,
`target` and `bindings`. Each target/binding has a nominal local numeric `id`,
`name`, `kind`, `reference`, `span` and `resolution`. The current local resolution
is exactly `unresolved`. These are **requested** references, not durable identity
claims. Preserve the decoded Writfold citation string without normalization or
inventing a new citation syntax. Never conflate a local ID with a corpus object ID.

`needs` retains the complete ordered explicit requirement occurrences. Each
hypothesis retains its declaration and expression spans; a formula root appears
only after successful materialization. Analysis does not fabricate a formula for
an invalid or unelaborated assumption. Reference resolution, remote assessments
and durable bindings remain WR1-WR5.

Native sets are recorded in `review.sets` with a report-local declaration ID, name,
source span, element type (or a genuinely parametric empty type), initializer/origin
DAG, materialization status and exact members when available. IDs are local and
kind-tagged, not Writfold object IDs. An unresolved set has no invented member list
or zero cardinality. Preserve duplicate origins and empty-spread dependencies even
when equal resolved values share one distinct member entry.

A set produced by algebra carries its operator (`union`/`intersection`/
`difference`), both operand records with spans, the normalization input count
for this result (union: both normalized operand lists, hence the cardinality
sum before cross-operand deduplication; intersection/difference: one entry per
qualifying or surviving left member, hence result cardinality), and a fresh
local materialization observation — never a fabricated imported-source
history. Removed members and the entire right operand stay reachable as
operand evidence even for an empty result; empty results retain their exact
element type and never publish zero cardinality for an unmaterialized binding.

## Check finding

Each check has:

- `id`, `name`, `span` and `result`: `entailed`, `refuted`, `undetermined`,
  `inconsistent-premises`, `unknown` or `not-evaluated`.
- `basis`: `hypothetical`, `unresolved`, `unusable` or `grounded`. Local symbolic
  results are hypothetical; unresolved external inputs remain independent gaps.
- `explanation`: deterministic statement of the actual checked relation and scope,
  not generated claims of global code safety.
- `hypotheses`: IDs of all preceding hypotheses conservatively included.
- `needs` and `dependencies`: explicit requirements and all used input bindings.
- `atoms`: exact ordered predicate names and typed literal arguments used by this
  check's finite theory. The same ground call receives one local atom index.
- `coverage`: `atom_count`, `required_valuations` (decimal string when computed),
  `checked_valuations`, `complete`. An unrepresentable/excessive domain uses an
  explicit `required_power_of_two` exponent instead of overflowing a counter.
- `models`: optional `positive`/`negative` objects containing `valuation`,
  `assignment` and `node_values`. Assignment positions follow the exact active
  `atoms` order, first atom most significant. A missing model is not an empty
  assignment.
- `trace_root`: present only for an actually constructed trace.

Each predicate argument is `{ kind: "boolean", value: bool }`,
`{ kind: "natural", value: decimal-string }` or `{ kind: "text", value: string }`.
External nominal values require the owner-published exact interpretation contract;
there is no source text-to-identity coercion.

For completed entailment/refutation, `checked_valuations` and captured accounting
must establish complete search, not merely a successful prefix. Undetermined
requires both model witnesses. Inconsistent requires complete absence of any
premise model. Budget exhaustion is unknown and `complete: false`.

## Trace nodes

Every node has `id`, `kind`, `inputs`, optional `span`, and kind-specific details.
Only prior nodes may appear in `inputs`; every root must exist. Initial kinds:

- `binding-request`: exact requested reference/kind and unresolved status.
- `literal` / `comparison`: typed operands, operator and actual computed result.
- `predicate`: exact name, arguments and local atom index; no asserted truth.
- `assumption`: hypothesis ID, formula root and source span.
- `evaluation`: exact finite query, premise roots, budget and complete valuation
  rows (each assignment, premise truth values and query truth value).
- `classification`: outcome, coverage, model witnesses and non-grounded basis.
- `set-binding`: named or anonymous immutable materialization, typed members and
  linked origin root. Spread operations are explicit nodes in the separate
  origin DAG, not a second invented logical operation.
- `set-operation`: union/intersection/difference with both operand set/link
  records, operator, typed result membership in stable first-occurrence order,
  the per-result normalization input count, and the complete operation-level
  dependency closure including eliminated members and the full right operand.
  Union origin nodes merge both operands' member origins; intersection retains
  contributing origins from both operands for retained identities; difference
  keeps surviving left origins and links the entire right operand closure.
- `comparison` covers `==`/`!=`, scalar membership `in` and subset `<=`:
  typed operands and links to both whole operand records (the scalar and the
  complete RHS set for `in`; both complete sets for `<=`), the computed truth
  or an explicit refusal. A false subset explanation carries the deterministic
  first-left member absent from the right operand, tied to those exact finite
  operands; it is not a symbolic model-relative witness. An unavailable operand
  is a refusal or gap, never `false`.
- `quantifier`: kind, source/binder identity, captured domain, enclosing instance,
  member/instantiated counts, expansion budget, complete coverage and vacuity.
- `quantifier-instance`: exact member and lexical environment/substitution,
  instantiated body trace root, dependencies and checked per-model outcomes.

Nested expansions have distinct trace/instance IDs even when they share one source
binder span. Witnesses and failing members reference a checked valuation row and
an actual member; uniform per-member entailment/refutation is a separate claim.
For example, `A or B` entails an existential without identifying one uniformly
entailed member. Do not downgrade that valid result or invent a uniform witness.
Keep materialization/search/report completeness and external-inventory completeness
distinct; no finite result claims a larger domain than its actual bound input.
Allocated intermediates from failed lowering are labelled
`unreferenced-intermediate`; allocation does not establish successful declaration
materialization or complete quantified coverage. Named unmaterialized sets have
no invented members or zero cardinality.

The qualified CLI supplies actual kernel results. The Rust projection library
checks coverage/linkage invariants, but does not authenticate arbitrary caller
records or constitute a standalone untrusted proof-certificate checker.

Rows may be streamed during serialization rather than duplicated in memory, but
must be complete within the selected report budget. If a full trace cannot be
retained/emitted, output explicit incomplete diagnostics instead of calling the
partial object complete or reusable. No opacity hidden behind a prose summary.

## Diagnostics

`{ code, phase, severity, message, primary, secondary, expected, actual, help }`.
Primary/secondary locations use `{ start, end }` half-open UTF-8 byte spans;
secondary entries also have a short label. Primary is omitted when no source
position is known (for example an unreadable file). Optional expected/actual/help
fields are omitted when not applicable, never populated with guesses. Phases: `lex`,
`parse`, `resolve`, `type`, `profile`, `evidence`, `evaluate`, `report`, `io`.
Severity is `error` or `warning`; a warning cannot waive a mandatory obligation.

Examples of diagnostic families: E10xx malformed tokens/grammar; E20xx binding
and type errors; E30xx unavailable profile/evidence; E40xx computation/trace limits;
E50xx IO/protocol failures. Specific message wording may improve without changing
the stable code or typed details. Tests assert behavior and positions, not wording.

## Exit and trust semantics

`analyze` returns 0 only for successful local structural analysis. `prove` returns
1 for a complete hypothetical/negative/undetermined result, and 2 for source,
required-input or budget failure; it cannot return a grounded-success code while
WR1-WR5 are unavailable. A future live grounded review may return 0 only under the
full positive grounding rule. Every report remains non-authoritative for effects.
