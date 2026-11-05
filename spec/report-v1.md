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

`needs` is the complete ordered set of explicit required binding/hypothesis IDs.
Each hypothesis retains its label, source span and formula. Reference resolution,
remote assessments and durable binding records cannot be fabricated by a local
source file; their eventual transport contract remains WR1-WR5.

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
- `models`: optional `positive`/`negative` complete Boolean assignments, indexed by
  `atoms`. Do not serialize a missing model as an empty valid assignment.
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
