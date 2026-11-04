# Reports, diagnostics, traces and identity

## Stable output direction

Use a versioned JSON envelope `weft.report/1`, with a discriminated report kind:
`diagnostics` (source cannot be elaborated) or `assessment` (typed review with
per-obligation results). Human text is a deterministic projection of that same
object. JSON goes to stdout; progress and process diagnostics go to stderr.

An assessment includes:

- query/source digest and byte spans; language/evaluator/profile identities;
- requested and, only when actually resolved, exact subject/context/release/cut;
- intended use and assessment time, never an invented current-world timestamp;
- each binding's role, canonical Writfold identity, acquisition status, applicable
  independent support/freshness/validation/contestation/availability assessment;
- per-check logical result, execution status, grounding basis, hypotheses,
  explicit needs, conservative used dependencies, trace roots and explanations;
- completeness/budget accounting and model/counterexample witnesses;
- report-wide gaps, coverage limits and non-authority status.

Never fill unavailable producer, profile, context, receipt or citation metadata
with plausible placeholders. Unresolved requested references are represented as
unresolved; they cannot occupy the resolved-binding variant.

## Outcome dimensions

Logical: entailed, refuted, undetermined, inconsistent-premises, unknown, or
not-evaluated. Execution: complete, incomplete, failed. Basis: grounded,
hypothetical, unusable or unresolved. Writfold support remains its distinct
NONE/POSITIVE/NEGATIVE/BOTH dimension. Do not collapse these axes into success.

A positive summary requires every declared required obligation to be entailed
on grounded applicable inputs with complete captured closure. Refuted findings
name the violated obligation and actual counterexample/comparison. Conditional
success names each hypothesis and says what evidence would discharge it.
Inconsistency is diagnosed before interpreting classical consequences.

Do not promise minimal unsat cores, minimal dependencies or complete discovery.
Record a conservative complete dependency set and identify it as such. Report
limits are independent of inference limits: truncation must retain an explicit
omission and cannot turn an incomplete report into a reusable complete artifact.

## Trace contract

A report contains an immutable DAG of numbered trace nodes, not a prose-only
explanation. Node variants: input binding, field interpretation, typed comparison,
assumption, rule instantiation, logical evaluation and final classification.
Each node records its rule/profile, input node IDs, output proposition/value,
source span and exact external dependencies. Nodes refer only backward; no cycles,
foreign report IDs or dangling roots. Trace construction/projection must preserve
all required inputs even if an expression could short-circuit.

Positive traces show why a requirement follows and what would invalidate reuse.
Negative traces expose the exact differing values or a checked model and the
incorrect/missing premise. They are observable derivations, not private model
chain-of-thought. Learning candidates may cite them only through separate Writfold
retention/evaluation/admission; a report cannot teach the KB by self-approval.

## Diagnostics

Stable code, phase, severity, primary byte span, secondary labelled spans, expected
and actual types/values, short cause, and concrete remediation. Distinguish lexer,
parser, resolution, typing, profile, evidence, protocol and budget errors. Preserve
all safe independent findings; do not fabricate a downstream type after recovery.
Agent-friendly errors still matter: an LLM can produce malformed strings, stale
citations, wrong kinds or assumptions with the wrong scope.

CLI exit categories: 0 only for complete positive results within the command's
explicit scope; 1 for completed negative/conditional/undetermined assessment;
2 for source/input/protocol/budget failure or unavailable required capability.
A local `analyze` command must identify its non-grounded scope in its output; exit
0 from analysis is not a passed grounded review or authority to act.

## Citation compatibility

Retain the surface `citation STRING`. The decoded string contains exactly the
Writfold public citation token, currently the authored `⟦cite key=value …⟧`
family, or a server-issued handle accepted by the negotiated profile. Weft never
assigns new Writfold IDs or guesses references from labels, working directories,
latest files, source text equality or an apparent unique search hit.

A token's syntactic validity is not its durable binding validity. The owner-side
resolver returns the full typed binding: citation identity, realm, context,
release, repository/source revision, path/provenance, representation/profile,
content identity and selector with explicit units. Initial selectors are half-open
byte ranges into retained Git blobs. A legacy normalized 16-hex span checksum is
not a universal collision-resistant identity or a lineage witness.

Compact handles are scoped to audience/principal, realm, session, generation,
context and cut, with expiry and access recheck. Startup instance/incarnation/
request generation and citation-table generation are distinct nominal domains.
Export records durable bindings; reconnect cannot silently reuse a numeric handle.

Do not invent a global UUID/URI scheme. Globally unambiguous references require
qualified namespace/realm + object kind + stable identity + revision/content and
scope, but Writfold owns their concrete representation and resolver. Existing
`wf1:<kind>:sha256:<digest>` fingerprints keep their registered kinds and preimages;
a Weft query SHA256 is not silently a new Writfold fingerprint kind.

## Shared code boundary

No live relative-path dependency on the other agent's checkout. Request a pinned
owner-landed protocol/identity artifact or Git revision and consume it unchanged
once qualified. Until then, Weft local IDs are nominal and external references
are opaque requests, not counterfeit resolved Writfold domain objects. Do not
copy identity validators and call them shared. No credentials in build images.
