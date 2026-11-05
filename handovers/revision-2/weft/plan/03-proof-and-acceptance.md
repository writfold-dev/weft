# Proof-first finite collection acceptance

Add P01S/WEFT01S between original calculus qualification P01 and frontend/implementation
P02-P04. Final P05-P09 integration requirements remain unchanged and required.
The old `lean-009` pass retains only its exact revision-1 scope.

## Required new theorem families

| ID | Required meaning |
| --- | --- |
| Q01 | Normalization preserves exact extensional membership and deterministic first-occurrence representation. |
| Q02 | Materialized sets preserve the declared homogeneous scalar/nominal type; unsupported/mixed values cannot pass. |
| Q03 | Spreading/union/dedup retains every required origin and cannot hide unresolved members. |
| Q04 | Successful immutable binding extends without changing prior values; failed/duplicate/self-dependent binding cannot install a value. |
| Q05 | Lexical bound-variable substitution/environment extension is capture-avoiding and preserves term/body meaning. |
| Q06 | Complete finite `forall` lowering agrees with independent universal membership semantics, including empty domains. |
| Q07 | Complete finite `exists` lowering agrees with independent existential membership semantics and produces valuation-scoped witnesses. |
| Q08 | Quantifier/instance traces faithfully bind the exact domain, member substitutions, coverage, vacuity, dependencies and outcomes. |
| Q09 | Exhausted/incomplete expansion or lookup cannot produce a completed quantified verdict or successful binding. |
| Q10 | Embedding the earlier scalar/propositional fragment preserves its meaning and non-authority guarantees. |

Use the same pinned Lean core-only toolchain and complete source-bound audit. Every
new theorem needs explicit assumptions, inhabited positive premises, substantive
negative calibration and a shipping-symbol/fixture mapping once Rust exists.
A theorem about a fold of arbitrary Booleans alone does not prove binder hygiene,
field interpretation, source-domain completeness or collection materialization.

## Required adversarial scenarios

S31 explicit finite literal and duplicate normalization; S32 same text/different
nominal kind or realm; S33 spread union and repeated/diamond spread dependency
preservation; S34 missing/expired member not dropped by deduplication; S35 immutable
binding, duplicate name, forward/self cycle and failure atomicity; S36 nested binder
shadowing, outer-variable reference and alpha-renaming/capture calibration;
S37 universal success and model-scoped failing members; S38 existential witnesses,
nonuniform-witness entailment and complete no-witness results; S39 empty-domain laws,
visible vacuity and invalid body still rejected; S40 mixed/ambiguous element typing
and scalar/set misuse;
S41 nested expansion budget exhaustion without a partial result; S42 incomplete
external inventory cannot claim a broader complete domain; S43 faithful per-member
trace, origin preservation and forged witness/counterexample refusal;
S44 prior scalar-language conservation and unchanged authority boundary.

## Implementation consequences

Update the EBNF/lexing contract for `:=`, `...`, set braces and quantifier keywords;
maximal munch must not confuse `...` with field `.` or `:=` with check/assume `:`.
There is no `let` compatibility form. Keep existing citation declarations unchanged.

Frontend passes must resolve lexical binders before substitution, infer/check set
and predicate types, preserve immutable set snapshots and cache only qualified
materializations. Reporting must retain source locations through every expansion.
Do not represent a failed collection as an empty Vec or a wrong-kind reference as
an untyped string. No actual Writfold IDs are minted by this extension.

The Writfold owner is asked to provide captured finite collection manifests and
exact member bindings with query/cut/profile/coverage information through shared
agent APIs. This is an addition to WR4/WR5 proposals, not permission to add a
Weft-specific endpoint or alter that repository.

After the new Lean gate passes, execute real Rust examples and negative cases for
all S31-S44, plus the earlier scenarios. Build and smoke the actual musl CLI through
the existing admitted BuildKit/Compose path. No symbolic set example qualifies the
still-blocked real execution/admission workflow.
