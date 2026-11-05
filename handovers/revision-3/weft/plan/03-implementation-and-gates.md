# Implementation milestones and qualification gates

This file is the implementing agent's working acceptance checklist. Gates are
requirements, not status. Keep actual progress/receipts in mutable qualification
records outside the frozen handover. Do not run expensive producers concurrently
against shared caches or ignore the admitted workstation's resource headroom.

## M0 — Contract adoption, before implementation

- Verify this package's `MANIFEST.sha256`, its revision-2 base pin and the inherited
  revision-1 pin. Preserve the old adoption, status, proof/reference, engineering,
  runtime and traceability ledgers as exact historical snapshots; do not overwrite
  historical receipts or append progress inside immutable handovers.
- Update `spec/grammar.ebnf`, `spec/language.md`, `docs/implementation-profile.md`
  and, where needed, `spec/report-v1.md` to the selected semantics. Settle bounded
  parsing, type propagation, normalization input counts and actual work accounting
  before proofs. Do not quietly change operator precedence or reduce syntax positions.
- Explicitly adopt revision 3 in `qualification/handover-adoption.json`, with both
  base authorities pinned, inventory 12 stages/12 gates/30 theorem families/60
  scenarios, actual source-contract hashes, the new required registry, and the
  expanded audit/mutation profiles. Recompute counts from real inventories.
- Preserve the existing engineering policy and already adopted dependency edges;
  reconcile `qualification/engineering-adoption.json` with the new authority rather
  than losing its documented allowances. No new dependency is expected for this work.
- Add P01A/WEFT01A to mutable status as not passed. Scope old component passes to
  their historical bytes; P02/P03/P04/P08 require new evidence for this extension.
  P00 can be reused only while its admitted inputs/tool/storage identity still apply.
- Use `scripts/contracts.py` as the enforcing mechanism. It checks manifests,
  transitive base conservation, dependency order, counts, source-contract hashes,
  audit policy and mutation-family coverage. A mismatch is a gate failure, not a
  reason to relax the checker. Missing local tool images or preserved receipts are
  exact prerequisites to resolve, not permission to substitute a moving checkout.

**Exit:** one explicit, internally consistent new contract; old evidence retained;
new obligations visibly unpassed. Lean implementation/audit preparation may proceed.
No production Rust syntax/evaluator/report implementation for this feature yet.

## M1 — Lean gate

Complete [the proof/reference plan](02-proofs-and-reference.md). Record the exact
new calculus receipt before starting M2. Keep the original interpretation boundary:
formal source AST semantics are not a raw-source parser proof, and reference
agreement does not prove the shipping Rust implementation correct.

**Exit:** P01A and inherited calculus obligations actually pass under the new
contract; the extended reference is executable and source-bound. The Rust producer
must refuse if the proof/reference prerequisites are missing, stale or mismatched.

## M2 — Complete runtime cutover

Reuse the current architecture and nominal IDs. Extend existing representations;
there must be one authoritative set materialization path and one report projection.

| Existing path | Required work |
| --- | --- |
| `crates/weft-frontend/src/lexer/token.rs`, `lexer.rs` | Add the selected punctuation, maximal munch and actionable token descriptions. Keep keyword boundaries and unsigned natural literals. |
| `crates/weft-frontend/src/ast.rs`, `parser/values.rs`, `parser/expressions.rs`, `parser/cursor.rs` | Set operator nodes/precedence, membership/subset comparisons, parentheses and non-chaining checks in every permitted position; charge token/AST depth including compound comparables. |
| `crates/weft-frontend/src/typing.rs`, `types.rs`, `resolve.rs`, `semantic.rs` | Unify complete operand types, preserve parametric/typed empties, visit every operand for transitive dependencies, and distinguish scalar binders from same-spelled set declarations. |
| `crates/weft-frontend/src/lower_sets.rs`, `lower_expr.rs`, `lower_quantifier.rs`, `lower.rs`, `lower/finish.rs` | Materialize both operands through existing `SetId`/origin paths; lower membership/subset to checked literals with semantic detail; preserve domain/body capture and binding failure atomicity. |
| `crates/weft-domain/src/theory/finite.rs`, `records.rs`, `builder.rs`, `limits.rs` | Reuse `TheoryBuilder::add_set`, `add_origin`, `charge`, member reservation and backward-only origin links. Preserve typed result/operand closure, operator details and honest checked accounting. |
| `crates/weft-wire/src/finite.rs`, `publication.rs`, `trace.rs`, related projection modules | Project the actual captured records; publication reachability must retain both operands and removed-member origins, including empty results and predicates. No reevaluation or fabricated members on failed sets. |
| `crates/weft-cli/src/run.rs` and existing frontend/domain/wire/CLI behavioral tests | Exercise unchanged exit/output boundaries on new syntax. Keep kernel classification/model semantics unchanged unless an actual new record requires a mechanical consumer update. |
| `scripts/rust_scenarios.py`, `rust_smoke.py`, `rust_differential.py`, `run_rust.py` | Add real source scenarios, operator-level reference comparison and required scenario accounting. Preserve existing logical/model differential checks. |

Search all consumers of changed exported enums/records before editing them; update
all exhaustive matches, validators, builders and report projections. Use language
server references where available. Do not leave compatibility aliases, dead enum
variants, hidden fallback evaluation or obsolete comments behind.

Bound every new traversal and account for the real algorithm: a nested membership
scan can be quadratic, so charging only linear member counts is insufficient.
Use a checked conservative precharge or metered scans consistent with the proved
cost model. Check overflow; do not use wrapping/saturating arithmetic to fake a
completed budget. Borrow immutable inputs, share IDs/origins, and allocate only
needed output; membership/subset must not construct throwaway difference sets.
Do not add a dependency or abstraction merely to avoid a small bounded operation.

**Exit:** all selected syntax positions execute with matching semantics, types,
provenance and failure behavior. Compilation or a single happy-path check is not
this milestone's acceptance.

## M3 — Required behavior and runtime evidence

Add S45–S60 to traceability, retaining S01–S44 and their honest existing scopes.
Each row is a scenario family: cover its distinct branches, not merely one example
bearing its ID. Permanent tests must catch consumer-visible semantics, boundaries,
transitions or errors; do not add source-text assertions, mock echoes or tautologies.

| ID | Observable acceptance |
| --- | --- |
| S45 | Exact union/intersection/difference memberships, duplicates and disjoint/overlapping/identical operands; membership hit/miss and inclusive subset true/false/equal cases. |
| S46 | Witness inputs distinguish `&` precedence, left-associative mixed `|`/`-`, parentheses, comparison/`not` precedence and binder `in`; reject chained comparisons and unsupported aliases/operators. |
| S47 | Empty literals infer through full expression trees; context-free empties remain parametric where allowed; typed empty results cannot hide later nominal/type mismatch; unresolved required predicate types remain diagnostic. |
| S48 | Same text with different nominal kind/realm remains distinct and incompatible types fail; scalar/set misuse, set-left membership, Boolean/number bitwise-looking expressions and numeric `<=` fail. Use admitted low-level typed fixtures where source syntax cannot construct nominal values. |
| S49 | Union matches spread membership and stable first-occurrence order; repeated aliases retain both origins. Validate observed normalization input counts separately from cardinality. |
| S50 | Intersection/difference follow left order, keep correct surviving-member origins and preserve both full operand closures even with no members. Difference's right operand is not misattributed to an unrelated surviving value. |
| S51 | Unavailable/invalid operands cannot be hidden by self-difference, empty intersection, vacuous subset or an early membership hit. Source-backed unresolved cases refuse; malformed/denied/expired capture cases use the formal/domain boundary without pretending to exercise live Writfold. |
| S52 | `need` on an empty derived set retains every captured dependency; repeated/diamond expression origins stay shared and bounded, with complete transitive closure rather than exponentially copied histories. |
| S53 | Compound domains/spreads and membership/subset inside nested binders preserve outer-domain scope, shadowing, alpha-renaming and exact binder identity. Include `(a - b)` domains and `{...(a | b)}`. |
| S54 | Failed algebraic binding does not install a value or publish fake zero cardinality; prior successful bindings/checks stay faithful and dependent later work is blocked. Existing duplicate/forward/self-reference rejection remains. |
| S55 | Empty algebraic domains report vacuous `forall` and false `exists`, but still validate invalid bodies. Decidable set predicates lower to checked literals, not unconstrained symbolic atoms. |
| S56 | At admitted work/member/source-depth limits valid operations complete; insufficient work, actual membership-scan cost, overflow and excessive expression depth refuse without partial successful state. Exercise configurable library limits; no invented CLI limit flags. |
| S57 | Real JSON and human reports show operator/operand source links, typed membership/order, retained empty-result dependencies and deterministic false-subset counterexamples. Publication reachability does not drop eliminated operand evidence. |
| S58 | Quantifier/model/output exhaustion retains existing incomplete/diagnostic behavior; no truncated operation/instance trace claims completion or permits a reusable completed conclusion. |
| S59 | The inherited source corpus, outcome categories and required-closure rules still work. Every local result remains non-grounded/non-authoritative; no absence/subset result claims broader external inventory completeness. |
| S60 | Actual Lean/Rust operation-level results agree on the selected positive/adverse vectors, independently of Boolean trace replay; existing formula/model witness differential checks also pass. Invalid/unknown/refused outcomes are not collapsed to false or empty. |

Run an actual new `examples/set-algebra.weft` through `weft analyze` and `weft prove`
in JSON and human modes. Include all five operations, an empty result whose operand
evidence is visible, a false subset with its counterexample, and quantification over
a derived domain. Keep malformed/unresolved examples separate so the happy-path
review reaches all its checks. Add targeted negative source scenarios to the real
CLI smoke corpus and isolated nominal/budget regressions at the correct library
boundary. Update `examples/README.md` with actual observed outcomes, not predictions.

Use the produced musl binary, not a host rebuild or a mock. Analysis exits 0 only
for complete structural success. Complete local proof outcomes exit 1, including
entailed/refuted/undetermined/inconsistent; malformed/unresolved/incomplete paths
exit 2. Inspect findings, both output formats and authority flags, not exit codes
alone. Preserve exact source bytes, command lines, stdout/stderr and binary hashes.

**Exit:** every new family has substantive evidence at its proper boundary, inherited
regressions still pass, and actual CLI/report/reference paths have been exercised.
External captures not available locally remain explicitly scoped, not fabricated.

## M4 — Quality producers, artifact and traceability

Use [the existing workflow](../../../../docs/build-and-qualification.md), pinned
Lean/Rust tool image and read-only/network-disabled Compose worker. Host Python
orchestrates only. Keep operator storage policy, resource floors, separate Weft
caches and attempt-owned cleanup; do not prune or mutate Writfold resources.

Set `EVIDENCE` to a fresh operator-selected directory outside this checkout. Every
receipt's immediate parent must be new: the producers create it and refuse reuse.
The following are distinct checkpoints, **not an uninterrupted script**; adopt each
actual result as described before invoking a dependent command.

```sh
# Only when the tool recipe/lock/admission actually requires bootstrap:
scripts/gate bootstrap --receipt "$EVIDENCE/tools/report.json"

# M1: full inherited + extended calculus and reference checks.
scripts/gate lean --receipt "$EVIDENCE/algebra-calculus/report.json"
# After success, record the new qualification/finite-calculus.json checkpoint.

# Matching reference checkpoint; do not change calculus bodies between these.
scripts/gate lean --receipt "$EVIDENCE/algebra-reference/report.json"
# After success, bind qualification/reference-calibration.json to that calculus.

# Optional, only if an owned preparation copy is needed; not qualification:
scripts/gate prepare-rust --receipt "$EVIDENCE/prepare/report.json"
# Review/apply prepared formatter/lock output before the actual Rust producer.

# M4: only after complete implementation and new proof/reference prerequisites.
scripts/gate rust --receipt "$EVIDENCE/algebra-rust/report.json"

# After exact-binary scratch packaging and complete traceability ledger updates:
python3 scripts/check_traceability.py --receipt "$EVIDENCE/algebra-traceability/report.json"
```

The Rust gate already executes workspace and quality-tool formatting, locked/offline
metadata/tests, Clippy with warnings denied and compiler-resolved forbidden-operation
lints, calibrated AST policy, nominal compile-fail controls, dependency/license
checks, static musl build, `file`/`readelf` linkage checks, no-toolchain-PATH CLI smoke,
and reference comparisons. Extend the real producer where needed; never replace it
with hand-entered pass JSON. Preserve the inherited limits: handwritten Rust modules
at most 400 nonblank/noncomment lines (warning 250), functions 80 (warning 50),
orchestration modules 250, and Lean modules 500 per theorem family. Split cohesive
units rather than suppressing policy. Keep pure crates IO-/serde-free and nominal
boundaries intact. Disclose unavailable advisory data and soft size warnings.

Packaging is separate from `scripts/gate rust`: it does not itself build/exercise
the scratch image or publish a release. Use `docker/Dockerfile.runtime` with the
exact retained executable in a uniquely owned packaging context; inspect its
non-root UID/GID 65532, run it read-only/network-disabled/capability-free and exercise
positive plus refusal cases. Retain the actual image/binary identities, command/log
hashes and a scratch-runtime receipt. Package only the matching musl binary,
scope/identity metadata and qualified dependency notices; use the existing license
collector rather than inventing notices. Do not publish without a separate request.

Before the final traceability command, update `qualification/traceability.json`,
`qualification/local-runtime.json`, and `qualification/status.json` with actual
source-bound evidence. The checker expects a passing runtime/reference receipt,
actual AST-resolved shipping symbols, all theorem/supporting declarations, exact
fixture hashes, all S01–S60, the preserved gate graph and a scratch receipt for the
same binary. Missing/stale receipts or symbols, weakened requirements and promoted
blocked stages must fail. The traceability pass checks linkage; it is not new
mathematical or operational qualification.

After runtime proof, update README/example navigation and the language, report,
implementation and assurance docs to the actual delivered scope. If a pinned semantic
contract, formal source, audit profile or reference changes, explicitly re-adopt and
rerun the affected proof/reference/runtime gates; do not leave a stale checkpoint
under a fresh status label. Remove temporary scaffolds. Land semantic implementation,
behavioral tests, producer changes, docs and honest evidence together.

**Exit:** renewed P02/P03/P04/P08 component evidence plus P01A, exact retained artifact,
complete source/requirement mapping and current docs. P05/P06/P07/P09 retain their
external blockers. Do not declare the full product qualified or a Lean-to-Rust
refinement theorem established. A fail, skip, stale input or missing required
scenario is not a pass and does not permit silently reducing scope.
