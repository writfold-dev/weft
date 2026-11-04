# Dependency-ordered execution and acceptance

Stage requirements are immutable planning data. Current completion and exact
receipts belong in qualification/status.json. Every stage retains positive,
negative and interrupted/refused paths where applicable.

| Stage / gate | Dependencies | Required deliverable and observable acceptance |
| --- | --- | --- |
| P00 / WEFT00 | none | Exact tool/image/source identities; actual operator storage/resource preflight; separate safe caches and BuildKit image; no Writfold mutation. |
| P01 / WEFT01 | P00 | All L01-L12 Lean statements/proofs, independent assumptions and axiom audit; inhabited positive examples and named semantic mutations rejected. No production evaluator before pass. |
| P02 / WEFT02 | P01 | Source grammar/lexical/type contracts match formal surface/IR; bounded reference inputs, parser fidelity/precedence/Unicode cases and exact Lean executable vectors. |
| P03 / WEFT03 | P02 | Real Rust nominal domain, lexer/parser, name/type/lowering passes and finite evaluator; source-symbol mapping, behavioral/compile-fail tests and complete-response differential checks. |
| P04 / WEFT04 | P03 | Versioned JSON/human reports, full dependency traces, actionable diagnostics, local CLI smoke and explicit non-grounded hypothetical behavior; no fake external bindings. |
| P05 / WEFT05 | P04, WR1-WR5 | Real shared stdio host and pinned contracts; scoped citation resolution/assessment; handle expiry, stale session, access revocation, ambiguity, wrong units and missing evidence exercised. |
| P06 / WEFT06 | P05, WR6 | Authorized exact report retention and run/plan attachment with expected-head/idempotency semantics; lost replies reconciled; report cannot self-issue a gate receipt. |
| P07 / WEFT07 | P06, WR7-WR8 | Actual qualified execution and learning admission; negative authorization, stale evidence, effect-unknown/reconciliation and contrary-evidence cases. No direct graph writes or automatic promotions. |
| P08 / WEFT08 | P04 | Format/lint/nominal/size/dependency/unsafe gates; BuildKit musl artifact, installed-runtime smoke, artifact identity and declared assurance scope. Does not close P05-P07. |
| P09 / WEFT09 | P05-P08 | Composed agent-plan -> prove/assess -> report/run -> execute -> evaluate/admit flow using real Writfold. Full source-bound closure and final binary/package. Any blocked prerequisite blocks release. |

P08 can produce a development artifact while external P05-P07 dependencies are
blocked; this is not a reordered final release or a reduced acceptance scope.

## Acceptance scenarios

S01 lexical UTF-8 and exact byte spans; S02 malformed strings/control characters;
S03 precedence/non-chaining comparisons; S04 duplicate/forward/wrong-kind names;
S05 Boolean/natural/text/nominal mismatch; S06 missing/unsupported field/profile;
S07 all finite logical outcomes; S08 contradictory assumptions do not explode;
S09 finite-domain completeness and bounds; S10 exhausted computation yields unknown;
S11 explicit unused needs retained; S12 assumed fact never becomes observed;
S13 full positive/negative trace closure; S14 no false reuse after subject change;
S15 real durable citations; S16 alias generation/reconnect expiry; S17 scoped
same-spelled identifiers; S18 denied/revoked access; S19 stale/unknown validation;
S20 byte-selector/representation/provenance mismatch; S21 partial search never
implies exhaustive absence; S22 malformed/oversized/stale peer responses;
S23 exact report retention; S24 expected-head conflict and lost acknowledgement;
S25 trusted receipt producer binding; S26 real effect authorization; S27 unknown
effect reconciliation without replay; S28 reviewed learning with contrary evidence;
S29 static installed-runtime behavior; S30 complete composed source-bound flow.

## Stop and continuation rules

A missing external capability blocks its stage, not independent formal/compiler
work. Produce an exact proposal-only handoff for the owning Writfold agent and
finish reachable Weft work. Never implement mocks or fallback storage to disguise
a blocked stage. Do not silently remove P05-P09 from the final deliverable.

Freeze input and profile identities before each check. A changed rule, parser,
compiler, source, schema, toolchain or relevant dependency invalidates affected
evidence. A corpus advance preserves historical findings but requires current
applicability/authority checks before new effects.

## Required source mapping

Maintain a registry mapping each theorem/gate/scenario to Lean declarations,
shipping Rust functions, fixtures, assumptions and exact receipts. Scope missing
parser/refinement/native evidence explicitly. A theorem's existence is not its
proof gate; a valid proof gate is not the Rust implementation gate; a standalone
binary is not the composed workflow gate.
