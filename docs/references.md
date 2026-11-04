# Sources and status

Inspected on 4 November 2026. This is a design-source record, not a Writfold gate,
proof receipt, runtime qualification or implementation-status renewal. Exact
file hashes below bind the inspected local source snapshots; mutable documents
may differ from their repository's current `main`.

## Writfold references

Paths are relative to the separate private
[`writfold-dev/writfold`](https://github.com/writfold-dev/writfold) repository.
Original files were read, not copied or modified. In particular, the exploration
handover was already being updated separately; its opcode withdrawal is preserved.

| Source | Used for |
| --- | --- |
| `docs/writfold/proof-query-exploration.md` | External language exploration, shared stdio direction, proof boundaries and unresolved choices. |
| `docs/writfold/handover-adoption.md` | Current revision-5 authority, scoped v9 adoption and component/status limits. |
| `docs/writfold/domain-boundary.md` | Independent support, applicability, freshness, validation, availability and authority dimensions. |
| `docs/writfold/wire-boundary.md` | Structured RPC/session boundaries; codec support is not production method implementation. |
| `handovers/revision-5/writfold/plan/17-engineering-graphs-and-layout.md` | Context/Execution/Learning views, ledger authority, activity projections and exact cuts. |
| `handovers/revision-5/writfold/plan/18-identities-fingerprints-and-cuts.md` | Typed identities, declared read-set closure and reuse/freshness conditions. |
| `handovers/revision-5/writfold/plan/20-execution-and-cross-repository.md` | Assumption tracking, design/validation workflow and current effect guards. |
| `handovers/revision-5/writfold/plan/21-learning-and-promotion.md` | Observation/candidate/evaluation/admission separation; no hidden chain-of-thought dependency. |
| `handovers/revision-5/writfold/plan/22-engineering-calculus.md` | Context usability, evidence judgments and explicitly conditional safety assumptions. |

The private historical playbook was not opened, copied or published. No native
storage blocker or proof-demo experiment was rerun. No new external proof engine,
Writfold API, admission profile or universal Lean-certificate rule was activated.

## Sovel inspiration

Local source root: `../sovel/sovel-handover/`. The relevant files are
`spec/grammar.ebnf`, `spec/LEXING-AND-PARSING.md`, `spec/LANGUAGE.md`,
`spec/SEMANTICS-MAP.md` and `spec/REFINEMENTS-AND-CONTRACTS.md`.

Borrowed practices: define the EBNF dialect, specify lexical rules and precedence,
separate syntax acceptance from static/evaluation meaning, and map constructs to
explicit assurance obligations. Weft does not inherit Sovel's syntax, compiler,
proofs, ownership system, effects, staging or macros. No Sovel source bundle is
republished here.

## Inspected source identities

Writfold paths use its repository root; Sovel paths are prefixed `sovel/` below.

```text
39348ae639994365f6a4d8f76ca8cceb118216d64bc6488f1a3ac53bcb586260  docs/writfold/proof-query-exploration.md
fc56361e7bf02e8718267c6ae4b67a1ca768f29009efefe952316d5f52c98507  docs/writfold/handover-adoption.md
2471e44772f516351684da45b72adb449714f102a4146bb63d761f314829dc03  docs/writfold/domain-boundary.md
4862cc71450b687d92f996d2be6363387ecd26ae2de72742e96a0a90d6702597  docs/writfold/wire-boundary.md
6785864dbb4989f2adb7232dddf1fac83516de202c86e333bb13e2ed230913aa  handovers/revision-5/writfold/plan/17-engineering-graphs-and-layout.md
35ffed9a9c8e1cb944de1f20b57a7705619df15eb76e64cd8ff6a1e949971eb0  handovers/revision-5/writfold/plan/18-identities-fingerprints-and-cuts.md
60deeedb78db453d9255078af6489c08231cdd4f803202f2af929223bd431d11  handovers/revision-5/writfold/plan/20-execution-and-cross-repository.md
9c0612b220a500b4265c9b4379614603dbc96e162fe900ab17133f5660ac1d70  handovers/revision-5/writfold/plan/21-learning-and-promotion.md
00cff424f9557e0bfcf986164eeb0106b74fe57923e9f9f9f865787bf341a216  handovers/revision-5/writfold/plan/22-engineering-calculus.md
7c1d58223d771d306d7161b04df69319899d79b49ef6cecb2b561f781659930e  sovel/spec/grammar.ebnf
237a1abf1d0652cf0a307f50618fc396b2ddbc5a2fbeb1b4d3138f64fdea4c45  sovel/spec/LEXING-AND-PARSING.md
b2ea5a32ed2c12097c5cb8aa6e014e8de7d52f49eb6705da48ea87251a53dc9c  sovel/spec/LANGUAGE.md
c30cd871ed1e16dce5bf11f6fb400bb1a01fb624e723b81fc5052b0f021dc6e2  sovel/spec/SEMANTICS-MAP.md
f4678539e240aaed2a0919a5cb014d77f08234ad81c6919e5e9d9c60ce8135ff  sovel/spec/REFINEMENTS-AND-CONTRACTS.md
```
