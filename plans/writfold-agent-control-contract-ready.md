# Writfold owner handoff: qualified ordinary stdio control contract

The Writfold owner has implemented and exercised `writfold serve`. This handoff
supersedes the availability statements in
[writfold-stdio-contract-inflight.md](writfold-stdio-contract-inflight.md) for the
**control profile only**. It does not close the grounded-data or full composed
integration obligations in
[writfold-integration-sync-2026-11-05.md](writfold-integration-sync-2026-11-05.md).
Only plans-folder communication is written in Weft by the Writfold session.

## Exact artifact pins available now

| Artifact | Retained local path | SHA-256 |
| --- | --- | --- |
| Static Linux/WSL x86_64 musl executable | `~/.local/share/writfold/evidence/stdio-control-20261105-001.json.attempt/writfold` | `70b0d07b18e2f1bd70fc34fce4cc5335fccdd5c6307c014f55abf81ecd97fcca` |
| Self-contained contract archive | `~/.local/share/writfold/evidence/stdio-control-20261105-001.json.attempt/writfold-agent-contract.tar.gz` | `1971ed3fb84a210eee6e53a9af3fb331affb3ad931e7717adb8926b641bba842` |
| `contract.json` inside that archive | `contract.json` | `b673d10f7c14c73d8f5778cfb9b2e84a98a159f1553d5c008054402ee85e7be2` |

The archive includes the exact request/response/parameter schemas, citation binding
data schema, stateful conformance vectors and MIT license. Its root contract binds
payload hashes/lengths. Archive SHA-256 and embedded contract SHA-256 are different
identities; initialization returns the latter. Copy/vendor this immutable artifact
with its expected hash for offline client work. Do not depend on the mutable
sibling checkout or infer a data-service capability from the presence of a schema.

The binary is 615,112 bytes and was inspected as static x86_64 ELF with no dynamic
interpreter/shared-library requirements. It was also run directly on WSL with
nonexistent PATH/HOME. This is a control executable, not a complete Writfold product
release or corpus/Omnigraph qualification.

## Connect through real pipes

Run the pinned executable with the single argument `serve`. Send UTF-8 JSON-RPC
2.0 objects separated by LF, for example:

```json
{"jsonrpc":"2.0","id":"init","method":"initialize","params":{"protocol_version":"2","capabilities":["notifications"]}}
{"jsonrpc":"2.0","id":"stop","method":"shutdown"}
```

Initialization returns profile `writfold.agent/1`, implementation scope
`transport-control-only`, the pinned contract digest, actual ephemeral session
identity, checked generation, and only the implemented methods/capabilities.
Shutdown flushes its response and closes the process; do not wait to send a
separate LSP `exit` method. The framing is newline JSON, not `Content-Length`.

## Client obligations for this profile

- Implemented methods: **initialize, shutdown**. Implemented capability:
  **notifications**. A requested `knowledge`, `citations`, storage or edit
  capability refuses initialization. Absent data methods return Method not found;
  they are not placeholders returning invented empty material.
- Preserve string versus integer versus explicit-null IDs. Missing id means a
  notification only after envelope admission. Fraction/exponent/bool IDs are
  invalid; arbitrary integer IDs are not binary64 values. Clients may choose small
  string IDs for their own requests, without narrowing the server contract.
- Both directions are bounded at **65,536 bytes including LF**. A complete
  correlated reply that cannot fit closes the connection; there is no truncated
  reply or substituted null ID. EOF without a reply is not a positive outcome.
- Valid notifications execute lifecycle without responses; invalid envelopes still
  receive errors. Unknown methods are resolved before lifecycle failures.
- Bind the session's exact instance/incarnation and response generations. Every
  valid envelope, including notifications/refusals, consumes a generation; malformed
  JSON/envelopes do not. Generation is not a citation-table epoch or a durable ID.
- The instance/incarnation labels are entropy-backed invocation identifiers, **not
  a selected realm/KB, persistent owner or grant**. Initialization grants no corpus
  read or edit authority.
- EOF/shutdown exit 0; setup/read/encoding errors exit 1; broken stdout maps to
  cancellation 130. SIGINT/SIGTERM retain native signal termination. Reap the owned
  process before releasing client resources. This profile starts no backend child.
- JSON Schema alone does not enforce lexical integer rules, selector ordering,
  preimages, retained provenance or authorization. Consume the contract's semantic
  constraints and its actual vectors as well as structural schemas.

## What remains unavailable

There is no authorized realm/context/completed-release selection, citation RPC,
assessment/interpretation service, authoritative finite collection reader, frozen
live read closure, large-artifact transfer/retention, ledger/effect or learning
method. Keep `writfold_grounded: false` for current local symbolic work; do not
relabel it after a successful control handshake. No `writfold-ref`, Python host,
Git-only corpus, mock authority or guessed method fallback.

Writfold has reconciled the inherited finite-collection request and the observed
revision-3 complete-operand-closure requirement. Weft still owns set algebra and
logical interpretation. Empty/filtered results cannot erase failed references,
operand dependencies or independent required assessments. These remain future
ordinary reader requirements, not new endpoint names. The 16 MiB report allowance
does not widen the 64 KiB transport ceiling.

Splicery's worktree-edit /1 proposal was also reviewed by the Writfold owner.
Writfold retains run/Worktrunk/grant/dispatch/native-effect ownership. A Weft report
or citation is not an edit grant; no Splicery write capability is enabled here.

## Executed owner evidence

- `stdio-control-20261105-001.json`: 24 real static-musl transport/package checks,
  including actual pipes, exact frame bounds, notifications, malformed/UTF-8 input,
  large IDs, output overflow, shutdown, SIGTERM and broken stdout.
- `stdio-verus-20261105-001.json`: 1,112 domain and 41 protocol obligations, with
  13 semantic mutant families and 198 total producer/admission checks. This includes
  the actual session identity/lifecycle bodies, not a whole-transport refinement.
- `stdio-unit-20261105-002.json`: 262 workspace tests.
- `stdio-quality-20261105-001.json`: 239 quality checks.
- Independent artifact controls: 19 acceptance/refusal probes, including byte
  reproducibility, standalone inspection, stale hash, duplicate/traversal/link/
  extra-member rejection and bounded decompression.

Receipts are under `~/.local/share/writfold/evidence/`. Failed attempts
remain retained. Existing P01O/WF24 and downstream authority/native prerequisites
still block grounded data/effect integration; full WR1–WR8 and P09 are not passed.

## Published source checkpoint

Writfold commit `81f3314707b1da4c2793e6b0b68b77a5e7818432` is pushed to
`origin/main`. The archive and binary identities above remain the client pins.
The source checkpoint does not renew historical whole-tree receipts or promote
the control component to full P09/WF13/WR1–WR8 admission. Exact source applicability,
later index/prose deltas and preserved failures are recorded in
`~/.local/share/writfold/evidence/stdio-component-admission-20261105-001.json`
(SHA-256 `72eae3f2e5102d52348c5c87c8eefb85d4c8e7b18a5cecb86b7d3d4c4d12bdea`).

