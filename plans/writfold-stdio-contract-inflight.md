# Writfold owner: ordinary stdio contract implementation in flight

Coordination only; not a published contract pin or a qualification receipt.
The Writfold session is implementing the owner-side work from
[writfold-integration-sync-2026-11-05.md](writfold-integration-sync-2026-11-05.md).
No Weft source/configuration/qualification/handover files are being edited by it.

## Concrete owner-side design

- Actual Rust command: `writfold serve`, preserving the existing serve spelling.
- Newline-delimited JSON-RPC 2.0; initialize protocol string `"2"`.
- Current implementation profile: `writfold.agent/1`, explicitly
  `transport-control-only`. The first advertised methods are **initialize and
  shutdown**, with `notifications` as the only implemented capability.
- Real entropy-backed ephemeral instance/incarnation labels, a separately
  monotonic request generation, strict malformed/unknown/notification behavior,
  and 65,536-byte LF-inclusive input and output bounds.
- Session state changes occur only after validation and complete reply encoding.
  A valid request ID too large for a bounded correlated reply closes the
  connection; it is never shortened or silently replaced by null.
- The binary will identify a self-contained owner contract by raw SHA-256. The
  owner will supply its exact source pin, schemas, vectors and qualified runtime
  evidence after verification, not just a mutable sibling checkout path.

## Important boundary for the Weft agent

The transport can be implemented and exercised independently. The known
P01O/WF24 storage blocker still prevents qualified corpus/retained-release reads.
No citation, assessment, collection, artifact-retention, ledger or effect method
will be advertised or implemented as a placeholder. Do not interpret successful
initialization as grounding availability, request invented methods, or connect
`writfold-ref` as a fallback.

Keep the existing symbolic engine and its completion/authority semantics intact.
Once the owner publishes the exact contract, a real client can exercise lifecycle
and capability refusal against this process. Grounded read-only E2E additionally
requires the actual authorized reader and a qualified interpretation profile;
the complete report/run/effect/learning flow remains required afterward.

The owner is reconciling the revision-2 finite-collection request into WR4/WR5.
Exact collection membership, authoritative-domain identity, independent member
assessment, coverage/completeness/omissions and permission-aware disclosure are
requirements, not currently callable service names. Larger reports/models also
retain the planned generic bounded artifact-transfer prerequisite; the frame
ceiling is not being raised.
