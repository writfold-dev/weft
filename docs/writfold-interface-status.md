# Current owner-side integration status

The Writfold owner has reconciled WR1-WR8 in its
`docs/writfold/shared-client-references.md` and
`qualification/weft-integration.json`. These are accepted shared-client requirements,
not advertised production RPC methods or an owner-published contract artifact.

New source-inspected citation components include nominal table generations,
selector/binding/alias/reuse predicates, a closed `writfold-citation` schema-1 binding
descriptor, domain-separated citation digests and retained Git acquisition primitives.
The owner explicitly states that these components are not live corpus services,
normal Git-only storage, authenticated scope resolution or an admission host.

Weft must continue to:

- Consume an exact owner-landed shared contract/pin, not a mutable path dependency
  or a duplicate handwritten identity implementation.
- Preserve logical IDs versus immutable material, complete role/context/selector
  bindings, native Git hashes versus raw capture hashes, and raw Weft source SHA256
  versus Writfold's domain-separated CBOR fingerprints.
- Keep citation-table generation distinct from request generation/incarnation;
  qualify local proof-node IDs by the exact report artifact and schema.
- Preserve every applicable assessment dimension, read-set/cut dependency and
  coverage meaning. Retention is not knowledge admission or effect permission.
- Honor the 65,536-byte protocol frame ceiling; large artifacts require the owner's
  qualified transfer/selection contract, not oversized frames or local fallbacks.

## 5 November 2026 integration sync

The mutable coordination note
[plans/writfold-integration-sync-2026-11-05.md](../plans/writfold-integration-sync-2026-11-05.md)
records the latest reviewed boundary: Weft's qualified local symbolic engine and
Writfold's citation components agree on their intended boundary, but they are
**not connected runtime products**. The owner has not yet exposed the production
initialized stdio host, a pinned shared identity/protocol contract, or its real
service mapping; capability-enum entries are not evidence of running methods.
`writfold-ref` accepts supplied semantic inputs and is not a grounding fallback.
The planned ordinary transport is bounded JSON-RPC 2.0 over stdio (frame ceiling
65,536 bytes; Weft's report budget is larger, so oversized artifacts need the
planned bounded transfer mechanism). That note passes no P05-P07/P09 gate and
changes no Weft authority; once the exact owner contract and real services land,
Weft implements the ordinary client — initialization, scope binding,
correlation/generation, bounded framing, refusal and owned-child cancellation —
and feeds acquired references into the explicitly qualified external
interpretation path without relabelling `weft.symbolic/1` results as grounded.

The owner inventory still marks WR1-WR8 `not_run` at the service boundary. P05-P07
and final composed Weft release remain blocked. No Writfold files were modified
by this session. The additional finite-collection proposal is in
[writfold-finite-collections-request.md](writfold-finite-collections-request.md).

This is a source-inspected status note, not new Writfold qualification evidence.
The original immutable handoff remains preserved; mutable owner work may advance.

## Weft control client landed

The qualified control-contract handoff above is now consumed end to end on the
Weft side: the owner archive is vendored unchanged at
`contracts/writfold-agent-1/`, the `weft-writfold` crate implements the
ordinary stdio client (typed initialize/shutdown only, local capability
refusal, correlated replies, strict generation matching, 65,536-byte frames
both directions, owned-child reaping, pinned contract-digest verification),
and `weft control BIN --expect-sha256 HEX` runs a real session against the
pinned executable. The `control` gate requalifies this against the actual
binary, including the digest-mismatch refusal. This is still transport control
only: no citation, assessment, collection, retention, ledger or effect method
exists, P05-P07/P09 remain blocked at the owner data services, and every
output stays `writfold_grounded: false`.

**Re-pinned to the owner's `writfold.trial/1` contract.** The owner published a
revision of the same profile that adds a negotiated `writfold.trial/1`
capability (`trial/show`, `trial/retain`, `trial/prepare`; approve, apply and
recover stay CLI-only), pinned at contract `0baf69b2…` (archive `1b4049c4…`) and
executable `91a1924f…`.

**Re-pinned again to the 10 November 2026 revision.** The owner revised
`writfold.trial/1` to add `trial/run`, `trial/evidence-list` and
`trial/evidence-show` (the Weft binary for `trial/run` is fixed by
`writfold serve --weft`, never named by the client). The vendored archive and
the client pin now name contract `bfa436ba…` (archive `eb5f4114…`), and the
`control` gate's executable pin names `2fdf09ed…`, the binary from Writfold's
fresh `stdio-control` receipt for its state-directory change (contract
unchanged; the previous pin `3087e467…` is retired). The Weft client still does not request the
capability, so its sessions advertise only control methods. Servers built for
either earlier contract (`0baf69b2…`, `b673d10f…`) present a different digest
and are refused; a unit test covers the most recent one. The TLA+ control model
below names the first digest in its comments; it models control transport
only, which is unchanged.

## Control-protocol model qualification

The pinned `writfold.agent/1` transport-control contract now has a local TLA+
seed with executed TLAPS proofs ([model](../model/README.md), gate P10 in
[the status ledger](../qualification/status.json)): TLC finds no violation of
the eleven invariants across the finite seed, seven single-deviation mutants
each fail exactly their targeted invariant, and tlapm proves all inductive
safety obligations. This models the shared contract text only. It is not a
running Writfold service, not a Weft client implementation, and it changes no
P05-P07/P09 blocker: initialization grants no grounding or effect authority.
