# Owner-pinned writfold.agent/1 contract

This is an unchanged copy of the Writfold owner's self-contained contract archive,
vendored for offline client work exactly as the owner instructed in
`plans/writfold-agent-control-contract-ready.md`. Weft consumes it; it does not
redefine, extend or re-sign it. The owner published this revision with the
negotiated `writfold.trial/1` capability, in its 10 November 2026 revision that adds
`trial/run` and `trial/evidence-*` (the Weft binary for `trial/run` is fixed by
`writfold serve --weft`, never named by the client).

| Identity | Value |
| --- | --- |
| Archive SHA-256 | `eb5f411479e80e7820e4461e95c879f416a03dd4518e6596166ebfaebd547952` |
| Embedded `contract.json` SHA-256 | `bfa436bac90a97a38b5b70d8a20713cfbd38a12ce35283637d5ac9fa235f3f4a` |
| Profile | `writfold.agent/1` |
| Implementation scope | `transport-control-only`; `transport-control+trial-worktree` when `writfold.trial/1` is negotiated |
| Implemented methods | `initialize`, `shutdown`; with `writfold.trial/1`: `trial/show`, `trial/retain`, `trial/prepare`, `trial/run`, `trial/evidence-list`, `trial/evidence-show` |
| CLI-only (Method not found over stdio) | `trial/approve`, `trial/apply`, `trial/recover` |
| Advertised capabilities | `notifications`, `writfold.trial/1` (the latter only when requested and the server has a trial state) |
| Frame ceiling | 65,536 bytes each direction, LF inclusive |
| Owner source checkpoint | Writfold commit `6679aa0` on `main` |
| Owner executable pin | `3087e467328fd9eb6e4764a77295a98bfa43c9e1ab71d34d6a2297a460f16e41`, the static executable built by Writfold's `stdio-control` gate at this contract (receipt `cursor-serve-IN3JTNJz/stdio-control-003.json`). The earlier pins `91a1924f…` (contract `0baf69b2…`) and `70b0d07b…` (contract `b673d10f…`) are refused. |

The archive carries the request/response/parameter schemas (`methods.json` for
a control-only session, `trial-methods.json` for a session that negotiated
`writfold.trial/1`), the `writfold-citation/1` binding descriptor, stateful
conformance vectors and the MIT license. Its root contract binds the payload
hashes. The archive digest and the embedded contract digest are different
identities; `initialize` returns the embedded one, and the Weft client pins that
value exactly. A server built for an earlier contract
(`0baf69b21f1051ee620ca89ba4ec659605c0cf3ddc4ae82a7a9ad8eaf1d9ac3f` or `b673d10f7c14c73d8f5778cfb9b2e84a98a159f1553d5c008054402ee85e7be2`) is refused.

Weft's client does not request `writfold.trial/1`; it still requests only
control methods, so a session it opens advertises exactly `initialize`,
`shutdown` and `notifications`. Nothing here is a live corpus service, an
authorized scope selection, a citation reader, an assessment service or an
effect engine, and consuming it grants none of those. Weft reports stay
`writfold_grounded: false` and `effect_authority: false` after any successful
handshake.
