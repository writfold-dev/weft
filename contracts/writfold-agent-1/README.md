# Owner-pinned writfold.agent/1 contract

This is an unchanged copy of the Writfold owner's self-contained contract archive,
vendored for offline client work exactly as the owner instructed in
`plans/writfold-agent-control-contract-ready.md`. Weft consumes it; it does not
redefine, extend or re-sign it. The owner published this revision with the
negotiated `writfold.trial/1` capability (Writfold branch `serve/trial`).

| Identity | Value |
| --- | --- |
| Archive SHA-256 | `1b4049c481eff17a29f1d4e1cc81918f6c58014800937ee295b792105b7fe626` |
| Embedded `contract.json` SHA-256 | `0baf69b21f1051ee620ca89ba4ec659605c0cf3ddc4ae82a7a9ad8eaf1d9ac3f` |
| Profile | `writfold.agent/1` |
| Implementation scope | `transport-control-only`; `transport-control+trial-worktree` when `writfold.trial/1` is negotiated |
| Implemented methods | `initialize`, `shutdown`; with `writfold.trial/1`: `trial/show`, `trial/retain`, `trial/prepare` |
| CLI-only (Method not found over stdio) | `trial/approve`, `trial/apply`, `trial/recover` |
| Advertised capabilities | `notifications`, `writfold.trial/1` (the latter only when requested and the server has a trial state) |
| Frame ceiling | 65,536 bytes each direction, LF inclusive |
| Owner source checkpoint | Writfold commit `5808a67` on branch `serve/trial` |
| Owner executable pin | **Pending.** The previous pin `70b0d07b18e2f1bd70fc34fce4cc5335fccdd5c6307c014f55abf81ecd97fcca` predates this contract and presents digest `b673d10f…`, so this client refuses it. The new pin comes from Writfold's fresh `stdio-control` receipt. |

The archive carries the request/response/parameter schemas (`methods.json` for
a control-only session, `trial-methods.json` for a session that negotiated
`writfold.trial/1`), the `writfold-citation/1` binding descriptor, stateful
conformance vectors and the MIT license. Its root contract binds the payload
hashes. The archive digest and the embedded contract digest are different
identities; `initialize` returns the embedded one, and the Weft client pins that
value exactly. A server built for the earlier control-only contract
(`b673d10f7c14c73d8f5778cfb9b2e84a98a159f1553d5c008054402ee85e7be2`) is refused.

Weft's client does not request `writfold.trial/1`; it still requests only
control methods, so a session it opens advertises exactly `initialize`,
`shutdown` and `notifications`. Nothing here is a live corpus service, an
authorized scope selection, a citation reader, an assessment service or an
effect engine, and consuming it grants none of those. Weft reports stay
`writfold_grounded: false` and `effect_authority: false` after any successful
handshake.
