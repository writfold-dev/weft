# Owner-pinned writfold.agent/1 control contract

This is an unchanged copy of the Writfold owner's self-contained contract archive,
vendored for offline client work exactly as the owner instructed in
`plans/writfold-agent-control-contract-ready.md`. Weft consumes it; it does not
redefine, extend or re-sign it.

| Identity | Value |
| --- | --- |
| Archive SHA-256 | `1971ed3fb84a210eee6e53a9af3fb331affb3ad931e7717adb8926b641bba842` |
| Embedded `contract.json` SHA-256 | `b673d10f7c14c73d8f5778cfb9b2e84a98a159f1553d5c008054402ee85e7be2` |
| Profile | `writfold.agent/1` |
| Implementation scope | `transport-control-only` |
| Implemented methods | `initialize`, `shutdown` |
| Advertised capability | `notifications` |
| Frame ceiling | 65,536 bytes each direction, LF inclusive |
| Owner source checkpoint | Writfold commit `81f3314707b1da4c2733e6b0b68b77a5e7818432` |
| Owner executable pin | `70b0d07b18e2f1bd70fc34fce4cc5335fccdd5c6307c014f55abf81ecd97fcca` (static musl `writfold serve`, retained by the owner under `~/.local/share/writfold/evidence/stdio-control-20261105-001.json.attempt/`) |

The archive carries the request/response/parameter schemas, the
`writfold-citation/1` binding descriptor, stateful conformance vectors and the
MIT license. Its root contract binds the payload hashes. The archive digest and
the embedded contract digest are different identities; `initialize` returns the
embedded one, and the Weft client pins that value.

This artifact is transport-control only. It is not a live corpus service, an
authorized scope selection, a citation RPC, an assessment service, a retention
ledger or an effect engine, and consuming it grants none of those. Weft reports
stay `writfold_grounded: false` and `effect_authority: false` after any
successful control handshake.
