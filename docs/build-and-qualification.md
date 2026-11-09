# Build and qualification workflow

Linux/WSL x86_64 only. Builds use the operator's admitted Docker/BuildKit storage
binding and resource floors, not guessed paths or a replacement storage backend.
Host Python is orchestration; compilers/provers run in the pinned tool container.

## Admitted workstation

The Weft tool image is
`sha256:d75f5675cc943b439c0b7a1df4dc47bc24ada14ab0346044cd8fdfd0c2724c2a`,
built with BuildKit from the exact locally retained Writfold tool parent in
[`toolchains.lock.json`](../toolchains.lock.json). Qualification rechecks the
actual executable hashes and versions: Rust/Cargo 1.98.0, Lean 4.21.0, musl,
and the admitted TLA+ tools (tla2tools.jar TLC 2.19 and tlapm) used by the
model producer.

The commands below target that admitted workstation. A different machine needs
its own actual storage/tool admission and the exact preserved proof/reference
artifacts selected by the qualification records. A copied status flag, missing
image, unavailable historical receipt or moving sibling checkout is not a fallback.

## Producers

Each receipt path must be fresh and outside the checkout. Examples use a new
operator-selected evidence directory:

```sh
scripts/gate bootstrap --receipt "$EVIDENCE/tools/report.json"
scripts/gate lean --receipt "$EVIDENCE/lean/report.json"
scripts/gate model --receipt "$EVIDENCE/model/report.json"
python3 scripts/check_traceability.py --receipt "$EVIDENCE/traceability/report.json"
```

Bootstrap is required when the tool recipe/lock changes; do not repeat it merely
to obtain a new status label. The Lean producer performs a clean core-only build,
complete registered axiom audit, executable reference checks and copied-source
semantic mutations. The Rust producer requires the exact adopted calculus and
separately qualified reference checkpoint, then runs the real local runtime gates.

The model producer runs TLC on the writfold.agent/1 control-protocol seed
([model](../model/README.md)) and on each single-deviation mutant, then
executes every TLAPS obligation with tlapm; it requires the TLA+ tool bytes
admitted in the renewed bootstrap. It is a protocol model only, not a running
Writfold service, a Weft client or a grounding path.

Cargo.lock files are committed, exact and checked offline. The optional preparation
producer operates only in an owned copy:

```sh
scripts/gate prepare-rust --receipt "$EVIDENCE/prepare/report.json"
```

It reuses existing locks with locked/offline metadata validation and generates a
lock only when absent. It emits `prepared-rust.zip` containing formatter output and
locks; it never writes the read-only source mount. Apply generated files only after
review and comparison against the recorded original input hashes. Preparation is
not a compiler, proof or runtime pass.

## Isolation and artifact

Compose mounts source read-only, disables network, and uses separate Weft-named
Cargo/Lean caches. Qualification is bounded to 8 CPUs, 12 GiB and 1,024 PIDs, after
observing actual available resources. Only uniquely owned temporary trees and
containers are cleaned. No Writfold caches, storage, source or credentials are
changed; no publishing secrets enter the worker.

Rust qualification covers actual workspace/tool tests, compiler-resolved forbidden
operation lints, calibrated AST policies, source size/dependency boundaries,
nominal compile-fail controls, real CLI reports and Lean/Rust outcome/model checks.
`file`/`readelf` verify the retained musl executable; the exact binary is then
exercised without a toolchain on its child `PATH`.

[`docker/Dockerfile.runtime`](../docker/Dockerfile.runtime) packages that exact
binary, project license and collected dependency notices in `scratch`,
UID/GID `65532:65532`. Supply `weft`, `LICENSE`, `third-party-licenses.zip` and
`third-party-licenses.json` in its build context. The runtime is read-only,
network-disabled, capability-free, and has no companion or language runtime.
The release archive includes the binary, scope/identity metadata, the project
[MIT license](../LICENSE) and actual third-party notices collected from the
qualified offline dependency closure. License adoption does not renew any
historical compiler, proof or runtime receipt.

## Shipped-kernel proofs

`cd proofs && docker compose run --build --rm proofs` builds the pinned
Charon/Aeneas/Lean image (`proofs/Dockerfile`) and runs `proofs/gate.sh`:
translate `crates/weft-core`, refuse drift against `proofs/Extracted/`, build
the theorems, audit axioms, and require all 15 Rust mutants to fail in their
named theorems. It is its own compose project, needs
none of the variables above, and is not one of the WEFT gates. After
changing `crates/weft-core`, run `sh proofs/refresh.sh` and commit the new
translation. The cold image is about 20 GB and 11 minutes to build; a warm
gate run takes under three minutes. Record:
[`qualification/aeneas-kernel.json`](../qualification/aeneas-kernel.json).

## Scope of a pass

The development artifact closes the local P02–P04/P08 component work. It does not
close real Writfold citation/assessment, retention/run attachment, effect execution
or reviewed knowledge admission. P09 stays blocked while any of those prerequisites
is missing. See [runtime assurance](runtime-assurance.md) for exact evidence,
known limits and the unavailable advisory-snapshot disclosure.
