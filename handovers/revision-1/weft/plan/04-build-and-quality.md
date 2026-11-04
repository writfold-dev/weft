# BuildKit, Compose and qualification

## Machine contract

Linux/WSL x86_64 only. Use the operator's currently selected Docker/BuildKit daemon
and existing `ci_infra.storage.check` binding. Read actual local configuration;
never commit drive letters, relocate storage, weaken free-space floors, prune
unrelated resources or install publishing credentials on workers. Missing binding
or changed daemon/storage identity refuses before a build.

Read-only host preflight imports the operator's installed ci_infra package and
calls storage.check on its configured state root. Compare resource availability
with the admitted 8 CPUs, 12,884,901,888 bytes memory and 1,024 PID container bound.
Do not assume both projects can consume that bound simultaneously; observe other
qualification workloads and preserve headroom. Host Python is orchestration only,
never the compiler or proof checker.

## Exact initial tools

Reuse the locally retained image, with no implicit pull:
`writfold-tools@sha256:c854889f19c83174e69600ee28f0d4d35a0d2de1a23b3a35b1ecf4c4a88e0fc6`.
Its authority is Writfold's inspected tool lock, not a renewed Writfold gate pass.
Weft records its own adoption/observation and receipt. Lean is 4.21.0, Rust/Cargo
1.98.0, target x86_64-unknown-linux-musl. Verify exact in-image tool hashes before
qualification. Do not modify Writfold's tool lock or invoke its gate runner.

BuildKit builds a Weft-owned qualification image from that digest-pinned base and
Weft-owned recipes. No moving apt, tool download or network access in qualified
builds. Compose executes fresh proof/check/build commands in that exact image;
a cached image layer alone is not new proof evidence. Source mounts are read-only.

Use separate Weft-named target, registry and git caches. A one-time read-only copy
of the existing Writfold Cargo registry can seed Weft's cache; Cargo.lock checksums
and --locked --offline must verify the isolated result. Never write to Writfold's
caches. Namespace Rust targets and Lean caches by tool/source identity; serialize
conflicting writers. Large outputs must stay in admitted Docker-managed caches,
not source-tree target/. Retain final artifacts/receipts outside disposable caches.

## Dependency policy

Lean core only, no mathlib or remote packages. Rust starts with cached exact
versions where needed: serde 1.0.229, serde_json 1.0.151, num-bigint 0.4.8,
sha2 0.11.0 and thiserror 2.0.20. Do not add a dependency without a concrete need.
No clap is required for the small CLI. No OpenSSL/native-tls or embedded prover/
engine. No private Git credentials inside the build image. External Writfold
crates require an exact owner-landed pin and separately captured offline closure.

## Required quality checks

- cargo fmt --all -- --check; Clippy all targets with -D warnings; locked/offline
  dependency graph and licenses. Disclose absent/stale advisory snapshots.
- Cohesive handwritten Rust modules <=400 nonblank noncomment lines, warning at
  250; functions <=80, warning at 50; orchestration modules <=250. Lean modules
  <=500 per theorem family. Count syntactically, not by stripping // from strings.
- Calibrated AST-based unsafe/panic/unwrap/todo/public-constructor/domain-serde
  checks; dependency direction and pure-core IO prohibition. Exceptions require
  exact source scope, owner, reason and expiry; no blanket allow.
- Deterministic behavioral regression and nominal compile-fail cases; no skipped
  required tests or source-text/snapshot assertions masquerading as semantics.
- Lean clean build, complete registered axiom audit, executable positive/negative
  examples and mutation calibration. Reference/Rust differential cases bind both
  actual executables. No proof by testing and no assumed cross-logic theorem.

## Gate command and receipt contract

Implement `scripts/gate <gate> --receipt <new-external-path>` with real producers.
A missing producer is blocked, never a shell command that merely prints pass.
Record source manifest, handover/registry identity, tools, target/features,
Cargo.lock, fixtures, exact argv/environment, output/log hashes, exit codes and
all failures/skips. Preserve attempts and create a new receipt for each rerun.
No write into the immutable handover after it is landed; adoption deltas are new
revisions or explicit mutable records, not silent edits of acceptance criteria.

A release aggregator verifies the applicability and complete required inventory;
it cannot pass because some component produced an executable. It must include the
real Writfold integration obligations, or remain blocked with their exact owner
prerequisites. Unknown/native storage blockers are not rerun merely to confirm.

## Binary delivery

Build a static musl executable through BuildKit/Compose. Verify ELF/linkage with
file/readelf, execute the actual CLI without Rust/Lean/Python on PATH, exercise
positive and negative source cases and inspect full reports/traces. Package exact
binary hash, version/source identity, supported command scope and assumptions.
Do not claim byte reproducibility without independent clean builds.

A development binary can expose local parse/analyze/prove behavior before backend
integration, with unmistakable ungrounded/conditional scope. It is not the final
requested end-to-end product. Final acceptance additionally exercises authorized
citation resolution, assessment, retained report/run binding, actual execution,
and reviewed knowledge admission against the qualified Writfold instance.
