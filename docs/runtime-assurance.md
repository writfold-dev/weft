# Local runtime assurance

The development executable is a real static Linux x86_64 musl binary. It parses
and checks the selected finite language, evaluates local symbolic theories and
emits complete `weft.report/1` reports. It is **not** the final Writfold-integrated
release, an authorization token, or a refinement theorem for the whole Rust
program. A small pure decision core is proved over its shipped Rust; see
[Proved over the shipped kernel](#proved-over-the-shipped-kernel).

## Exercised evidence

| Obligation | Recorded result |
| --- | --- |
| Lean theorem families | All 30 L01–L12 / Q01–Q10 / A01–A08 families; 327 audited declarations |
| Lean executable reference cases | 8 propositional and 27 finite-calculus cases (17 inherited + 10 set-algebra) |
| Semantic mutation calibration | 36 rejected mutants, at least one substantive mutant per A family |
| Rust behavioral regressions | 106 passed; none failed or ignored |
| AST policy regressions | 42 passed; none failed or ignored |
| Compiler/macro operation controls | 23 cases, preserving the observed compiler macro-lint gap |
| Nominal compiler controls | 1 valid consumer and 4 rejected cross-kind/raw/private/promoted-input cases |
| Actual CLI semantic/refusal scenarios | 32, plus 6 examples, 2 external-source cases, 3 reuse cases, direct analysis and human-view execution |
| Lean/Rust differential checks | 62 logical outcomes, 65 supplied model witnesses, 9 set-algebra operation pairs |
| Requirement/source mapping | 30 theorem families, 12 gates, 60 scenarios, 54 shipping-symbol links; 6 negative controls |
| Runtime packaging | Exact binary plus project license and 30 collected package notices in a non-root scratch image; exported rootfs bytes verified; version, 2 positive examples and 2 refusals exercised read-only, network-disabled and capability-free |

The original calculus gate preceded Rust implementation. The finite extension
received its own complete gate; the original pass was not relabelled. A later
reference-only update added actual Lean checking of supplied polarity models,
while retaining every previously qualified calculus body. Revision 3 added the
set-algebra gate (A01–A08) before any feature Rust landed, then requalified the
frontend, evaluator, reports and musl artifact with native `|`, `&`, `-`, `in`
and `<=`; no earlier pass was relabelled.

Machine records:

- [First finite-calculus checkpoint](../qualification/finite-calculus.json).
- [Reference witness calibration](../qualification/reference-calibration.json).
- [Current local runtime](../qualification/local-runtime.json).
- [Complete source mapping](../qualification/traceability.json) and
  [stage ledger](../qualification/status.json).

The runtime producer checks source/tool/image/lock identities, offline dependency
and license inventory, format, Clippy with forbidden operation lints, calibrated
AST checks, nominal compile-fail cases, ELF linkage and the actual executable.
Child executions run with `/no-toolchain` as `PATH`. The packaged scratch image
has no Rust, Lean, Python, shell, libc loader or other runtime toolchain.

The qualified executable SHA256 is
`a74f773e56752b15759cd55143c72fae0051d4e322563f659c2df5e2e3813e9e`
(Rust gate `rust-004`, which includes `crates/weft-core`).
Its build-supplied source-closure SHA256 is
`50b41240c8589abe397b787f4c4509a9e16898bff6c5917487656ada0da5b04c`.
The scratch image `sha256:d4d50b7d8beef14ec9abbb507b71ff6ee5c707acd4cc9efb4b88d5b315253aa7`
packages exactly that executable (`runtime-package-002`, produced by
[`scripts/package_runtime.py`](../scripts/package_runtime.py)). The counts above
are derived from those receipts by
[`scripts/runtime_record.py`](../scripts/runtime_record.py).
A build-supplied digest identifies inputs; it is not itself a qualification receipt.
No independent clean-build byte-reproducibility claim is made.

## Proved over the shipped kernel

`crates/weft-core` is a dependency-free `no_std` crate holding the pure
decisions production calls:

| Production caller | Kernel decision |
| --- | --- |
| `weft_domain` `add_set` (literals, spreads, every algebra result) | `sets::normalize` (first-occurrence deduplication), `sets::position_of` |
| `set_union` / `set_intersection` / `set_difference` | `sets::union` / `sets::intersection` / `sets::difference` |
| `set_member` / `set_subset` / `sets_equal` | `sets::contains` / `sets::subset` / `sets::same_members` |
| `weft_kernel` finite evaluator (`enumerate`) | `verdict::role` per trace row, `verdict::classify` for the verdict |
| `weft_wire` `PriorScope::compare` (`weft reuse`) | `scope::refusals` over byte-exact `scope::same_bytes` |

The `proofs` gate (`cd proofs && docker compose run --build --rm proofs`)
translates that crate with Charon and Aeneas, refuses any drift against the
committed translation `proofs/Extracted/WeftCore.lean`, builds Lean theorems
over the translated functions, audits every theorem's axioms and calibrates
with semantic mutants of the Rust source. Every theorem is a total-correctness
statement: the translated function terminates without failure (no panic, no
overflow, no out-of-bounds index) and its result satisfies the stated property.

What is proved, **over the Aeneas translation of `crates/weft-core`**:

- Set algebra (A01/A03, at the level of value identities): normalization is
  exactly the calculus's first-occurrence `unique`; union is
  `unique (left ++ right)` (left order first) with exactly the members of
  either side; intersection and difference are the qualifying left values in
  left order with exactly "both" / "left and not right" membership; membership
  is `∈`; subset answers no counterexample iff every left value is on the
  right, otherwise the first left position that is not; set equality is
  mutual inclusion. `union_spec` assumes the two operand lengths sum to at
  most `usize::MAX`, which any two in-memory `usize` slices satisfy.
- Classification: `verdict_of` is the calculus's `verdictOf`, and over a trace
  the verdict is entailed iff some row is a premise model and the query holds
  in every premise model; refuted symmetrically; undetermined iff both
  polarities occur; inconsistent premises iff no row is a premise model.
- Reuse: byte equality is exact, length included; the refusals are exactly
  the unsatisfied comparisons, ascending; reuse is admitted iff every
  comparison holds, so any difference in a must-be-equal field is refused.

Trust base: the Charon (commit `8cae8fd1`) and Aeneas
(`nightly-2026.11.07-c5eb4a2`) translation of the Rust source, the Aeneas Lean
library's models of the Rust core operations the kernel uses (slice indexing,
`Vec::push`/`deref`, `usize` arithmetic, `Option::is_some`/`is_none`), the
Lean 4 kernel (`v4.35.0`), and Lean's standard axioms `propext`,
`Classical.choice` and `Quot.sound`. The translation contains no `axiom`; the
audit admits nothing else. Exact pins, theorem and mutant inventories and the
measured gate are in
[the shipped-kernel record](../qualification/aeneas-kernel.json).

What remains modeled or tested, not proved over shipped code:

- Typing, budget charging, origin/provenance closure, quantifiers, lowering,
  traces and reports (A02, A04–A08 and the L/Q families) are proved in the
  calculus (`formal/`) and exercised by tests, the Lean/Rust differential and
  CLI scenarios. The calculus is on Lean `v4.21.0` and is not upgraded or
  imported: the two definitions the kernel theorems use (`unique`,
  `verdictOf`) are restated in `proofs/Kernel/Spec.lean`, a reviewed
  restatement rather than a machine-checked link.
- That the evaluator's trace rows are exactly every valuation of the active
  atoms, and that each row's Booleans are the premises' and query's values,
  is the evaluator's obligation (tests and differential), not a theorem.
- Which fields reuse compares and how they are encoded are the wire layer's
  (tests and CLI scenarios). The parser, lowering and report projection have
  no refinement theorem.

The kernel's searches are linear scans, so set decisions cost
`O(|left|·|right|)` comparisons where the earlier implementation used hash
sets; the construction work budget, which still charges linear units, bounds
the operands. On the default budget the heaviest refused union measured
0.14 s against 0.05 s before; every compared report was byte-identical.

## What the reports establish

Checks classify a finite theory under the exact preceding hypotheses. Typed
comparisons do not coerce values; large naturals remain exact. Sets retain raw
occurrence accounting, normalized membership and all source origins, including
diamond spreads. Quantifiers retain lexical environments, every actual instance,
vacuity and model-relative witnesses/counterexamples. Empty domains do not skip
name/type checks. Invalid assumptions cannot disappear from subsequent checks.

Reports bind the exact source bytes and preserve requested context/profile/target,
requirements, hypotheses, dependencies, model assignments and replayable traces.
Budget or output exhaustion never publishes a successful prefix. The projection
library checks linkage/coverage consistency but assumes actual trusted compiler/
kernel records; it is not an untrusted proof-certificate ingestion endpoint.

## Explicit limits

- Local predicates are uninterpreted and hypothetical. No text-to-fact inference,
  citation resolution, freshness assessment or rule admission is fabricated.
- Formal world-facing grounding uses explicit interpretation/acquisition and
  `EvidenceSound` assumptions. Admission alone does not establish truth.
- There is no proof that the raw Rust parser/compiler refines the Lean calculus.
  Executable conformance and source review are evidence, not that theorem. Only
  the `weft-core` decisions above are proved over shipped code.
- The runtime gate exercises the binary that calls `weft-core`; it does not
  renew the shipped-kernel theorems, and those theorems do not cover the rest
  of the binary.
- No current advisory database is admitted to the offline build; no
  vulnerability-free claim is made. Source-size soft warnings remain recorded;
  all hard limits and compiler warnings-as-errors passed.
- Writfold WR1–WR8 are still unqualified at the service boundary. P05–P07 and P09
  remain blocked. The retained-branch storage blocker was not rerun or bypassed.
  No Writfold checkout was modified.

All failed attempts remain retained with their exact source snapshots and logs.
Current evidence does not erase them or turn unrun external obligations into passes.
