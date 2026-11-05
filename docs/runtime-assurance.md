# Local runtime assurance

The development executable is a real static Linux x86_64 musl binary. It parses
and checks the selected finite language, evaluates local symbolic theories and
emits complete `weft.report/1` reports. It is **not** the final Writfold-integrated
release, an authorization token, or a shipping-Rust refinement theorem.

## Exercised evidence

| Obligation | Recorded result |
| --- | --- |
| Lean theorem families | All 22 L01–L12 / Q01–Q10 families; 181 audited declarations |
| Lean executable reference cases | 8 propositional and 17 finite-calculus cases |
| Semantic mutation calibration | 24 rejected mutants |
| Rust behavioral regressions | 66 passed; none failed or ignored |
| AST policy regressions | 42 passed; none failed or ignored |
| Compiler/macro operation controls | 23 cases, preserving the observed compiler macro-lint gap |
| Nominal compiler controls | 1 valid consumer and 4 rejected cross-kind/raw/private/promoted-input cases |
| Actual CLI semantic/refusal scenarios | 25, plus direct analysis and human-view execution |
| Lean/Rust differential checks | 29 logical outcomes and 32 supplied model witnesses |
| Requirement/source mapping | 22 theorem families, 11 gates, 44 scenarios, 46 shipping-symbol links; 6 negative controls |
| Runtime packaging | Non-root, read-only, network-disabled scratch image exercised |

The original calculus gate preceded Rust implementation. The finite extension
received its own complete gate; the original pass was not relabelled. A later
reference-only update added actual Lean checking of supplied polarity models,
while retaining every previously qualified calculus body.

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
`68872ca283d91d1ad6be6e3a090ed6a50c0b890a3291dddf3aaa03450993851a`.
Its build-supplied source-closure SHA256 is
`8c64b1848367230be6db076ec8d7747433c21bfa69db22628371e5f6c225e16f`.
A build-supplied digest identifies inputs; it is not itself a qualification receipt.
No independent clean-build byte-reproducibility claim is made.

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
  Executable conformance and source review are evidence, not that theorem.
- No current advisory database is admitted to the offline build; no
  vulnerability-free claim is made. Source-size soft warnings remain recorded;
  all hard limits and compiler warnings-as-errors passed.
- Writfold WR1–WR8 are still unqualified at the service boundary. P05–P07 and P09
  remain blocked. The retained-branch storage blocker was not rerun or bypassed.
  No Writfold checkout was modified.

All failed attempts remain retained with their exact source snapshots and logs.
Current evidence does not erase them or turn unrun external obligations into passes.
