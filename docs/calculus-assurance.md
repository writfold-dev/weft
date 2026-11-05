# Calculus qualification checkpoint

The original finite propositional/typed-ground fragment passed the complete local
Lean gate before production Rust implementation began. The subsequently requested
native finite sets, `:=` bindings, spread and bounded quantifiers are **new scope**;
this receipt does not qualify those additions.

## Exercised evidence

- Clean Lean 4.21.0 build with warnings as errors and automatic implicit parameters
  disabled, using the exact locally admitted BuildKit/Compose tool image.
- Complete axiom audit of 43 declarations: the 12 required theorem families plus
  independent ground-term semantics, interner coverage, typed report axes, checked
  detailed explanations and jointly inhabited positive/refuted composition.
- Eight actual executable-reference cases covering entailment, refutation, wrong
  polarity, two models, inconsistency, exhausted budget, invalid domain and the
  one-valuation empty atom domain.
- Fourteen copied-source semantic mutants rejected at their expected proof files.
  They cover type checks, inequality lowering, substitution, implication,
  enumeration, inconsistency, budget, required inputs, stale evidence, reuse,
  projection, authority, independent comparison meaning and error classification.
- Eight qualification-boundary regression tests, including source symlink refusal,
  attempt-owned cleanup and immutable requirement tampering.

Passing receipt:
`~/.local/share/weft/evidence/implementation-20261104T232254539927Z/lean-009/report.json`

Receipt SHA256:
`09bdef80d9b624af441ae8788b95f9b0e4523b483d67282dfbc51d59fa9d9ecf`.
Its 47 source inputs were matched against the current files immediately after the
pass. Full source ZIPs, commands and raw output are retained beside the receipt.
The reference executable SHA256 is
`ee0d37bcbdb1259e3403e9032fef23120ad26e2596bca02c53d8df8a83591dd9`.
This is a qualification reference, not the shipping Weft binary.

## What is proved

The specified resolved surface AST has an independent typed meaning. Successful
elaboration preserves it; substitution and actual sugar preserve semantics;
finite enumeration covers the declared domain; completed logical classifications
have their model-theoretic meanings, with consistency required before ordinary
entailment/refutation. Insufficient budgets do not manufacture answers.

Grounded success requires eligible exact-scope input closure and no unresolved
required hypotheses. Trace/report checks preserve the actual result, origins,
dependencies and authority boundary. Positive and refuted source judgments compose
with the same interpretation and evidence premises, with concrete joint witnesses.

External-world truth is conditional on accurate interpretation/acquisition and
`EvidenceSound`; the proof does not turn admission into universal truth. Current
assessment/freshness correctness, producer qualification and complete declared
footprints remain explicit environmental assumptions.

## What is not proved or exercised

No raw-source lexer/parser refinement, shipping Rust refinement, live Writfold
citation service, operational graph, real effect or knowledge admission was
qualified by this gate. Differential agreement is not a refinement theorem. No
new per-proposal Lean-instance requirement or Writfold admission route was adopted.

## Preserved failures and repairs

`tools-001` retains the failed registry metadata lookup for the exact local-only
base image. `tools-002` built through a Weft-owned alias whose immutable parent
identity was checked before and after BuildKit execution; no unpinned fallback.

`lean-001` through `lean-008` retain compile failures and source snapshots. Repairs
covered reserved Lean binders, Boolean equality rewriting, an explicit scope
premise, map reduction, structure-update layout and reference-decoder layout.
Independent review additionally led to stronger comparison semantics, meaningful
interner coverage, richer checked reports, exact-budget reuse and joint positive/
negative composition. Unused propositional-equivalence helpers were removed;
L04 now maps actual implication and independently checked typed equality/inequality.
No required language guarantee or negative acceptance case was weakened.

Qualification regressions reproduced and repaired omitted directory symlinks and
leaked temporary proof trees. Old attempt trees were removed only after their exact
formal inputs had been verified in retained source ZIPs; unrelated caches and all
Writfold source/storage remained untouched.
