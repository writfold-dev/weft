# Calculus qualification checkpoint

The revision-3 set-algebra extension passed its complete Lean gate before the
production Rust implementation began. The revision-2 finite-set checkpoint and
the original revision-1 checkpoint remain separately recorded below; neither was
retroactively relabelled.

## Revision-3 set algebra

`algebra-calculus-3/report.json` and the matching reference checkpoint
`algebra-reference/report.json` passed in the admitted evidence root
`~/.local/share/weft/evidence/algebra-20261105T185401992646349Z`. Receipt SHA256:
`69ea3a9ea12b475d4eb8c66d8740ee792d60df648cc5e1e75fc5bff920f6340a` (calculus) and `4627cf69d53d9123d96a64706d04a3fbf95752cda34952a2da31fb69ce55f767` (reference). Two earlier failed attempts
(`algebra-calculus`, `algebra-calculus-2`) are retained unmodified in the same
root; both were mutation-profile metadata corrections, not weakened checks.

- 327 audited declarations cover all L01–L12, Q01–Q10 and A01–A08 obligations
  and their registered supporting results. Only `propext`, `Quot.sound` and
  `Classical.choice` occur as foundational axioms.
- Eight propositional and twenty-seven finite-calculus cases (seventeen
  inherited plus ten set-algebra cases) ran through actual compiled reference
  executables. Thirty-six semantic mutants — including at least one substantive
  mutant per A family — were rejected at their registered proof sites.
- Union, intersection and difference preserve exact extensional membership,
  homogeneous operand types (typed empties included), deterministic
  first-occurrence order and complete operand origin closure, including removed
  members and the entire right operand of a difference.
- `in`/`<=` resolve to checked Boolean literals of the algebra operations;
  unavailable operands have no Boolean denotation and a false subset keeps its
  deterministic first-left counterexample.
- Budgeted algebra agrees with unbudgeted meaning on success, charges both whole
  operands before filtering and refuses incomplete work without partial results.
- Source AST semantics and executable agreement are the proven scope: this is
  not a raw-source parser theorem or a Lean-to-Rust refinement theorem.

## Revision-2 finite calculus

`finite-022/report.json` passed in the same admitted evidence root as the original
checkpoint. Receipt SHA256:
`e2ae0ea54965cedadbf323084a5630d837c18ce2444db7582d86c60e9baa94a8`.
All 74 recorded source inputs matched immediately after the pass.

- 181 audited declarations cover all L01–L12 and Q01–Q10 obligations and their
  registered supporting results. Only `propext`, `Quot.sound` and
  `Classical.choice` occur as foundational axioms.
- Eight propositional and seventeen finite-calculus cases ran through actual
  compiled reference executables. Twenty-four semantic mutants were rejected at
  their registered proof sites; eleven qualification-boundary regressions passed.
- Sets preserve exact typed membership, first-occurrence representation and all
  origins across duplicates and empty spreads. Bindings are immutable; substitution
  and nested quantifier domains preserve lexical scope.
- Quantifiers agree with independent finite membership semantics. Checked reports
  preserve complete member coverage, actual substitutions, model-relative
  witnesses/counterexamples, raw counts, provenance and the no-authority boundary.
- One remaining-work state passes through capture, Boolean siblings and every
  quantified instance. Exhaustion after a completed prefix cannot publish a
  partial result. This is structural admission accounting, not a wall-clock or
  allocator-complexity theorem.

Exact source/tool/artifact identities are in
[`qualification/finite-calculus.json`](../qualification/finite-calculus.json).
Attempts `finite-001`–`finite-021` remain retained, including compilation failures,
the source-adoption refusal, and diagnostic runs. A dependent `Work.bind`
projection caused concrete kernel reductions to exhaust resources; destructuring
the actual result constructors fixed the observed failure without changing
semantic statements, example inputs or execution budgets. Temporary profiling
and diagnostic code was removed before the passing run.

This gate does not prove raw parsing or shipping Rust refinement, validate real
Writfold acquisition, or close the final composed release gate.

## Original revision-1 evidence

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
