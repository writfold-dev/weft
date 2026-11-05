# Lean obligations and the proof-first checkpoint

P01A/WEFT01A is a new required stage after P01S and before P02. It is produced by
the existing `scripts/gate lean` command with the expanded active contract. A
revision-2 receipt cannot satisfy it. Existing L01–L12 and Q01–Q10 remain required
and must still pass with the extension, not merely compile in an unused namespace.

## Required outcomes

The [registry](../registries/theorems.json) fixes primary and supporting declaration
names in `Weft.Finite.Algebra`. That namespace organizes the new obligations; it
is not permission to implement an easier second evaluator. Put cohesive files
under the existing finite calculus and prove facts about the actual extended
syntax, typing, capture, lowering and report paths.

| Family | Required mathematical and operational result |
| --- | --- |
| A01 | Successful union/intersection/difference have exactly the specified extensional memberships; duplicate-free result and deterministic display order follow from the actual operations. Prove union/intersection identity, idempotence, commutativity and associativity extensionally, plus self/empty difference laws. |
| A02 | Successful operations preserve the unified homogeneous element type, including typed empty results. Incompatible nominal kinds/realms and scalar/set misuse cannot succeed; empty output cannot erase typing obligations. |
| A03 | `in` is true exactly for typed membership; `<=` is true exactly for inclusive subset. Prove empty/reflexive subset and antisymmetry with extensional equality, plus a valid first-left counterexample for false subset. Unavailable operands have no Boolean denotation. |
| A04 | Successful operations and predicates retain complete operand origins/dependencies, including removed members and empty results. Per-member origin attribution remains faithful. Either operand's failure prevents success; successful complete inputs have a successful semantic result. |
| A05 | Extend capture-avoiding substitution, typing preservation and lowering/independent-meaning agreement to all new constructors, including expressions inside quantified domains and bodies. No raw-name substitution or uninterpreted-atom replacement for decidable set predicates. |
| A06 | Operation/comparison traces expose the actual operands, typed membership, source linkage, dependency closure and capture accounting; empty output does not erase input evidence. Binding failure remains atomic and checked subset counterexamples are faithful. |
| A07 | Budgeted operations agree with unbudgeted meaning on success, never increase remaining work, and refuse incomplete work without a successful partial binding/comparison/verdict. Cover operand visits, membership scans, output normalization and provenance work. |
| A08 | Embedding the previous finite language preserves meaning, typing, required closure, binding/binder behavior and local non-authority. New finite comparisons cannot promote inventory completeness, hypotheses or authoritative state. |

Provide non-vacuous positive and negative examples for each family. A theorem with
impossible premises, a redefinition equal to its own result, or a Boolean fold
without typed operand capture is not the requested proof. State all interpretation,
availability, nominal-identity and finite-domain assumptions explicitly. Prove the
operations are usable on valid finite inputs, not only that failure is safe.

## Existing formal extension points

| Files under `formal/Weft/Finite/` | Extend/reuse |
| --- | --- |
| `Sets.lean`, `Sets/Properties.lean` | `CapturedSet`, `Member`, `normalize`, `validate`, `Closed`, exact membership, origin merging, capture statistics and completeness facts. |
| `Syntax.lean` | `SetExpr` already has an internal union used for spreads; reuse it. Add intersection/difference and membership/subset atoms, then extend `elementType`, `evalSet` and substitution. Surface precedence is not proved by this AST. |
| `Typing.lean`, `Semantics.lean` | `checkSet`/`checkAtom`, strict-availability `resolveAtom`, `meaning`/`available`/`Denotes`. Membership/subset resolve to checked Boolean literals like set equality, not free predicate atoms. |
| `Substitution.lean`, `SubstitutionTyping.lean` | Every structural-induction branch for set/atom substitution, lifted lexical environments and typing. Inherited Q05 must cover the extended constructors. |
| `CaptureBudget.lean`, `Lowering.lean` | Budgeted `Program`, `evalSet`/`resolveAtom`, work agreement and complete expansion. Reuse Boolean elaboration for the new predicates; no new logical evaluator is needed. |
| `Traces.lean`, `TraceContext.lean`, example files | Complete provenance and quantified-instance facts through the new expression paths; adversarial examples with inhabited environments. |

Register every new primary/supporting theorem in the required registry and every
other trusted declaration needed by the proof path in `formal/audit-targets.json`.
Avoid duplicate audit entries. A wrapper theorem must not hide an unaudited,
unqualified operation implementation. Lean remains core-only on the pinned
4.21.0 toolchain; no mathlib, remote package, `sorry`, admitted/custom axiom or
native-decide axiom. Only the existing foundational axiom policy is allowed.

## Executable reference and independent comparison

Extend `formal/Weft/FiniteReference.lean` and its exact expected case inventory in
`scripts/run_proofs.py`. Keep existing cases. Execute all five operations on real
typed inputs, not hardcoded expected answers. Include successful/false predicates,
empty/deduplicated results, wrong nominal types, unavailable operands, surviving
and removed origins, typed empties, capture counts, nested substitution and budget
refusal. Reference output must expose enough of those results to compare them.

The current `scripts/rust_differential.py` translates Rust's already-lowered Boolean
formula graph into the `weftref` protocol. That checks classification/model behavior;
it does **not** independently validate the set calculation that produced a literal.
Retain that check and add operation-level Lean/Rust comparison using the actual
`weftfiniteref` executable. Fixed paired vectors are sufficient: the Lean side
independently constructs/evaluates the same typed inputs and the Rust side compiles
corresponding source. Compare memberships, types, stable order, semantic origin
closure, predicate truth/refusal and relevant accounting. Normalize only documented
cross-runtime IDs, never erase distinctions being tested. Do not feed Rust's
computed Boolean back as Lean's expected set answer.

Finish the extended finite reference before the first proof checkpoint. The current
`scripts/rust_gate.py::proof_prerequisite` permits only a separately qualified
`formal/Weft/Reference.lean` protocol delta between its two checkpoints; do not widen
that exemption to admit changed calculus or finite-reference bodies. A later
semantic change reopens M1, then requires a matching fresh reference checkpoint.

## Mutation and qualification calibration

Extend `scripts/lean_mutations.json`; preserve existing coverage and require at
least one substantive semantic mutant per A family. Include these failure classes:

- Wrong union membership, swapped difference direction, or intersection behaving
  as union; changed stable-order behavior must also be detected.
- Remove the operand-type check or discard a typed empty's type.
- Implement inclusive subset as strict subset, accept only overlap as subset, or
  return false for an unavailable membership operand.
- Drop right-operand/removed-member origins, including on an empty result.
- Skip substitution for a new constructor, or substitute through a shadowing binder.
- Forge an operand/counterexample trace or misreport normalization input counts.
- Bypass a comparison/provenance work charge and return a completed prefix.
- Upgrade external-inventory completeness or local authority in a new result path.

Each mutant has a unique applicable edit anchor and fails a relevant substantive
proof/example, not merely parsing, a stale name, a missing import or an unrelated
build error. Mutation counts are measured from the actual profile, not copied from
this plan. Keep source-bound failed attempts. Extend `scripts/test_qualification.py`
if necessary to reject missing A families, bypassed P01A, stale source/reference
artifacts and changed active authority. Do not weaken `contracts.reconcile` or
`conserve_requirements` to make a receipt green.

## Objective M1 exit gate

Before any feature Rust implementation lands, retain a fresh external receipt
showing all of the following for the exact frozen/adopted inputs:

1. Clean pinned-toolchain build of the full inherited and extended Lean calculus.
2. Complete registered axiom audit, including supporting declarations; no forbidden
   axioms and no skipped required declarations.
3. Executed original and extended reference cases with exact inventories and real
   retained `weftref`/`weftfiniteref` binary hashes.
4. All inherited/new semantic mutants rejected for their intended obligations, plus
   qualification-boundary negative controls.
5. Reconciled immutable ancestry, source contracts, registries, audit/mutation
   profiles, exact tool identities and complete stdout/stderr/exit evidence.
6. An explicit mapping from A01–A08 to actual declarations, assumptions, fixtures,
   and the shipping paths planned for M2. No claim of raw-parser or Rust refinement.

Archive the old active proof/reference ledgers without altering their receipts.
Only after actual success update `qualification/finite-calculus.json` to the new
checkpoint. Produce and record a matching fresh reference-calibration receipt
before the Rust gate consumes it; an unchanged formal tree may be used for this
second checkpoint. `qualification/reference-calibration.json` must bind the new
calculus-ledger hash and exact reference artifacts, not the old revision-2 pass.
A failed, skipped, missing or stale input keeps P01A closed.
