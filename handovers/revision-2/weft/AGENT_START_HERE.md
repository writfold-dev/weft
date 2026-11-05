# Weft revision 2 — native finite collections

This supplement adopts Tarek's requested native finite sets, immutable `:=`
bindings, set spread and bounded `forall`/`exists`. There is **no `let` alias**, no
mutable assignment, and no Turing-complete execution language.

Revision 1 remains the base implementation/architecture/build/integration contract.
Read its entrypoint and all six plans, then this supplement's three plans and
registries. Its immutable manifest is pinned in base.json. Writfold work remains
proposal-only; the other agent owns that checkout. The complete real workflow is
still required, not replaced by local symbolic examples.

The original calculus passed `lean-009` with 43 audited declarations and 14
semantic mutant rejections. That exact earlier scope is retained in
qualification/revision-1-status.json and docs/calculus-assurance.md. It does not
qualify this extension. Add P01S/WEFT01S before P02 and before the Rust evaluator.

Execution order: preserve the old qualified scope; freeze collection/binding and
quantifier semantics; prove Q01-Q10 and their composition with the old calculus;
run fresh axiom/reference/adversarial/mutation checks; only then implement the
selected extended language in Rust. Keep all source and failed-attempt identities.

Read:
- plan/01-sets-and-bindings.md
- plan/02-quantifiers-and-reports.md
- plan/03-proof-and-acceptance.md
- registries/theorems.json and registries/gates.json

Do not count a parsed set, an unrolled template or a useful partial report as the
full feature. Membership identity, complete materialization, provenance, lexical
scope, type checking, budgets, vacuity and per-instance explanations are required.
Unresolved references never disappear during deduplication or become an empty set.
