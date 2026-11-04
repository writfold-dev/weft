# Language, calculus and proof-first boundary

## Selected language

Preserve the small review syntax in spec/grammar.ebnf: explicit context/snapshot,
profile, prospective target, claim/asset/rule bindings, need, assume and check.
The initial logical fragment is **finite propositional logic over typed ground
comparisons and predicate applications**. No general recursion, native functions,
implicit imports, arithmetic, quantifiers or effectful source constructs.

Natural literals are arbitrary-precision nonnegative values. Values distinguish
Boolean, natural, text and nominal external identities; equal bytes do not erase
the identity kind. Predicate signatures and field interpretations are profile
inputs, not arbitrary host callbacks accepted on the strength of their names.

Scope/profile/target syntax denotes requests for exact binding, not trusted data.
Citation strings preserve the Writfold public token; unresolved references remain
requests, never observations. A prospective subject is not admitted knowledge.

## Mathematical layers

1. **Ground values and typed terms.** Explicit type assignment and environment
   well-formedness. Field/path lookup cannot coerce text into an identity or turn
   absence into a Boolean value. Natural values never wrap.
2. **Surface propositions.** Booleans, typed equality/inequality, declared predicate
   applications, not/and/or. Source names and field selections remain explicit.
3. **Elaboration.** Validate term types/signatures; intern exact ground predicate
   applications; lower comparisons to justified constants and != to negated ==.
   Preserve source spans/dependencies in the implementation's separate provenance
   side table. Elaboration cannot assert that a missing observation is false.
4. **Logical IR.** Formula over nominal atom indices, with constants, negation,
   conjunction and disjunction. A rule contributes an explicitly checked formula
   (e.g. implication desugared as not-premise or conclusion), not an executable
   function and not an inference licensed by a source label alone.
5. **Finite semantics.** A valuation maps every captured atom to a Boolean.
   Premises are a finite conjunction of imported evidence, admitted/qualified
   rules and explicit hypotheses. A well-scoped formula uses only captured atoms.
6. **Outcome checker.** Enumerate/check the finite valuation domain within an
   explicit budget. Exhaustion yields unknown, never a logical verdict. Require
   a model of the premises before reporting entailment/refutation.
7. **Grounding judgment.** Logical success and evidence eligibility are independent.
   All explicit needs and conservative used dependencies remain required. Current
   applicable Writfold assessments, adequate captured closure and no unresolved
   required hypotheses are necessary for a grounded positive claim.
8. **Report projection.** A result carries actual derivation/comparison steps,
   model witnesses or exhaustive-check accounting plus all premise origins. A
   display string cannot strengthen it or confer authority.

## Precise logical outcomes

For consistent premises P and query Q: entailed means every P-model satisfies Q;
refuted means every P-model falsifies Q; undetermined requires both models.
Inconsistent means P has no model in the complete selected finite theory. Unknown
means the required computation/check did not finish. Acquisition, authorization,
malformed input and invalid evidence are typed failures, not refutations.

The reference evaluator may enumerate models; the production evaluator may avoid
retaining all models by streaming valuations and recording completeness bounds,
first positive/negative witnesses and checked dependencies. An optimization must
preserve the reference result and cannot drop required evidence on a short circuit.

## Substitution, sugar and binding

There are no expression binders or implicit variable capture. Names resolve once
in declaration order to nominal local bindings; shadowing and forward references
are errors. Ground predicate arguments are typed values. Atom renaming and formula
substitution must commute with evaluation under the corresponding environment.
Prove desugaring preserves meaning; do not merely compare two example outputs.

Assumptions scope over subsequent checks, remain structurally separate from
observations and propagate conservatively. Rule expansion is bounded and uses
qualified pinned rule schemas. There is no arbitrary user rule-to-truth shortcut.

## Required theorem families

The registry names L01-L12. Each must have an actual statement, source declaration,
explicit premises and a negative calibration before being counted complete:

- L01: typed term evaluation preserves its type; missing lookup cannot yield value.
- L02: successful elaboration agrees with the independent surface semantics.
- L03: atom renaming/substitution commutes with valuation semantics.
- L04: equality/inequality and implication sugar preserve meaning.
- L05: finite valuation enumeration is complete for the declared atom domain.
- L06: entailed/refuted/undetermined/inconsistent results have their stated meaning.
- L07: incomplete search/failure cannot produce a completed logical verdict.
- L08: required dependency aggregation preserves every explicit need.
- L09: grounded success implies eligible inputs and no unresolved required hypothesis.
- L10: context/binding equality is required for reuse; no cross-context pooling.
- L11: trace projection preserves checked result/dependency/assumption content.
- L12: analysis/reporting cannot manufacture effect or corpus-admission authority.

Do not define the intended theorem as the checker returning true and then prove
that tautology. Define denotational meaning independently of execution. Positive
examples must inhabit the premises; negative cases must exercise wrong polarity,
contradictory assumptions, same-spelled IDs in different contexts, dropped needs,
stale/unknown evidence, malformed terms and exhausted budgets.

## Assurance scope and implementation bridge

Lean 4.21.0, core only. Audit every registered declaration's transitive axioms;
allow only explicitly reviewed Lean foundational axioms. No native_decide as a
substitute for kernel-checked proof of the registered semantic claims.

The calculus theorem starts at the specified surface AST and explicit validated
input interpretation. It is not a proof that a byte lexer or the shipping Rust
compiler implements that AST correctly. P02/P03 therefore require parser fidelity,
source-to-IR conformance, named production mappings and adversarial tests. If a
formal Rust/refinement theorem is later claimed, it needs a separate proved bridge;
differential agreement alone never supplies it.

EvidenceSound, authorized acquisition, correct registered interpretations and the
Writfold assessment/admission boundary remain explicit environmental assumptions.
They cannot be discharged by a Weft syntax check or by a hash matching bytes.
