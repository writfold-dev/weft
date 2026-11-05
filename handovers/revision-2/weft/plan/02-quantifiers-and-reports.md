# Bounded quantifiers and report semantics

## Syntax and scope

```text
sdks := {"sdk-v1", "sdk-v2"};
all_sdks := {"sdk-v3", ...sdks};

assume support:
    forall sdk in sdks { accepts_cursor(sdk) };

check required_support:
    forall sdk in all_sdks { accepts_cursor(sdk) };

check at_least_one:
    exists sdk in sdks { accepts_cursor(sdk) };
```

Quantifiers are expressions, with `forall IDENT in SET { EXPR }` and the analogous
`exists`. The domain is evaluated in the enclosing scope; the new binder is visible
only in the body. Inner lexical scopes may shadow outer names, with unambiguous
nearest-binding resolution. Top-level `:=` rebinding remains forbidden.

Nested quantifiers are allowed, including finite inner domains depending on outer
members. Use hygienic resolved binder identities/de Bruijn indices; never implement
substitution by replacing identifier text. A spread reference resolves as a set,
not as a scalar with the same display name. Unknown/out-of-scope variables refuse.

`assume forall ...` remains a named hypothetical premise. Recording it does not
establish admission, freshness or factual truth for its members. `check forall ...`
asks for justification. Every hypothesis stays visible in later conclusions.

## Logical meaning and lowering

For a captured finite typed set S, `forall x in S { P(x) }` denotes conjunction of
all well-typed instances; `exists` denotes disjunction. Lower into the existing
finite propositional IR only after capture and typing. Prove capture-avoiding
substitution/environment extension and semantic preservation of this lowering.
The interpreter remains non-Turing-complete; there are no effectful loops, recursion,
mutable stores, dynamic native calls or a second Writfold execution engine.

Every instance is interpreted under the same exact captured context/profile and
appropriate lexical environment. Missing interpretations/fields are typed failures,
not false atoms. A successful outer predicate cannot hide unavailable required
inputs in another branch. No partial expansion may masquerade as a complete fold.

The reference semantics must be independent of lowering. Define finite universal
and existential meaning directly over set membership and bound environments, then
prove the generated conjunction/disjunction agrees. Keep unresolved observations,
execution failure and inconsistent logical premises distinct.

## Empty domains and evidence

`forall` over an empty typed domain is true; `exists` is false. Do not change these
laws to avoid vacuity. Instead report `domain_size: 0`, `vacuous: true` for universal
success, and no witness for an empty existential. A separate requirement
`exists x in S { true }` expresses non-emptiness without a new privileged predicate.

Vacuous success is not evidence that all real-world dependencies were discovered.
Retain the intended-domain binding, declared/materialized coverage, source origins
and independent required-input gaps. Writfold's governing plan/procedure requirements
cannot be weakened by choosing an empty proof domain.

## Budgets and failure atomicity

Bound set expansion, unique members, quantifier depth, instantiated body nodes,
atom count, valuation search and trace bytes separately. Nested finite domains can
still expand exponentially. Charge before accepting results; inability to finish
capture/typing/expansion/search/reporting produces explicit incomplete status.
No guessed partial universal success, existential failure, empty replacement or
silent omission of required references.

Memoization applies only to the same immutable binding/cut/profile, never to a
moving alias or a refreshed observation. Failed bindings/cells do not publish values.
Current authority/freshness is still rechecked before later Writfold effects.

## Quantified report extension

Retain the ordinary report axes and add actual collection/instance structure:

- Set binding identity/name, element type, exact distinct members, source/spread
  origin DAG, raw occurrence count, complete materialization status and inventory
  completeness/omissions where provided.
- Quantifier kind, source span, binder identity, domain binding, member count,
  instantiated count, expansion/search budgets and vacuity.
- Per-instance member identity, substitution/environment binding, body trace root,
  outcome and actual dependencies/hypotheses.
- Counterexamples and witnesses identify actual members under a checked valuation.
  A member is labelled uniformly entailed/refuted only when that stronger result
  was separately established under the same premises.
  Negative/unknown members and omitted/unavailable instances remain visible.
  Do not fabricate witnesses from discovery ranking.

Existential entailment need not supply a single uniform witness: premises `A or B`
entail an existential over members with bodies A/B, although neither instance is
individually entailed. Universal refutation can likewise have different failing
members in different models. Preserve model-scoped witnesses and full coverage;
never replace existential semantics with "some individual instance is entailed".

Known instance findings may be useful while the aggregate assessment is incomplete;
label their scope and never promote partial coverage to a complete reusable result.
Set deduplication may share values, not erase conflicting provenance or failed reads.

This model concerns checked derivation structure, not private LLM reasoning. Any
retention, execution-graph linkage or learning admission still uses the existing
separate Writfold gates.
