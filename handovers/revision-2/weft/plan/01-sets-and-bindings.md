# Native finite sets and `:=` bindings

## Surface contract

```text
citation_set_s1 := {c1, c2};
all_inputs := {c3, ...citation_set_s1};
need all_inputs;

check inputs_ready:
    forall c in all_inputs { usable(c) };
```

Bindings are immutable and declaration-ordered. `:=` introduces one set binding;
`=` retains its existing role in target/citation declarations. No parallel `let`
syntax, reassignment, self-reference or forward-reference cycle. A failed initializer
does not install a successful value. A new source/cut requires a new review, not
mutation of an earlier set or derivation.

Set expressions are literals, existing set bindings or profile-defined captured
collection paths. Items are scalar/reference terms or `...set_expression` spreads.
Trailing commas are allowed in set literals. Spreading a scalar is a type error;
placing a set where a scalar member is expected is a type error with a spread hint.
Nested sets and higher-order/set-valued predicate arguments are not in this profile.
Set equality/inequality is extensional and type-checked, not list-order equality.

## Types and identity

Sets are finite and homogeneous by scalar/nominal element type. Supported members
are the existing Boolean, natural, text and nominal reference values. A reference
is a resolved typed value, never the spelling of an alias or citation label.
Different nominal kinds/realms cannot be silently coerced into one element type.
The owner-provided interpretation must preserve full durable binding distinctions,
including the relevant scope, revision, representation, selector and profile.
A stable entity ID alone is not equality of evidence bindings.

The type checker infers element type from members, spread operands and use-site
constraints. Empty literals have no arbitrary default element type. An unconstrained
empty type may stay parametric where irrelevant (e.g. `exists x in {} { true }`);
otherwise require sufficient type context or report ambiguity. Unknown external
profiles/fields never become generic functions merely to make an empty query pass.
Type/name-check the body even when the domain is empty; `1 == "1"` and unknown
references do not become acceptable because no instance will execute.

## Materialization and equality

Resolve and validate every member/spread input before normalization. Missing,
denied, expired, malformed, wrong-kind, mixed-type or budget-exhausted inputs return
an explicit incomplete/failure result. Never drop a failed member, substitute HEAD,
or treat an unavailable set as empty.

Canonical display order is first occurrence in the declared expansion. Equality
and membership ignore order and duplicates. This is set union, not textual macro
pasting. Equal resolved members may share one value entry, but every input origin,
required read, scope/assessment obligation and spread edge remains in the dependency
closure. An invalid alias cannot disappear because another alias reached the same
bytes. Model field interpretation is keyed by the full resolved value and selector,
not by whichever display alias survived normalization.

Memoize successful immutable set bindings within one captured review. Repeated
spread does not recursively recopy an exponential dependency tree. Preserve a DAG
of origin references and disclose raw occurrences, distinct members and expansion
work separately. Bound expansion work and retained provenance as well as cardinality.

`need S` requires successful materialization and all of S's required captured/member
dependencies; it is not satisfied merely by S's name existing. Literal values are
not thereby promoted to facts in the KB. Existing explicit-needs preservation
continues to apply even if a quantified body simplifies to a constant.

## Coverage boundary

A materialized explicit set is complete **as that declared expression**. It is not
necessarily the complete set of relevant assets, affected steps or KB facts.
Captured collections preserve query/cut/profile/inventory identities, completeness
and omissions supplied by Writfold. A spread union cannot invent a missing inventory
certificate or upgrade top-k discovery into an exhaustive universe.

Broader plan obligations must bind their intended domain. An agent cannot satisfy
"all affected assets" by substituting an arbitrary smaller literal set. Final
Writfold admission still enforces the applicable procedure/obligation floor.

## Mathematical boundary

Model typed captured values and all origin dependencies independently of source
spelling. Prove normalization membership, homogeneity, idempotence/extensional
identity, spread-origin preservation and immutable environment extension. Prove
that a failed capture/initializer leaves no successful binding. These proofs do
not establish the correctness of an unimplemented owner-side resolver.
