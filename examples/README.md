# Executed local examples and external proposals

The local `weft.symbolic/1` examples run through the actual static Rust binary.
They do not resolve the deliberately unavailable context/proposal references or
claim admitted KB facts. Exact evidence is in
[runtime assurance](../docs/runtime-assurance.md).

| Source | Exercised logical results |
| --- | --- |
| [symbolic.weft](symbolic.weft) | Entailed readiness; refuted contrary premise; undetermined unrelated predicate |
| [inconsistent.weft](inconsistent.weft) | Inconsistent premises, never an unrelated entailed conclusion |
| [sets.weft](sets.weft) | Entailed known members; undetermined wider domain; entailed existence/non-emptiness |
| [quantifier-models.weft](quantifier-models.weft) | Existential entailment without a uniform member; undetermined then refuted universal |
| [empty-domain.weft](empty-domain.weft) | Explicit vacuous universal and refuted non-emptiness |

Run `weft prove FILE` for JSON or add `--human`. Complete local proof outcomes
exit 1; they remain hypothetical, non-grounded and non-authoritative.

The two external examples below are still **design proposals**. Their syntax and
unresolved-input refusal were exercised; no live field/rule interpretation was
invented. All `example-*` references are non-live labels.

## Declared ordering contract

[ordering.weft](ordering.weft) asks about an explicit declared plan/contract
comparison, while retaining an independent required SDK-validation dependency.

The imagined input bindings for discussion are:

- Proposal `example-plan-17`: a structured prospective plan whose nominal `order`
  field is `unspecified`.
- Asset `example-contract-4`: a structured API contract whose `required_order`
  field is `stable`.
- Claim `example-contract-scope-8`: about the exact contract asset and intended
  endpoint/use; supposed for this example to have an admitted, applicable,
  positive-only, fresh, validated, uncontested and usable assessment.
- Claim `example-sdk-validation-9`: about the exact affected SDK binding; supposed
  to have positive support but a stale validation basis, and to be unusable under
  this example's strict policy. The actual profile must distinguish claim
  freshness from receipt applicability; neither may be inferred from the other.

The example interpretation maps the first two fields to the same finite
`Ordering = stable | unspecified` domain. It verifies the scope claim's exact
asset/endpoint binding; it does not extract a theorem from prose.

**Expected design behavior:** the ordering obligation is violated on those
assumed usable bindings. The separate required SDK-validation dependency remains
unmet. The summary cannot say all obligations are grounded and satisfied. The
report mockup shows these two different reasons, not a single confidence score.

Changing the proposal field to `stable` would remove this declared-field
mismatch, but would neither refresh SDK evidence nor prove actual implementation
behavior. Missing or undecodable fields produce an interpretation failure, not a
false equality. A stale contract basis would prevent a currently grounded
violation even though the historical fields still differ.

## Conditional inference

[conditional.weft](conditional.weft) illustrates the other branch: exploring what
would follow if a missing premise were supplied.

The imagined pinned rule is deliberately narrow:

```text
accepts_cursor(change.client)
and change.cursor_format == "opaque"
  => cursor_precondition_met(change)
```

The profile defines `cursor_precondition_met` as exactly this limited condition,
not global API compatibility, safety, rollout authorization or implementation
correctness. The proposal declares `cursor_format = "opaque"`; the client
acceptance premise is an explicit hypothesis. A qualified finite-rule checker
would have to establish this derivation and preserve that dependency.

**Expected design behavior:** a conditional finding under `client_acceptance`,
never a grounded pass. The hypothesis could later be discharged only through an
explicit valid evidence-to-premise bridge for that exact client/format binding.
An admitted record saying "we assume the client accepts cursors" would not suffice.

The local CLI refuses this external profile/field/rule path rather than supplying
the imagined values. That refusal is exercised; the proposed real derivation is
not a qualified Writfold capability.
