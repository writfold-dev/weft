# Illustrative examples

These are specification examples, **not runnable commands or executed reports**.
All `example-*` references are intentionally non-live labels. No real corpus
records, admissions, approvals, hashes or receipts are fabricated. The EBNF smoke
checks only syntax recognition, not the behaviors described below.

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

No rule evaluator, solver or proof checker was run for this example. This is a
way to discuss inference semantics before choosing an implementation.
