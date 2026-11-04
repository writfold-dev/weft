# Verification report proposal

Status: proposed information model, not a frozen wire schema or an implemented
report command. The [mockup](visual-guide.md#report-surface) is synthetic.

## What a human should learn

- Which exact change and knowledge snapshot were assessed?
- Which declared obligations are satisfied or violated, and why?
- Which conclusions depend on hypotheses or unusable knowledge?
- What is missing, stale, contested or outside the assessment's coverage?
- What exact dependency would need new evidence before a finding could change?

Avoid an unqualified green "makes sense" badge. A deterministic contract mismatch,
a stale supporting receipt and an unresolved hypothesis are different problems.

## Keep separate axes

| Layer | Proposed information | Do not infer |
| --- | --- | --- |
| Execution | Completed, incomplete, failed or not run; typed cause and completed steps | A timeout or failed read means the proposition is false. |
| Writfold assessment | Original support/applicability/freshness/validation/contestation/availability/usability fields where applicable | Positive support means current truth, or BOTH means classical refutation. |
| Obligation result | Satisfied, violated, undetermined, inconsistent premises or not evaluated, under the named method | All methods establish the same kind of theorem. |
| Basis | Grounded for the declared use, hypothetical, unusable or unassessed | A conditional derivation is a grounded permission to act. |
| Coverage | Declared obligation inventory, captured dependencies, justified domains and omissions | No additional search hits means exhaustive knowledge. |
| Later use | Informational report versus separately admitted gate evidence | Retaining a report makes it an authoritative receipt. |

These names are discussion labels. A concrete profile must define the exact
variants and their combinations before they become a serialization contract.

For a finite exact comparison, satisfied/violated means the checked comparison
returned true/false on well-typed bound values. For future classical reasoning,
retain the backend's own precise conclusion: entailment, refutation, two checked
models, inconsistent premises or unknown search/checking. The human presentation
must not erase that distinction. Unknown search is not two-sided undeterminedness.

A usable grounded contradiction is a valuable result even though the proposed
plan fails an obligation. Conversely, a historical mismatch based on a stale
contract is not a currently grounded violation. Record the comparison and its
unusable basis separately rather than deleting the useful observation.

## Required information groups

### Identity and context

- Exact query source and resolved typed representation identities; language and
  semantic-profile versions; intended use and explicit assessment time.
- Exact subject identity and kind: proposed plan, patch or design. The subject
  may be prospective, not admitted supporting knowledge.
- Realm, context and corpus release/storage pin. Include an engineering read cut
  only if activity data is actually needed; disclose its watermarks and omissions.
- Actual evaluator/interpretation identities. Include solver, lowering, checker
  and proof dialect identities only when those components were actually used.

### Evidence inventory

For every premise/asset: its exact durable binding, selector units, acquisition
outcome, interpreted value/formula, dependency closure and applicable Writfold
assessment. Preserve supporting and contrary witnesses required by the profile.
Record the assessment time and the policy/validation profile used.

An opaque retained asset may need integrity/availability and an associated
scope/validation claim, not a fabricated claim-support enum for the bytes.
Associate that claim with the exact asset, not merely a matching human label.

Compact citations are input conveniences. Export expands them to durable
bindings; a report must not depend on a process-local alias surviving.

### Findings and explanations

Each finding identifies its obligation, method, result, basis, rule/interpretation,
used evidence, hypotheses, diagnostic/counterexample and unresolved dependencies.
A proof or checked model is retained when the chosen method requires one. A
comparison can retain its exact typed operands and computation witness instead.
Do not invent a cryptographic receipt namespace before a contract exists.

Explain why a result holds under its model; do not generate stronger prose such
as "the patch is safe" from a narrow field comparison. Invalid proof artifacts
are verification failures, not evidence against the requested proposition.

### Coverage and reuse

Keep declared, actually read and checked-used dependencies distinguishable. If the
checker cannot establish a smaller used set, retain a conservative closure.
Explicit `need` declarations are requirements even if no final expression uses
them. Unresolved required hypotheses cannot disappear through presentation.

Bind the obligation inventory and its source. Completeness of the evidence read
set says nothing by itself about completeness of the real-world requirements.
No automatic replacement of a missing object with HEAD or a newer observation.

Reassessment is selective but conservative: changed subjects/rules invalidate
affected findings; changed authority/corrections/freshness require current-policy
reassessment. An unrelated corpus advance does not rewrite historical evidence.
A historical report remains historical, not a new observation at replay time.

## Proposed summary rule

Only describe a review as **all declared obligations satisfied on grounded
inputs** when every required obligation completed positively, the required
knowledge meets its applicable Writfold policy, the captured closure is adequate
for the declared task and no required hypothesis remains unresolved.

The phrase intentionally says nothing about undeclared requirements, arbitrary
code correctness or current execution permission. Any other summary must name
its gaps and preserve every per-obligation result, including mixed outcomes.

## Adversarial design cases

These are expected design behaviors, not executed product tests.

| Case | Required report behavior |
| --- | --- |
| Positive support, stale validation | Preserve support; flag staleness; do not claim current grounded satisfaction. |
| Positive and negative witnesses | Preserve BOTH/contestation and relevant evidence; no explosion or cherry-picking. |
| No witness or inaccessible citation | Preserve missing/unavailable/unauthorized cause; no false proposition inferred. |
| Proposal differs from contract | Show exact declared fields and comparison; do not claim implementation behavior. |
| Malformed field/selector | Interpretation failure, never inequality or a logical counterexample. |
| Stored assumption with no discharge | Hypothetical basis, even if its record is admitted. |
| Satisfiable premises and checked counterexample | Scope the counterexample to the selected model/theory. |
| Inconsistent classical premises | Explicit inconsistency; no ordinary entailment/admission conclusion. |
| Incomplete inventory or discovery results | No universal conclusion over an alleged complete corpus domain. |
| New context, expired grant or correction | New applicable assessment required; do not silently reuse old authority. |
| Wrong CNF or wrong proof binding | Reject verification; proof validity alone does not establish correct lowering. |
| Solver budget exhausted | Unknown/incomplete search, not refutation or two-sided undeterminedness. |
| Valid report copied to another plan | Subject/dependency mismatch; no reusable verdict. |
| Run attachment attempted without authority | Refuse the effect; keep report analysis distinct from attachment outcome. |
