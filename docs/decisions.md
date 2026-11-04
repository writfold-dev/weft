# Decisions and open questions

Status: discussion record, 4 November 2026. This repository does not change
Writfold's implementation/admission authority.

## Decided direction

1. **Ordinary client, not VM.** Weft drives Writfold through its shared structured
   stdio interface, as an agent does. The earlier Writfold-opcode/recipe-executor
   idea is withdrawn. Local AST/IR evaluation is not a remote instruction set.
2. **Language ownership.** Parsing, semantic passes, local evaluation, inference
   orchestration and report presentation belong to Weft.
3. **Knowledge ownership.** Writfold remains the authority for corpus admission,
   exact scoped evidence, applicability/freshness assessment and permitted effects.
4. **Private design repository.** Keep the design in `writfold-dev/weft`. Do not
   copy private source bundles or playbook material into it.
5. **Explicit uncertainty.** Do not quietly turn a proposed syntax, rule or report
   into an implemented feature, qualified proof system or new admission path.

## Recommended starting point, not yet frozen

A read-only grounded-plan report for one exact proposed change. Begin with finite
comparisons between structured plan declarations and retained contracts, together
with Writfold's existing evidence assessments. Add symbolic inference only when a
real question needs it and its evidence-to-premise bridge is specified.

Why this start: a report is useful without editing the execution graph, choosing a
solver, designing bytecode or claiming arbitrary code correctness. Its dependency
structure is also the information a later integration would need for retained
history, reassessment and review.

## Decisions still to make

| Question | Current proposal | What a different choice changes |
| --- | --- | --- |
| First real task | A declared API change checked against its contract | Determines actual inputs, predicates and adequacy criteria. |
| Meaning of grounding | Required obligations justified from usable, captured knowledge; no unresolved required hypotheses | A weaker conditional mode must remain visibly conditional. |
| Source of obligations | Explicit authored plan and admitted profile | Automatically extracting obligations from prose needs a separate, reviewed interpretation boundary. |
| Initial logic | Total finite comparisons, then a small qualified rule fragment | General quantifiers, arithmetic or SMT create new totality, model and proof obligations. |
| Rule introduction | Pinned registered interpretations/qualified rule profiles | User-authored rules must be treated as hypotheses until separately justified; admission alone is not a soundness proof. |
| Grammar | Illustrative EBNF with explicit contexts, bindings, needs and checks | Parser acceptance is not semantic acceptance or proof discharge. |
| Report shape | Independent evidence axes, per-obligation findings and dependency closure | Exact serialization, fingerprints and retention envelope need a separate contract. |
| Execution-history use | Optional retained evidence referenced through Writfold | Trusted gate consumption requires an admitted producer/checker profile and typed integration. |
| Coverage enforcement | Declared obligations and captured reads only | Covering arbitrary agent reads/effects requires additional containment, not a language keyword. |

## Before implementing

- Walk through a real plan with its actual authorized evidence and contrary cases.
  Freeze what counts as sufficient coverage for that task.
- Define exact rule/predicate signatures, their interpretation of evidence and
  the selected logical outcomes. Prove or qualify the needed semantic bridges;
  record assumptions rather than claiming universal truth.
- Map the required reads and assessments to actual shared Writfold operations.
  Missing APIs remain prerequisites, not fictional method names or fallbacks.
- Decide a versioned report/evaluation contract with adversarial examples. Only
  then settle parser/runtime packaging and any proof backend dependencies.

## Writfold boundaries preserved

Revision 5 and the scoped revision-9 feature adoption remain controlling. This
repository neither activates v9's global policy/registries nor its deferred
universal per-proposal Lean certificate requirement. It does not qualify an
external solver, add a new admission route or relax existing witnesses, review,
grants, freshness, expected heads or publication checks.

The known P01O/WF24 storage blocker is not rerun or bypassed here. Current Writfold
production integration proceeds in its existing dependency order; this design
work does not redirect or modify its in-flight implementation.
