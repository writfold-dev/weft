# Weft implementation handover — revision 1

Authority: Tarek's 4 November 2026 instruction to prove the language, land an
execution plan, then implement it. This supersedes the exploratory status of the
initial Weft design where this handover settles a choice. It does not alter any
Writfold authority, gate, identifier, signed byte or immutable handover.

## Ownership and objective

Work only in the Weft repository. Another agent owns Writfold. All requested
Writfold changes are **proposals**, recorded in plan/06-writfold-handoff.md; never
edit that checkout, move it into a monorepo, invent its method schemas or bypass
its admission gates. Retain two repositories. Consume exact owner-landed shared
contracts when available, rather than fork their identities.

Deliver a small, soundly specified language that exposes the justification of an
agent's plan while preserving freedom to explore hypotheses. Weft is an ordinary
structured-stdio Writfold client, not a VM/opcode/recipe extension to Writfold.
The final required flow is agent proposal -> grounded assessment -> retained
report/run binding -> separately authorized execution -> evaluated knowledge
admission. A local syntax checker or hypothetical report alone is not completion.

## Execution order

1. Read every plan file and both registries. Reconcile mutable qualification/status.json
   and exact source/tool evidence, never copy status from this contract.
2. P00 admits the local tool/storage setup without changing the operator's policy.
3. P01 proves the complete finite language calculus, elaboration/substitution laws,
   logical outcomes, dependency accounting and grounding/non-authority judgments
   in Lean. No production Rust evaluator before the required Lean gate passes.
4. P02-P04 implement the matching frontend, pure evaluator, trace/report and CLI.
   Source-bound differential agreement is not a Lean-to-Rust refinement theorem.
5. P05-P07 consume the real owner-landed Writfold services in dependency order.
   They remain required even if externally blocked; no mocks, alternate writer,
   guessed protocol, synthetic admission or automatic effect retry.
6. P08/P09 qualify and deliver the composed Linux/WSL x86_64 musl release. A
   development binary may be exercised earlier but must disclose its exact scope.

## Required reading

- plan/01-language-and-proofs.md
- plan/02-report-and-identity.md
- plan/03-rust-architecture.md
- plan/04-build-and-quality.md
- plan/05-stages-and-acceptance.md
- plan/06-writfold-handoff.md
- registries/theorems.json and registries/gates.json

## Evidence rules

No sorry, admitted theorem, custom axiom or proof of a renamed easier evaluator.
List mathematical premises explicitly; Lean does not prove remote facts true,
source declarations faithful to code, or Writfold APIs implemented. Separate the
language theorem, parser/compiler correspondence, production implementation and
operational integration evidence. Preserve failed attempts and negative controls.

Every gate receipt binds exact inputs, tool image/executable identity, commands,
exit status, stdout/stderr, fixtures and output hashes. Missing, skipped, blocked
and stale are not pass. Current status lives outside this immutable handover.

Keep functions cohesive, IDs nominal, errors actionable and unknown distinct from
false. Reports show positive justifications as fully as violations. No unsupported
claim that every unstated LLM premise or every external dependency was captured.
