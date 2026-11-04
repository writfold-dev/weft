# Design checks

Executed on 4 November 2026 during initial repository preparation. These checks
exercise the **design artifacts**, not a Weft runtime, inference calculus,
Writfold integration or trusted proof checker. No production verification report
was generated.

## Grammar and document smoke

An in-memory, standard-library Python recognizer read the actual EBNF and built
an interpreter for its sequence, choice, optional and repetition productions.
It did not use a separately hardcoded parser for the example programs.

- All 22 productions were defined and reachable from `source_file`; no undefined
  nonterminal or lexical terminal remained.
- Four positive syntax cases were recognized: both `.weft` examples, connective
  precedence syntax and a string containing an escaped quote/comment delimiter.
- Nine negative syntax cases were rejected: missing terminator, chained
  comparison, unsupported mutation, missing snapshot, misplaced duplicate scope
  header, unknown escape, raw string newline, isolated CR and unbounded quantifier.
- Local Markdown link targets and the used heading anchor resolved within this
  repository. This does not claim external links were fetched or authenticated.
- The SVG parsed as XML, had the intended viewBox and contained no scripts,
  external references, animation, foreign objects or painted background.

The recognizer was a throwaway in-memory check, not a shipped parser or a new
production dependency. Syntax recognition does not prove grammar unambiguity,
type correctness, name resolution, semantic soundness or the examples' outcomes.
In particular, the conditional derivation was **not** executed or proof-checked.

## Visual smoke

All three Mermaid diagrams were parsed and rendered with Mermaid **11.12.1** in
Chromium. Screenshots were inspected for the client boundary, grounding flow and
possible later execution-history integration. The preview page had no horizontal
overflow at a 1200 by 900 viewport.

The standalone report SVG was rendered as an image and inspected on light and
dark browser surfaces. It has a 920 by 620 viewBox and explicit intrinsic size;
its text and boundaries remained readable. It is a synthetic mockup, not a
screenshot of an implemented application. Preview-only library loading is not
an admitted Weft dependency or a qualification of GitHub's renderer.

### Retained limitations and repairs

- The first generic SVG raster preview appeared black/unreadable. That preview
  contrast issue was reported to the tool owner; Chromium rendering was used to
  inspect the actual SVG instead.
- Initial long left-to-right diagrams made labels too small. The boundary diagram
  was simplified and the execution-history diagram changed to a vertical layout;
  the final diagrams were rendered and inspected again.
- No Writfold build, native storage campaign, live corpus query, solver execution,
  certificate replay or effect/admission operation was run. Existing Writfold
  qualification status is unchanged.

## Exact checked design inputs

SHA256 of the relevant source artifacts, after visual-layout repairs:

```text
7cd224cfd89f20ffecca08ad8efc6ae9de9b4b767c77e63b0d69af4eee5dd73a  spec/grammar.ebnf
286806cd3ae56b43723e92a3208a847869e548721038ad0c19aa1228e9e614a9  spec/language.md
b960c009d79c2d5791454d83a83c4ceaf2c041d512c08d2a489da138088ce340  examples/ordering.weft
c36fbfaf088058b7e6ae44f49d9c6f7a61f3fa171a70c94cbabdaaf72ea2444d  examples/conditional.weft
69fc3cb483339c7bdb4a2ef1e24489e197d5ed881c0d23f57e3664d32f00c188  docs/grounded-plans.md
dacc7edde9af1f17cdb08c28f0e0b9323c860de45de6272689f1c2347f7d8816  docs/verification-report.md
444329e910c0d04831c93c787194b71b78b582dd1c87cd86faaf5e06819805d3  docs/visual-guide.md
902c7017aac590aab72f9e46b1d3f56cf7aa23df01ec9de1d8f321d6fca4f22b  docs/report-mockup.svg
```

These identities bind documentation and examples only. They are not Writfold
fingerprints, authenticated receipts or evidence that the proposed semantics are
implemented or proved.
