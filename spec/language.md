# Language contract

Selected surface contract under the
[revision-2 supplement](../handovers/revision-2/weft/AGENT_START_HERE.md).
The original resolved-AST calculus is qualified; the finite-set/binder extension
requires its own new proof gate. This file and the [EBNF](grammar.ebnf) are not an
implemented parser or a shipping-Rust refinement theorem. Syntax, lexing and meaning
remain separate, following Sovel's specification discipline rather than its language.

## Why EBNF is only one part

EBNF is Extended Backus-Naur Form. It describes how tokens combine. A language
also needs tokenization, name/type rules, evaluation meaning and an assurance
argument. A parse tree alone does not establish that a claim is grounded or a
proof is valid.

Each review has one explicit context/snapshot, a profile, a prospective target,
evidence bindings, immutable set bindings, requirements, hypotheses and checks.
These are Weft source constructs, not new Writfold method names or opcodes.

## Lexical draft

- Source is UTF-8. Diagnostic spans use byte offsets into the exact source.
- `IDENT` is an ASCII letter or underscore followed by ASCII letters, digits or
  underscores, excluding keywords. Names are case-sensitive; no normalization.
- `STRING` is double-quoted. Accept only `\"`, `\\`, `\n`, `\r` and `\t` escapes;
  other escapes are errors. Unescaped control characters, raw newlines and
  interpolation are not allowed. Non-control UTF-8 characters are allowed.
- `INTEGER` is `0` or a nonzero ASCII digit followed by ASCII digits. No sign,
  leading zeroes, exponent or floating point in this sketch. Its semantic value
  is a natural number; a resource limit must reject explicitly rather than wrap.
- `BOOLEAN` is exactly `true` or `false`.
- Space, tab, LF and CRLF separate tokens; an isolated CR is rejected outside a
  string escape. `//` starts a comment through the next newline or end of source.
  Comments are not recognized inside strings. No block comments.
- Maximal munch recognizes `...` before field `.`, `:=` before `:`, and `==`/`!=`
  before `=`. There is no standalone `!`; tokens cannot be joined across whitespace.
  A keyword must end at an identifier boundary: `android` is one identifier.

Keywords: `review`, `context`, `at`, `profile`, `target`, `proposal`, `claim`,
`asset`, `rule`, `citation`, `need`, `assume`, `check`, `by`, `and`, `or`, `not`,
`true`, `false`, `forall`, `exists`, `in`. `let` is not a declaration keyword.

### Precedence and ambiguity decisions

From tightest to loosest: field selection/calls; equality or inequality; `not`;
`and`; `or`. Thus `not a.order == b.order` means `not (a.order == b.order)`.
Boolean connective chains associate left; recursive `not` nests right.

1. Comparisons do not chain: `a == b == c` is rejected. No implicit coercion
   between numbers, strings, identities or units.
2. Parentheses group propositions. Predicate arguments are scalar/reference values,
   not arbitrary effectful expressions or native sets. Quantify over set members.
   Function return values cannot be nested as arguments in this profile.
3. `asset x = citation "..."` binds evidence, not its semantic truth. `x.field`
   requires a profile-defined typed interpretation of those exact bytes.
4. Scope/profile/target headers occur once, in that order. Snapshot strings are
   opaque references; resolution must return full exact bindings. No ambient
   latest release or context is used as an invisible default.
5. Semicolons terminate declarations/checks. Set literals permit a trailing comma;
   argument/rule lists do not. A source file contains one review.
6. Bounded quantifiers use `forall x in S { P }` / `exists x in S { P }`.
   The closing brace bounds the body; an outer `and`/`or` is outside that body.
7. General recursion, arithmetic, imports, arbitrary functions, shell code,
   mutable assignment, automatic admission and implicit refresh are absent.

## Static meaning proposal

Resolve top-level declarations in source order. Targets, evidence/set bindings,
hypotheses and check labels have unique top-level names; no reassignment or forward
references. Quantifier binders are lexical: their domains use the enclosing scope
and their bodies use the new binder. Inner scopes may shadow outer names without
capturing them. Resolve to hygienic binder identities, never text substitution.
Predicate names belong to the profile namespace, not arbitrary host functions.
Field paths, element types, calls and comparisons must type-check even in an empty
quantifier body. Unknown profiles/fields are not silently generalized away.

- `context` selects one authorized context and exact snapshot. A contextual
  locator must resolve unambiguously to realm/context/release identities; an
  ambiguous or unavailable locator is a refusal, not a guess.
- `profile` names the semantic/interpretation/evaluation contract. An input alias
  is usable only after resolution to an exact admitted/qualified profile binding.
  This repository defines no live profile identifiers or registry entries.
- `target` binds a retained prospective subject. It is not a premise that the
  proposed behavior is true or that the plan has been admitted.
- `claim`, `asset`, `rule` request distinct kinds of evidence. Resolution alone
  does not grant usability. Rules also require qualified logical meaning and
  inherited assumptions; corpus admission alone does not prove soundness.
- `name := set_expression` binds a finite immutable set, with no parallel `let`
  form. Set literals contain scalar/reference members and typed `...set` spreads.
  Sets are homogeneous; mixed nominal kinds/realms are not implicit coercions.
  Equality ignores order/duplicates, while all origins and required reads survive.
  Nested sets and set-valued predicate arguments are outside this profile.
  Empty sets acquire element type from context or remain parametric where that
  type is irrelevant; report ambiguity rather than choosing a concrete default.
- `need x` makes x a required grounding dependency even if no expression mentions
  it. Every binding is resolved/assessed and listed, but unused optional bindings
  do not silently become proof premises. Used bindings add dependencies without
  requiring a redundant `need` declaration. `need` may name a target, evidence
  binding, hypothesis or set, not a check result. For a set, require its complete
  materialization and all captured/member dependencies. Required hypotheses must
  be discharged for strict grounding.
- `assume h: P` records a hypothetical premise for subsequent checks. It never
  writes P into Writfold. The hypothesis label is diagnostic, not a Boolean
  variable or a substitute for a Writfold claim.
- `check label: P` asks the selected profile to evaluate/justify P. It is an
  assertion to investigate, not an assertion that succeeds by construction.
- `by r1, r2` supplies already-bound rule candidates. Reject duplicate names or
  non-rule bindings. The evaluator must check each actual derivation; naming a
  rule is not proof that it applies. Listing rules cannot suppress required
  contrary evidence or inherited dependencies.

Even `check ...: true` does not erase explicit `need` declarations, unavailable
required inputs or gaps in the declared obligation inventory.
Finite quantification concerns exactly its captured domain. Empty `forall` is true
and empty `exists` is false; reports disclose vacuity and the actual member count.
`exists x in S { true }` expresses non-emptiness. No literal, spread or search result
implicitly certifies all relevant KB objects or all plan dependencies.


## Evaluation proposal

Capture exact inputs through shared Writfold operations; obtain the applicable
knowledge assessments; interpret fields under the pinned profile; evaluate the
finite comparisons or selected rule fragment; return findings and dependencies.
No local database access or fabricated response replaces a missing operation.

The simple comparison fragment uses typed equality on known values. Boolean
connectives combine its classical values only after the necessary interpretations
succeed. Do not treat acquisition/type/interpretation failures as Boolean false,
including under `not`. Evaluate and report required dependencies even if a pure
Boolean branch could short-circuit. Missing evidence is a report gap, not a
formula literal.
Materialize every set member/spread before normalization; a missing/expired/denied
input cannot disappear as a duplicate or become an empty collection. Preserve
first-occurrence display order, exact typed membership and a shared origin DAG.
Expand bound variables hygienically under the captured environment, with explicit
limits on set work, quantifier depth, body instances, atoms, valuations and output.
Universal/existential lowering is complete conjunction/disjunction, not a partial
loop prefix. Keep per-member explanations, witnesses/counterexamples and all
hypothesis/dependency linkage. Unknown or incomplete work grants no conclusion.


The selected logical core is finite propositional reasoning over typed ground
values and explicitly captured predicate interpretations. Local symbolic analysis
uses the separate hypothetical `weft.symbolic/1` profile; it does not invent a
Writfold assessment. Unsupported external profiles refuse. Full inference, capture,
typing, expansion and output limits remain explicit; exhaustion is not refutation.

Writfold's support states are not the truth values of these connectives. A checked
bridge is required before importing a Writfold formula into this local theory.
Maintain all inherited hypotheses and the exact dependency closure. No theorem
here authorizes effects or promotes a report into the knowledge base.

## Formation and assurance map

| Syntax family | Formation/evaluation obligation | Current status |
| --- | --- | --- |
| Review/header | Exact authorized scope, profile and subject; no ambient context | Owner-side services remain external prerequisites |
| Evidence binding | Kind-safe resolution; durable binding; assessment preservation | Calculus boundary stated; live service mapping unresolved |
| Field/comparison | Independent typed interpretation and exact equality | Original resolved-AST calculus qualified; Rust correspondence pending |
| Predicate/rule use | Signature, interpretation, sound application and dependency closure | Original calculus qualified under explicit assumptions |
| `need` / `assume` | Preserve requirements and hypothetical origins; no authority | Original calculus qualified; set extension requires new proof |
| `check`/connectives | Honest finite outcomes and consistency; no effects | Original calculus qualified; implementation pending |
| `:=` / set literal / spread | Homogeneous finite membership, immutable state, complete origins | New revision-2 proof/implementation obligations |
| `forall` / `exists` | Hygienic binders, complete finite expansion, vacuity and instance traces | New revision-2 proof/implementation obligations |

No grammar family gets a default "safe" case. New source forms require their own
meaning, proof and implementation evidence; the prior calculus or grammar smoke
does not automatically qualify them. Current execution evidence belongs in the
qualification ledger, not in an illustrative syntax example.
