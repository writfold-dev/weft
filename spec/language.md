# Language sketch

Status: illustrative proposal, not a parser, an accepted production language or a
proof of soundness. The [EBNF](grammar.ebnf) specifies syntax; this file records
lexing and meaning decisions separately. The compact split follows Sovel's
specification discipline without copying its language or compiler design.

## Why EBNF is only one part

EBNF is Extended Backus-Naur Form. It describes how tokens combine. A language
also needs tokenization, name/type rules, evaluation meaning and an assurance
argument. A parse tree alone does not establish that a claim is grounded or a
proof is valid.

The current sketch has one named review, one explicit context/snapshot, a pinned
profile, a prospective target, evidence bindings, requirements, hypotheses and
checks. These are Weft source constructs, not new Writfold method names.

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
- Maximal munch distinguishes `==` and `!=` from `=`. There is no standalone `!`.
  A keyword must end at an identifier boundary: `android` is one identifier.

Keywords: `review`, `context`, `at`, `profile`, `target`, `proposal`, `claim`,
`asset`, `rule`, `citation`, `need`, `assume`, `check`, `by`, `and`, `or`, `not`,
`true`, `false`.

### Precedence and ambiguity decisions

From tightest to loosest: field selection/calls; equality or inequality; `not`;
`and`; `or`. Thus `not a.order == b.order` means `not (a.order == b.order)`.
Boolean connective chains associate left; recursive `not` nests right.

1. Comparisons do not chain: `a == b == c` is rejected. No implicit coercion
   between numbers, strings, identities or units.
2. Parentheses group propositions; call arguments are values, not arbitrary
   effectful expressions. Function return values cannot be nested as arguments
   in this small sketch.
3. `asset x = citation "..."` binds evidence, not its semantic truth. `x.field`
   requires a profile-defined typed interpretation of those exact bytes.
4. Scope/profile/target headers occur once, in that order. Snapshot strings are
   opaque references; resolution must return full exact bindings. No ambient
   latest release or context is used as an invisible default.
5. A trailing semicolon is required for declarations/checks; a trailing comma in
   argument/rule lists is not accepted. A source file contains one review.
6. Quantifiers, recursion, arithmetic, imports, arbitrary functions, shell code,
   mutation, automatic admission and implicit refresh are absent. Bounded
   quantification needs an explicit finite-domain/completeness contract first.

## Static meaning proposal

Resolve declarations in source order. Each target, evidence binding, hypothesis
and check label has one unique name in its review; no shadowing or forward
references. Predicate names come from a separate profile namespace, not from
arbitrary host functions. Field paths and calls must type-check against the
pinned profile; unknown names, unsupported predicates and unit mismatches fail
before evaluation where possible.

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
- `need x` makes x a required grounding dependency even if no expression mentions
  it. Every binding is resolved/assessed and listed, but unused optional bindings
  do not silently become proof premises. Used bindings add dependencies without
  requiring a redundant `need` declaration. `need` may name a target, evidence
  binding or hypothesis, not a check result; a required hypothesis must be
  discharged for strict grounding.
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

Symbolic predicates require a separate finite theory profile. The illustrative
conditional example describes one such rule, not a selected solver or universal
inference engine. The profile must specify premise import, contradiction handling,
consistency checks, resource bounds and proof/model checking before execution.
Unsupported profiles refuse; exhausting a budget does not establish a negative.

Writfold's support states are not the truth values of these connectives. A checked
bridge is required before importing a Writfold formula into this local theory.
Maintain all inherited hypotheses and the exact dependency closure. No theorem
here authorizes effects or promotes a report into the knowledge base.

## Formation and assurance map

| Syntax family | Formation/evaluation obligation | Current status |
| --- | --- | --- |
| Review/header | Exact authorized scope, profile and subject; no ambient context | Proposed, unimplemented |
| Evidence binding | Kind-safe resolution; full durable binding; assessment preservation | Proposed; shared service mapping unresolved |
| Field/comparison | Registered interpretation, selectors/units, total typed operation | Proposed finite first example |
| Predicate/rule use | Signature, premise bridge, sound rule application, dependency/assumption closure | Unqualified proposal; theory/backend unresolved |
| `need` | Preserve explicit required dependency even when expression-unused | Proposed, unimplemented |
| `assume` | Conditional environment; no conversion into observed/admitted truth | Proposed, unimplemented |
| `check`/connectives | Honest outcomes; failed acquisition is not false; no authority | Proposed, unimplemented |

No grammar family gets a default "safe" case. A future implementation must either
supply the specified meaning and its assurance evidence or explicitly reject the
form. The exploratory grammar smoke only recognizes example syntax; it does not
qualify these semantics.
