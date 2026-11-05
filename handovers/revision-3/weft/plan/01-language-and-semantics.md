# Selected syntax and semantics

This contract extends the inherited finite language; it does not introduce a
second collection representation or a general expression/effect language. The
syntax below is the implementation target, not supported behavior at handover time.

## Surface contract

| Form | Operand/result contract |
| --- | --- |
| `a | b` | Union of two same-element-type finite sets; set result. |
| `a & b` | Intersection of two same-element-type finite sets; set result. |
| `a - b` | Members of `a` absent from `b`; same-element-type set result. |
| `x in a` | Scalar/reference `x` and a compatible finite set; proposition. |
| `a <= b` | Every member of `a` is in `b`, including equality; proposition. |

`==`/`!=` retain exact typed scalar or extensional set equality. `<=` is set-only,
not integer ordering; `|`/`&` are not Boolean or integer operators. `-` does not add
signed literals or arithmetic. Keep Boolean `not`, `and`, `or` unchanged. No aliases,
implicit singleton conversion, implicit coercions or chained comparisons.

Precedence, tightest first: field selection; set atoms/parenthesized set expressions;
`&`; `|` and `-` at equal precedence; `==`, `!=`, `in`, `<=` at equal non-chaining
comparison precedence; `not`; `and`; `or`. Binary set operators associate left.
Thus `a | b & c` means `a | (b & c)`, `a | b - c` means `(a | b) - c`, and
`not x in a` means `not (x in a)`. Reject `x in a <= b` and `a <= b == c`.
Existing proposition parentheses continue to work; `(a | b) == c` is also valid.

Accept set expressions everywhere the inherited grammar accepts a set: immutable
binding RHS, spread operand, quantifier domain, and set comparisons. Parentheses
must compose across those contexts, including `forall x in (a - b) { x in a }`
and `{...(a | b), "extra"}`. A spread consumes its set expression to the enclosing
item delimiter; parentheses make mixed expressions explicit. Membership/subset
are usable inside `assume`, `check`, Boolean combinations and quantified bodies.
Do not admit set-valued predicate arguments or nested sets.

Update the EBNF, lexical/maximal-munch rules and source-span behavior together.
Recognize `<=` as one token; bare `<`, `>`, `>=`, `+`, `^`, `~`, `&&`, `||` and
Unicode set-operator aliases remain unsupported. `in` already serves quantifier
syntax; parse both roles without changing lexical scope or keyword boundaries.
Use bounded parsing; do not resolve parentheses by unbounded speculative parsing.

## Values, types and order

Use existing exact scalar/nominal identity, including nominal kind and realm.
Determine compatible operand types before filtering. A zero-member result retains
its inferred element type; intersection/difference must not erase a type mismatch.
For example, a text-typed empty result cannot later silently unify with naturals.

Propagate contextual element types through the complete operator tree, spreads,
comparisons and binders. Preserve parametric empties where the type is irrelevant:
`{} <= {}` and `{} == {}` are true, while `"x" in {}` is false with text context.
An unresolved type required by a predicate or field remains a diagnostic; never
choose a default type to make a case pass. Validate quantified bodies even when
an algebraic domain is empty.

Membership is extensional and duplicate-free; display order is deterministic:

- Union: left members in their first-occurrence order, then unseen right members
  in right order. This agrees with `{...a, ...b}` on membership and display order.
- Intersection/difference: retain qualifying left members in left order.
- Membership/subset: exact typed membership, not truth of a predicate about a
  member. A false subset has a concrete left member absent from the right; retain
  a deterministic first-left counterexample in its explanation.

Algebraic laws concern membership, not identical source traces or origin-DAG bytes.
Union/intersection commute extensionally, but swapping operands can change display
order and source provenance. Do not sort or canonicalize away those distinctions.

Keep the existing meaning of `raw_occurrences`: members supplied to this result's
normalization, not total transitive source occurrences or computational work.
Union supplies both normalized operand lists, so its count is their cardinality
sum before cross-operand deduplication. Intersection supplies each qualifying left
member once, merging matching right origins; difference supplies each surviving
left member once. Their normalization input counts therefore equal result
cardinality. These counts do not measure inspected/removed inputs: retain both
operand records and charge their complete traversal separately, even for zero
output. A derived set has a fresh local materialization observation; do not
mislabel it as an imported payload or synthesize imported-source history.

## Complete operand closure

A successful result requires both operands completely materialized and typed.
For membership this includes the scalar value and the whole RHS set; for subset
it includes both whole sets. An implementation may terminate with an explicit
failure, but must never produce success from a skipped/incomplete operand.

Keep two concepts distinct: origins for surviving member identities, and the
complete operation-level dependency closure needed to compute the result.

- Union merges origins for identities present in either operand; intersection
  retains the contributing origins for retained identities from both operands.
- Difference keeps surviving left-member origins; it still retains the entire
  right operand's materialization and dependency closure at operation level.
- Eliminated members and their origins stay reachable as operand evidence, not
  falsely relabelled as origins of an unrelated surviving member.
- `a - a`, `{} & a`, `a & {}`, `{} <= a`, and an already-true membership probe
  do not license dropping required reads, unknown inputs or failed materialization.
- Explicit `need` on an empty computed binding still requires its full captured
  closure. Repeated/diamond expressions share origin nodes rather than copy an
  exponentially expanding history.

Do not simplify `a - a` to a fresh provenance-free empty literal or short-circuit
an operation before validating its operands. Missing/expired/denied/partial external
inputs remain failures or gaps under the inherited profile, never non-membership.
This requirement does not authorize implementing or simulating Writfold services.

All source traversal, member comparisons, normalization, provenance nodes and
report expansion must be bounded by admitted limits. Budget exhaustion is explicit
incomplete work: no partial set binding, Boolean comparison or completed quantified
verdict. Specify the cost accounting before proving its budget laws.

## Reports and epistemic boundary

Retain source spans for operators/operands, typed result membership and stable
order, operand identities, complete origin/dependency links, and comparison truth
or refusal. Empty results must still explain which exact operands produced them.
A membership or subset explanation must be tied to those finite operands; a subset
counterexample is not a symbolic model-relative quantifier witness. Existing
quantifier traces still carry hygienic substitutions, coverage, vacuity and
valuation-scoped witnesses/counterexamples.

Extend the existing shared records/wire projection only as needed for these facts;
do not recompute set operations in the reporter or create an alternate provenance
system. Keep JSON and human output aligned and update `spec/report-v1.md` if its
contract changes. Preserve the source/profile/report identity and existing exit
categories.

Absence is relative to the exact supplied finite sets. Difference, membership
failure, subset success or an empty domain do not prove complete real-world
inventory discovery. Every local report retains `writfold_grounded: false` and
`effect_authority: false`; assumptions stay hypothetical and do not become admitted
knowledge. Complement is out of scope: use an explicit `universe - selected`.
