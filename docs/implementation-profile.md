# Local symbolic development profile

The full release contract is the revision-1 handover with the revision-2 finite
language supplement, including real Writfold integration. This file selects the
storage-independent development behavior; it is not an alternative grounding or
admission route.

## Commands and scope

- `weft analyze FILE [--json|--human]`: parse the complete review syntax and check
  declarations, names, kinds and locally decidable types; report exact binding/profile requirements.
  External references stay unresolved. Success means local structural analysis,
  not proof, grounding, admission or permission.
- `weft prove FILE [--json|--human]`: for the explicit local profile `weft.symbolic/1`, elaborate
  literal comparisons and typed ground symbolic predicates, retain explicit
  assumptions and classify each check with the proved finite semantics. Preserve
  all requested bindings and needs. No result is marked Writfold-grounded.
- `weft --version`: identify the actual development artifact/profile.

JSON is the default. `--` ends option parsing; help is available as `--help`/`-h`.
Local analysis exits 0 on complete structural success. A complete hypothetical
proof outcome exits 1, including refuted/undetermined/inconsistent outcomes.
Malformed, unresolved or resource-incomplete paths exit 2. There is no local
grounded-success exit.

Other profile names require the owner-landed Writfold profile/assessment contract.
Unknown profiles, unresolved fields and `by` rules whose qualified definition is
unavailable produce precise unresolved-input diagnostics, not invented values or
an unchecked rule application. Do not add a fake live `check`, `admit` or `run`
command while those contracts are unavailable.

## `weft.symbolic/1`

A predicate name denotes an **uninterpreted proposition parameterized by typed
ground literal arguments**, not a host function or an assertion about the world.
The first occurrence determines a local signature; subsequent occurrences must
have identical arity and argument kinds. Atom identity is the exact predicate
name plus its typed argument values. The signature table is hypothetical local
syntax, never an admitted Writfold interpretation profile.

Literal Boolean, arbitrary-precision natural and text arguments are supported.
External field values require real capture and therefore cannot be synthesized
by this profile. There is no natural-language inference or implicit extraction of
facts from citations. Names such as `safe` have no privileged semantics.

`assume h: P` adds P only to subsequent checks. A check does not become a premise
for the next check. Each query includes the full current hypothesis list and its
source spans; no attempt to claim a minimal used subset. Rules may be explored as
explicit hypothetical propositions, such as `not A or B`, never as qualified
knowledge merely because they have a convenient name.

Even a logical tautology remains a local theory result, not a successful grounded
review of a prospective plan. Empty captured knowledge cannot stand in for a
resolved context. Every required unavailable binding is listed independently of
the Boolean result.

## Finite sets and lexical quantification

The local profile includes immutable `name := { ... };` bindings, typed scalar
sets, spread, extensional equality and bounded `forall`/`exists`. It does not add
general loops, mutation, recursive functions or effects. Quantifier domains see
the outer environment; bodies see the newly bound member. Nested binders may
shadow names, but top-level declarations cannot rebind them.

Check the complete body before expansion, including bodies over empty sets.
Unification may infer an empty set's element type from a spread or comparison;
where the type is irrelevant, retain a parametric empty set instead of silently
choosing a concrete type. An unresolved type needed by a predicate signature or
field selection is a diagnostic.
Deferred type variables may be constrained by a later consistent predicate use;
unresolved required types are diagnosed at the original occurrence. The admitted
parser/AST depth is at most 64; implementation/resource details are in
[the Rust boundary record](rust-implementation.md).

Reports retain every materialized member and its source origins before
deduplication, normalized membership, each instantiated body and the exact
valuation supporting a witness or counterexample. Empty universals explicitly
say they are vacuous. An entailed existential need not have a single member
whose instance is entailed; never promote a model-relative witness into one.

Local finite membership is not a claim of complete KB discovery. The future
Writfold finite-domain manifest and coverage assessment remain owner prerequisites.

## Report content

The concrete `weft.report/1` envelope distinguishes `analysis`, `assessment` and
`diagnostics`. All local outputs say `scope: local-symbolic` or `local-analysis`
and `writfold_grounded: false`, `effect_authority: false`.

Reports bind exact source SHA256/length, requested context/snapshot/profile/target,
local name IDs and source spans. Per-check data includes logical outcome,
conservative hypotheses/needs/dependencies, atom definitions, required/checked
valuation counts, positive/negative model witnesses, full evaluation accounting,
and deterministic explanations. Semantic trace nodes refer to prior local nodes;
no invented durable external binding or authenticated receipt is emitted.

Execution and report budgets are explicit. If a complete trace cannot be emitted
within the selected budget, return an explicit incomplete outcome; no truncated
trace may claim complete reusable evidence. Machine diagnostics carry stable code,
phase, primary/secondary spans, expected/actual details and a repair suggestion.

Ordinary semantic failures retain safe earlier checks and block later checks
whose premises failed. Exhaustion that prevents complete metadata construction
returns diagnostics, not an incomplete assessment disguised as complete.
The report includes a separate source-origin DAG and model-relative instance
links. A library caller must supply the actual trusted frontend/kernel records;
the output projector is not an untrusted certificate-verification endpoint.

This profile makes compiler/proof/report behavior executable before the owning
Writfold agent supplies WR1-WR8. It does not close P05-P07 or the final release gate.
