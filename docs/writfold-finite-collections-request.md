# Proposal-only finite collection request for Writfold

This extends WR4/WR5 in the revision-1 handoff. It requests ordinary shared agent
services, not a Weft-only collection endpoint, opcode, graph writer or policy change.
No Writfold source is modified by this repository.

Weft now has a selected finite-set surface (`S := {c1, c2, ...T}`) and bounded
quantifiers. To ground those reviews, the owning agent should expose a captured
finite collection contract with:

- A pinned context/release/read cut, query and interpretation profile, intended
  collection/domain identity, inventory/watermark closure where applicable.
- Exact typed member bindings in Writfold's own durable identity representation.
  Preserve realm/kind/revision/representation/selector distinctions; compact handles
  must expand under their original session/generation and current access checks.
- Element type, deterministic member ordering, materialization completeness,
  measured coverage and omissions. Unknown/unavailable enumeration is not zero.
- Independent provenance/assessment for every relevant member and dependency,
  including contrary/stale/ambiguous evidence. Duplicate values do not erase a
  failed reference or an independent required assessment.
- Explicit acquisition/resource bounds and typed denied/expired/unavailable/
  unsupported/partial outcomes. Never silently switch a paginated cut to HEAD.
- Permission-aware disclosure of member identities, counts, names and omissions.
  "Complete" means the qualified authorized domain, not secret global inventory.

A top-k discovery result is a finite candidate set, but is not an exhaustive
universe. The owner should retain that distinction in the returned type/profile.
A plan obligation such as "every affected asset" needs the actual authoritative
plan/inventory domain, not an arbitrary literal subset supplied by the agent.

If existing retained artifacts already carry this information, expose their exact
shared typed reader contract rather than create a parallel service. Source-level
method names and serialization are for the Writfold owner to settle and qualify;
Weft will consume the landed version/pin unchanged.

Required qualification includes duplicate aliases, cross-realm same-spelled IDs,
expired handles, partial/empty discovery, stale member validation, read-cut changes,
unauthorized count disclosure and collection/subject mismatches. Existing storage,
authority, native-read and publication prerequisites remain in force.
