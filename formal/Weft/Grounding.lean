import Weft.Grounding.Model
import Weft.Grounding.Trace
import Weft.Grounding.Examples
import Weft.Grounding.ReportView
import Weft.Grounding.DetailedTrace
import Weft.Grounding.ReportExamples

/-!
P01 grounding/report boundary, Lean 4.21 core only.

Registry/source map (all declarations in namespace Weft.Grounding):
* L08 explicitNeedsPreserved — Grounding/Model.lean, required-list inclusion.
* L09 groundedSound — Grounding/Model.lean, independent GroundedMeaning under
  explicit EvidenceSound; classificationSound supplies consistency/entailment.
* L10 reuseSound — Grounding/Model.lean, exact scope and full assessed input key.
* L11 traceFaithful — Grounding/Trace.lean, complete canonical report projection,
  backward local links and acyclicity; no authority strengthening or omissions.
* L12 analysisNonAuthority — Grounding/Trace.lean, pure analysis transition leaves
  owner state intact and returns no execution permission.

Additional report contracts (the registered L08–L12 meanings are unchanged):
* reuseOutcomeSound binds exact budgets for reruns; historical replay is the old
  request, never a claim that a reduced-budget rerun completed.
* groundedBasisExactly separates eligible captured closure from logical success;
  invalidDomainIsFailure/exhaustionIsUnknown keep failure distinct from exhaustion.
* reportViewFaithful preserves all independent axes and forbids effect authority.
* detailedTraceFaithful binds annotations to successful Language elaboration of
  Review.query, preserves coverage, and proves independent typed term/comparison
  meanings. fieldDetailFacts and comparisonDetailFacts expose actual lookup and
  comparison facts. Ground-rule provenance is not variable-rule instantiation.
Grounding/ReportExamples.lean supplies positive/refuted grounded-basis reports,
unresolved/hypothetical/unusable cases, changed-budget rejection, accepted rich
explanations, and rejected forged annotations and omitted elaboration detail.

Grounding/Examples.lean supplies inhabited positive semantic premises and negative
calibrations: unused required needs, hypothesis laundering, stale/contested/unknown
assessments, incomplete transitive closure, unqualified rules, same-id cross-context
reuse, subject/revision/profile mismatches, dangling/cyclic/forged traces and
unauthorized or content-stripping projections. Its opening comment gives mutation
targets. Kernel-checked status is recorded by the integrated build, not this text.

Environment assumptions and limits:
* Exact nominal Scope/Binding values are supplied by an authorized resolver.
  These abstract records are not invented Writfold identifiers or validators.
* Assessments, qualification, dependency declarations, current scope and applicable
  time/profile are accurate imported judgments. Closure completeness here is
  relative to those declared edges; undisclosed producer dependencies are outside
  the model. Eligibility is stricter than positive support alone.
* EvidenceSound is needed for world truth, not for finite logical entailment.
  No theorem turns a hypothesis, citation, hash or passed assessment into truth.
* Reuse applies to identical captured assessments and exact execution budget.
  Fresh acquisition/expiry must update those inputs; this pure model does not
  discover wall-clock changes.
* Core trace nodes expose inputs and exhaustive-check accounting, not private
  reasoning. A separate checked elaboration subtrace accepts complete rich typed
  details in any order (and duplicate honest notes), without asserting source spans.
  Resolved field environments and profile interpretations are explicit inputs;
  their correspondence to external bytes/world facts is not established here.
* Non-authority concerns this transition system only. No IO sandbox, owner API,
  raw lexer, Rust evaluator or external resolver refinement is proved here.
-/
