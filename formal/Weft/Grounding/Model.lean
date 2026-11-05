import Weft.Logic

namespace Weft.Grounding

open Weft.Logic

/-! L08–L10: an abstract, exact-binding evidence boundary. These nominal tokens
are supplied by an authorized resolver; this module does not implement Writfold
identity validation. Assessment truth and EvidenceSound are environmental inputs,
not consequences of citation spelling, content hashes, or propositional checking.
-/

structure Scope where
  realm : Nat
  subject : Nat
  context : Nat
  revision : Nat
  profile : Nat
  release : Nat
  deriving DecidableEq, Repr

structure Binding where
  scope : Scope
  kind : Nat
  identity : Nat
  sourceRevision : Nat
  representation : Nat
  selector : Nat
  deriving DecidableEq, Repr

inductive Support | none | positive | negative | both
  deriving DecidableEq, Repr
inductive Freshness | current | stale | unknown
  deriving DecidableEq, Repr
inductive Applicability | applicable | inapplicable | unknown
  deriving DecidableEq, Repr
inductive Validation | valid | invalid | unknown
  deriving DecidableEq, Repr
inductive Availability | available | unavailable | unknown
  deriving DecidableEq, Repr
inductive Contestation | clear | contested | unknown
  deriving DecidableEq, Repr
inductive Admission | admitted | unadmitted | unknown
  deriving DecidableEq, Repr

structure Assessment where
  support : Support
  freshness : Freshness
  applicability : Applicability
  validation : Validation
  availability : Availability
  contestation : Contestation
  admission : Admission
  deriving DecidableEq, Repr

/-- Independent dimensions: support alone never licenses an input. -/
def AssessmentEligible (a : Assessment) : Prop :=
  a.support = .positive ∧ a.freshness = .current ∧
  a.applicability = .applicable ∧ a.validation = .valid ∧
  a.availability = .available ∧ a.contestation = .clear ∧
  a.admission = .admitted

instance (a : Assessment) : Decidable (AssessmentEligible a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Hypotheses are structurally distinct from observations and qualified rules.
A hypothesis cannot be discharged by changing its display label. A new resolved,
assessed observation must be supplied instead. Rule qualification is an imported
judgment about the exact pinned binding, not permission to execute code. -/
inductive Origin where
  | observation (assessment : Assessment)
  | rule (assessment : Assessment) (qualified : Bool)
  | hypothesis (localIdentity : Nat)
  deriving DecidableEq, Repr

def EligibleOrigin : Origin → Prop
  | .observation a => AssessmentEligible a
  | .rule a qualified => AssessmentEligible a ∧ qualified = true
  | .hypothesis _ => False

instance (o : Origin) : Decidable (EligibleOrigin o) := by
  cases o <;> unfold EligibleOrigin <;> infer_instance

def IsHypothesis : Origin → Prop
  | .hypothesis _ => True
  | _ => False

structure Input where
  binding : Binding
  proposition : Formula
  dependencies : List Binding
  origin : Origin
  deriving DecidableEq, Repr

def EligibleInput (scope : Scope) (input : Input) : Prop :=
  input.binding.scope = scope ∧ EligibleOrigin input.origin

instance (s : Scope) (i : Input) : Decidable (EligibleInput s i) :=
  inferInstanceAs (Decidable (_ ∧ _))

structure Review where
  scope : Scope
  atomCount : Nat
  query : Formula
  explicitNeeds : List Binding
  usedInputs : List Binding
  captured : List Input
  budget : Nat
  deriving DecidableEq, Repr

/-- All premises retain their origins in captured; no anonymous logical premise
is admitted through a separate list. Conservative used inputs include hypotheses
and qualified rules even if Boolean simplification would erase their occurrence. -/
def premises (r : Review) : List Formula := r.captured.map Input.proposition

def required (r : Review) : List Binding := r.explicitNeeds ++ r.usedInputs

/-- L08. Needs survive even a constant query and an empty used-input list. -/
theorem explicitNeedsPreserved (r : Review) (b : Binding)
    (h : b ∈ r.explicitNeeds) : b ∈ required r := by
  exact List.mem_append.mpr (Or.inl h)

def Captured (r : Review) (b : Binding) : Prop :=
  ∃ input ∈ r.captured, input.binding = b

instance (r : Review) (b : Binding) : Decidable (Captured r b) := by
  unfold Captured
  infer_instance

/-- Required closure is a semantic reachability relation, not a checker result. -/
inductive Required (r : Review) : Binding → Prop
  | root {b} : b ∈ required r → Required r b
  | dependency {input b} : Required r input.binding →
      input ∈ r.captured → b ∈ input.dependencies → Required r b

/-- Captured inputs must contain every declared edge, including edges of captured
inputs not syntactically needed by the final Boolean expression. This is a
conservative closure, not a minimal-dependency claim. -/
def ClosureCaptured (r : Review) : Prop :=
  (∀ b ∈ required r, Captured r b) ∧
  (∀ input ∈ r.captured, ∀ b ∈ input.dependencies, Captured r b)

instance (r : Review) : Decidable (ClosureCaptured r) := by
  unfold ClosureCaptured
  infer_instance

theorem requiredCaptured (r : Review) (closed : ClosureCaptured r)
    {b : Binding} (h : Required r b) : Captured r b := by
  induction h with
  | root h => exact closed.1 _ h
  | dependency _ member edge _ => exact closed.2 _ member _ edge

def GroundingChecks (r : Review) : Prop :=
  classify r.atomCount (premises r) r.query r.budget = .entailed ∧
  ClosureCaptured r ∧ (∀ input ∈ r.captured, EligibleInput r.scope input)

instance (r : Review) : Decidable (GroundingChecks r) := by
  unfold GroundingChecks
  infer_instance

def checkGrounding (r : Review) : Bool := decide (GroundingChecks r)

/-- This assumption is about the real-world interpretation, independently of the
finite checker: eligible imported observations/rules must actually hold. Its
justification belongs to the evidence producer and authorized acquisition path. -/
def EvidenceSound (r : Review) (world : Nat → Bool) : Prop :=
  ∀ input ∈ r.captured, EligibleOrigin input.origin →
    evaluate world input.proposition = true

/-- Denotational success: nonempty models, semantic entailment, exact-scope
eligible closure, no required hypotheses, and truth in the supplied world. -/
structure GroundedMeaning (r : Review) (world : Nat → Bool) : Prop where
  consistent : ∃ valuation, PremisesHold (premises r) valuation
  entails : ∀ valuation, PremisesHold (premises r) valuation →
    evaluate valuation r.query = true
  eligibleClosure : ∀ b, Required r b →
    ∃ input ∈ r.captured, input.binding = b ∧ EligibleInput r.scope input
  noRequiredHypothesis : ∀ input ∈ r.captured,
    Required r input.binding → ¬ IsHypothesis input.origin
  worldTruth : evaluate world r.query = true

theorem eligibleNotHypothesis (o : Origin) (h : EligibleOrigin o) :
    ¬ IsHypothesis o := by
  cases o <;> simp_all [EligibleOrigin, IsHypothesis]

/-- L09. The world-truth conclusion is conditional on EvidenceSound; eligibility
alone is not a proof that an external observation is true. Logical consistency and
entailment come from the independently proved finite semantic classification. -/
theorem groundedSound (r : Review) (world : Nat → Bool)
    (checked : checkGrounding r = true) (evidence : EvidenceSound r world) :
    GroundedMeaning r world := by
  have checks : GroundingChecks r := of_decide_eq_true checked
  rcases checks with ⟨logical, closed, eligible⟩
  have meaning := classificationSound r.atomCount (premises r) r.query r.budget
  rw [logical] at meaning
  rcases meaning with ⟨_scoped, consistent, entails⟩
  have worldPremises : PremisesHold (premises r) world := by
    intro f hf
    obtain ⟨input, member, equality⟩ := List.mem_map.mp hf
    subst f
    exact evidence input member (eligible input member).2
  refine ⟨consistent, entails, ?_, ?_, entails world worldPremises⟩
  · intro b requiredBinding
    obtain ⟨input, member, equality⟩ := requiredCaptured r closed requiredBinding
    exact ⟨input, member, equality, eligible input member⟩
  · intro input member _required
    exact eligibleNotHypothesis input.origin (eligible input member).2

/-- Rerun reuse binds every semantic input, including the exact search budget.
Historical replay displays the old request and outcome; it does not assert that a
different-budget execution completed. New acquisition requires a fresh decision. -/
structure ReuseKey where
  scope : Scope
  atomCount : Nat
  query : Formula
  needs : List Binding
  used : List Binding
  captured : List Input
  budget : Nat
  deriving DecidableEq, Repr

def reuseKey (r : Review) : ReuseKey :=
  ⟨r.scope, r.atomCount, r.query, r.explicitNeeds, r.usedInputs, r.captured, r.budget⟩

def checkReuse (old fresh : Review) : Bool := decide (reuseKey old = reuseKey fresh)

/-- L10. Exact abstract identity includes subject, context, revision, and profile,
as well as complete assessed bindings/dependencies/origins and the proposition. -/
theorem reuseSound (old fresh : Review) (h : checkReuse old fresh = true) :
    old.scope = fresh.scope ∧ old.scope.subject = fresh.scope.subject ∧
    old.scope.context = fresh.scope.context ∧ old.scope.revision = fresh.scope.revision ∧
    old.scope.profile = fresh.scope.profile ∧ old.captured = fresh.captured ∧
    old.explicitNeeds = fresh.explicitNeeds ∧ old.usedInputs = fresh.usedInputs ∧
    old.query = fresh.query := by
  have key : reuseKey old = reuseKey fresh := of_decide_eq_true h
  have scope : old.scope = fresh.scope := congrArg ReuseKey.scope key
  exact ⟨scope, congrArg Scope.subject scope, congrArg Scope.context scope,
    congrArg Scope.revision scope, congrArg Scope.profile scope,
    congrArg ReuseKey.captured key, congrArg ReuseKey.needs key,
    congrArg ReuseKey.used key, congrArg ReuseKey.query key⟩

/-- Exact rerun keys preserve the request itself, not only its identity fields. -/
theorem reuseReviewEqual (old fresh : Review) (h : checkReuse old fresh = true) :
    old = fresh := by
  have key : reuseKey old = reuseKey fresh := of_decide_eq_true h
  cases old
  cases fresh
  cases key
  rfl

/-- A completed verdict cannot be carried into an exhausted rerun. -/
theorem reuseOutcomeSound (old fresh : Review) (h : checkReuse old fresh = true) :
    classify old.atomCount (premises old) old.query old.budget =
      classify fresh.atomCount (premises fresh) fresh.query fresh.budget ∧
    checkGrounding old = checkGrounding fresh ∧ old.budget = fresh.budget := by
  have equal := reuseReviewEqual old fresh h
  subst fresh
  exact ⟨rfl, rfl, rfl⟩

end Weft.Grounding
