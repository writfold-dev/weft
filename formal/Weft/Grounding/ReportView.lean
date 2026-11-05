import Weft.Grounding.Trace

namespace Weft.Grounding

open Weft.Logic

/-! Mathematical report axes, not a JSON/span or owner-identity implementation.
Basis is computed without inspecting the query verdict. Gap flags retain overlaps;
the displayed basis prioritizes unresolved closure, then hypotheses, then unusable
inputs. Eligible evidence can ground a refutation without making a plan succeed.
Mutation anchors: invalid-domain branch; budget branch; evidenceBasis; viewAccepted;
strictSuccess. Neither rendering nor accepting these axes grants authority. -/

inductive LogicalResult where
  | entailed | refuted | undetermined | inconsistent | unknown | notEvaluated
  deriving DecidableEq, Repr

inductive ExecutionStatus where
  | complete | incomplete | failed
  deriving DecidableEq, Repr

inductive FailureReason where
  | notRequested | invalidDomain | budgetExhausted
  deriving DecidableEq, Repr

inductive Basis where
  | grounded | hypothetical | unusable | unresolved
  deriving DecidableEq, Repr

def AllEligible (r : Review) : Prop :=
  ∀ input ∈ r.captured, EligibleInput r.scope input

instance (r : Review) : Decidable (AllEligible r) := by
  unfold AllEligible
  infer_instance

def evidenceBasis (r : Review) : Basis :=
  if ClosureCaptured r then
    if AllEligible r then .grounded
    else if (hypotheses r).isEmpty then .unusable else .hypothetical
  else .unresolved

/-- This equivalence does not require any successful logical outcome. -/
theorem groundedBasisExactly (r : Review) :
    evidenceBasis r = .grounded ↔ ClosureCaptured r ∧ AllEligible r := by
  unfold evidenceBasis
  split <;> rename_i closed
  · split <;> rename_i eligible
    · simp [closed, eligible]
    · split <;> simp_all
  · simp [closed]

structure ReportView where
  logical : LogicalResult
  execution : ExecutionStatus
  failure : Option FailureReason
  basis : Basis
  closureMissing : Bool
  ineligibleInputs : Bool
  hasHypotheses : Bool
  groundedSuccess : Bool
  effectAuthority : Bool
  deriving DecidableEq, Repr

def logicalResult : Verdict → LogicalResult
  | .entailed => .entailed
  | .refuted => .refuted
  | .undetermined => .undetermined
  | .inconsistent => .inconsistent
  | .unknown => .unknown

/-- False means no evaluation was requested, not an invented unknown result. -/
def executionAxes (r : Review) (requested : Bool) :
    LogicalResult × ExecutionStatus × Option FailureReason :=
  if requested then
    if inputsInBounds r.atomCount (premises r) r.query = true then
      if r.budget < requiredBudget r.atomCount then
        (.unknown, .incomplete, some .budgetExhausted)
      else (logicalResult (outcome r), .complete, none)
    else (.notEvaluated, .failed, some .invalidDomain)
  else (.notEvaluated, .incomplete, some .notRequested)

def strictSuccess (r : Review) (requested : Bool) : Bool :=
  requested && checkGrounding r

def reportView (r : Review) (requested : Bool) : ReportView :=
  let axes := executionAxes r requested
  ⟨axes.1, axes.2.1, axes.2.2, evidenceBasis r,
    !decide (ClosureCaptured r), !decide (AllEligible r),
    !(hypotheses r).isEmpty, strictSuccess r requested, false⟩

theorem invalidDomainIsFailure (r : Review)
    (invalid : inputsInBounds r.atomCount (premises r) r.query ≠ true) :
    (reportView r true).logical = .notEvaluated ∧
    (reportView r true).execution = .failed ∧
    (reportView r true).failure = some .invalidDomain := by
  simp [reportView, executionAxes, invalid]

theorem exhaustionIsUnknown (r : Review)
    (valid : inputsInBounds r.atomCount (premises r) r.query = true)
    (exhausted : r.budget < requiredBudget r.atomCount) :
    (reportView r true).logical = .unknown ∧
    (reportView r true).execution = .incomplete ∧
    (reportView r true).failure = some .budgetExhausted := by
  simp [reportView, executionAxes, valid, exhausted]

theorem notRequestedNotEvaluated (r : Review) :
    (reportView r false).logical = .notEvaluated ∧
    (reportView r false).failure = some .notRequested ∧
    (reportView r false).groundedSuccess = false := by
  simp [reportView, executionAxes, strictSuccess]

theorem strictGroundedSuccess (r : Review) (requested : Bool)
    (success : (reportView r requested).groundedSuccess = true) :
    requested = true ∧ outcome r = .entailed ∧ evidenceBasis r = .grounded := by
  have both : requested = true ∧ checkGrounding r = true := by
    simpa only [reportView, strictSuccess, Bool.and_eq_true] using success
  have checks : GroundingChecks r := of_decide_eq_true both.2
  exact ⟨both.1, checks.1, (groundedBasisExactly r).mpr ⟨checks.2.1, checks.2.2⟩⟩

/-- Success also requires a completed execution, not just eligible evidence. -/
theorem groundedSuccessComplete (r : Review) (requested : Bool)
    (success : (reportView r requested).groundedSuccess = true) :
    (reportView r requested).execution = .complete ∧
    (reportView r requested).logical = .entailed := by
  obtain ⟨requestedTrue, logical, _basis⟩ := strictGroundedSuccess r requested success
  subst requested
  by_cases valid : inputsInBounds r.atomCount (premises r) r.query = true
  · by_cases exhausted : r.budget < requiredBudget r.atomCount
    · simp [outcome, classify, valid, exhausted] at logical
    · simp [reportView, executionAxes, valid, exhausted, logical, logicalResult]
  · simp [outcome, classify, valid] at logical

/-- Full-field validation rejects strengthening one axis using another. -/
def viewAccepted (r : Review) (requested : Bool) (candidate : ReportView) : Bool :=
  decide (candidate = reportView r requested)

theorem reportViewFaithful (r : Review) (requested : Bool) (candidate : ReportView)
    (accepted : viewAccepted r requested candidate = true) :
    candidate = reportView r requested ∧ candidate.effectAuthority = false ∧
    candidate.basis = evidenceBasis r := by
  have same : candidate = reportView r requested := of_decide_eq_true accepted
  subst candidate
  exact ⟨rfl, rfl, rfl⟩

def projectView (r : Review) (requested : Bool) (candidate : ReportView) :
    Option ReportView :=
  if viewAccepted r requested candidate then some candidate else none

theorem reportViewProjectionFaithful (r : Review) (requested : Bool)
    (candidate : ReportView)
    (projected : projectView r requested candidate = some candidate) :
    candidate = reportView r requested ∧ candidate.effectAuthority = false ∧
    candidate.basis = evidenceBasis r := by
  have accepted : viewAccepted r requested candidate = true := by
    by_cases checked : viewAccepted r requested candidate = true
    · exact checked
    · simp [projectView, checked] at projected
  exact reportViewFaithful r requested candidate accepted

/-- A pure view transition does not modify owner-side admission or grants. -/
def viewStep (state : AuthorityState) (r : Review) (requested : Bool) :
    AuthorityState × ReportView := (state, reportView r requested)

theorem reportViewNonAuthority (state : AuthorityState) (r : Review) (requested : Bool) :
    (viewStep state r requested).1 = state ∧
    (viewStep state r requested).2.effectAuthority = false := ⟨rfl, rfl⟩

end Weft.Grounding
