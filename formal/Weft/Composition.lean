import Weft.Language
import Weft.Grounding

namespace Weft.Composition

/-- The actual surface elaboration, finite checker and grounding judgment compose.
World truth remains conditional on an accurate external interpretation and
EvidenceSound. This is not a raw-byte parser or shipping-Rust refinement theorem. -/
theorem reviewSound
    (env : Language.Environment) (profile : Language.Profile)
    (intern : Language.GroundCall → Option Nat)
    (meaning : Language.GroundCall → Bool) (world : Nat → Bool)
    (interpretation : Language.Interpretation intern meaning world)
    (surface : Language.Surface) (review : Grounding.Review)
    (elaborated : Language.elaborate env profile intern surface = some review.query)
    (grounded : Grounding.checkGrounding review = true)
    (evidence : Grounding.EvidenceSound review world) :
    Language.denote env profile meaning surface = some true ∧
    Grounding.GroundedMeaning review world := by
  have result := Grounding.groundedSound review world grounded evidence
  refine ⟨?_, result⟩
  calc
    Language.denote env profile meaning surface =
        some (Logic.evaluate world review.query) :=
      Language.elaborationSound env profile intern meaning world interpretation
        surface review.query elaborated
    _ = some true := congrArg some result.worldTruth


/-- Strengthened source meaning is relational and independent of the operational
comparison/call helpers used by elaboration. -/
theorem reviewSemanticSound
    (env : Language.Environment) (profile : Language.Profile)
    (intern : Language.GroundCall → Option Nat)
    (meaning : Language.GroundCall → Bool) (world : Nat → Bool)
    (interpretation : Language.Interpretation intern meaning world)
    (surface : Language.Surface) (review : Grounding.Review)
    (elaborated : Language.elaborate env profile intern surface = some review.query)
    (grounded : Grounding.checkGrounding review = true)
    (evidence : Grounding.EvidenceSound review world) :
    Language.SurfaceMeaning env profile meaning surface true ∧
    Grounding.GroundedMeaning review world := by
  have result := Grounding.groundedSound review world grounded evidence
  have semantic := Language.elaborationSemanticSound env profile intern meaning world
    interpretation surface review.query elaborated
  rw [result.worldTruth] at semantic
  exact ⟨semantic, result⟩

/-- A grounded violation has equally explicit source meaning. Eligible evidence
does not make the proposed obligation true; completed refutation establishes false. -/
theorem reviewRefutationSound
    (env : Language.Environment) (profile : Language.Profile)
    (intern : Language.GroundCall → Option Nat)
    (meaning : Language.GroundCall → Bool) (world : Nat → Bool)
    (interpretation : Language.Interpretation intern meaning world)
    (surface : Language.Surface) (review : Grounding.Review)
    (elaborated : Language.elaborate env profile intern surface = some review.query)
    (refuted : Logic.classify review.atomCount (Grounding.premises review)
      review.query review.budget = .refuted)
    (basis : Grounding.evidenceBasis review = .grounded)
    (evidence : Grounding.EvidenceSound review world) :
    Language.SurfaceMeaning env profile meaning surface false ∧
    (∃ valuation, Logic.PremisesHold (Grounding.premises review) valuation) ∧
    Grounding.ClosureCaptured review := by
  have eligible := (Grounding.groundedBasisExactly review).mp basis
  have worldPremises : Logic.PremisesHold (Grounding.premises review) world := by
    intro formula member
    obtain ⟨input, present, equality⟩ := List.mem_map.mp member
    subst formula
    exact evidence input present (eligible.2 input present).2
  have result := Logic.classificationSound review.atomCount
    (Grounding.premises review) review.query review.budget
  rw [refuted] at result
  obtain ⟨_inScope, consistent, negative⟩ := result
  have semantic := Language.elaborationSemanticSound env profile intern meaning world
    interpretation surface review.query elaborated
  rw [negative world worldPremises] at semantic
  exact ⟨semantic, consistent, eligible.1⟩

namespace Examples

open Language

/-- This single ground call denotes the consequence B of the grounded A -> B rule. -/
def jointIntern (call : GroundCall) : Option Nat :=
  if call = Language.Examples.acceptedCall then some 1 else none

theorem jointCaptured (call : GroundCall) (index : Nat)
    (captured : jointIntern call = some index) :
    call = Language.Examples.acceptedCall := by
  by_cases same : call = Language.Examples.acceptedCall
  · exact same
  · simp [jointIntern, same] at captured

theorem jointInterpretation :
    Interpretation jointIntern Language.Examples.meaning Grounding.Examples.world := by
  constructor
  · intro a b index ha hb
    exact (jointCaptured a index ha).trans (jointCaptured b index hb).symm
  · intro call index captured
    have same := jointCaptured call index captured
    subst call
    rfl

def jointSurface : Surface :=
  .predicate Language.Examples.accepted [.field Language.Examples.countPath]

/-- All composed premises are jointly inhabited by one field interpretation,
one world, an eligible observation A and an eligible rule A -> B. -/
theorem jointPremisesInhabited :
    SurfaceMeaning Language.Examples.env Language.Examples.profile
      Language.Examples.meaning jointSurface true ∧
    Grounding.GroundedMeaning Grounding.Examples.positiveReview Grounding.Examples.world :=
  reviewSemanticSound Language.Examples.env Language.Examples.profile jointIntern
    Language.Examples.meaning Grounding.Examples.world jointInterpretation
    jointSurface Grounding.Examples.positiveReview (by decide)
    Grounding.Examples.positiveAccepted Grounding.Examples.positiveEvidenceSound

def jointNegativeReview : Grounding.Review :=
  { Grounding.Examples.positiveReview with query := .neg (.atom 1) }

theorem jointRefutationInhabited :
    SurfaceMeaning Language.Examples.env Language.Examples.profile
      Language.Examples.meaning (.neg jointSurface) false ∧
    (∃ valuation, Logic.PremisesHold (Grounding.premises jointNegativeReview) valuation) ∧
    Grounding.ClosureCaptured jointNegativeReview :=
  reviewRefutationSound Language.Examples.env Language.Examples.profile jointIntern
    Language.Examples.meaning Grounding.Examples.world jointInterpretation
    (.neg jointSurface) jointNegativeReview (by decide) (by decide) (by decide)
    Grounding.Examples.positiveEvidenceSound

end Examples

end Weft.Composition
