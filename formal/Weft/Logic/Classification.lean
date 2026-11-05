import Weft.Logic.Search

namespace Weft.Logic

/-- Each completed branch has independent denotational meaning. Entailment and
refutation require consistency; undetermined requires both polarities. -/
def VerdictMeaning (atomCount : Nat) (premises : List Formula) (query : Formula) :
    Verdict → Prop
  | .entailed => InputsScoped atomCount premises query ∧
      (∃ valuation, PremisesHold premises valuation) ∧
      (∀ valuation, PremisesHold premises valuation → evaluate valuation query = true)
  | .refuted => InputsScoped atomCount premises query ∧
      (∃ valuation, PremisesHold premises valuation) ∧
      (∀ valuation, PremisesHold premises valuation → evaluate valuation query = false)
  | .undetermined => InputsScoped atomCount premises query ∧
      PolarityModel premises query true ∧ PolarityModel premises query false
  | .inconsistent => InputsScoped atomCount premises query ∧
      ¬ (∃ valuation, PremisesHold premises valuation)
  | .unknown => True

def verdictOf : Bool → Bool → Verdict
  | false, false => .inconsistent
  | true, false => .entailed
  | false, true => .refuted
  | true, true => .undetermined

/-- Validate the whole input and reserve the complete valuation budget before
constructing any valuation list. Budget units count valuations, not wall-clock
steps or formula nodes. Invalid domains are unknown, never false atoms. -/
def classify (atomCount : Nat) (premises : List Formula) (query : Formula)
    (budget : Nat) : Verdict :=
  if inputsInBounds atomCount premises query = true then
    if budget < requiredBudget atomCount then .unknown
    else
      let flags := summarize premises query (valuations atomCount)
      verdictOf flags.1 flags.2
  else .unknown

private theorem flags_sound (atomCount : Nat) (premises : List Formula) (query : Formula)
    (inScope : InputsScoped atomCount premises query) (positiveFlag negativeFlag : Bool)
    (positive : positiveFlag = true ↔ PolarityModel premises query true)
    (negative : negativeFlag = true ↔ PolarityModel premises query false) :
    VerdictMeaning atomCount premises query (verdictOf positiveFlag negativeFlag) := by
  cases positiveFlag with
  | false =>
      cases negativeFlag with
      | false =>
          refine ⟨inScope, ?_⟩
          rintro ⟨valuation, hp⟩
          cases hq : evaluate valuation query with
          | false =>
              have impossible : false = true := negative.mpr ⟨valuation, hp, hq⟩
              cases impossible
          | true =>
              have impossible : false = true := positive.mpr ⟨valuation, hp, hq⟩
              cases impossible
      | true =>
          obtain ⟨witness, hw, _⟩ := negative.mp rfl
          refine ⟨inScope, ⟨witness, hw⟩, ?_⟩
          intro valuation hp
          cases hq : evaluate valuation query with
          | false => rfl
          | true =>
              have impossible : false = true := positive.mpr ⟨valuation, hp, hq⟩
              cases impossible
  | true =>
      cases negativeFlag with
      | false =>
          obtain ⟨witness, hw, _⟩ := positive.mp rfl
          refine ⟨inScope, ⟨witness, hw⟩, ?_⟩
          intro valuation hp
          cases hq : evaluate valuation query with
          | false =>
              have impossible : false = true := negative.mpr ⟨valuation, hp, hq⟩
              cases impossible
          | true => rfl
      | true =>
          exact ⟨inScope, positive.mp rfl, negative.mp rfl⟩

/-- L06: every completed classification means its ordinary model-theoretic claim.
No evidence soundness or real-world interpretation follows from this theorem. -/
theorem classificationSound (atomCount : Nat) (premises : List Formula) (query : Formula)
    (budget : Nat) : VerdictMeaning atomCount premises query
      (classify atomCount premises query budget) := by
  by_cases inScope : inputsInBounds atomCount premises query = true
  · by_cases exhausted : budget < requiredBudget atomCount
    · simp [classify, inScope, exhausted, VerdictMeaning]
    · simp only [classify, inScope, if_true, exhausted, if_false]
      exact flags_sound atomCount premises query inScope _ _
        (search_positive atomCount premises query inScope)
        (search_negative atomCount premises query inScope)
  · simp [classify, inScope, VerdictMeaning]

/-- L07: an insufficient budget can never produce a completed logical verdict. -/
theorem budgetUnknown (atomCount : Nat) (premises : List Formula) (query : Formula)
    (budget : Nat) (exhausted : budget < requiredBudget atomCount) :
    classify atomCount premises query budget = .unknown := by
  by_cases inScope : inputsInBounds atomCount premises query = true <;>
    simp [classify, inScope, exhausted]

theorem invalidDomainUnknown (atomCount : Nat) (premises : List Formula) (query : Formula)
    (budget : Nat) (invalid : inputsInBounds atomCount premises query ≠ true) :
    classify atomCount premises query budget = .unknown := by
  simp [classify, invalid]

/-- With a valid domain and complete budget, unknown is not returned. -/
theorem sufficientBudgetCompletes (atomCount : Nat) (premises : List Formula)
    (query : Formula) (budget : Nat) (inScope : InputsScoped atomCount premises query)
    (enough : requiredBudget atomCount ≤ budget) :
    classify atomCount premises query budget ≠ .unknown := by
  change inputsInBounds atomCount premises query = true at inScope
  have notExhausted : ¬ budget < requiredBudget atomCount := Nat.not_lt.mpr enough
  simp only [classify, inScope, if_true, notExhausted, if_false]
  cases (summarize premises query (valuations atomCount)).1 <;>
    cases (summarize premises query (valuations atomCount)).2 <;>
    decide

end Weft.Logic
