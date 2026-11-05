import Weft.Logic.Enumeration

namespace Weft.Logic

def satisfies (premises : List Formula) (valuation : Nat → Bool) : Bool :=
  premises.all (evaluate valuation)

theorem satisfies_iff (premises : List Formula) (valuation : Nat → Bool) :
    satisfies premises valuation = true ↔ PremisesHold premises valuation := by
  simp [satisfies, PremisesHold, List.all_eq_true]

/-- One scan computes both witness-existence flags; premise satisfaction is shared.
The pair records existence, never universal truth inferred from an empty model set. -/
def summarize (premises : List Formula) (query : Formula) : List (List Bool) → Bool × Bool
  | [] => (false, false)
  | values :: rest =>
      let valuation := extend values
      let admitted := satisfies premises valuation
      let answer := evaluate valuation query
      let remaining := summarize premises query rest
      ((admitted && answer) || remaining.1,
       (admitted && !answer) || remaining.2)

private theorem negation_true (value : Bool) : (!value = true) ↔ value = false := by
  cases value <;> decide

theorem summarize_positive (premises : List Formula) (query : Formula)
    (rows : List (List Bool)) :
    (summarize premises query rows).1 = true ↔
      ∃ values ∈ rows,
        PremisesHold premises (extend values) ∧ evaluate (extend values) query = true := by
  induction rows with
  | nil => simp [summarize]
  | cons values rest ih =>
      simp [summarize, Bool.or_eq_true, Bool.and_eq_true, satisfies_iff, ih]

theorem summarize_negative (premises : List Formula) (query : Formula)
    (rows : List (List Bool)) :
    (summarize premises query rows).2 = true ↔
      ∃ values ∈ rows,
        PremisesHold premises (extend values) ∧ evaluate (extend values) query = false := by
  induction rows with
  | nil => simp [summarize]
  | cons values rest ih =>
      simp [summarize, Bool.or_eq_true, Bool.and_eq_true, negation_true, satisfies_iff, ih]

/-- A polarity witness is an ordinary valuation satisfying every explicit premise. -/
def PolarityModel (premises : List Formula) (query : Formula) (polarity : Bool) : Prop :=
  ∃ valuation : Nat → Bool,
    PremisesHold premises valuation ∧ evaluate valuation query = polarity

/-- The semantic bridge uses coverage of *all* mathematical valuations. -/
theorem enumerated_model_iff (atomCount : Nat) (premises : List Formula)
    (query : Formula) (polarity : Bool) (inScope : InputsScoped atomCount premises query) :
    (∃ values ∈ valuations atomCount,
      PremisesHold premises (extend values) ∧ evaluate (extend values) query = polarity) ↔
    PolarityModel premises query polarity := by
  constructor
  · rintro ⟨values, _, hp, hq⟩
    exact ⟨extend values, hp, hq⟩
  · rintro ⟨valuation, hp, hq⟩
    have bounds : (∀ formula ∈ premises, inBounds atomCount formula = true) ∧
        inBounds atomCount query = true := by
      simpa [InputsScoped, inputsInBounds, Bool.and_eq_true, List.all_eq_true] using inScope
    refine ⟨capture valuation atomCount, valuationsComplete _ _ (capture_valid _ _), ?_, ?_⟩
    · intro formula member
      rw [capture_evaluate valuation atomCount formula (bounds.1 formula member)]
      exact hp formula member
    · rw [capture_evaluate valuation atomCount query bounds.2]
      exact hq

theorem search_positive (atomCount : Nat) (premises : List Formula) (query : Formula)
    (inScope : InputsScoped atomCount premises query) :
    (summarize premises query (valuations atomCount)).1 = true ↔
      PolarityModel premises query true :=
  (summarize_positive premises query _).trans
    (enumerated_model_iff atomCount premises query true inScope)

theorem search_negative (atomCount : Nat) (premises : List Formula) (query : Formula)
    (inScope : InputsScoped atomCount premises query) :
    (summarize premises query (valuations atomCount)).2 = true ↔
      PolarityModel premises query false :=
  (summarize_negative premises query _).trans
    (enumerated_model_iff atomCount premises query false inScope)

end Weft.Logic
