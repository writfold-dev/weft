import Weft.Logic.Classification

namespace Weft.Logic.Examples

/-- A supplied premise supports its own polarity, not its negation. -/
theorem entailed : classify 1 [.atom 0] (.atom 0) 2 = .entailed := by decide

theorem refuted : classify 1 [.neg (.atom 0)] (.atom 0) 2 = .refuted := by decide

theorem wrongPolarity : classify 1 [.atom 0] (.neg (.atom 0)) 2 = .refuted := by decide

theorem wrongPolarityNotEntailed :
    classify 1 [.atom 0] (.neg (.atom 0)) 2 ≠ .entailed := by decide

/-- With no premise, both assignments really are models. -/
theorem twoModels : classify 1 [] (.atom 0) 2 = .undetermined := by decide

theorem twoModelWitnesses :
    PremisesHold [] (fun _ => true) ∧ evaluate (fun _ => true) (.atom 0) = true ∧
    PremisesHold [] (fun _ => false) ∧ evaluate (fun _ => false) (.atom 0) = false := by
  simp [PremisesHold, evaluate]

/-- Inconsistent premises do not vacuously establish any query. -/
theorem inconsistent :
    classify 1 [.atom 0, .neg (.atom 0)] (.atom 0) 2 = .inconsistent := by decide

theorem inconsistentNotEntailed :
    classify 1 [.atom 0, .neg (.atom 0)] (.literal true) 2 ≠ .entailed := by decide

/-- Rules are explicit formulas and require their antecedents. -/
theorem explicitRule :
    classify 2 [.atom 0, implication (.atom 0) (.atom 1)] (.atom 1) 4 = .entailed := by
  decide

theorem ruleWithoutAntecedent :
    classify 2 [implication (.atom 0) (.atom 1)] (.atom 1) 4 = .undetermined := by decide

theorem absentRule : classify 2 [.atom 0] (.atom 1) 4 = .undetermined := by decide

/-- The empty domain has one valuation, not zero valuations. -/
theorem emptyDomainTrue : classify 0 [] (.literal true) 1 = .entailed := by decide

theorem emptyDomainFalse : classify 0 [] (.literal false) 1 = .refuted := by decide

theorem emptyDomainInconsistent :
    classify 0 [.literal false] (.literal true) 1 = .inconsistent := by decide

theorem emptyDomainNoBudget : classify 0 [] (.literal true) 0 = .unknown := by decide

/-- Missing atoms cannot acquire false values from the implementation extension. -/
theorem invalidZeroAtom : classify 0 [] (.atom 0) 1 = .unknown := by decide

theorem invalidUpperBound : classify 1 [] (.atom 1) 2 = .unknown := by decide

theorem lastValidAtom : classify 2 [] (.atom 1) 4 = .undetermined := by decide

theorem invalidPremise : classify 1 [.atom 1] (.literal true) 2 = .unknown := by decide

theorem invalidShortCircuitBranch :
    classify 0 [] (.disj (.literal true) (.atom 0)) 1 = .unknown := by decide

/-- No partial enumeration is interpreted as a complete logical answer. -/
theorem zeroBudget : classify 1 [] (.atom 0) 0 = .unknown := by decide

theorem oneBelowBudget : classify 2 [] (.atom 0) 3 = .unknown := by decide

theorem exactBudget : classify 2 [] (.atom 0) 4 = .undetermined := by decide

theorem excessBudget : classify 2 [] (.atom 0) 5 = .undetermined := by decide

theorem enumerationZero : valuations 0 = [[]] := by decide

theorem enumerationTwo :
    valuations 2 = [[false, false], [false, true], [true, false], [true, true]] := by decide

/-- Substitution changes atom meaning and is not syntactic identity. -/
theorem substitutionNegativeCalibration :
    evaluate (fun _ => false) (substitute (fun _ => .literal true) (.atom 0)) ≠
      evaluate (fun _ => false) (.atom 0) := by decide

theorem implicationNegativeCalibration :
    evaluate (fun _ => false) (implication (.literal true) (.literal false)) = false := by
  decide

end Weft.Logic.Examples
