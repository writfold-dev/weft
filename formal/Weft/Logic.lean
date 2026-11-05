import Weft.Logic.Syntax
import Weft.Logic.Enumeration
import Weft.Logic.Search
import Weft.Logic.Classification
import Weft.Logic.Examples

/-!
# Finite propositional calculus

The mathematical boundary is an already constructed Formula AST and explicit
premises. Environmental evidence truth and byte-parser/Rust refinement are not
assumed or proved here. All five registered proofs concern denotational Boolean
semantics, not an evaluator accepting its own answer.

Registry mapping:
* L03 `Weft.Logic.substitutionSound`: Logic/Syntax.lean.
* L04 `Weft.Logic.sugarSound`: Logic/Syntax.lean, actual rule implication sugar.
  Actual source equality/inequality additionally use the independent
  Language.comparisonMeaningSound/inequalitySugarSound declarations.
* L05 `Weft.Logic.valuationsComplete`: Logic/Enumeration.lean.
* L06 `Weft.Logic.classificationSound`: Logic/Classification.lean.
* L07 `Weft.Logic.budgetUnknown`: Logic/Classification.lean.

`ValidValuation` characterizes finite assignments without mentioning enumeration;
`PremisesHold` and `VerdictMeaning` quantify over arbitrary Nat-to-Bool valuations.
`valuationsRepresent` bridges the two using bounded-formula extension invariance.
The checker rejects unbounded inputs before interpretation. Its budget counts
complete valuations, with `requiredBudget_pow` identifying the count as 2^n; it is
not a CPU, allocation or formula-size resource bound.

`Logic/Examples.lean` contains closed kernel-reduced positive and negative
calibrations, including contradictory premises and both actual model witnesses.
-/
