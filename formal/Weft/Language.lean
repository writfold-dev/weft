import Weft.Language.Core
import Weft.Language.Elaboration
import Weft.Language.Semantics
import Weft.Language.Examples

/-!
# Weft P01 language calculus

Registry source mapping:
* L01 `Weft.Language.termTypeSound`: Weft/Language/Core.lean.
  Explicit hypotheses: independent type assignment and successful checked term
  evaluation in the same explicit value/type environment. No environment
  well-formedness is presumed: unknown, missing and malformed fields fail.
* L02 `Weft.Language.elaborationSound`: Weft/Language/Elaboration.lean.
  Explicit hypotheses: exact ground-call interning, agreement of the independent
  profile interpretation with the IR valuation, and successful elaboration.
  Conclusion: equality with the separately recursive operational source denotation.
  `elaborationSemanticSound` uses L02 as a bridge to the independent relations in
  Weft/Language/Semantics.lean, which share no comparison/call checking helpers.

The complete expression/value constructor mapping is:
BOOLEAN -> Surface.boolean / Term.literal (Value.boolean ...);
INTEGER -> Term.literal (Value.natural ...);
STRING -> Term.literal (Value.text ...);
resolved path -> Term.field; ==/!= -> Surface.equal/notEqual;
predicate call -> Surface.predicate; not/and/or -> Surface.neg/conj/disj.
Parentheses and precedence choose the AST. Nominal external identities arrive
only through explicitly resolved profile values, never by interpreting text as
an identity. Review/context/profile/target declarations, citation acquisition,
needs and assumptions belong to binding/grounding; this module does not pretend
an expression theorem covers the complete raw file parser or its declarations.

Independent audit targets include termMeaningSound, comparisonMeaningSound,
callMeaningSound, denotationSound, elaborationSemanticSound, internerCoverage,
Interpretation.reinterpret and inequalitySugarSound. Partial collision-free
interning realizes every supplied ground-call meaning on its captured calls;
the existence proof uses classical choice and is not an extracted evaluator.
The inequality theorem covers the actual typed surface != lowering, including
natural, text and nominal identity comparisons, without changing L01–L12.

Examples and negative calibrations are in Weft/Language/Examples.lean. They
include a successful instance of each expression constructor and inhabited L01
and L02 premises. Importing this file exposes the declarations; actual checked
status must come from the pinned Lean 4.21.0 core-only integrated build and axiom
audit, not from the existence of this source file. No raw lexer, span table,
production evaluator, external evidence soundness, authorization or profile
registration refinement is claimed.
-/
