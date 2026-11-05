import Weft.Finite.Algebra.Operations
import Weft.Finite.Algebra.Predicates
import Weft.Finite.Algebra.Closure
import Weft.Finite.Algebra.Lowering
import Weft.Finite.Algebra.Traces
import Weft.Finite.Algebra.Budget
import Weft.Finite.Algebra.Conservation
import Weft.Finite.Algebra.Examples

/-! Revision-3 finite set algebra calculus: union, intersection, difference,
typed membership and inclusive subset over the captured finite sets. Source
presence is not a gate pass: current source-bound audit, reference cases and
mutations are required. No Writfold identities/IO, source inference or Rust
refinement is claimed here. -/
