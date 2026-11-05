import Weft.Finite.Algebra.Traces
import Weft.Finite.CaptureBudget

/-!
# Budgeted algebra

A07: budgeted operations agree with unbudgeted meaning on success, never
increase the remaining admission budget, and refuse incomplete work without a
successful partial binding, comparison or verdict. Operand visits, membership
scans, output normalization and provenance work are all charged: both whole
operands are traversed before any filtering, and the output is charged again
at publication.
-/

namespace Weft.Finite.Algebra

open Weft.Language Weft.Finite.Syntax Weft.Finite.Sets Weft.Finite.Semantics
open Weft.Finite.CaptureBudget Weft.Finite.Lowering Weft.Finite.Quantifiers

/-- A refused first stage refuses the whole sequencing: no successful prefix
of a `Program` chain is published. -/
theorem programAfterRefuses {α β : Type} {value : α} (first : Program (some value))
    {meaning : Option β} (next : Unit → Program meaning) (budget : Nat)
    (firstRefused : first.run budget = none) : (first.after next).run budget = none := by
  simp [Program.after, Program.bind, firstRefused]

/-- If the left operand's complete admission (members, origins, operator
charge) cannot be paid, every algebra operation over that operand refuses. -/
theorem operandAdmissionRefuses (left right : CapturedSet) (budget : Nat)
    (leftRefused : (acceptSet left).run budget = none) :
    (operands left right).run budget = none ∧
      (algebraUnion left right).run budget = none ∧
      (algebraIntersection left right).run budget = none ∧
      (algebraDifference left right).run budget = none ∧
      (algebraSubset left right).run budget = none := by
  have chained : (operands left right).run budget = none :=
    programAfterRefuses (acceptSet left)
      (fun _ => (acceptSet right).after (fun _ => spend 1)) budget leftRefused
  refine ⟨chained, programAfterRefuses (operands left right)
      (fun _ => publishSet (union left right)) budget chained,
    programAfterRefuses (operands left right)
      (fun _ => (scan (intersectionMembers left right)).after (fun _ =>
        publishSet (intersection left right))) budget chained,
    programAfterRefuses (operands left right)
      (fun _ => (scan (differenceMembers left right)).after (fun _ =>
        publishSet (difference left right))) budget chained,
    programAfterRefuses (operands left right)
      (fun _ => Program.lift (subset left right)) budget chained⟩

/-- A07: budgeted algebra programs agree with unbudgeted meaning on success —
including the `evalSet`/`resolveAtom` paths that feed lowering. -/
theorem budgetSuccessSound :
    (∀ (a b : CapturedSet) (result : CapturedSet) (budget rest : Nat),
        (algebraUnion a b).run budget = some (result, rest) → union a b = some result) ∧
    (∀ (a b : CapturedSet) (result : CapturedSet) (budget rest : Nat),
        (algebraIntersection a b).run budget = some (result, rest) →
          intersection a b = some result) ∧
    (∀ (a b : CapturedSet) (result : CapturedSet) (budget rest : Nat),
        (algebraDifference a b).run budget = some (result, rest) →
          difference a b = some result) ∧
    (∀ (value : Value) (set : CapturedSet) (outcome : Bool) (budget rest : Nat),
        (algebraMember value set).run budget = some (outcome, rest) →
          member value set = some outcome) ∧
    (∀ (a b : CapturedSet) (outcome : Bool) (budget rest : Nat),
        (algebraSubset a b).run budget = some (outcome, rest) →
          subset a b = some outcome) ∧
    (∀ (ctx : Context) (env : Env) (elementType : Ty) (left right : SetExpr)
        (result : CapturedSet) (budget rest : Nat),
        (CaptureBudget.evalSet ctx env (.intersection elementType left right)).run budget =
            some (result, rest) →
          Syntax.evalSet ctx env (.intersection elementType left right) = some result) ∧
    (∀ (ctx : Context) (env : Env) (term : Syntax.Term) (set : SetExpr)
        (resolved : ResolvedAtom) (budget rest : Nat),
        (CaptureBudget.resolveAtom ctx env (.member term set)).run budget =
            some (resolved, rest) →
          Semantics.resolveAtom ctx env (.member term set) = some resolved) := by
  refine ⟨fun a b _ _ _ success => (algebraUnion a b).sound success,
    fun a b _ _ _ success => (algebraIntersection a b).sound success,
    fun a b _ _ _ success => (algebraDifference a b).sound success,
    fun value set _ _ _ success => (algebraMember value set).sound success,
    fun a b _ _ _ success => (algebraSubset a b).sound success,
    fun ctx env elementType left right result budget rest success =>
      evalSet_agrees ctx env (.intersection elementType left right) budget result rest success,
    fun ctx env term set resolved budget rest success =>
      resolveAtom_agrees ctx env (.member term set) budget resolved rest success⟩

/-- A07: no successful run increases the remaining admission budget. -/
theorem remainingWorkNonincreasing :
    (∀ (a b : CapturedSet) (result : CapturedSet) (budget rest : Nat),
        (algebraUnion a b).run budget = some (result, rest) → rest ≤ budget) ∧
    (∀ (a b : CapturedSet) (result : CapturedSet) (budget rest : Nat),
        (algebraIntersection a b).run budget = some (result, rest) → rest ≤ budget) ∧
    (∀ (a b : CapturedSet) (result : CapturedSet) (budget rest : Nat),
        (algebraDifference a b).run budget = some (result, rest) → rest ≤ budget) ∧
    (∀ (value : Value) (set : CapturedSet) (outcome : Bool) (budget rest : Nat),
        (algebraMember value set).run budget = some (outcome, rest) → rest ≤ budget) ∧
    (∀ (a b : CapturedSet) (outcome : Bool) (budget rest : Nat),
        (algebraSubset a b).run budget = some (outcome, rest) → rest ≤ budget) := by
  refine ⟨fun a b result budget rest success =>
      (algebraUnion a b).decreasing (budget := budget) (value := result) (rest := rest) success,
    fun a b result budget rest success =>
      (algebraIntersection a b).decreasing (budget := budget) (value := result) (rest := rest) success,
    fun a b result budget rest success =>
      (algebraDifference a b).decreasing (budget := budget) (value := result) (rest := rest) success,
    fun value set outcome budget rest success =>
      (algebraMember value set).decreasing (budget := budget) (value := outcome) (rest := rest) success,
    fun a b outcome budget rest success =>
      (algebraSubset a b).decreasing (budget := budget) (value := outcome) (rest := rest) success⟩

/-- A07: a zero budget refuses the new constructors outright — operand visits
are charged before any membership scan, normalization or provenance work. -/
theorem zeroBudgetRefuses (ctx : Context) (env : Env) (elementType : Ty)
    (left right : SetExpr) :
    (CaptureBudget.evalSet ctx env (.intersection elementType left right)).run 0 = none ∧
      (CaptureBudget.evalSet ctx env (.difference elementType left right)).run 0 = none ∧
      (∀ term : Syntax.Term,
          (CaptureBudget.resolveAtom ctx env (.member term left)).run 0 = none) ∧
      (∀ term : Syntax.Term,
          (CaptureBudget.resolveAtom ctx env (.member term right)).run 0 = none) ∧
      (CaptureBudget.resolveAtom ctx env (.subset left right)).run 0 = none :=
  ⟨CaptureBudget.evalSet_zero ctx env _, CaptureBudget.evalSet_zero ctx env _,
    fun _ => CaptureBudget.resolveAtom_zero ctx env _,
    fun _ => CaptureBudget.resolveAtom_zero ctx env _,
    CaptureBudget.resolveAtom_zero ctx env _⟩

/-- A07 primary: incomplete work refuses without a successful partial result —
a membership/subset atom whose capture refuses is never lowered to a literal,
an algebraic quantifier domain whose capture refuses never publishes a vacuous
or prefix verdict, and unaffordable operand admission refuses every operator. -/
theorem budgetRefusesPartial (budget : Nat) (ctx : Context)
    (intern : GroundCall → Option Nat) (env : Env) :
    (∀ (term : Syntax.Term) (set : SetExpr)
        (_refused : (CaptureBudget.resolveAtom ctx env (.member term set)).run budget = none),
        lower (budget + 1) ctx intern env (.atom (.member term set)) = none) ∧
    (∀ (left right : SetExpr)
        (_refused : (CaptureBudget.resolveAtom ctx env (.subset left right)).run budget = none),
        lower (budget + 1) ctx intern env (.atom (.subset left right)) = none) ∧
    (∀ (body : Expr) (domain : SetExpr)
        (_refused : (CaptureBudget.evalSet ctx env domain).run budget = none),
        lower (budget + 1) ctx intern env (.all domain body) = none ∧
          lower (budget + 1) ctx intern env (.any domain body) = none) ∧
    (∀ (left right : CapturedSet),
        (acceptSet left).run budget = none →
          (algebraUnion left right).run budget = none ∧
            (algebraIntersection left right).run budget = none ∧
            (algebraDifference left right).run budget = none ∧
            (algebraSubset left right).run budget = none) :=
  ⟨fun _ _ refused => atomCaptureRefuses budget ctx intern env _ refused,
    fun _ _ refused => atomCaptureRefuses budget ctx intern env _ refused,
    fun _body domain refused =>
      ⟨forallCaptureRefuses budget ctx intern env domain _body refused,
        existsCaptureRefuses budget ctx intern env domain _body refused⟩,
    fun left right leftRefused =>
      (operandAdmissionRefuses left right budget leftRefused).2⟩

end Weft.Finite.Algebra
