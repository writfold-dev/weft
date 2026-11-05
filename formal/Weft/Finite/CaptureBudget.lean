import Init.Data.List.Monadic
import Weft.Finite.Semantics

namespace Weft.Finite.CaptureBudget
open Weft.Language Weft.Finite.Syntax Weft.Finite.Sets Weft.Finite.Semantics

variable {α β : Type}

/-!
Capture-work boundary (not a wall-clock or allocator bound).

A work unit charges a syntax/list spine visit, captured-member acceptance, or a
normalization/validation/equality invocation. Raw member entries and every origin
entry, including duplicates, are traversed under the remaining budget before
normalization or validation; both source segments are charged before append.
Intermediate collections produced by one stage are charged again at the next
stage, not replaced by final distinct cardinality. This is input/expansion
admission accounting, NOT a proved primitive-step complexity bound for the
existing normalization/validation/equality algorithms. Payload equality and
immutable captured-context lookups are abstract operations; string/identity byte
lengths and host lookup costs are not covered. No separate output cap is imposed:
every normalized output member and origin is charged again before publication.
Normalization can copy per-member provenance into the set-wide origin list;
the output scan accounts for both copies. Raw-input admission happens BEFORE
normalization, so this output check is not a cosmetic post-evaluation limit.
Repeated internal comparison work is not claimed to equal this admission counter.

Integration: `Lowering.Work.capture` consumes these programs at atom/domain
branches. `Lowering.lower` returns a `WorkExpansion` retaining the full semantic
derivation, actual remaining admission units, and the nonincrease proof. Its Work
sequencing passes that remainder through body nodes, Boolean siblings and every
quantified instance; one additional unit charges each body/member-list node.
`.sound` provides precisely the old operation equation required by `Expansion`;
it is a Prop proof erased at runtime, not a replay of the unbounded evaluator.
`none` contains neither a prefix result nor a residual budget. Quantified reports
bind the supplied budget, actual usage, remainder and semantic node count
separately; valuation enumeration and serialized byte limits remain independent.
-/

/-- A runnable computation with erased semantic and accounting certificates. -/
structure Program {α : Type} (meaning : Option α) where
  run : Nat → Option (α × Nat)
  sound : ∀ {budget value rest}, run budget = some (value, rest) → meaning = some value
  decreasing : ∀ {budget value rest}, run budget = some (value, rest) → rest ≤ budget

namespace Program

def pure (value : α) : Program (some value) where
  run := fun budget => some (value, budget)
  sound := by intro budget result rest h; cases h; rfl
  decreasing := by intro budget result rest h; cases h; exact Nat.le_refl _

def lift (meaning : Option α) : Program meaning where
  run := fun budget => meaning.map (fun value => (value, budget))
  sound := by
    intro budget value rest h
    cases meaning with
    | none => simp at h
    | some a => simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
                exact congrArg some h.1
  decreasing := by
    intro budget value rest h
    cases meaning with
    | none => simp at h
    | some a => simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
                exact Nat.le_of_eq h.2.symm

def bind {first : Option α} {next : α → Option β}
    (a : Program first) (b : (value : α) → Program (next value)) :
    Program (first.bind next) where
  run := fun budget => do
    let (value, rest) ← a.run budget
    (b value).run rest
  sound := by
    intro budget value rest h
    cases ha : a.run budget with
    | none => simp [ha] at h
    | some pair =>
      obtain ⟨x, remaining⟩ := pair
      have hb : (b x).run remaining = some (value, rest) := by simpa [ha] using h
      rw [a.sound ha]
      exact (b x).sound hb
  decreasing := by
    intro budget value rest h
    cases ha : a.run budget with
    | none => simp [ha] at h
    | some pair =>
      obtain ⟨x, remaining⟩ := pair
      have hb : (b x).run remaining = some (value, rest) := by simpa [ha] using h
      exact Nat.le_trans ((b x).decreasing hb) (a.decreasing ha)

/-- Sequencing a guaranteed semantic value; the callback remains lazy. -/
def after {value : α} {meaning : Option β} (a : Program (some value))
    (b : Unit → Program meaning) : Program meaning :=
  a.bind (fun _ => b ())

/-- Transport only the erased certificate. The executable closure is unchanged,
so neither runtime evaluation nor kernel reduction must traverse a proof cast. -/
def reindex {first second : Option α} (program : Program first)
    (agreement : first = second) : Program second where
  run := program.run
  sound := fun success => agreement.symm.trans (program.sound success)
  decreasing := program.decreasing

end Program

/-- Atomic reservation. No traversal is needed to reject an oversized charge. -/
def spend (amount : Nat) : Program (some ()) where
  run := fun budget => if amount ≤ budget then some ((), budget - amount) else none
  sound := by intro budget value rest h; cases value; rfl
  decreasing := by
    intro budget value rest h
    split at h
    · cases h; exact Nat.sub_le _ _
    · contradiction

theorem spend_insufficient (amount budget : Nat) (h : budget < amount) :
    (spend amount).run budget = none := by
  simp [spend, Nat.not_le.mpr h]

/-- Branching preserves the semantic index without evaluating the other branch. -/
def choose {yes no : Option α} (condition : Prop) [Decidable condition]
    (left : Unit → Program yes) (right : Unit → Program no) :
    Program (if condition then yes else no) :=
  if h : condition then (left ()).reindex (by simp only [if_pos h])
  else (right ()).reindex (by simp only [if_neg h])

/-- Count without ever inspecting an uncharged cons cell's tail. -/
def scan {α : Type} : (xs : List α) → Program (some xs.length)
  | [] => Program.pure 0
  | _ :: xs => (spend 1).after (fun _ =>
      (scan xs).bind (fun n => Program.pure (n + 1)))

/-- CB05: even duplicate list entries cannot evade admission accounting. -/
theorem scan_insufficient {α : Type} (xs : List α) (budget : Nat)
    (insufficient : budget < xs.length) : (scan xs).run budget = none := by
  induction xs generalizing budget with
  | nil => simp at insufficient
  | cons x xs ih =>
    cases budget with
    | zero => simp [scan, Program.after, Program.bind, spend]
    | succ budget =>
      have smaller : budget < xs.length := Nat.lt_of_succ_lt_succ insufficient
      simp [scan, Program.after, Program.bind, spend, ih budget smaller]

theorem scan_admitted_length {α : Type} (xs : List α) (budget value rest : Nat)
    (success : (scan xs).run budget = some (value, rest)) : xs.length ≤ budget := by
  by_cases fits : xs.length ≤ budget
  · exact fits
  · have refused := scan_insufficient xs budget (Nat.lt_of_not_ge fits)
    rw [refused] at success
    contradiction

def scanMembers : (members : List Member) →
    Program (some (members.length + (memberOrigins members).length))
  | [] => Program.pure 0
  | member :: rest =>
      ((spend 1).after (fun _ => (scan member.origins).bind (fun n =>
        (scanMembers rest).bind (fun m => Program.pure (1 + n + m))))).reindex
        (by simp [memberOrigins, List.flatMap_cons, List.length_append,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])

/-- Raw duplicate entries and empty-set provenance are counted independently. -/
def preflight (members : List Member) (origins : List Weft.Grounding.Binding) :
    Program (some ()) :=
  (scanMembers members).after (fun _ =>
    (scan origins).after (fun _ => spend 1))

/-- Both source segments are checked before append allocates its result. -/
def append {α : Type} (left right : List α) : Program (some (left ++ right)) :=
  (scan left).after (fun _ => (scan right).after (fun _ => Program.pure (left ++ right)))

/-- Output entries have their own charge, in the same aggregate budget. -/
def acceptSet (set : CapturedSet) : Program (some set) :=
  (scanMembers set.members).after (fun _ =>
    (scan set.origins).after (fun _ => Program.pure set))

def publishSet (set : Option CapturedSet) : Program set :=
  ((Program.lift set).bind acceptSet).reindex (by cases set <;> rfl)

def normalize (ty : Ty) (members : List Member) (origins : List Weft.Grounding.Binding) :
    Program (Sets.normalize ty members origins) :=
  (preflight members origins).after (fun _ => publishSet (Sets.normalize ty members origins))

def validate (raw : CapturedSet) : Program (Sets.validate raw) :=
  (preflight raw.members raw.origins).after (fun _ => publishSet (Sets.validate raw))

/-- Traversal precedes even the external-record closure/type checks. -/
def acceptMember (member : Member) : Program (some member) :=
  (spend 1).after (fun _ => (scan member.origins).after (fun _ => Program.pure member))

def lookupMember (member : Option Member) : Program member :=
  ((Program.lift member).bind acceptMember).reindex (by cases member <;> rfl)

def resolveTerm (ctx : Context) (env : Env) :
    (term : Syntax.Term) → Program (Syntax.resolveTerm ctx env term)
  | .literal value => (spend 1).after (fun _ => Program.pure (⟨value, []⟩ : Member))
  | .captured member => (spend 1).after (fun _ => acceptMember member)
  | .named index => (spend 1).after (fun _ => lookupMember (ctx.named index))
  | .bound index => (spend 1).after (fun _ => lookupMember (env index))
  | .global path => (spend 1).after (fun _ =>
      (scan path.fields).after (fun _ => lookupMember
      ((Language.resolveTerm ctx.legacy (.field path)).map
        (fun value => ⟨value, ctx.globalOrigins path⟩))))
  | .field base selector => (spend 1).after (fun _ =>
      (scan selector).after (fun _ =>
      (resolveTerm ctx env base).bind (fun member =>
      (Program.lift (ctx.fieldType member.value.type selector)).bind (fun ty =>
      (lookupMember (ctx.field member.value selector)).bind (fun result =>
        choose (result.value.type = ty)
          (fun _ => (append member.origins result.origins).bind (fun origins =>
            Program.pure (⟨result.value, origins⟩ : Member)))
          (fun _ => Program.lift none))))))

section Algebra

/-- Complete operand admission before any algebraic filtering: both operands'
members and origins are traversed, then one operator charge. Eliminated
members and the entire right operand are charged, never skipped. -/
def operands (left right : CapturedSet) : Program (some ()) :=
  (acceptSet left).after (fun _ => (acceptSet right).after (fun _ => spend 1))

/-- Budgeted algebra mirrors the single authoritative `Weft.Finite.Algebra`
operations: inputs are charged before filtering and outputs again at
publication, in one aggregate budget. -/
def algebraUnion (left right : CapturedSet) : Program (Algebra.union left right) :=
  (operands left right).after (fun _ => publishSet (Algebra.union left right))

def algebraIntersection (left right : CapturedSet) :
    Program (Algebra.intersection left right) :=
  (operands left right).after (fun _ =>
    (scan (Algebra.intersectionMembers left right)).after (fun _ =>
      publishSet (Algebra.intersection left right)))

def algebraDifference (left right : CapturedSet) :
    Program (Algebra.difference left right) :=
  (operands left right).after (fun _ =>
    (scan (Algebra.differenceMembers left right)).after (fun _ =>
      publishSet (Algebra.difference left right)))

/-- Membership and subset probes charge the complete operand traversals — the
whole RHS set for `in`, both whole sets for `<=` — plus one comparison charge. -/
def algebraMember (value : Value) (set : CapturedSet) :
    Program (Algebra.member value set) :=
  ((acceptMember ⟨value, []⟩).after (fun _ =>
    (acceptSet set).after (fun _ => spend 1))).after (fun _ =>
      Program.lift (Algebra.member value set))

def algebraSubset (left right : CapturedSet) : Program (Algebra.subset left right) :=
  (operands left right).after (fun _ => Program.lift (Algebra.subset left right))

end Algebra


def evalSet (ctx : Context) (env : Env) :
    (expr : SetExpr) → Program (Syntax.evalSet ctx env expr)
  | .empty ty => (spend 1).after (fun _ => normalize ty [] [])
  | .singleton term => (spend 1).after (fun _ =>
      (resolveTerm ctx env term).bind (fun member => normalize member.value.type [member] []))
  | .union ty left right => (spend 1).after (fun _ =>
      (evalSet ctx env left).bind (fun a =>
      (evalSet ctx env right).bind (fun b =>
        choose (a.elementType = ty ∧ b.elementType = ty)
          (fun _ => (append a.members b.members).bind (fun members =>
          (append a.origins b.origins).bind (fun origins => normalize ty members origins)))
          (fun _ => Program.lift none))))
  | .intersection ty left right => (spend 1).after (fun _ =>
      (evalSet ctx env left).bind (fun a =>
      (evalSet ctx env right).bind (fun b =>
        choose (a.elementType = ty ∧ b.elementType = ty)
          (fun _ => algebraIntersection a b)
          (fun _ => Program.lift none))))
  | .difference ty left right => (spend 1).after (fun _ =>
      (evalSet ctx env left).bind (fun a =>
      (evalSet ctx env right).bind (fun b =>
        choose (a.elementType = ty ∧ b.elementType = ty)
          (fun _ => algebraDifference a b)
          (fun _ => Program.lift none))))
  | .named ty index => (spend 1).after (fun _ =>
      (Program.lift (ctx.sets index)).bind (fun raw =>
        choose (raw.elementType = ty)
          (fun _ => validate raw) (fun _ => Program.lift none)))
  | .select ty base selector => (spend 1).after (fun _ =>
      (scan selector).after (fun _ =>
      (resolveTerm ctx env base).bind (fun member =>
      (Program.lift (ctx.collectionType member.value.type selector)).bind (fun declared =>
      (Program.lift (ctx.collection member.value selector)).bind (fun raw =>
        choose (declared = ty ∧ raw.elementType = ty)
          (fun _ => (validate raw).bind (fun checked =>
          (append member.origins checked.origins).bind (fun origins =>
            normalize ty checked.members origins)))
          (fun _ => Program.lift none))))))

/-- Argument-list nodes and every term share the same residual state.
The library's cons equation transports the tail-recursive `mapM` index only. -/
def resolveArguments (ctx : Context) (env : Env) :
    (args : List Syntax.Term) → Program (args.mapM (Syntax.resolveTerm ctx env))
  | [] => Program.pure []
  | arg :: args => ((spend 1).after (fun _ =>
      (resolveTerm ctx env arg).bind (fun member =>
      (resolveArguments ctx env args).bind (fun members => Program.pure (member :: members))))).reindex
        (by simp only [List.mapM_cons]; rfl)

def legacyTermOrigins (ctx : Context) :
    (term : Language.Term) → Program (some (Semantics.legacyTermOrigins ctx term))
  | .literal _ => (spend 1).after (fun _ => Program.pure [])
  | .field path => (spend 1).after (fun _ =>
      (scan path.fields).after (fun _ =>
      (scan (ctx.globalOrigins path)).after (fun _ => Program.pure (ctx.globalOrigins path))))

/-- Legacy argument flattening also charges every source segment before append. -/
def legacyArguments (ctx : Context) : (args : List Language.Term) →
    Program (some (args.flatMap (Semantics.legacyTermOrigins ctx)))
  | [] => Program.pure []
  | arg :: args => (spend 1).after (fun _ =>
      (legacyTermOrigins ctx arg).bind (fun origins =>
      (legacyArguments ctx args).bind (fun rest => append origins rest)))

def legacyOrigins (ctx : Context) :
    (surface : Surface) → Program (some (Semantics.legacyOrigins ctx surface))
  | .boolean _ => (spend 1).after (fun _ => Program.pure [])
  | .equal a b | .notEqual a b => (spend 1).after (fun _ =>
      (legacyTermOrigins ctx a).bind (fun x =>
      (legacyTermOrigins ctx b).bind (fun y => append x y)))
  | .predicate _ args => (spend 1).after (fun _ => legacyArguments ctx args)
  | .neg body => (spend 1).after (fun _ => legacyOrigins ctx body)
  | .conj a b | .disj a b => (spend 1).after (fun _ =>
      (legacyOrigins ctx a).bind (fun x =>
      (legacyOrigins ctx b).bind (fun y => append x y)))

def equal (a b : CapturedSet) : Program (Sets.equal a b) :=
  (scanMembers a.members).after (fun _ =>
    (scanMembers b.members).after (fun _ =>
      (spend 1).after (fun _ => Program.lift (Sets.equal a b))))

def resolveAtom (ctx : Context) (env : Env) :
    (atom : Atom) → Program (Semantics.resolveAtom ctx env atom)
  | .legacy surface => (spend 1).after (fun _ =>
      (legacyOrigins ctx surface).bind (fun origins => Program.pure (⟨surface, origins⟩ : ResolvedAtom)))
  | .equal a b => (spend 1).after (fun _ =>
      (resolveTerm ctx env a).bind (fun x =>
      (resolveTerm ctx env b).bind (fun y =>
      (append x.origins y.origins).bind (fun origins =>
        Program.pure (⟨.equal (.literal x.value) (.literal y.value), origins⟩ : ResolvedAtom)))))
  | .notEqual a b => (spend 1).after (fun _ =>
      (resolveTerm ctx env a).bind (fun x =>
      (resolveTerm ctx env b).bind (fun y =>
      (append x.origins y.origins).bind (fun origins =>
        Program.pure (⟨.notEqual (.literal x.value) (.literal y.value), origins⟩ : ResolvedAtom)))))
  | .predicate name args => (spend 1).after (fun _ =>
      (resolveArguments ctx env args).bind (fun members =>
      (scanMembers members).after (fun _ => Program.pure
        (⟨.predicate name (members.map (fun m => .literal m.value)), memberOrigins members⟩ : ResolvedAtom))))
  | .setEqual a b => (spend 1).after (fun _ =>
      (evalSet ctx env a).bind (fun x =>
      (evalSet ctx env b).bind (fun y =>
      (equal x y).bind (fun result =>
      (append x.origins y.origins).bind (fun origins =>
        Program.pure (⟨.boolean result, origins⟩ : ResolvedAtom))))))
  | .member term set => (spend 1).after (fun _ =>
      (resolveTerm ctx env term).bind (fun x =>
      (evalSet ctx env set).bind (fun captured =>
      (algebraMember x.value captured).bind (fun result =>
      (append x.origins captured.origins).bind (fun origins =>
        Program.pure (⟨.boolean result, origins⟩ : ResolvedAtom))))))
  | .subset a b => (spend 1).after (fun _ =>
      (evalSet ctx env a).bind (fun x =>
      (evalSet ctx env b).bind (fun y =>
      (algebraSubset x y).bind (fun result =>
      (append x.origins y.origins).bind (fun origins =>
        Program.pure (⟨.boolean result, origins⟩ : ResolvedAtom))))))

/-- CB01: exact semantic agreement, including every member and origin identity. -/
theorem resolveTerm_agrees (ctx : Context) (env : Env) (term : Syntax.Term)
    (budget : Nat) (value : Member) (rest : Nat)
    (h : (resolveTerm ctx env term).run budget = some (value, rest)) :
    Syntax.resolveTerm ctx env term = some value := (resolveTerm ctx env term).sound h

theorem evalSet_agrees (ctx : Context) (env : Env) (expr : SetExpr)
    (budget : Nat) (value : CapturedSet) (rest : Nat)
    (h : (evalSet ctx env expr).run budget = some (value, rest)) :
    Syntax.evalSet ctx env expr = some value := (evalSet ctx env expr).sound h

theorem resolveAtom_agrees (ctx : Context) (env : Env) (atom : Atom)
    (budget : Nat) (value : ResolvedAtom) (rest : Nat)
    (h : (resolveAtom ctx env atom).run budget = some (value, rest)) :
    Semantics.resolveAtom ctx env atom = some value := (resolveAtom ctx env atom).sound h

/-- CB02: one theorem covers every combinator and every public operation. -/
theorem remaining_never_increases {α : Type} {meaning : Option α}
    (program : Program meaning) (budget : Nat) (value : α) (rest : Nat)
    (h : program.run budget = some (value, rest)) : rest ≤ budget := program.decreasing h

/-- CB03: refusal exposes no successful prefix. -/
theorem insufficient_refuses {α : Type} {meaning : Option α}
    (amount budget : Nat) (h : budget < amount) (next : Unit → Program meaning) :
    ((spend amount).after next).run budget = none := by
  simp [Program.after, Program.bind, spend_insufficient amount budget h]

theorem resolveTerm_zero (ctx : Context) (env : Env) (term : Syntax.Term) :
    (resolveTerm ctx env term).run 0 = none := by
  cases term <;> simp [resolveTerm, Program.after, Program.bind, spend]

theorem evalSet_zero (ctx : Context) (env : Env) (expr : SetExpr) :
    (evalSet ctx env expr).run 0 = none := by
  cases expr <;> simp [evalSet, Program.after, Program.bind, spend]

theorem resolveAtom_zero (ctx : Context) (env : Env) (atom : Atom) :
    (resolveAtom ctx env atom).run 0 = none := by
  cases atom <;> simp [resolveAtom, Program.after, Program.bind, spend]

/-- CB04: normalization retains all extra and per-member origins, not a subset. -/
theorem normalize_origins (ty : Ty) (members : List Member)
    (origins : List Weft.Grounding.Binding) (budget : Nat) (result : CapturedSet) (rest : Nat)
    (h : (normalize ty members origins).run budget = some (result, rest))
    (origin : Weft.Grounding.Binding) :
    origin ∈ result.origins ↔ origin ∈ origins ∨ origin ∈ memberOrigins members :=
  Sets.normalizeOrigins ty members origins result ((normalize ty members origins).sound h) origin

/-- Each surviving member retains the origins of every equal-valued input alias. -/
theorem normalize_member_origins (ty : Ty) (members : List Member)
    (origins : List Weft.Grounding.Binding) (budget : Nat) (result : CapturedSet) (rest : Nat)
    (h : (normalize ty members origins).run budget = some (result, rest))
    (member : Member) (present : member ∈ result.members) (origin : Weft.Grounding.Binding) :
    origin ∈ member.origins ↔
      ∃ source ∈ members, source.value = member.value ∧ origin ∈ source.origins :=
  Sets.normalizeMemberOrigins ty members origins result
    ((normalize ty members origins).sound h) member present origin

/-- Equality of complete results transports any provenance obligation unchanged. -/
theorem evalSet_origins (ctx : Context) (env : Env) (expr : SetExpr)
    (budget rest : Nat) (result expected : CapturedSet)
    (h : (evalSet ctx env expr).run budget = some (result, rest))
    (semantic : Syntax.evalSet ctx env expr = some expected) : result.origins = expected.origins := by
  have same : result = expected :=
    Option.some.inj (((evalSet ctx env expr).sound h).symm.trans semantic)
  exact congrArg CapturedSet.origins same

/-- CB06: the bounded path exposes the actual raw count from its normalization
event. This proof consumes the erased semantic certificate, not a runtime replay. -/
theorem normalize_rawOccurrences (ty : Ty) (members : List Member)
    (origins : List Weft.Grounding.Binding) (budget : Nat) (result : CapturedSet) (rest : Nat)
    (success : (normalize ty members origins).run budget = some (result, rest)) :
    result.rawOccurrences = some members.length :=
  (Sets.normalizeRawOccurrences ty members origins result
    ((normalize ty members origins).sound success)).2

theorem validate_rawOccurrences (raw result : CapturedSet) (budget rest : Nat)
    (success : (validate raw).run budget = some (result, rest)) :
    result.capture = some (importedStatistics raw) ∧
      result.rawOccurrences = some raw.members.length :=
  Sets.validateRawOccurrences raw result ((validate raw).sound success)

private theorem bindSome {α β : Type} (first : Option α) (next : α → Option β)
    (value : β) (success : first.bind next = some value) :
    ∃ a, first = some a ∧ next a = some value := by
  cases first with
  | none => simp at success
  | some a => exact ⟨a, rfl, success⟩

private theorem normalizedCapture (ty : Ty) (members : List Member)
    (origins : List Weft.Grounding.Binding) (result : CapturedSet)
    (success : Sets.normalize ty members origins = some result) :
    ∃ capture, result.capture = some capture :=
  ⟨_, (Sets.normalizeRawOccurrences ty members origins result success).1⟩

/-- Every successful source-domain evaluation records an actual local input
event. Optional metadata permits unknown external history, not missing output
counts at a successful checked domain. No recursive source text is recounted. -/
theorem evalSetCapturePresent (ctx : Context) (env : Env) (expr : SetExpr)
    (result : CapturedSet) (success : Syntax.evalSet ctx env expr = some result) :
    ∃ capture, result.capture = some capture := by
  cases expr with
  | empty ty => exact normalizedCapture ty [] [] result success
  | singleton term =>
    obtain ⟨member, _, normalized⟩ := bindSome _ _ _ success
    exact normalizedCapture member.value.type [member] [] result normalized
  | union ty left right =>
    obtain ⟨a, _, afterLeft⟩ := bindSome _ _ _ success
    obtain ⟨b, _, afterRight⟩ := bindSome _ _ _ afterLeft
    by_cases typed : a.elementType = ty ∧ b.elementType = ty
    · exact normalizedCapture ty (a.members ++ b.members) (a.origins ++ b.origins) result
        (by simpa [typed] using afterRight)
    · simp [typed] at afterRight
  | intersection ty left right =>
    obtain ⟨a, _, afterLeft⟩ := bindSome _ _ _ success
    obtain ⟨b, _, afterRight⟩ := bindSome _ _ _ afterLeft
    by_cases typed : a.elementType = ty ∧ b.elementType = ty
    · have algebraCase : Algebra.intersection a b = some result := by
        simpa [typed] using afterRight
      by_cases same : a.elementType = b.elementType
      · exact normalizedCapture a.elementType (Algebra.intersectionMembers a b)
          (a.origins ++ b.origins) result
          (by simpa [Algebra.intersection, same] using algebraCase)
      · simp [Algebra.intersection, same] at algebraCase
    · simp [typed] at afterRight
  | difference ty left right =>
    obtain ⟨a, _, afterLeft⟩ := bindSome _ _ _ success
    obtain ⟨b, _, afterRight⟩ := bindSome _ _ _ afterLeft
    by_cases typed : a.elementType = ty ∧ b.elementType = ty
    · have algebraCase : Algebra.difference a b = some result := by
        simpa [typed] using afterRight
      by_cases same : a.elementType = b.elementType
      · exact normalizedCapture a.elementType (Algebra.differenceMembers a b)
          (a.origins ++ b.origins) result
          (by simpa [Algebra.difference, same] using algebraCase)
      · simp [Algebra.difference, same] at algebraCase
    · simp [typed] at afterRight
  | named ty index =>
    obtain ⟨raw, _, checked⟩ := bindSome _ _ _ success
    by_cases typed : raw.elementType = ty
    · exact ⟨_, (Sets.validateRawOccurrences raw result
        (by simpa [typed] using checked)).1⟩
    · simp [typed] at checked
  | select ty base selector =>
    obtain ⟨member, _, afterMember⟩ := bindSome _ _ _ success
    obtain ⟨declared, _, afterDeclared⟩ := bindSome _ _ _ afterMember
    obtain ⟨raw, _, afterRaw⟩ := bindSome _ _ _ afterDeclared
    by_cases typed : declared = ty ∧ raw.elementType = ty
    · have checked : (Sets.validate raw).bind (fun value =>
          Sets.normalize ty value.members (member.origins ++ value.origins)) = some result := by
        simpa [typed] using afterRaw
      obtain ⟨value, _, normalized⟩ := bindSome _ _ _ checked
      exact normalizedCapture ty value.members (member.origins ++ value.origins) result normalized
    · simp [typed] at afterRaw

end Weft.Finite.CaptureBudget
