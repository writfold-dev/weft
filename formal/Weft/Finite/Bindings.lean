import Weft.Finite.Sets

namespace Weft.Finite.Bindings

open Weft.Language Weft.Grounding Sets

/-! Declaration-ordered immutable set bindings. A declaration sees only the
finite prefix passed to it. This is the semantic boundary for `name := set`;
there is no second declaration syntax and no update or reassignment operation. -/

abbrev Environment := List (String × CapturedSet)

 def lookup : Environment → String → Option CapturedSet
  | [], _ => none
  | (name, value) :: rest, query => if name = query then some value else lookup rest query

/-- Reject absent initializers, duplicate names, and malformed external records.
A successful declaration appends exactly one validated immutable value. Its
current count describes the validated payload; the initializer's supplied source
count remains explicitly imported provenance, not a fresh evidence observation. -/
def extend (env : Environment) (name : String) (initializer : Option CapturedSet) :
    Option Environment :=
  match lookup env name, initializer with
  | none, some set =>
      match validate set with
      | none => none
      | some value => some (env ++ [(name, value)])
  | _, _ => none

 theorem lookupAppendPrior (env suffix : Environment) (name : String) (value : CapturedSet)
    (prior : lookup env name = some value) : lookup (env ++ suffix) name = some value := by
  induction env with
  | nil => simp [lookup] at prior
  | cons entry rest ih =>
      rcases entry with ⟨bound, set⟩
      by_cases same : bound = name
      · simpa [lookup, same] using prior
      · simp only [List.cons_append, lookup, same, ↓reduceIte] at prior ⊢
        exact ih prior

 theorem lookupAppendMissing (env suffix : Environment) (name : String)
    (missing : lookup env name = none) : lookup (env ++ suffix) name = lookup suffix name := by
  induction env with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨bound, set⟩
      by_cases same : bound = name
      · simp [lookup, same] at missing
      · simp only [List.cons_append, lookup, same, ↓reduceIte] at missing ⊢
        exact ih missing

 theorem extensionFacts (env result : Environment) (name : String)
    (initializer : Option CapturedSet) (success : extend env name initializer = some result) :
    ∃ source value, initializer = some source ∧ lookup env name = none ∧
      validate source = some value ∧ result = env ++ [(name, value)] := by
  cases prior : lookup env name with
  | some old => simp [extend, prior] at success
  | none =>
      cases initial : initializer with
      | none => simp [extend, prior, initial] at success
      | some source =>
          cases valid : validate source with
          | none => simp [extend, prior, initial, valid] at success
          | some value =>
              have same : env ++ [(name, value)] = result := by
                simpa [extend, prior, initial, valid] using success
              exact ⟨source, value, rfl, rfl, valid, same.symm⟩

/-- Q04: actual successful append preserves every earlier lookup exactly. -/
theorem extensionPreservesPrior (env result : Environment) (name : String)
    (initializer : Option CapturedSet) (success : extend env name initializer = some result)
    (priorName : String) (priorValue : CapturedSet)
    (prior : lookup env priorName = some priorValue) :
    lookup result priorName = some priorValue := by
  obtain ⟨_, value, _, _, _, rfl⟩ := extensionFacts _ _ _ _ success
  exact lookupAppendPrior env [(name, value)] priorName priorValue prior

 theorem extensionInstalls (env result : Environment) (name : String)
    (initializer : Option CapturedSet) (success : extend env name initializer = some result) :
    ∃ source value, initializer = some source ∧ validate source = some value ∧
      lookup result name = some value := by
  obtain ⟨source, value, initial, missing, valid, rfl⟩ := extensionFacts _ _ _ _ success
  refine ⟨source, value, initial, valid, ?_⟩
  rw [lookupAppendMissing env [(name, value)] name missing]
  simp [lookup]

 theorem duplicateBindingFails (env : Environment) (name : String)
    (initializer : Option CapturedSet) (value : CapturedSet)
    (duplicate : lookup env name = some value) : extend env name initializer = none := by
  simp [extend, duplicate]

 theorem missingInitializerFails (env : Environment) (name : String) :
    extend env name none = none := by
  cases prior : lookup env name <;> simp [extend, prior]

 theorem malformedInitializerFails (env : Environment) (name : String) (source : CapturedSet)
    (malformed : validate source = none) : extend env name (some source) = none := by
  cases prior : lookup env name <;> simp [extend, prior, malformed]

/-- Transaction outcome explicitly distinguishes refusal from installation. A
refused declaration retains the exact old environment, not a successful prefix. -/
structure Outcome where
  environment : Environment
  installed : Bool
  deriving DecidableEq, Repr

 def declare (env : Environment) (name : String) (initializer : Option CapturedSet) : Outcome :=
  match extend env name initializer with
  | none => ⟨env, false⟩
  | some result => ⟨result, true⟩

 theorem failureAtomic (env : Environment) (name : String) (initializer : Option CapturedSet)
    (failure : extend env name initializer = none) :
    declare env name initializer = ⟨env, false⟩ := by simp [declare, failure]

 theorem declarationPreservesPrior (env : Environment) (name : String)
    (initializer : Option CapturedSet) (priorName : String) (value : CapturedSet)
    (prior : lookup env priorName = some value) :
    lookup (declare env name initializer).environment priorName = some value := by
  cases result : extend env name initializer with
  | none => simpa [declare, result] using prior
  | some next =>
      simpa [declare, result] using extensionPreservesPrior _ _ _ _ result _ _ prior

 theorem extensionPreservesOrigins (env result : Environment) (name : String)
    (source : CapturedSet) (success : extend env name (some source) = some result)
    (origin : Binding) (required : origin ∈ source.origins) :
    ∃ value, lookup result name = some value ∧ origin ∈ value.origins := by
  obtain ⟨actual, value, initial, valid, found⟩ := extensionInstalls _ _ _ _ success
  cases Option.some.inj initial
  exact ⟨value, found, (validateOrigins _ _ valid origin).mpr required⟩

/-- Immutable binding metadata retains the initializer's source-count claim while
recording the actual number of payload occurrences checked at installation. -/
theorem extensionCaptureStatistics (env result : Environment) (name : String)
    (source : CapturedSet) (success : extend env name (some source) = some result) :
    ∃ value, lookup result name = some value ∧
      value.capture = some (importedStatistics source) ∧
      value.rawOccurrences = some source.members.length := by
  obtain ⟨actual, value, initial, valid, found⟩ := extensionInstalls _ _ _ _ success
  cases Option.some.inj initial
  exact ⟨value, found, validateRawOccurrences source value valid⟩

/-- A reference initializer is resolved in the old prefix, before extension. Thus
self/forward references without a prior binding fail; duplicates cannot update it. -/
def declarePrior (env : Environment) (name priorName : String) : Outcome :=
  declare env name (lookup env priorName)

 theorem missingPriorFails (env : Environment) (name priorName : String)
    (missing : lookup env priorName = none) : declarePrior env name priorName = ⟨env, false⟩ := by
  simp [declarePrior, missing, declare, missingInitializerFails]

 theorem selfReferenceFails (env : Environment) (name : String) :
    declarePrior env name name = ⟨env, false⟩ := by
  cases prior : lookup env name with
  | none => exact missingPriorFails env name name prior
  | some value =>
      simp [declarePrior, prior, declare, duplicateBindingFails env name (some value) value prior]

end Weft.Finite.Bindings
