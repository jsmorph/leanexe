import LeanExe.Extract.ScalarBindings
import LeanExe.Source.ScalarStepValues
import LeanExe.Source.ScalarRangeExit

namespace LeanExe.Extract.Core

/-- The two read-only projections of a source loop-step result. -/
structure ScalarStepCode where
  value : LeanExe.IR.Expr
  done : LeanExe.IR.Expr
  deriving Repr

def ScalarStepCode.Holds (P : LeanExe.IR.Expr → Prop) (code : ScalarStepCode) : Prop :=
  P code.value ∧ P code.done

def ScalarStepCode.Meaning (code : ScalarStepCode) (store : LeanExe.IR.ScalarStore)
    (outcome : ForInStep UInt64) : Prop :=
  code.value.ScalarEval store (LeanExe.Source.Scalar.Range.Exit.value outcome) store ∧
  code.done.ScalarEval store (if LeanExe.Source.Scalar.Range.Exit.isDone outcome then 1 else 0) store

inductive ScalarStepBinding where
  | resultFunction (apply : ScalarStepCode → Option ScalarStepCode)
  | result (code : ScalarStepCode)
  | scalar (binding : ScalarBinding)
  | function (withUnit : Bool) (apply : LeanExe.IR.Expr → Option ScalarStepCode)

def ScalarStepBinding.kind : ScalarStepBinding → LeanExe.Source.Scalar.Step.BindingKind
  | .resultFunction _ => .resultFunction
  | .result _ => .result
  | .scalar binding => .scalar binding.kind
  | .function withUnit _ => .function withUnit

def ScalarStepBinding.toScalar : ScalarStepBinding → ScalarBinding
  | .resultFunction _ => .unit
  | .result _ => .unit
  | .scalar binding => binding
  | .function _ _ => .unit

def ScalarStepBinding.function? (withUnit : Bool) :
    ScalarStepBinding → Option (LeanExe.IR.Expr → Option ScalarStepCode)
  | .resultFunction _ => none
  | .result _ => none
  | .scalar _ => none
  | .function shape f => if shape == withUnit then some f else none

@[simp] theorem ScalarStepBinding.function?_some {binding : ScalarStepBinding} {withUnit : Bool}
    {f : LeanExe.IR.Expr → Option ScalarStepCode} :
    binding.function? withUnit = some f ↔ binding = .function withUnit f := by
  cases binding with
  | resultFunction _ => simp [function?]
  | result _ => simp [function?]
  | scalar _ => simp [function?]
  | function shape g => cases shape <;> cases withUnit <;> simp [function?]

@[simp] theorem ScalarStepBinding.toScalar_kind (binding : ScalarStepBinding) :
    binding.toScalar.kind = binding.kind.toScalar := by cases binding <;> rfl

def ScalarStepBinding.Total : ScalarStepBinding → Prop
  | .resultFunction f => ∀ argument, ∃ code, f argument = some code
  | .result _ => True
  | .scalar binding => binding.Total
  | .function _ f => ∀ argument, ∃ code, f argument = some code

def ScalarStepBinding.Holds (P : LeanExe.IR.Expr → Prop) : ScalarStepBinding → Prop
  | .resultFunction f => ∀ argument code, argument.Holds P → f argument = some code → code.Holds P
  | .result code => code.Holds P
  | .scalar binding => binding.Holds P
  | .function _ f => ∀ argument code, P argument → f argument = some code → code.Holds P

theorem ScalarStepBinding.total_toScalar {binding : ScalarStepBinding} (total : binding.Total) :
    binding.toScalar.Total := by
  cases binding with
  | resultFunction _ => trivial
  | result _ => trivial
  | scalar _ => exact total
  | function _ _ => trivial

theorem ScalarStepBinding.holds_toScalar {binding : ScalarStepBinding} {P : LeanExe.IR.Expr → Prop}
    (holds : binding.Holds P) : binding.toScalar.Holds P := by
  cases binding with
  | resultFunction _ => trivial
  | result _ => trivial
  | scalar _ => exact holds
  | function _ _ => trivial

def ScalarStepBinding.Matches (store : LeanExe.IR.ScalarStore) :
    ScalarStepBinding → LeanExe.Source.Scalar.Step.Value → Prop
  | .resultFunction compile, .resultFunction apply =>
      ∀ argument outcome code, argument.Meaning store outcome → compile argument = some code →
        code.Meaning store (apply outcome)
  | .result code, .result outcome => code.Meaning store outcome
  | .scalar binding, .scalar value => binding.Matches store value
  | .function _ compile, .function _ apply =>
      ∀ argument value code, argument.ScalarEval store value store → compile argument = some code →
        code.Meaning store (apply value)
  | _, _ => False

def ScalarStepBindingsMatch (locals : List ScalarStepBinding) (values : List LeanExe.Source.Scalar.Step.Value)
    (store : LeanExe.IR.ScalarStore) : Prop :=
  ∀ (index : Nat) (binding : ScalarStepBinding) (value : LeanExe.Source.Scalar.Step.Value),
    locals[index]? = some binding → values[index]? = some value →
    binding.Matches store value

theorem ScalarStepBindingsMatch.cons {locals values store binding value}
    (tail : ScalarStepBindingsMatch locals values store) (head : binding.Matches store value) :
    ScalarStepBindingsMatch (binding :: locals) (value :: values) store := by
  intro index target source ht hs
  cases index with
  | zero => cases ht; cases hs; exact head
  | succ index => exact tail index target source ht hs

theorem ScalarStepBindingsMatch.toScalar {locals values store}
    (bindings : ScalarStepBindingsMatch locals values store) :
    ScalarBindingsMatch (locals.map ScalarStepBinding.toScalar)
      (values.map LeanExe.Source.Scalar.Step.Value.toScalar) store := by
  intro index binding value hb hv
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hb hv
  obtain ⟨originalBinding, foundBinding, rfl⟩ := hb
  obtain ⟨originalValue, foundValue, rfl⟩ := hv
  have matched := bindings index originalBinding originalValue foundBinding foundValue
  cases originalBinding <;> cases originalValue <;> first | exact matched | contradiction | trivial

theorem ScalarStepBindingsMatch.function {locals : List ScalarStepBinding}
    {values : List LeanExe.Source.Scalar.Step.Value} {store : LeanExe.IR.ScalarStore}
    {index : Nat} {withUnit : Bool} {compile : LeanExe.IR.Expr → Option ScalarStepCode}
    {apply : UInt64 → ForInStep UInt64}
    (bindings : ScalarStepBindingsMatch locals values store)
    (compiled : (locals[index]?.bind (ScalarStepBinding.function? withUnit)) = some compile)
    (source : values[index]? = some (.function withUnit apply)) :
    (ScalarStepBinding.function withUnit compile).Matches store (.function withUnit apply) := by
  obtain ⟨binding, found, matched⟩ := Option.bind_eq_some_iff.mp compiled
  have same := ScalarStepBinding.function?_some.mp matched
  subst binding
  exact bindings index _ _ found source

theorem scalarStepBindings_typed {locals : List ScalarStepBinding}
    {types : List LeanExe.Source.Scalar.Step.BindingKind}
    (typed : locals.map ScalarStepBinding.kind = types) :
    (locals.map ScalarStepBinding.toScalar).map ScalarBinding.kind =
      types.map LeanExe.Source.Scalar.Step.BindingKind.toScalar := by
  rw [← typed]
  simp [List.map_map, Function.comp_def]

theorem scalarStepBindings_total {locals : List ScalarStepBinding}
    (total : ∀ binding ∈ locals, binding.Total) :
    ∀ binding ∈ locals.map ScalarStepBinding.toScalar, binding.Total := by
  intro binding member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact ScalarStepBinding.total_toScalar (total original present)

theorem scalarStepBindings_holds {locals : List ScalarStepBinding} {P : LeanExe.IR.Expr → Prop}
    (holds : ∀ binding ∈ locals, binding.Holds P) :
    ∀ binding ∈ locals.map ScalarStepBinding.toScalar, binding.Holds P := by
  intro binding member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact ScalarStepBinding.holds_toScalar (holds original present)

theorem scalarStepFunction_lookup {locals : List ScalarStepBinding} {index : Nat} {withUnit : Bool}
    (present : (locals.map ScalarStepBinding.kind)[index]? = some (.function withUnit)) :
    ∃ f, locals[index]? = some (.function withUnit f) := by
  rw [List.getElem?_map] at present
  obtain ⟨binding, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases binding with
  | resultFunction _ => cases kind
  | result _ => cases kind
  | scalar _ => cases kind
  | function shape f => cases kind; exact ⟨f, found⟩

theorem scalarStepFunction_kind {locals : List ScalarStepBinding} {index : Nat}
    {f : LeanExe.IR.Expr → Option ScalarStepCode} {withUnit : Bool}
    (found : (locals[index]?.bind (ScalarStepBinding.function? withUnit)) = some f) :
    (locals.map ScalarStepBinding.kind)[index]? = some (.function withUnit) := by
  obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
  have same := ScalarStepBinding.function?_some.mp matched
  subst binding
  simp [List.getElem?_map, present, ScalarStepBinding.kind]

def ScalarStepBinding.result? : ScalarStepBinding → Option ScalarStepCode
  | .result code => some code
  | _ => none

@[simp] theorem ScalarStepBinding.result?_some {binding : ScalarStepBinding} {code : ScalarStepCode} :
    binding.result? = some code ↔ binding = .result code := by
  cases binding <;> simp [result?]

theorem scalarStepResult_lookup {locals : List ScalarStepBinding} {index : Nat}
    (present : (locals.map ScalarStepBinding.kind)[index]? = some .result) :
    ∃ code, locals[index]? = some (.result code) := by
  rw [List.getElem?_map] at present
  obtain ⟨binding, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases binding with
  | resultFunction _ => cases kind
  | result code => exact ⟨code, found⟩
  | scalar _ => cases kind
  | function _ _ => cases kind

theorem scalarStepResult_kind {locals : List ScalarStepBinding} {index : Nat} {code : ScalarStepCode}
    (found : (locals[index]?.bind ScalarStepBinding.result?) = some code) :
    (locals.map ScalarStepBinding.kind)[index]? = some .result := by
  obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
  have same := ScalarStepBinding.result?_some.mp matched
  subst binding
  simp [List.getElem?_map, present, ScalarStepBinding.kind]

theorem ScalarStepBindingsMatch.result {locals : List ScalarStepBinding}
    {values : List LeanExe.Source.Scalar.Step.Value} {store : LeanExe.IR.ScalarStore}
    {index : Nat} {code : ScalarStepCode} {outcome : ForInStep UInt64}
    (bindings : ScalarStepBindingsMatch locals values store)
    (compiled : (locals[index]?.bind ScalarStepBinding.result?) = some code)
    (source : values[index]? = some (.result outcome)) : code.Meaning store outcome := by
  obtain ⟨binding, found, matched⟩ := Option.bind_eq_some_iff.mp compiled
  have same := ScalarStepBinding.result?_some.mp matched
  subst binding
  exact bindings index _ _ found source

def ScalarStepBinding.resultFunction? : ScalarStepBinding → Option (ScalarStepCode → Option ScalarStepCode)
  | .resultFunction f => some f
  | _ => none

@[simp] theorem ScalarStepBinding.resultFunction?_some {binding : ScalarStepBinding}
    {f : ScalarStepCode → Option ScalarStepCode} :
    binding.resultFunction? = some f ↔ binding = .resultFunction f := by
  cases binding <;> simp [resultFunction?]

theorem scalarStepResultFunction_lookup {locals : List ScalarStepBinding} {index : Nat}
    (present : (locals.map ScalarStepBinding.kind)[index]? = some .resultFunction) :
    ∃ f, locals[index]? = some (.resultFunction f) := by
  rw [List.getElem?_map] at present
  obtain ⟨binding, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases binding with
  | resultFunction f => exact ⟨f, found⟩
  | result _ => cases kind
  | scalar _ => cases kind
  | function _ _ => cases kind

theorem scalarStepResultFunction_kind {locals : List ScalarStepBinding} {index : Nat}
    {f : ScalarStepCode → Option ScalarStepCode}
    (found : (locals[index]?.bind ScalarStepBinding.resultFunction?) = some f) :
    (locals.map ScalarStepBinding.kind)[index]? = some .resultFunction := by
  obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
  have same := ScalarStepBinding.resultFunction?_some.mp matched
  subst binding
  simp [List.getElem?_map, present, ScalarStepBinding.kind]

theorem ScalarStepBindingsMatch.resultFunction {locals : List ScalarStepBinding}
    {values : List LeanExe.Source.Scalar.Step.Value} {store : LeanExe.IR.ScalarStore}
    {index : Nat} {compile : ScalarStepCode → Option ScalarStepCode}
    {apply : ForInStep UInt64 → ForInStep UInt64}
    (bindings : ScalarStepBindingsMatch locals values store)
    (compiled : (locals[index]?.bind ScalarStepBinding.resultFunction?) = some compile)
    (source : values[index]? = some (.resultFunction apply)) :
    (ScalarStepBinding.resultFunction compile).Matches store (.resultFunction apply) := by
  obtain ⟨binding, found, matched⟩ := Option.bind_eq_some_iff.mp compiled
  have same := ScalarStepBinding.resultFunction?_some.mp matched
  subst binding
  exact bindings index _ _ found source

theorem ScalarStepBindingsMatch.noWordFunction {locals : List ScalarStepBinding}
    {values : List LeanExe.Source.Scalar.Step.Value} {store : LeanExe.IR.ScalarStore}
    {index : Nat} {apply : ForInStep UInt64 → ForInStep UInt64}
    (bindings : ScalarStepBindingsMatch locals values store)
    (source : values[index]? = some (.resultFunction apply)) :
    locals[index]?.bind (ScalarStepBinding.function? false) = none := by
  cases found : locals[index]? with
  | none => simp
  | some binding =>
    have matched := bindings index binding _ found source
    cases binding <;> simp_all [ScalarStepBinding.Matches, ScalarStepBinding.function?]

theorem ScalarStepBindingsMatch.noResultFunction {locals : List ScalarStepBinding}
    {values : List LeanExe.Source.Scalar.Step.Value} {store : LeanExe.IR.ScalarStore}
    {index : Nat} {apply : UInt64 → ForInStep UInt64}
    (bindings : ScalarStepBindingsMatch locals values store)
    (source : values[index]? = some (.function false apply)) :
    locals[index]?.bind ScalarStepBinding.resultFunction? = none := by
  cases found : locals[index]? with
  | none => simp
  | some binding =>
    have matched := bindings index binding _ found source
    cases binding <;> simp_all [ScalarStepBinding.Matches, ScalarStepBinding.resultFunction?]

end LeanExe.Extract.Core
