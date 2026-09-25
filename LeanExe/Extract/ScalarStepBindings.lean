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
  | scalar (binding : ScalarBinding)
  | function (withUnit : Bool) (apply : LeanExe.IR.Expr → Option ScalarStepCode)

def ScalarStepBinding.kind : ScalarStepBinding → LeanExe.Source.Scalar.Step.BindingKind
  | .scalar binding => .scalar binding.kind
  | .function withUnit _ => .function withUnit

def ScalarStepBinding.toScalar : ScalarStepBinding → ScalarBinding
  | .scalar binding => binding
  | .function _ _ => .unit

def ScalarStepBinding.function? (withUnit : Bool) :
    ScalarStepBinding → Option (LeanExe.IR.Expr → Option ScalarStepCode)
  | .scalar _ => none
  | .function shape f => if shape == withUnit then some f else none

@[simp] theorem ScalarStepBinding.function?_some {binding : ScalarStepBinding} {withUnit : Bool}
    {f : LeanExe.IR.Expr → Option ScalarStepCode} :
    binding.function? withUnit = some f ↔ binding = .function withUnit f := by
  cases binding with
  | scalar _ => simp [function?]
  | function shape g => cases shape <;> cases withUnit <;> simp [function?]

@[simp] theorem ScalarStepBinding.toScalar_kind (binding : ScalarStepBinding) :
    binding.toScalar.kind = binding.kind.toScalar := by cases binding <;> rfl

def ScalarStepBinding.Total : ScalarStepBinding → Prop
  | .scalar binding => binding.Total
  | .function _ f => ∀ argument, ∃ code, f argument = some code

def ScalarStepBinding.Holds (P : LeanExe.IR.Expr → Prop) : ScalarStepBinding → Prop
  | .scalar binding => binding.Holds P
  | .function _ f => ∀ argument code, P argument → f argument = some code → code.Holds P

theorem ScalarStepBinding.total_toScalar {binding : ScalarStepBinding} (total : binding.Total) :
    binding.toScalar.Total := by
  cases binding with
  | scalar _ => exact total
  | function _ _ => trivial

theorem ScalarStepBinding.holds_toScalar {binding : ScalarStepBinding} {P : LeanExe.IR.Expr → Prop}
    (holds : binding.Holds P) : binding.toScalar.Holds P := by
  cases binding with
  | scalar _ => exact holds
  | function _ _ => trivial

def ScalarStepBinding.Matches (store : LeanExe.IR.ScalarStore) :
    ScalarStepBinding → LeanExe.Source.Scalar.Step.Value → Prop
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
  cases originalBinding <;> cases originalValue
  · exact matched
  · contradiction
  · contradiction
  · trivial

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

end LeanExe.Extract.Core
