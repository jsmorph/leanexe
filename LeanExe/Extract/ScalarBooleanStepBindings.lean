import LeanExe.Source.ScalarBooleanStepValues
import LeanExe.Source.ScalarBooleanIteration
import LeanExe.Extract.ScalarStepBindings

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

inductive BooleanStepBinding where
  | scalar (binding : ScalarBinding)
  | wordFunction (apply : LeanExe.IR.Expr → Option ScalarStepCode)
  | booleanFunction (apply : LeanExe.IR.Expr → Option ScalarStepCode)

def BooleanStepBinding.kind : BooleanStepBinding → BooleanStep.BindingKind
  | .scalar binding => .scalar binding.kind
  | .wordFunction _ => .wordFunction
  | .booleanFunction _ => .booleanFunction

def BooleanStepBinding.toScalar : BooleanStepBinding → ScalarBinding
  | .scalar binding => binding
  | .wordFunction _ | .booleanFunction _ => .unit

@[simp] theorem BooleanStepBinding.toScalar_kind (binding : BooleanStepBinding) :
    binding.toScalar.kind = binding.kind.toScalar := by cases binding <;> rfl

@[simp] theorem BooleanStepBinding.scalar_kind (binding : ScalarBinding) :
    (BooleanStepBinding.scalar binding).kind = .scalar binding.kind := rfl

@[simp] theorem BooleanStepBinding.toScalar_scalar (binding : ScalarBinding) :
    (BooleanStepBinding.scalar binding).toScalar = binding := rfl

def BooleanStepBinding.Total : BooleanStepBinding → Prop
  | .scalar binding => binding.Total
  | .wordFunction f | .booleanFunction f => ∀ argument, ∃ code, f argument = some code

def BooleanStepBinding.Holds (P : LeanExe.IR.Expr → Prop) : BooleanStepBinding → Prop
  | .scalar binding => binding.Holds P
  | .wordFunction f | .booleanFunction f =>
      ∀ argument code, P argument → f argument = some code → code.Holds P

def BooleanStepBinding.Matches (store : LeanExe.IR.ScalarStore) : BooleanStepBinding → BooleanStep.Value → Prop
  | .scalar binding, .scalar value => binding.Matches store value
  | .wordFunction compile, .wordFunction apply =>
      ∀ argument value code, argument.ScalarEval store value store → compile argument = some code →
        code.Meaning store (BooleanAccumulator.encodeStep (apply value))
  | .booleanFunction compile, .booleanFunction apply =>
      ∀ argument value code, argument.ScalarEval store (Bool.toUInt64 value) store → compile argument = some code →
        code.Meaning store (BooleanAccumulator.encodeStep (apply value))
  | _, _ => False

def BooleanStepBindingsMatch (locals : List BooleanStepBinding) (values : List BooleanStep.Value)
    (store : LeanExe.IR.ScalarStore) : Prop :=
  ∀ (index : Nat) (binding : BooleanStepBinding) (value : BooleanStep.Value),
    locals[index]? = some binding → values[index]? = some value → binding.Matches store value

theorem BooleanStepBindingsMatch.cons {locals values store binding value}
    (tail : BooleanStepBindingsMatch locals values store) (head : binding.Matches store value) :
    BooleanStepBindingsMatch (binding :: locals) (value :: values) store := by
  intro index target source ht hs
  cases index with
  | zero => cases ht; cases hs; exact head
  | succ index => exact tail index target source ht hs

theorem BooleanStepBindingsMatch.toScalar {locals values store}
    (bindings : BooleanStepBindingsMatch locals values store) :
    ScalarBindingsMatch (locals.map BooleanStepBinding.toScalar) (values.map BooleanStep.Value.toScalar) store := by
  intro index binding value hb hv
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hb hv
  obtain ⟨originalBinding, foundBinding, rfl⟩ := hb
  obtain ⟨originalValue, foundValue, rfl⟩ := hv
  have matched := bindings index originalBinding originalValue foundBinding foundValue
  cases originalBinding <;> cases originalValue <;> first | exact matched | contradiction | trivial

theorem BooleanStepBindingsMatch.ofScalar {locals values store}
    (bindings : ScalarBindingsMatch locals values store) :
    BooleanStepBindingsMatch (locals.map BooleanStepBinding.scalar) (values.map BooleanStep.Value.scalar) store := by
  intro index binding value hb hv
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hb hv
  obtain ⟨originalBinding, foundBinding, rfl⟩ := hb
  obtain ⟨originalValue, foundValue, rfl⟩ := hv
  exact bindings index originalBinding originalValue foundBinding foundValue

theorem booleanStepBindings_typed {locals : List BooleanStepBinding} {types : List BooleanStep.BindingKind}
    (typed : locals.map BooleanStepBinding.kind = types) :
    (locals.map BooleanStepBinding.toScalar).map ScalarBinding.kind = types.map BooleanStep.BindingKind.toScalar := by
  rw [← typed]
  simp [List.map_map, Function.comp_def]

theorem booleanStepBindings_total {locals : List BooleanStepBinding}
    (total : ∀ binding ∈ locals, binding.Total) :
    ∀ binding ∈ locals.map BooleanStepBinding.toScalar, binding.Total := by
  intro binding member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  have holds := total original present
  cases original with
  | scalar _ => exact holds
  | wordFunction _ | booleanFunction _ => trivial

theorem booleanStepBindings_holds {locals : List BooleanStepBinding} {P : LeanExe.IR.Expr → Prop}
    (holds : ∀ binding ∈ locals, binding.Holds P) :
    ∀ binding ∈ locals.map BooleanStepBinding.toScalar, binding.Holds P := by
  intro binding member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  have fact := holds original present
  cases original with
  | scalar _ => exact fact
  | wordFunction _ | booleanFunction _ => trivial

def BooleanStepBinding.wordFunction? : BooleanStepBinding → Option (LeanExe.IR.Expr → Option ScalarStepCode)
  | .wordFunction f => some f
  | _ => none

@[simp] theorem BooleanStepBinding.wordFunction?_some {binding : BooleanStepBinding}
    {f : LeanExe.IR.Expr → Option ScalarStepCode} :
    binding.wordFunction? = some f ↔ binding = .wordFunction f := by
  cases binding <;> simp [wordFunction?]

theorem booleanStep_wordFunction_lookup {locals : List BooleanStepBinding} {index : Nat}
    (present : (locals.map BooleanStepBinding.kind)[index]? = some .wordFunction) :
    ∃ f, locals[index]? = some (.wordFunction f) := by
  rw [List.getElem?_map] at present
  obtain ⟨binding, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases binding with
  | wordFunction f => exact ⟨f, found⟩
  | scalar _ | booleanFunction _ => cases kind

theorem booleanStep_wordFunction_kind {locals : List BooleanStepBinding} {index : Nat}
    {f : LeanExe.IR.Expr → Option ScalarStepCode}
    (found : (locals[index]?.bind BooleanStepBinding.wordFunction?) = some f) :
    (locals.map BooleanStepBinding.kind)[index]? = some .wordFunction := by
  obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
  have same := BooleanStepBinding.wordFunction?_some.mp matched
  subst binding
  simp [List.getElem?_map, present, BooleanStepBinding.kind]

theorem BooleanStepBindingsMatch.wordFunction {locals : List BooleanStepBinding}
    {values : List BooleanStep.Value} {store : LeanExe.IR.ScalarStore} {index : Nat}
    {compile : LeanExe.IR.Expr → Option ScalarStepCode} {apply : UInt64 → ForInStep Bool}
    (bindings : BooleanStepBindingsMatch locals values store)
    (compiled : (locals[index]?.bind BooleanStepBinding.wordFunction?) = some compile)
    (source : values[index]? = some (.wordFunction apply)) :
    (BooleanStepBinding.wordFunction compile).Matches store (.wordFunction apply) := by
  obtain ⟨binding, found, matched⟩ := Option.bind_eq_some_iff.mp compiled
  have same := BooleanStepBinding.wordFunction?_some.mp matched
  subst binding
  exact bindings index _ _ found source

def BooleanStepBinding.booleanFunction? : BooleanStepBinding → Option (LeanExe.IR.Expr → Option ScalarStepCode)
  | .booleanFunction f => some f
  | _ => none

@[simp] theorem BooleanStepBinding.booleanFunction?_some {binding : BooleanStepBinding}
    {f : LeanExe.IR.Expr → Option ScalarStepCode} :
    binding.booleanFunction? = some f ↔ binding = .booleanFunction f := by
  cases binding <;> simp [booleanFunction?]

theorem booleanStep_booleanFunction_lookup {locals : List BooleanStepBinding} {index : Nat}
    (present : (locals.map BooleanStepBinding.kind)[index]? = some .booleanFunction) :
    ∃ f, locals[index]? = some (.booleanFunction f) := by
  rw [List.getElem?_map] at present
  obtain ⟨binding, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases binding with
  | booleanFunction f => exact ⟨f, found⟩
  | scalar _ | wordFunction _ => cases kind

theorem booleanStep_booleanFunction_kind {locals : List BooleanStepBinding} {index : Nat}
    {f : LeanExe.IR.Expr → Option ScalarStepCode}
    (found : (locals[index]?.bind BooleanStepBinding.booleanFunction?) = some f) :
    (locals.map BooleanStepBinding.kind)[index]? = some .booleanFunction := by
  obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
  have same := BooleanStepBinding.booleanFunction?_some.mp matched
  subst binding
  simp [List.getElem?_map, present, BooleanStepBinding.kind]

theorem BooleanStepBindingsMatch.booleanFunction {locals : List BooleanStepBinding}
    {values : List BooleanStep.Value} {store : LeanExe.IR.ScalarStore} {index : Nat}
    {compile : LeanExe.IR.Expr → Option ScalarStepCode} {apply : Bool → ForInStep Bool}
    (bindings : BooleanStepBindingsMatch locals values store)
    (compiled : (locals[index]?.bind BooleanStepBinding.booleanFunction?) = some compile)
    (source : values[index]? = some (.booleanFunction apply)) :
    (BooleanStepBinding.booleanFunction compile).Matches store (.booleanFunction apply) := by
  obtain ⟨binding, found, matched⟩ := Option.bind_eq_some_iff.mp compiled
  have same := BooleanStepBinding.booleanFunction?_some.mp matched
  subst binding
  exact bindings index _ _ found source

theorem BooleanStepBindingsMatch.noWordFunction {locals : List BooleanStepBinding}
    {values : List BooleanStep.Value} {store : LeanExe.IR.ScalarStore} {index : Nat}
    {apply : Bool → ForInStep Bool}
    (bindings : BooleanStepBindingsMatch locals values store)
    (source : values[index]? = some (.booleanFunction apply)) :
    locals[index]?.bind BooleanStepBinding.wordFunction? = none := by
  cases found : locals[index]? with
  | none => simp
  | some binding =>
    have matched := bindings index binding _ found source
    cases binding <;> simp_all [BooleanStepBinding.Matches, BooleanStepBinding.wordFunction?]

end LeanExe.Extract.Core
