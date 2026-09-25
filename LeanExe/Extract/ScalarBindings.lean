import LeanExe.Source.ScalarValues
import LeanExe.IR.ScalarSemantics

namespace LeanExe.Extract.Core

/-- Compile-time lexical bindings. A function closes over compiled bindings;
its application recursively compiles only its original, smaller source body. -/
inductive ScalarBinding where
  | word (expression : LeanExe.IR.Expr)
  | unit
  | function (withUnit : Bool) (apply : LeanExe.IR.Expr → Option LeanExe.IR.Expr)

def ScalarBinding.kind : ScalarBinding → LeanExe.Source.Scalar.BindingKind
  | .word _ => .word
  | .unit => .unit
  | .function withUnit _ => .function withUnit

def ScalarBinding.word? : ScalarBinding → Option LeanExe.IR.Expr
  | .word expression => some expression
  | .unit | .function _ _ => none

def ScalarBinding.function? (withUnit : Bool) : ScalarBinding → Option (LeanExe.IR.Expr → Option LeanExe.IR.Expr)
  | .function shape f => if shape == withUnit then some f else none
  | _ => none

@[simp] theorem ScalarBinding.word?_some {binding : ScalarBinding} {target : LeanExe.IR.Expr} :
    binding.word? = some target ↔ binding = .word target := by
  cases binding <;> simp [word?]

@[simp] theorem ScalarBinding.function?_some {binding : ScalarBinding} {withUnit : Bool}
    {f : LeanExe.IR.Expr → Option LeanExe.IR.Expr} :
    binding.function? withUnit = some f ↔ binding = .function withUnit f := by
  cases binding with
  | word _ | unit => simp [function?]
  | function shape g => cases shape <;> cases withUnit <;> simp [function?]

def ScalarBinding.Total : ScalarBinding → Prop
  | .word _ => True
  | .unit => True
  | .function _ f => ∀ argument, ∃ target, f argument = some target

def ScalarBinding.Holds (P : LeanExe.IR.Expr → Prop) : ScalarBinding → Prop
  | .word expression => P expression
  | .unit => True
  | .function _ f => ∀ argument target, P argument → f argument = some target → P target

def ScalarBinding.Matches (store : LeanExe.IR.ScalarStore) :
    ScalarBinding → LeanExe.Source.Scalar.Value → Prop
  | .word expression, .word value => expression.ScalarEval store value store
  | .unit, .unit => True
  | .function _ compile, .function _ apply =>
      ∀ argument value target, argument.ScalarEval store value store → compile argument = some target →
        target.ScalarEval store (apply value) store
  | _, _ => False

def ScalarBindingsMatch (locals : List ScalarBinding) (values : List LeanExe.Source.Scalar.Value)
    (store : LeanExe.IR.ScalarStore) : Prop :=
  ∀ (index : Nat) (binding : ScalarBinding) (value : LeanExe.Source.Scalar.Value), locals[index]? = some binding → values[index]? = some value →
    binding.Matches store value

theorem ScalarBindingsMatch.cons {locals values store binding value}
    (tail : ScalarBindingsMatch locals values store) (head : binding.Matches store value) :
    ScalarBindingsMatch (binding :: locals) (value :: values) store := by
  intro index target source ht hs
  cases index with
  | zero => cases ht; cases hs; exact head
  | succ index => exact tail index target source ht hs

theorem ScalarBindingsMatch.word {locals : List ScalarBinding} {values : List LeanExe.Source.Scalar.Value}
    {store : LeanExe.IR.ScalarStore} {index : Nat} {target : LeanExe.IR.Expr} {value : UInt64}
    (bindings : ScalarBindingsMatch locals values store)
    (compiled : (locals[index]?.bind ScalarBinding.word?) = some target)
    (source : values[index]? = some (.word value)) : target.ScalarEval store value store := by
  obtain ⟨binding, found, matched⟩ := Option.bind_eq_some_iff.mp compiled
  have same := ScalarBinding.word?_some.mp matched
  subst binding
  exact bindings index _ _ found source

theorem ScalarBindingsMatch.function {locals : List ScalarBinding} {values : List LeanExe.Source.Scalar.Value}
    {store : LeanExe.IR.ScalarStore} {index : Nat}
    {compile : LeanExe.IR.Expr → Option LeanExe.IR.Expr} {apply : UInt64 → UInt64} {withUnit : Bool}
    (bindings : ScalarBindingsMatch locals values store)
    (compiled : (locals[index]?.bind (ScalarBinding.function? withUnit)) = some compile)
    (source : values[index]? = some (.function withUnit apply)) :
    (ScalarBinding.function withUnit compile).Matches store (.function withUnit apply) := by
  obtain ⟨binding, found, matched⟩ := Option.bind_eq_some_iff.mp compiled
  have same := ScalarBinding.function?_some.mp matched
  subst binding
  exact bindings index _ _ found source

theorem scalarWord_kind {locals : List ScalarBinding} {index : Nat} {target : LeanExe.IR.Expr}
    (found : (locals[index]?.bind ScalarBinding.word?) = some target) :
    (locals.map ScalarBinding.kind)[index]? = some .word := by
  obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
  have same := ScalarBinding.word?_some.mp matched
  subst binding
  simp [List.getElem?_map, present, ScalarBinding.kind]

theorem scalarFunction_kind {locals : List ScalarBinding} {index : Nat} {f : LeanExe.IR.Expr → Option LeanExe.IR.Expr} {withUnit : Bool}
    (found : (locals[index]?.bind (ScalarBinding.function? withUnit)) = some f) :
    (locals.map ScalarBinding.kind)[index]? = some (.function withUnit) := by
  obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
  have same := ScalarBinding.function?_some.mp matched
  subst binding
  simp [List.getElem?_map, present, ScalarBinding.kind]

theorem scalarWord_lookup {locals : List ScalarBinding} {index : Nat}
    (present : (locals.map ScalarBinding.kind)[index]? = some .word) :
    ∃ target, (locals[index]?.bind ScalarBinding.word?) = some target := by
  rw [List.getElem?_map] at present
  obtain ⟨binding, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases binding with
  | word target => exact ⟨target, by simp [found, ScalarBinding.word?]⟩
  | unit | function _ _ => cases kind

theorem scalarFunction_lookup {locals : List ScalarBinding} {index : Nat} {withUnit : Bool}
    (present : (locals.map ScalarBinding.kind)[index]? = some (.function withUnit)) :
    ∃ f, locals[index]? = some (.function withUnit f) := by
  rw [List.getElem?_map] at present
  obtain ⟨binding, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases binding with
  | word _ | unit => cases kind
  | function shape f => cases kind; exact ⟨f, found⟩

end LeanExe.Extract.Core
