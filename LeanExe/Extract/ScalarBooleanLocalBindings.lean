import LeanExe.Extract.ScalarBindings
import LeanExe.Extract.ScalarBooleanLocal
import LeanExe.Extract.ScalarBooleanLocalSyntax
import LeanExe.Source.ScalarBooleanLocalValues

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Boolean lookup and scalar operand compilation remain separately typed. -/
def extractBooleanLocalWith (locals : List ScalarBinding) (value : BooleanLocal)
    (compile : (operand : Lean.Expr) → operand ∈ value.operands → Option LeanExe.IR.Expr) :
    Option LeanExe.IR.Cond :=
  extractBooleanLocal value (fun index _ => locals[index]?.bind ScalarBinding.boolean?) compile

theorem extractBooleanLocalWith_accepts (locals : List ScalarBinding) (value : BooleanLocal)
    (compile : (operand : Lean.Expr) → operand ∈ value.operands → Option LeanExe.IR.Expr)
    (variables : value.VariablesTyped (locals.map ScalarBinding.kind))
    (operands : ∀ operand member, ∃ target, compile operand member = some target) :
    ∃ target, extractBooleanLocalWith locals value compile = some target := by
  exact extractBooleanLocal_accepts value _ compile
    (fun index member => scalarBoolean_lookup (variables index member)) operands

theorem extractBooleanLocalWith_variables {locals : List ScalarBinding} {value : BooleanLocal}
    {compile : (operand : Lean.Expr) → operand ∈ value.operands → Option LeanExe.IR.Expr}
    {target : LeanExe.IR.Cond} (compiled : extractBooleanLocalWith locals value compile = some target) :
    value.VariablesTyped (locals.map ScalarBinding.kind) := by
  intro index member
  obtain ⟨expression, found⟩ := extractBooleanLocal_variables value _ compile compiled index member
  exact scalarBoolean_kind found

theorem extractBooleanLocalWith_operands {locals : List ScalarBinding} {value : BooleanLocal}
    {compile : (operand : Lean.Expr) → operand ∈ value.operands → Option LeanExe.IR.Expr}
    {target : LeanExe.IR.Cond} (compiled : extractBooleanLocalWith locals value compile = some target) :
    ∀ operand member, ∃ expression, compile operand member = some expression :=
  extractBooleanLocal_operands value _ compile compiled

theorem extractBooleanLocalWith_correct {locals : List ScalarBinding} {values : List Value}
    {store : LeanExe.IR.ScalarStore} (value : BooleanLocal)
    (compile : (operand : Lean.Expr) → operand ∈ value.operands → Option LeanExe.IR.Expr)
    (native : Lean.Expr → UInt64) (booleans : Nat → Bool) {target : LeanExe.IR.Cond}
    (compiled : extractBooleanLocalWith locals value compile = some target)
    (bindings : ScalarBindingsMatch locals values store)
    (variables : value.VariablesMean values booleans)
    (operands : ∀ operand member expression, compile operand member = some expression →
      expression.ScalarEval store (native operand) store) :
    target.ScalarEval store (value.denote native booleans) store := by
  exact extractBooleanLocal_correct value _ compile native booleans compiled
    (fun index member expression found => bindings.boolean found (variables index member)) operands

theorem extractBooleanLocalWith_choice (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {locals : List ScalarBinding} (value : BooleanLocal)
    (compile : (operand : Lean.Expr) → operand ∈ value.operands → Option LeanExe.IR.Expr)
    {target : LeanExe.IR.Cond} (compiled : extractBooleanLocalWith locals value compile = some target)
    (bindings : ∀ binding ∈ locals, binding.Holds P)
    (operands : ∀ operand member expression, compile operand member = some expression → P expression) :
    ∀ t e, P t → P e → P (.ite target t e) := by
  apply extractBooleanLocal_choice P literal binary choice value _ compile compiled _ operands
  intro index member expression found
  obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
  have same := ScalarBinding.boolean?_some.mp matched
  subst binding
  exact bindings _ (List.mem_of_getElem? present)

end LeanExe.Extract.Core
