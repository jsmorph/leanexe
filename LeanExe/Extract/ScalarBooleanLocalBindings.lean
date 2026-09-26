import LeanExe.Extract.ScalarBindings
import LeanExe.Extract.ScalarBooleanLocal
import LeanExe.Extract.ScalarBooleanLocalSyntax
import LeanExe.Source.ScalarBooleanLocalValues

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Flags, predicate functions and word operands use distinct typed lookups. -/
def extractBooleanLocalWith (locals : List ScalarBinding) (value : BooleanLocal)
    (compile : (operand : Lean.Expr) → operand ∈ value.operands → Option LeanExe.IR.Expr) :
    Option LeanExe.IR.Cond :=
  extractBooleanLocal (fun index => locals[index]?.bind ScalarBinding.predicateFunction?) value
    (fun index _ => locals[index]?.bind ScalarBinding.boolean?) compile

theorem extractBooleanLocalWith_accepts (locals : List ScalarBinding) (value : BooleanLocal)
    (compile : (operand : Lean.Expr) → operand ∈ value.operands → Option LeanExe.IR.Expr)
    (variables : value.VariablesTyped (locals.map ScalarBinding.kind))
    (operands : ∀ operand member, ∃ target, compile operand member = some target)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ target, extractBooleanLocalWith locals value compile = some target := by
  apply extractBooleanLocal_accepts value _ _ compile variables.wellScoped
    (fun index member => scalarBoolean_lookup (variables.flags index member)) operands
  intro index member
  obtain ⟨function, found⟩ := scalarPredicateFunction_lookup (variables.functions index member)
  refine ⟨function, ?_, total _ (List.mem_of_getElem? found)⟩
  simp [found, ScalarBinding.predicateFunction?]

theorem extractBooleanLocalWith_variables {locals : List ScalarBinding} {value : BooleanLocal}
    {compile : (operand : Lean.Expr) → operand ∈ value.operands → Option LeanExe.IR.Expr}
    {target : LeanExe.IR.Cond} (compiled : extractBooleanLocalWith locals value compile = some target) :
    value.VariablesTyped (locals.map ScalarBinding.kind) := by
  refine ⟨extractBooleanLocal_scoped value _ _ _ compiled, ?_, ?_⟩
  · intro index member
    obtain ⟨expression, found⟩ := extractBooleanLocal_variables value _ _ compile compiled index member
    exact scalarBoolean_kind found
  · intro index member
    obtain ⟨function, found⟩ := extractBooleanLocal_functions value _ _ compile compiled index member
    exact scalarPredicateFunction_kind found

theorem extractBooleanLocalWith_operands {locals : List ScalarBinding} {value : BooleanLocal}
    {compile : (operand : Lean.Expr) → operand ∈ value.operands → Option LeanExe.IR.Expr}
    {target : LeanExe.IR.Cond} (compiled : extractBooleanLocalWith locals value compile = some target) :
    ∀ operand member, ∃ expression, compile operand member = some expression :=
  extractBooleanLocal_operands value _ _ compile compiled

theorem extractBooleanLocalWith_correct {locals : List ScalarBinding} {values : List Value}
    {store : LeanExe.IR.ScalarStore} (value : BooleanLocal)
    (compile : (operand : Lean.Expr) → operand ∈ value.operands → Option LeanExe.IR.Expr)
    (native : Lean.Expr → UInt64) (booleans : BooleanEnvironment) {target : LeanExe.IR.Cond}
    (compiled : extractBooleanLocalWith locals value compile = some target)
    (bindings : ScalarBindingsMatch locals values store)
    (variables : value.VariablesMean values booleans)
    (operands : ∀ operand member expression, compile operand member = some expression →
      expression.ScalarEval store (native operand) store) :
    target.ScalarEval store (value.denote native booleans) store := by
  apply extractBooleanLocal_correct value _ _ compile native booleans compiled
    (fun index member expression found => bindings.boolean found (variables.flags index member)) operands
  intro index member function found argument nativeValue target argumentMeaning application
  exact bindings.predicateFunction found (variables.functions index member)
    argument nativeValue target argumentMeaning application

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
  refine extractBooleanLocal_choice P literal binary choice value _ _ compile compiled ?_ operands ?_
  · intro index member expression found
    obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
    have same := ScalarBinding.boolean?_some.mp matched
    subst binding
    exact bindings _ (List.mem_of_getElem? present)
  · intro index member function found
    obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
    have same := ScalarBinding.predicateFunction?_some.mp matched
    subst binding
    exact bindings _ (List.mem_of_getElem? present)

end LeanExe.Extract.Core
