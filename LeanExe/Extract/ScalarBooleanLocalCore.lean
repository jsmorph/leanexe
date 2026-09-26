import LeanExe.Extract.ScalarGuard
import LeanExe.Extract.ScalarBooleanChoiceLowering
import LeanExe.Extract.ScalarBooleanFunctionLookup
import LeanExe.Extract.ScalarBooleanLetVariables
import LeanExe.Source.ScalarBooleanLocal

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (BooleanLocal booleanLetExpr booleanWordLetExpr booleanLetBooleans)

/-- The callback only receives operands of this exact parsed guard. Membership
allows the surrounding source compiler to prove its recursive calls decrease. -/
def extractBooleanLocal (compileFunctions : BooleanFunctionLookup) : (guard : BooleanLocal) →
    ((index : Nat) → index ∈ guard.variables → Option LeanExe.IR.Expr) →
    ((operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr) → Option LeanExe.IR.Cond
  | .var n index, compileVariables, _ => do
      let expression ← compileVariables index (by simp [BooleanLocal.variables])
      pure (lowerGuardNegations n (wordGuard expression))
  | .predicate n index argument, _, compile => do
      let function ← compileFunctions index
      let value ← compile argument (by simp [BooleanLocal.operands])
      let result ← function value
      pure (lowerGuardNegations n (wordGuard result))
  | .literal n value, _, _ => some (lowerGuardLiteral (LeanExe.Source.Scalar.GuardNegation.denote n value))
  | .compare op a b, _, compile => do
      let left ← compile a (by simp [BooleanLocal.operands])
      let right ← compile b (by simp [BooleanLocal.operands])
      pure (lowerComparison (LeanExe.Source.Scalar.BooleanGuard.comparison op) left right)
  | .junction n op a b, compileVariables, compile => do
      let left ← extractBooleanLocal compileFunctions a (fun index member => compileVariables index (List.mem_append_left _ member))
        (fun operand member => compile operand (List.mem_append_left _ member))
      let right ← extractBooleanLocal compileFunctions b (fun index member => compileVariables index (List.mem_append_right _ member))
        (fun operand member => compile operand (List.mem_append_right _ member))
      pure (lowerGuardNegations n (lowerJunction op left right))
  | .equality n unequal a b, compileVariables, compile
  | .relationDecision n unequal a b, compileVariables, compile => do
      let left ← extractBooleanLocal compileFunctions a (fun index member => compileVariables index (List.mem_append_left _ member))
        (fun operand member => compile operand (List.mem_append_left _ member))
      let right ← extractBooleanLocal compileFunctions b (fun index member => compileVariables index (List.mem_append_right _ member))
        (fun operand member => compile operand (List.mem_append_right _ member))
      pure (lowerGuardNegations n (lowerBooleanEquality unequal left right))
  | .choice n unequal a b t e, compileVariables, compile
  | .dependentChoice n _ unequal a b t e, compileVariables, compile => do
      let left ← extractBooleanLocal compileFunctions a (fun index member => compileVariables index (List.mem_append_left _ member))
        (fun operand member => compile operand (List.mem_append_left _ member))
      let right ← extractBooleanLocal compileFunctions b (fun index member => compileVariables index (List.mem_append_right _ (List.mem_append_left _ member)))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_left _ member)))
      let yes ← extractBooleanLocal compileFunctions t (fun index member => compileVariables index (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ member))))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ member))))
      let no ← extractBooleanLocal compileFunctions e (fun index member => compileVariables index (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (member)))))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (member)))))
      pure (lowerGuardNegations n (lowerBooleanChoice (lowerBooleanChoiceCondition unequal b.isTrueLiteral left right) yes no))
  | .proposition n g t e, compileVariables, compile
  | .dependentProposition n _ g t e, compileVariables, compile => do
      let test ← extractGuard g.value (fun operand member => compile operand (List.mem_append_left _ member))
      let yes ← extractBooleanLocal compileFunctions t (fun index member => compileVariables index (List.mem_append_left _ member))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_left _ member)))
      let no ← extractBooleanLocal compileFunctions e (fun index member => compileVariables index (List.mem_append_right _ member))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_right _ member)))
      pure (lowerGuardNegations n (lowerBooleanChoice test yes no))
  | .binding n name form value body _, compileVariables, compile => do
      let left ← extractBooleanLocal compileFunctions value (fun index member => compileVariables index (List.mem_append_left _ member)) (fun operand member => compile operand (List.mem_append_left _ member))
      let right ← extractBooleanLocal compileFunctions.shift body (booleanLetLookup body.variables (guardWord left) (fun index member => compileVariables index (List.mem_append_right _ member))) (fun operand member => compile (booleanLetExpr name form.nondep value.expr operand) (List.mem_append_right _ (List.mem_map.mpr ⟨operand, member, rfl⟩)))
      pure (lowerGuardNegations n right)
  | .wordBinding n name form value body _, compileVariables, compile =>
      if noLocal : 0 ∉ body.variables then do
        let _word ← compile value (by simp [BooleanLocal.operands])
        let condition ← extractBooleanLocal compileFunctions.shift body (booleanWordLetLookup body.variables noLocal compileVariables) (fun operand member => compile (booleanWordLetExpr name form.nondep value operand) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨operand, member, rfl⟩)))
        pure (lowerGuardNegations n condition)
      else none
  | .wrapped n _ body, compileVariables, compile => do
      let condition ← extractBooleanLocal compileFunctions body compileVariables compile
      pure (lowerGuardNegations n condition)
  | .decision n g, _, compile => do
      let condition ← extractGuard g.value compile
      pure (lowerGuardNegations n condition)


end LeanExe.Extract.Core
