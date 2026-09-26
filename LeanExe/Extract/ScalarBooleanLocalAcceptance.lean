import LeanExe.Extract.ScalarBooleanLocalCore

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (BooleanLocal booleanLetExpr booleanWordLetExpr booleanLetBooleans)

theorem extractBooleanLocal_accepts (guard : BooleanLocal) (compileFunctions : BooleanFunctionLookup)
    (compileVariables : (index : Nat) → index ∈ guard.variables → Option LeanExe.IR.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    (wellScoped : guard.WellScoped)
    (totalVariables : ∀ index member, ∃ target, compileVariables index member = some target)
    (total : ∀ operand member, ∃ target, compile operand member = some target)
    (totalFunctions : compileFunctions.Total guard.functions) :
    ∃ target, extractBooleanLocal compileFunctions guard compileVariables compile = some target := by
  induction guard generalizing compileFunctions with
  | var n index =>
    obtain ⟨value, hv⟩ := totalVariables index (by simp [BooleanLocal.variables])
    exact ⟨lowerGuardNegations n (wordGuard value), by simp [extractBooleanLocal, hv]⟩
  | predicate n index argument =>
    obtain ⟨function, hf, totalFunction⟩ := totalFunctions index (by simp [BooleanLocal.functions])
    obtain ⟨value, hv⟩ := total argument (by simp [BooleanLocal.operands])
    obtain ⟨result, hr⟩ := totalFunction value
    exact ⟨lowerGuardNegations n (wordGuard result), by simp [extractBooleanLocal, hf, hv, hr]⟩
  | literal n value => exact ⟨_, rfl⟩
  | compare op a b =>
    obtain ⟨left, hl⟩ := total a (by simp [BooleanLocal.operands])
    obtain ⟨right, hr⟩ := total b (by simp [BooleanLocal.operands])
    exact ⟨lowerComparison (LeanExe.Source.Scalar.BooleanGuard.comparison op) left right, by simp [extractBooleanLocal, hl, hr]⟩
  | junction n op a b iha ihb =>
    obtain ⟨left, hl⟩ := iha (compileFunctions := compileFunctions) (totalFunctions := totalFunctions.left) (wellScoped := wellScoped.1) (fun index member => compileVariables index (List.mem_append_left _ member))
      (fun operand member => compile operand (List.mem_append_left _ member))
      (fun index member => totalVariables index _)
      (fun operand member => total operand _)
    obtain ⟨right, hr⟩ := ihb (compileFunctions := compileFunctions) (totalFunctions := totalFunctions.right) (wellScoped := wellScoped.2) (fun index member => compileVariables index (List.mem_append_right _ member))
      (fun operand member => compile operand (List.mem_append_right _ member))
      (fun index member => totalVariables index _)
      (fun operand member => total operand _)
    exact ⟨lowerGuardNegations n (lowerJunction op left right), by simp [extractBooleanLocal, hl, hr]⟩
  | equality n unequal a b iha ihb
  | relationDecision n unequal a b iha ihb =>
    obtain ⟨left, hl⟩ := iha (compileFunctions := compileFunctions) (totalFunctions := totalFunctions.left) (wellScoped := wellScoped.1) (fun index member => compileVariables index (List.mem_append_left _ member))
      (fun operand member => compile operand (List.mem_append_left _ member))
      (fun index member => totalVariables index _)
      (fun operand member => total operand _)
    obtain ⟨right, hr⟩ := ihb (compileFunctions := compileFunctions) (totalFunctions := totalFunctions.right) (wellScoped := wellScoped.2) (fun index member => compileVariables index (List.mem_append_right _ member))
      (fun operand member => compile operand (List.mem_append_right _ member))
      (fun index member => totalVariables index _)
      (fun operand member => total operand _)
    exact ⟨lowerGuardNegations n (lowerBooleanEquality unequal left right), by simp [extractBooleanLocal, hl, hr]⟩
  | choice n unequal a b t e iha ihb iht ihe
  | dependentChoice n shape unequal a b t e iha ihb iht ihe =>
    obtain ⟨left, hl⟩ := iha (compileFunctions := compileFunctions) (totalFunctions := totalFunctions.left) (wellScoped := wellScoped.1) (fun index member => compileVariables index (List.mem_append_left _ member))
        (fun operand member => compile operand (List.mem_append_left _ member))
      (fun index member => totalVariables index _) (fun operand member => total operand _)
    obtain ⟨right, hr⟩ := ihb (compileFunctions := compileFunctions) (totalFunctions := totalFunctions.right.left) (wellScoped := wellScoped.2.1) (fun index member => compileVariables index (List.mem_append_right _ (List.mem_append_left _ member)))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_left _ member)))
      (fun index member => totalVariables index _) (fun operand member => total operand _)
    obtain ⟨yes, ht⟩ := iht (compileFunctions := compileFunctions) (totalFunctions := totalFunctions.right.right.left) (wellScoped := wellScoped.2.2.1) (fun index member => compileVariables index (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ member))))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ member))))
      (fun index member => totalVariables index _) (fun operand member => total operand _)
    obtain ⟨no, he⟩ := ihe (compileFunctions := compileFunctions) (totalFunctions := totalFunctions.right.right.right) (wellScoped := wellScoped.2.2.2) (fun index member => compileVariables index (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (member)))))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (member)))))
      (fun index member => totalVariables index _) (fun operand member => total operand _)
    exact ⟨lowerGuardNegations n (lowerBooleanChoice (lowerBooleanChoiceCondition unequal b.isTrueLiteral left right) yes no), by simp [extractBooleanLocal, hl, hr, ht, he]⟩
  | proposition n g t e iht ihe
  | dependentProposition n shape g t e iht ihe =>
    obtain ⟨test, hc⟩ := extractGuard_accepts g.value
      (fun operand member => compile operand (List.mem_append_left _ member))
      (fun operand member => total operand _)
    obtain ⟨yes, ht⟩ := iht (compileFunctions := compileFunctions) (totalFunctions := totalFunctions.left) (wellScoped := wellScoped.1) (fun index member => compileVariables index (List.mem_append_left _ member))
      (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_left _ member)))
      (fun index member => totalVariables index _) (fun operand member => total operand _)
    obtain ⟨no, he⟩ := ihe (compileFunctions := compileFunctions) (totalFunctions := totalFunctions.right) (wellScoped := wellScoped.2) (fun index member => compileVariables index (List.mem_append_right _ member))
      (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_right _ member)))
      (fun index member => totalVariables index _) (fun operand member => total operand _)
    exact ⟨lowerGuardNegations n (lowerBooleanChoice test yes no), by simp [extractBooleanLocal, hc, ht, he]⟩
  | binding n name form value body type ihv ihb =>
    obtain ⟨left, hl⟩ := ihv (compileFunctions := compileFunctions) (totalFunctions := totalFunctions.left) (wellScoped := wellScoped.1) (fun index member => compileVariables index (List.mem_append_left _ member)) (fun operand member => compile operand (List.mem_append_left _ member))
      (fun index member => totalVariables index _) (fun operand member => total operand _)
    obtain ⟨right, hr⟩ := ihb (compileFunctions := compileFunctions.shift) (totalFunctions := totalFunctions.right.shift wellScoped.2.2) (wellScoped := wellScoped.2.1) (booleanLetLookup body.variables (guardWord left) (fun index member => compileVariables index (List.mem_append_right _ member))) (fun operand member => compile (booleanLetExpr name form.nondep value.expr operand) (List.mem_append_right _ (List.mem_map.mpr ⟨operand, member, rfl⟩)))
      (booleanLetLookup_accepts _ _ _ (fun index member => totalVariables index _))
      (fun operand member => total _ _)
    exact ⟨lowerGuardNegations n right, by simp [extractBooleanLocal, hl, hr]⟩
  | decision n g =>
    obtain ⟨condition, hc⟩ := extractGuard_accepts g.value compile total
    exact ⟨lowerGuardNegations n condition, by simp [extractBooleanLocal, hc]⟩

  | wordBinding n name form value body type ihb =>
    have noLocal := wellScoped.1
    obtain ⟨word, hv⟩ := total value (by simp [BooleanLocal.operands])
    obtain ⟨condition, hb⟩ := ihb (compileFunctions := compileFunctions.shift) (totalFunctions := totalFunctions.shift wellScoped.2.2) (booleanWordLetLookup body.variables noLocal compileVariables) (fun operand member => compile (booleanWordLetExpr name form.nondep value operand) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨operand, member, rfl⟩))) wellScoped.2.1
      (booleanWordLetLookup_accepts _ _ _ totalVariables) (fun operand member => total _ _)
    exact ⟨lowerGuardNegations n condition, by simp [extractBooleanLocal, noLocal, hv, hb]⟩
  | wrapped n wrapper body ih =>
    obtain ⟨condition, hc⟩ := ih (compileFunctions := compileFunctions) (totalFunctions := totalFunctions) compileVariables compile wellScoped totalVariables total
    exact ⟨lowerGuardNegations n condition, by simp [extractBooleanLocal, hc]⟩


end LeanExe.Extract.Core
