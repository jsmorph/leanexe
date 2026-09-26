import LeanExe.Extract.ScalarBooleanLocalFacts

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (BooleanLocal booleanLetExpr booleanWordLetExpr booleanLetBooleans)

theorem extractBooleanLocal_correct (guard : BooleanLocal) (compileFunctions : BooleanFunctionLookup)
    (compileVariables : (index : Nat) → index ∈ guard.variables → Option LeanExe.IR.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    (native : Lean.Expr → UInt64) (booleans : LeanExe.Source.Scalar.BooleanEnvironment) {target : LeanExe.IR.Cond} {store : LeanExe.IR.ScalarStore}
    (compiled : extractBooleanLocal compileFunctions guard compileVariables compile = some target)
    (booleanMeanings : ∀ index member expression, compileVariables index member = some expression →
      expression.ScalarEval store (Bool.toUInt64 (booleans index)) store)
    (meanings : ∀ operand member expression, compile operand member = some expression →
      expression.ScalarEval store (native operand) store)
    (functionMeanings : compileFunctions.Meaning guard.functions booleans.predicates store) :
    target.ScalarEval store (guard.denote native booleans) store := by
  induction guard generalizing target native booleans compileFunctions with
  | var n index =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨value, hv, rfl⟩ := compiled
    exact lowerGuardNegations_correct n (wordGuard_correct (booleanMeanings _ _ _ hv))
  | predicate n index argument =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨function, hf, value, hv, result, hr, rfl⟩ := compiled
    exact lowerGuardNegations_correct n (wordGuard_correct
      (functionMeanings index (by simp [BooleanLocal.functions]) function hf value (native argument) result
        (meanings _ _ _ hv) hr))
  | literal n value =>
    simp only [extractBooleanLocal, Option.some.injEq] at compiled
    subst target
    exact lowerGuardLiteral_correct _ _
  | compare op a b =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    simpa only [BooleanLocal.denote, LeanExe.Source.Scalar.BooleanGuard.comparison_denote] using
      lowerComparison_correct (LeanExe.Source.Scalar.BooleanGuard.comparison op) (meanings _ _ _ hl) (meanings _ _ _ hr)
  | junction n op a b iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact lowerGuardNegations_correct n (lowerJunction_correct op
      (iha (compileFunctions := compileFunctions) (functionMeanings := functionMeanings.left) _ _ native booleans hl (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found))
      (ihb (compileFunctions := compileFunctions) (functionMeanings := functionMeanings.right) _ _ native booleans hr (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found)))
  | equality n unequal a b iha ihb
  | relationDecision n unequal a b iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    simp only [BooleanLocal.denote, LeanExe.Source.Scalar.booleanRelationDecision_correct]
    exact lowerGuardNegations_correct n (lowerBooleanEquality_correct unequal
      (iha (compileFunctions := compileFunctions) (functionMeanings := functionMeanings.left) _ _ native booleans hl (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found))
      (ihb (compileFunctions := compileFunctions) (functionMeanings := functionMeanings.right) _ _ native booleans hr (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found)))
  | choice n unequal a b t e iha ihb iht ihe
  | dependentChoice n shape unequal a b t e iha ihb iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, yes, ht, no, he, rfl⟩ := compiled
    simp only [BooleanLocal.denote, LeanExe.Source.Scalar.booleanRelationDecision_correct]
    exact lowerGuardNegations_correct n (lowerBooleanChoice_correct
      (lowerBooleanChoiceCondition_correct unequal b.isTrueLiteral
        (iha (compileFunctions := compileFunctions) (functionMeanings := functionMeanings.left) _ _ native booleans hl (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found))
        (ihb (compileFunctions := compileFunctions) (functionMeanings := functionMeanings.right.left) _ _ native booleans hr (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found))
        (fun literal => BooleanLocal.isTrueLiteral_denote native booleans literal))
      (iht (compileFunctions := compileFunctions) (functionMeanings := functionMeanings.right.right.left) _ _ native booleans ht (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found))
      (ihe (compileFunctions := compileFunctions) (functionMeanings := functionMeanings.right.right.right) _ _ native booleans he (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found)))
  | proposition n g t e iht ihe
  | dependentProposition n shape g t e iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨test, hc, yes, ht, no, he, rfl⟩ := compiled
    exact lowerGuardNegations_correct n (lowerBooleanChoice_correct
      (extractGuard_correct g.value _ native hc (fun operand member expression found => meanings _ _ _ found))
      (iht (compileFunctions := compileFunctions) (functionMeanings := functionMeanings.left) _ _ native booleans ht (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found))
      (ihe (compileFunctions := compileFunctions) (functionMeanings := functionMeanings.right) _ _ native booleans he (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found)))
  | decision n g =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    exact lowerGuardNegations_correct n (extractGuard_correct g.value compile native hc meanings)

  | binding n name form value body type ihv ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    have first := ihv (compileFunctions := compileFunctions) (functionMeanings := functionMeanings.left) _ _ native booleans hl
      (fun index member expression found => booleanMeanings _ _ _ found)
      (fun operand member expression found => meanings _ _ _ found)
    apply lowerGuardNegations_correct n
    exact ihb (compileFunctions := compileFunctions.shift) (functionMeanings := BooleanFunctionLookup.Meaning.shift (value.denote native booleans) functionMeanings.right) _ _ (fun operand => native (booleanLetExpr name form.nondep value.expr operand))
      (booleans.bind (value.denote native booleans)) hr
      (booleanLetLookup_correct _ _ _ _ _ _ (guardWord_correct first)
        (fun index member expression found => booleanMeanings _ _ _ found))
      (fun operand member expression found => meanings _ _ _ found)

  | wordBinding n name form value body type ihb =>
    simp only [extractBooleanLocal] at compiled
    split at compiled
    · rename_i noLocal
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨word, hv, condition, hb, rfl⟩ := compiled
      apply lowerGuardNegations_correct n
      exact ihb (compileFunctions := compileFunctions.shift) (functionMeanings := BooleanFunctionLookup.Meaning.shift false functionMeanings) _ _ (fun operand => native (booleanWordLetExpr name form.nondep value operand))
        (booleans.bind false) hb
        (booleanWordLetLookup_correct _ _ _ _ _ booleanMeanings)
        (fun operand member expression found => meanings _ _ _ found)
    · contradiction
  | wrapped n wrapper body ih =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    simpa only [BooleanLocal.denote, LeanExe.Source.Scalar.BooleanWrapper.denote_eq] using
      lowerGuardNegations_correct n (ih (compileFunctions := compileFunctions) (functionMeanings := functionMeanings) compileVariables compile native booleans hc booleanMeanings meanings)


theorem extractBooleanLocal_choice (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (guard : BooleanLocal) (compileFunctions : BooleanFunctionLookup)
    (compileVariables : (index : Nat) → index ∈ guard.variables → Option LeanExe.IR.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    {target : LeanExe.IR.Cond} (compiled : extractBooleanLocal compileFunctions guard compileVariables compile = some target)
    (variables : ∀ index member expression, compileVariables index member = some expression → P expression)
    (operands : ∀ operand member expression, compile operand member = some expression → P expression)
    (functionHolds : compileFunctions.Holds guard.functions P) :
    ∀ t e, P t → P e → P (.ite target t e) := by
  induction guard generalizing target compileFunctions with
  | var n index =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨value, hv, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (fun t e ht he => choice .eq _ _ _ _ (variables _ _ _ hv) (literal 1) ht he)
  | predicate n index argument =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨function, hf, value, hv, result, hr, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (fun t e ht he => choice .eq _ _ _ _
        (functionHolds index (by simp [BooleanLocal.functions]) function hf value result (operands _ _ _ hv) hr)
        (literal 1) ht he)
  | literal n value =>
    simp only [extractBooleanLocal, Option.some.injEq] at compiled
    subst target
    exact lowerGuardLiteral_choice P literal choice _
  | compare op a b =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact fun t e ht he => choice (LeanExe.Source.Scalar.BooleanGuard.comparison op) _ _ _ _ (operands _ _ _ hl) (operands _ _ _ hr) ht he
  | junction n op a b iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (lowerJunction_choice P literal binary choice op left right
        (iha (compileFunctions := compileFunctions) (functionHolds := functionHolds.left) _ _ hl (fun index member expression found => variables _ _ _ found)
        (fun operand member expression found => operands _ _ _ found))
        (ihb (compileFunctions := compileFunctions) (functionHolds := functionHolds.right) _ _ hr (fun index member expression found => variables _ _ _ found)
        (fun operand member expression found => operands _ _ _ found)))
  | equality n unequal a b iha ihb
  | relationDecision n unequal a b iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (lowerBooleanEquality_choice P literal choice unequal left right
        (iha (compileFunctions := compileFunctions) (functionHolds := functionHolds.left) _ _ hl (fun index member expression found => variables _ _ _ found)
        (fun operand member expression found => operands _ _ _ found))
        (ihb (compileFunctions := compileFunctions) (functionHolds := functionHolds.right) _ _ hr (fun index member expression found => variables _ _ _ found)
        (fun operand member expression found => operands _ _ _ found)))
  | choice n unequal a b t e iha ihb iht ihe
  | dependentChoice n shape unequal a b t e iha ihb iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, yes, ht, no, he, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (lowerBooleanChoice_choice P literal choice (lowerBooleanChoiceCondition unequal b.isTrueLiteral left right) yes no
        (lowerBooleanChoiceCondition_choice P literal choice unequal b.isTrueLiteral left right
          (iha (compileFunctions := compileFunctions) (functionHolds := functionHolds.left) _ _ hl (fun index member expression found => variables _ _ _ found)
        (fun operand member expression found => operands _ _ _ found))
          (ihb (compileFunctions := compileFunctions) (functionHolds := functionHolds.right.left) _ _ hr (fun index member expression found => variables _ _ _ found)
        (fun operand member expression found => operands _ _ _ found)))
        (iht (compileFunctions := compileFunctions) (functionHolds := functionHolds.right.right.left) _ _ ht (fun index member expression found => variables _ _ _ found)
        (fun operand member expression found => operands _ _ _ found))
        (ihe (compileFunctions := compileFunctions) (functionHolds := functionHolds.right.right.right) _ _ he (fun index member expression found => variables _ _ _ found)
        (fun operand member expression found => operands _ _ _ found)))
  | proposition n g t e iht ihe
  | dependentProposition n shape g t e iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨test, hc, yes, ht, no, he, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (lowerBooleanChoice_choice P literal choice test yes no
        (extractGuard_choice P literal binary choice g.value _ hc
          (fun operand member expression found => operands _ _ _ found))
        (iht (compileFunctions := compileFunctions) (functionHolds := functionHolds.left) _ _ ht (fun index member expression found => variables _ _ _ found)
          (fun operand member expression found => operands _ _ _ found))
        (ihe (compileFunctions := compileFunctions) (functionHolds := functionHolds.right) _ _ he (fun index member expression found => variables _ _ _ found)
          (fun operand member expression found => operands _ _ _ found)))
  | decision n g =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (extractGuard_choice P literal binary choice g.value compile hc operands)
  | binding n name form value body type ihv ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    have first := ihv (compileFunctions := compileFunctions) (functionHolds := functionHolds.left) _ _ hl
      (fun index member expression found => variables _ _ _ found)
      (fun operand member expression found => operands _ _ _ found)
    exact lowerGuardNegations_choice P literal choice n _
      (ihb (compileFunctions := compileFunctions.shift) (functionHolds := functionHolds.right.shift) _ _ hr
        (booleanLetLookup_holds P _ _ _ (first _ _ (literal 1) (literal 0))
          (fun index member expression found => variables _ _ _ found))
        (fun operand member expression found => operands _ _ _ found))
  | wordBinding n name form value body type ihb =>
    simp only [extractBooleanLocal] at compiled
    split at compiled
    · rename_i noLocal
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨word, hv, condition, hb, rfl⟩ := compiled
      exact lowerGuardNegations_choice P literal choice n _
        (ihb (compileFunctions := compileFunctions.shift) (functionHolds := functionHolds.shift) _ _ hb (booleanWordLetLookup_holds P _ _ _ variables)
          (fun operand member expression found => operands _ _ _ found))
    · contradiction
  | wrapped n wrapper body ih =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (ih (compileFunctions := compileFunctions) (functionHolds := functionHolds) compileVariables compile hc variables operands)


end LeanExe.Extract.Core
