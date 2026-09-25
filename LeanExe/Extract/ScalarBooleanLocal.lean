import LeanExe.Extract.ScalarGuard
import LeanExe.Source.ScalarBooleanLocal

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (BooleanLocal)

/-- The callback only receives operands of this exact parsed guard. Membership
allows the surrounding source compiler to prove its recursive calls decrease. -/
def extractBooleanLocal : (guard : BooleanLocal) →
    ((index : Nat) → index ∈ guard.variables → Option LeanExe.IR.Expr) →
    ((operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr) → Option LeanExe.IR.Cond
  | .var n index, compileVariables, _ => do
      let expression ← compileVariables index (by simp [BooleanLocal.variables])
      pure (lowerGuardNegations n (wordGuard expression))
  | .literal n value, _, _ => some (lowerGuardLiteral (LeanExe.Source.Scalar.GuardNegation.denote n value))
  | .compare op a b, _, compile => do
      let left ← compile a (by simp [BooleanLocal.operands])
      let right ← compile b (by simp [BooleanLocal.operands])
      pure (lowerComparison (LeanExe.Source.Scalar.BooleanGuard.comparison op) left right)
  | .junction n op a b, compileVariables, compile => do
      let left ← extractBooleanLocal a (fun index member => compileVariables index (List.mem_append_left _ member))
        (fun operand member => compile operand (List.mem_append_left _ member))
      let right ← extractBooleanLocal b (fun index member => compileVariables index (List.mem_append_right _ member))
        (fun operand member => compile operand (List.mem_append_right _ member))
      pure (lowerGuardNegations n (lowerJunction op left right))
  | .choice n c t e, compileVariables, compile => do
      let test ← extractBooleanLocal c (fun index member => compileVariables index (List.mem_append_left _ member))
        (fun operand member => compile operand (List.mem_append_left _ member))
      let yes ← extractBooleanLocal t (fun index member => compileVariables index (List.mem_append_right _ (List.mem_append_left _ member)))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_left _ member)))
      let no ← extractBooleanLocal e (fun index member => compileVariables index (List.mem_append_right _ (List.mem_append_right _ member)))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_right _ member)))
      pure (lowerGuardNegations n (lowerBooleanChoice test yes no))
  | .proposition n g t e, compileVariables, compile => do
      let test ← extractGuard g.value (fun operand member => compile operand (List.mem_append_left _ member))
      let yes ← extractBooleanLocal t (fun index member => compileVariables index (List.mem_append_left _ member))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_left _ member)))
      let no ← extractBooleanLocal e (fun index member => compileVariables index (List.mem_append_right _ member))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_right _ member)))
      pure (lowerGuardNegations n (lowerBooleanChoice test yes no))
  | .decision n g, _, compile => do
      let condition ← extractGuard g compile
      pure (lowerGuardNegations n condition)


theorem extractBooleanLocal_accepts (guard : BooleanLocal)
    (compileVariables : (index : Nat) → index ∈ guard.variables → Option LeanExe.IR.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    (totalVariables : ∀ index member, ∃ target, compileVariables index member = some target)
    (total : ∀ operand member, ∃ target, compile operand member = some target) :
    ∃ target, extractBooleanLocal guard compileVariables compile = some target := by
  induction guard with
  | var n index =>
    obtain ⟨value, hv⟩ := totalVariables index (by simp [BooleanLocal.variables])
    exact ⟨lowerGuardNegations n (wordGuard value), by simp [extractBooleanLocal, hv]⟩
  | literal n value => exact ⟨_, rfl⟩
  | compare op a b =>
    obtain ⟨left, hl⟩ := total a (by simp [BooleanLocal.operands])
    obtain ⟨right, hr⟩ := total b (by simp [BooleanLocal.operands])
    exact ⟨lowerComparison (LeanExe.Source.Scalar.BooleanGuard.comparison op) left right, by simp [extractBooleanLocal, hl, hr]⟩
  | junction n op a b iha ihb =>
    obtain ⟨left, hl⟩ := iha (fun index member => compileVariables index (List.mem_append_left _ member))
      (fun operand member => compile operand (List.mem_append_left _ member))
      (fun index member => totalVariables index _)
      (fun operand member => total operand _)
    obtain ⟨right, hr⟩ := ihb (fun index member => compileVariables index (List.mem_append_right _ member))
      (fun operand member => compile operand (List.mem_append_right _ member))
      (fun index member => totalVariables index _)
      (fun operand member => total operand _)
    exact ⟨lowerGuardNegations n (lowerJunction op left right), by simp [extractBooleanLocal, hl, hr]⟩
  | choice n c t e ihc iht ihe =>
    obtain ⟨test, hc⟩ := ihc (fun index member => compileVariables index (List.mem_append_left _ member))
      (fun operand member => compile operand (List.mem_append_left _ member))
      (fun index member => totalVariables index _)
      (fun operand member => total operand _)
    obtain ⟨yes, ht⟩ := iht (fun index member => compileVariables index (List.mem_append_right _ (List.mem_append_left _ member)))
      (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_left _ member)))
      (fun index member => totalVariables index _)
      (fun operand member => total operand _)
    obtain ⟨no, he⟩ := ihe (fun index member => compileVariables index (List.mem_append_right _ (List.mem_append_right _ member)))
      (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_right _ member)))
      (fun index member => totalVariables index _)
      (fun operand member => total operand _)
    exact ⟨lowerGuardNegations n (lowerBooleanChoice test yes no), by simp [extractBooleanLocal, hc, ht, he]⟩
  | proposition n g t e iht ihe =>
    obtain ⟨test, hc⟩ := extractGuard_accepts g.value
      (fun operand member => compile operand (List.mem_append_left _ member))
      (fun operand member => total operand _)
    obtain ⟨yes, ht⟩ := iht (fun index member => compileVariables index (List.mem_append_left _ member))
      (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_left _ member)))
      (fun index member => totalVariables index _) (fun operand member => total operand _)
    obtain ⟨no, he⟩ := ihe (fun index member => compileVariables index (List.mem_append_right _ member))
      (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_right _ member)))
      (fun index member => totalVariables index _) (fun operand member => total operand _)
    exact ⟨lowerGuardNegations n (lowerBooleanChoice test yes no), by simp [extractBooleanLocal, hc, ht, he]⟩
  | decision n g =>
    obtain ⟨condition, hc⟩ := extractGuard_accepts g compile total
    exact ⟨lowerGuardNegations n condition, by simp [extractBooleanLocal, hc]⟩

theorem extractBooleanLocal_operands (guard : BooleanLocal)
    (compileVariables : (index : Nat) → index ∈ guard.variables → Option LeanExe.IR.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    {target : LeanExe.IR.Cond} (compiled : extractBooleanLocal guard compileVariables compile = some target) :
    ∀ operand member, ∃ expression, compile operand member = some expression := by
  induction guard generalizing target with
  | var n index | literal n index =>
    intro operand member
    simp [BooleanLocal.operands] at member
  | compare op a b =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro operand member
    simp only [BooleanLocal.operands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨left, hl⟩
    · exact ⟨right, hr⟩
  | junction n op a b iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro operand member
    rcases List.mem_append.mp member with first | second
    · exact iha _ _ hl operand first
    · exact ihb _ _ hr operand second
  | choice n c t e ihc iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨test, hc, yes, ht, no, he, _⟩ := compiled
    intro operand member
    rcases List.mem_append.mp member with first | rest
    · exact ihc _ _ hc operand first
    · rcases List.mem_append.mp rest with second | third
      · exact iht _ _ ht operand second
      · exact ihe _ _ he operand third
  | proposition n g t e iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨test, hc, yes, ht, no, he, _⟩ := compiled
    intro operand member
    rcases List.mem_append.mp member with first | rest
    · exact extractGuard_operands g.value _ hc operand first
    · rcases List.mem_append.mp rest with second | third
      · exact iht _ _ ht operand second
      · exact ihe _ _ he operand third
  | decision n g =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, _⟩ := compiled
    exact extractGuard_operands g compile hc

theorem extractBooleanLocal_variables (guard : BooleanLocal)
    (compileVariables : (index : Nat) → index ∈ guard.variables → Option LeanExe.IR.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    {target : LeanExe.IR.Cond} (compiled : extractBooleanLocal guard compileVariables compile = some target) :
    ∀ index member, ∃ expression, compileVariables index member = some expression := by
  induction guard generalizing target with
  | literal | compare | decision =>
    intro index member
    simp [BooleanLocal.variables] at member
  | var n index =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨expression, found, _⟩ := compiled
    intro other member
    have same : other = index := by simpa [BooleanLocal.variables] using member
    subst other
    exact ⟨expression, found⟩
  | junction n op a b iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro index member
    rcases List.mem_append.mp member with first | second
    · exact iha _ _ hl index first
    · exact ihb _ _ hr index second
  | choice n c t e ihc iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨test, hc, yes, ht, no, he, _⟩ := compiled
    intro index member
    rcases List.mem_append.mp member with first | rest
    · exact ihc _ _ hc index first
    · rcases List.mem_append.mp rest with second | third
      · exact iht _ _ ht index second
      · exact ihe _ _ he index third
  | proposition n g t e iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨test, hc, yes, ht, no, he, _⟩ := compiled
    intro index member
    rcases List.mem_append.mp member with first | second
    · exact iht _ _ ht index first
    · exact ihe _ _ he index second

theorem extractBooleanLocal_correct (guard : BooleanLocal)
    (compileVariables : (index : Nat) → index ∈ guard.variables → Option LeanExe.IR.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    (native : Lean.Expr → UInt64) (booleans : Nat → Bool) {target : LeanExe.IR.Cond} {store : LeanExe.IR.ScalarStore}
    (compiled : extractBooleanLocal guard compileVariables compile = some target)
    (booleanMeanings : ∀ index member expression, compileVariables index member = some expression →
      expression.ScalarEval store (Bool.toUInt64 (booleans index)) store)
    (meanings : ∀ operand member expression, compile operand member = some expression →
      expression.ScalarEval store (native operand) store) :
    target.ScalarEval store (guard.denote native booleans) store := by
  induction guard generalizing target with
  | var n index =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨value, hv, rfl⟩ := compiled
    exact lowerGuardNegations_correct n (wordGuard_correct (booleanMeanings _ _ _ hv))
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
      (iha _ _ hl (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found))
      (ihb _ _ hr (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found)))
  | choice n c t e ihc iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨test, hc, yes, ht, no, he, rfl⟩ := compiled
    exact lowerGuardNegations_correct n (lowerBooleanChoice_correct
      (ihc _ _ hc (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found))
      (iht _ _ ht (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found))
      (ihe _ _ he (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found)))
  | proposition n g t e iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨test, hc, yes, ht, no, he, rfl⟩ := compiled
    exact lowerGuardNegations_correct n (lowerBooleanChoice_correct
      (extractGuard_correct g.value _ native hc (fun operand member expression found => meanings _ _ _ found))
      (iht _ _ ht (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found))
      (ihe _ _ he (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found)))
  | decision n g =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    exact lowerGuardNegations_correct n (extractGuard_correct g compile native hc meanings)

theorem extractBooleanLocal_choice (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (guard : BooleanLocal)
    (compileVariables : (index : Nat) → index ∈ guard.variables → Option LeanExe.IR.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    {target : LeanExe.IR.Cond} (compiled : extractBooleanLocal guard compileVariables compile = some target)
    (variables : ∀ index member expression, compileVariables index member = some expression → P expression)
    (operands : ∀ operand member expression, compile operand member = some expression → P expression) :
    ∀ t e, P t → P e → P (.ite target t e) := by
  induction guard generalizing target with
  | var n index =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨value, hv, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (fun t e ht he => choice .eq _ _ _ _ (variables _ _ _ hv) (literal 1) ht he)
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
        (iha _ _ hl (fun index member expression found => variables _ _ _ found)
        (fun operand member expression found => operands _ _ _ found))
        (ihb _ _ hr (fun index member expression found => variables _ _ _ found)
        (fun operand member expression found => operands _ _ _ found)))
  | choice n c t e ihc iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨test, hc, yes, ht, no, he, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (lowerBooleanChoice_choice P literal choice test yes no
        (ihc _ _ hc (fun index member expression found => variables _ _ _ found)
          (fun operand member expression found => operands _ _ _ found))
        (iht _ _ ht (fun index member expression found => variables _ _ _ found)
          (fun operand member expression found => operands _ _ _ found))
        (ihe _ _ he (fun index member expression found => variables _ _ _ found)
          (fun operand member expression found => operands _ _ _ found)))
  | proposition n g t e iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨test, hc, yes, ht, no, he, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (lowerBooleanChoice_choice P literal choice test yes no
        (extractGuard_choice P literal binary choice g.value _ hc
          (fun operand member expression found => operands _ _ _ found))
        (iht _ _ ht (fun index member expression found => variables _ _ _ found)
          (fun operand member expression found => operands _ _ _ found))
        (ihe _ _ he (fun index member expression found => variables _ _ _ found)
          (fun operand member expression found => operands _ _ _ found)))
  | decision n g =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (extractGuard_choice P literal binary choice g compile hc operands)

end LeanExe.Extract.Core
