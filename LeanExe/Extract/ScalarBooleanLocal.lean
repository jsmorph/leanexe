import LeanExe.Extract.ScalarGuard
import LeanExe.Extract.ScalarBooleanChoiceLowering
import LeanExe.Extract.ScalarBooleanLetVariables
import LeanExe.Source.ScalarBooleanLocal

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (BooleanLocal booleanLetExpr booleanWordLetExpr booleanLetBooleans)

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
  | .equality n unequal a b, compileVariables, compile
  | .relationDecision n unequal a b, compileVariables, compile => do
      let left ← extractBooleanLocal a (fun index member => compileVariables index (List.mem_append_left _ member))
        (fun operand member => compile operand (List.mem_append_left _ member))
      let right ← extractBooleanLocal b (fun index member => compileVariables index (List.mem_append_right _ member))
        (fun operand member => compile operand (List.mem_append_right _ member))
      pure (lowerGuardNegations n (lowerBooleanEquality unequal left right))
  | .choice n unequal a b t e, compileVariables, compile
  | .dependentChoice n _ unequal a b t e, compileVariables, compile => do
      let left ← extractBooleanLocal a (fun index member => compileVariables index (List.mem_append_left _ member))
        (fun operand member => compile operand (List.mem_append_left _ member))
      let right ← extractBooleanLocal b (fun index member => compileVariables index (List.mem_append_right _ (List.mem_append_left _ member)))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_left _ member)))
      let yes ← extractBooleanLocal t (fun index member => compileVariables index (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ member))))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ member))))
      let no ← extractBooleanLocal e (fun index member => compileVariables index (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (member)))))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (member)))))
      pure (lowerGuardNegations n (lowerBooleanChoice (lowerBooleanChoiceCondition unequal b.isTrueLiteral left right) yes no))
  | .proposition n g t e, compileVariables, compile
  | .dependentProposition n _ g t e, compileVariables, compile => do
      let test ← extractGuard g.value (fun operand member => compile operand (List.mem_append_left _ member))
      let yes ← extractBooleanLocal t (fun index member => compileVariables index (List.mem_append_left _ member))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_left _ member)))
      let no ← extractBooleanLocal e (fun index member => compileVariables index (List.mem_append_right _ member))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_right _ member)))
      pure (lowerGuardNegations n (lowerBooleanChoice test yes no))
  | .binding n name nondep value body, compileVariables, compile => do
      let left ← extractBooleanLocal value (fun index member => compileVariables index (List.mem_append_left _ member)) (fun operand member => compile operand (List.mem_append_left _ member))
      let right ← extractBooleanLocal body (booleanLetLookup body.variables (guardWord left) (fun index member => compileVariables index (List.mem_append_right _ member))) (fun operand member => compile (booleanLetExpr name nondep value.expr operand) (List.mem_append_right _ (List.mem_map.mpr ⟨operand, member, rfl⟩)))
      pure (lowerGuardNegations n right)
  | .wordBinding n name nondep value body, compileVariables, compile =>
      if noLocal : 0 ∉ body.variables then do
        let _word ← compile value (by simp [BooleanLocal.operands])
        let condition ← extractBooleanLocal body (booleanWordLetLookup body.variables noLocal compileVariables) (fun operand member => compile (booleanWordLetExpr name nondep value operand) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨operand, member, rfl⟩)))
        pure (lowerGuardNegations n condition)
      else none
  | .decision n g, _, compile => do
      let condition ← extractGuard g.value compile
      pure (lowerGuardNegations n condition)


theorem extractBooleanLocal_accepts (guard : BooleanLocal)
    (compileVariables : (index : Nat) → index ∈ guard.variables → Option LeanExe.IR.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    (wellScoped : guard.WellScoped)
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
    obtain ⟨left, hl⟩ := iha (wellScoped := wellScoped.1) (fun index member => compileVariables index (List.mem_append_left _ member))
      (fun operand member => compile operand (List.mem_append_left _ member))
      (fun index member => totalVariables index _)
      (fun operand member => total operand _)
    obtain ⟨right, hr⟩ := ihb (wellScoped := wellScoped.2) (fun index member => compileVariables index (List.mem_append_right _ member))
      (fun operand member => compile operand (List.mem_append_right _ member))
      (fun index member => totalVariables index _)
      (fun operand member => total operand _)
    exact ⟨lowerGuardNegations n (lowerJunction op left right), by simp [extractBooleanLocal, hl, hr]⟩
  | equality n unequal a b iha ihb
  | relationDecision n unequal a b iha ihb =>
    obtain ⟨left, hl⟩ := iha (wellScoped := wellScoped.1) (fun index member => compileVariables index (List.mem_append_left _ member))
      (fun operand member => compile operand (List.mem_append_left _ member))
      (fun index member => totalVariables index _)
      (fun operand member => total operand _)
    obtain ⟨right, hr⟩ := ihb (wellScoped := wellScoped.2) (fun index member => compileVariables index (List.mem_append_right _ member))
      (fun operand member => compile operand (List.mem_append_right _ member))
      (fun index member => totalVariables index _)
      (fun operand member => total operand _)
    exact ⟨lowerGuardNegations n (lowerBooleanEquality unequal left right), by simp [extractBooleanLocal, hl, hr]⟩
  | choice n unequal a b t e iha ihb iht ihe
  | dependentChoice n shape unequal a b t e iha ihb iht ihe =>
    obtain ⟨left, hl⟩ := iha (wellScoped := wellScoped.1) (fun index member => compileVariables index (List.mem_append_left _ member))
        (fun operand member => compile operand (List.mem_append_left _ member))
      (fun index member => totalVariables index _) (fun operand member => total operand _)
    obtain ⟨right, hr⟩ := ihb (wellScoped := wellScoped.2.1) (fun index member => compileVariables index (List.mem_append_right _ (List.mem_append_left _ member)))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_left _ member)))
      (fun index member => totalVariables index _) (fun operand member => total operand _)
    obtain ⟨yes, ht⟩ := iht (wellScoped := wellScoped.2.2.1) (fun index member => compileVariables index (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ member))))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ member))))
      (fun index member => totalVariables index _) (fun operand member => total operand _)
    obtain ⟨no, he⟩ := ihe (wellScoped := wellScoped.2.2.2) (fun index member => compileVariables index (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (member)))))
        (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (member)))))
      (fun index member => totalVariables index _) (fun operand member => total operand _)
    exact ⟨lowerGuardNegations n (lowerBooleanChoice (lowerBooleanChoiceCondition unequal b.isTrueLiteral left right) yes no), by simp [extractBooleanLocal, hl, hr, ht, he]⟩
  | proposition n g t e iht ihe
  | dependentProposition n shape g t e iht ihe =>
    obtain ⟨test, hc⟩ := extractGuard_accepts g.value
      (fun operand member => compile operand (List.mem_append_left _ member))
      (fun operand member => total operand _)
    obtain ⟨yes, ht⟩ := iht (wellScoped := wellScoped.1) (fun index member => compileVariables index (List.mem_append_left _ member))
      (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_left _ member)))
      (fun index member => totalVariables index _) (fun operand member => total operand _)
    obtain ⟨no, he⟩ := ihe (wellScoped := wellScoped.2) (fun index member => compileVariables index (List.mem_append_right _ member))
      (fun operand member => compile operand (List.mem_append_right _ (List.mem_append_right _ member)))
      (fun index member => totalVariables index _) (fun operand member => total operand _)
    exact ⟨lowerGuardNegations n (lowerBooleanChoice test yes no), by simp [extractBooleanLocal, hc, ht, he]⟩
  | binding n name nondep value body ihv ihb =>
    obtain ⟨left, hl⟩ := ihv (wellScoped := wellScoped.1) (fun index member => compileVariables index (List.mem_append_left _ member)) (fun operand member => compile operand (List.mem_append_left _ member))
      (fun index member => totalVariables index _) (fun operand member => total operand _)
    obtain ⟨right, hr⟩ := ihb (wellScoped := wellScoped.2) (booleanLetLookup body.variables (guardWord left) (fun index member => compileVariables index (List.mem_append_right _ member))) (fun operand member => compile (booleanLetExpr name nondep value.expr operand) (List.mem_append_right _ (List.mem_map.mpr ⟨operand, member, rfl⟩)))
      (booleanLetLookup_accepts _ _ _ (fun index member => totalVariables index _))
      (fun operand member => total _ _)
    exact ⟨lowerGuardNegations n right, by simp [extractBooleanLocal, hl, hr]⟩
  | decision n g =>
    obtain ⟨condition, hc⟩ := extractGuard_accepts g.value compile total
    exact ⟨lowerGuardNegations n condition, by simp [extractBooleanLocal, hc]⟩

  | wordBinding n name nondep value body ihb =>
    have noLocal := wellScoped.1
    obtain ⟨word, hv⟩ := total value (by simp [BooleanLocal.operands])
    obtain ⟨condition, hb⟩ := ihb (booleanWordLetLookup body.variables noLocal compileVariables) (fun operand member => compile (booleanWordLetExpr name nondep value operand) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨operand, member, rfl⟩))) wellScoped.2
      (booleanWordLetLookup_accepts _ _ _ totalVariables) (fun operand member => total _ _)
    exact ⟨lowerGuardNegations n condition, by simp [extractBooleanLocal, noLocal, hv, hb]⟩

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
  | equality n unequal a b iha ihb
  | relationDecision n unequal a b iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro operand member
    rcases List.mem_append.mp member with first | second
    · exact iha _ _ hl operand first
    · exact ihb _ _ hr operand second
  | choice n unequal a b t e iha ihb iht ihe
  | dependentChoice n shape unequal a b t e iha ihb iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, yes, ht, no, he, _⟩ := compiled
    intro operand member
    simp only [BooleanLocal.operands, List.mem_append] at member
    rcases member with member | member | member | member
    · exact iha _ _ hl operand member
    · exact ihb _ _ hr operand member
    · exact iht _ _ ht operand member
    · exact ihe _ _ he operand member
  | proposition n g t e iht ihe
  | dependentProposition n shape g t e iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨test, hc, yes, ht, no, he, _⟩ := compiled
    intro operand member
    rcases List.mem_append.mp member with first | rest
    · exact extractGuard_operands g.value _ hc operand first
    · rcases List.mem_append.mp rest with second | third
      · exact iht _ _ ht operand second
      · exact ihe _ _ he operand third
  | binding n name nondep value body ihv ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro operand member
    simp only [BooleanLocal.operands, List.mem_append, List.mem_map] at member
    rcases member with first | ⟨inner, innerMember, equality⟩
    · exact ihv _ _ hl operand first
    · subst operand
      exact ihb _ _ hr inner innerMember
  | decision n g =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, _⟩ := compiled
    exact extractGuard_operands g.value compile hc

  | wordBinding n name nondep value body ihb =>
    simp only [extractBooleanLocal] at compiled
    split at compiled
    · rename_i noLocal
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨word, hv, condition, hb, _⟩ := compiled
      intro operand member
      simp only [BooleanLocal.operands, List.mem_cons, List.mem_map] at member
      rcases member with equality | ⟨inner, innerMember, equality⟩
      · subst operand; exact ⟨word, hv⟩
      · subst operand; exact ihb _ _ hb inner innerMember
    · contradiction

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
  | equality n unequal a b iha ihb
  | relationDecision n unequal a b iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro index member
    rcases List.mem_append.mp member with first | second
    · exact iha _ _ hl index first
    · exact ihb _ _ hr index second
  | choice n unequal a b t e iha ihb iht ihe
  | dependentChoice n shape unequal a b t e iha ihb iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, yes, ht, no, he, _⟩ := compiled
    intro index member
    simp only [BooleanLocal.variables, List.mem_append] at member
    rcases member with member | member | member | member
    · exact iha _ _ hl index member
    · exact ihb _ _ hr index member
    · exact iht _ _ ht index member
    · exact ihe _ _ he index member
  | proposition n g t e iht ihe
  | dependentProposition n shape g t e iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨test, hc, yes, ht, no, he, _⟩ := compiled
    intro index member
    rcases List.mem_append.mp member with first | second
    · exact iht _ _ ht index first
    · exact ihe _ _ he index second
  | binding n name nondep value body ihv ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro index member
    rcases List.mem_append.mp member with first | second
    · exact ihv _ _ hl index first
    · exact booleanLetLookup_external _ _ _ (ihb _ _ hr) index second

  | wordBinding n name nondep value body ihb =>
    simp only [extractBooleanLocal] at compiled
    split at compiled
    · rename_i noLocal
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨word, hv, condition, hb, _⟩ := compiled
      exact booleanWordLetLookup_external _ _ _ (ihb _ _ hb)
    · contradiction

theorem extractBooleanLocal_scoped (guard : BooleanLocal)
    (compileVariables : (index : Nat) → index ∈ guard.variables → Option LeanExe.IR.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    {target : LeanExe.IR.Cond} (compiled : extractBooleanLocal guard compileVariables compile = some target) :
    guard.WellScoped := by
  induction guard generalizing target with
  | var | literal | compare | decision => trivial
  | junction n op a b iha ihb
  | equality n unequal a b iha ihb
  | relationDecision n unequal a b iha ihb
  | binding n name nondep a b iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    exact ⟨iha _ _ hl, ihb _ _ hr⟩
  | choice n unequal a b t e iha ihb iht ihe
  | dependentChoice n shape unequal a b t e iha ihb iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, yes, ht, no, he, _⟩ := compiled
    exact ⟨iha _ _ hl, ihb _ _ hr, iht _ _ ht, ihe _ _ he⟩
  | proposition n g t e iht ihe
  | dependentProposition n shape g t e iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨test, hc, yes, ht, no, he, _⟩ := compiled
    exact ⟨iht _ _ ht, ihe _ _ he⟩
  | wordBinding n name nondep value body ihb =>
    simp only [extractBooleanLocal] at compiled
    split at compiled
    · rename_i noLocal
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨word, hv, condition, hb, _⟩ := compiled
      exact ⟨noLocal, ihb _ _ hb⟩
    · contradiction

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
  induction guard generalizing target native booleans with
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
      (iha _ _ native booleans hl (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found))
      (ihb _ _ native booleans hr (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found)))
  | equality n unequal a b iha ihb
  | relationDecision n unequal a b iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    simp only [BooleanLocal.denote, LeanExe.Source.Scalar.booleanRelationDecision_correct]
    exact lowerGuardNegations_correct n (lowerBooleanEquality_correct unequal
      (iha _ _ native booleans hl (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found))
      (ihb _ _ native booleans hr (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found)))
  | choice n unequal a b t e iha ihb iht ihe
  | dependentChoice n shape unequal a b t e iha ihb iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, yes, ht, no, he, rfl⟩ := compiled
    simp only [BooleanLocal.denote, LeanExe.Source.Scalar.booleanRelationDecision_correct]
    exact lowerGuardNegations_correct n (lowerBooleanChoice_correct
      (lowerBooleanChoiceCondition_correct unequal b.isTrueLiteral
        (iha _ _ native booleans hl (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found))
        (ihb _ _ native booleans hr (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found))
        (fun literal => BooleanLocal.isTrueLiteral_denote native booleans literal))
      (iht _ _ native booleans ht (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found))
      (ihe _ _ native booleans he (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found)))
  | proposition n g t e iht ihe
  | dependentProposition n shape g t e iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨test, hc, yes, ht, no, he, rfl⟩ := compiled
    exact lowerGuardNegations_correct n (lowerBooleanChoice_correct
      (extractGuard_correct g.value _ native hc (fun operand member expression found => meanings _ _ _ found))
      (iht _ _ native booleans ht (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found))
      (ihe _ _ native booleans he (fun index member expression found => booleanMeanings _ _ _ found)
        (fun operand member expression found => meanings _ _ _ found)))
  | decision n g =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    exact lowerGuardNegations_correct n (extractGuard_correct g.value compile native hc meanings)

  | binding n name nondep value body ihv ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    have first := ihv _ _ native booleans hl
      (fun index member expression found => booleanMeanings _ _ _ found)
      (fun operand member expression found => meanings _ _ _ found)
    apply lowerGuardNegations_correct n
    exact ihb _ _ (fun operand => native (booleanLetExpr name nondep value.expr operand))
      (booleanLetBooleans (value.denote native booleans) booleans) hr
      (booleanLetLookup_correct _ _ _ _ _ _ (guardWord_correct first)
        (fun index member expression found => booleanMeanings _ _ _ found))
      (fun operand member expression found => meanings _ _ _ found)

  | wordBinding n name nondep value body ihb =>
    simp only [extractBooleanLocal] at compiled
    split at compiled
    · rename_i noLocal
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨word, hv, condition, hb, rfl⟩ := compiled
      apply lowerGuardNegations_correct n
      exact ihb _ _ (fun operand => native (booleanWordLetExpr name nondep value operand))
        (booleanLetBooleans false booleans) hb
        (booleanWordLetLookup_correct _ _ _ _ _ booleanMeanings)
        (fun operand member expression found => meanings _ _ _ found)
    · contradiction

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
  | equality n unequal a b iha ihb
  | relationDecision n unequal a b iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (lowerBooleanEquality_choice P literal choice unequal left right
        (iha _ _ hl (fun index member expression found => variables _ _ _ found)
        (fun operand member expression found => operands _ _ _ found))
        (ihb _ _ hr (fun index member expression found => variables _ _ _ found)
        (fun operand member expression found => operands _ _ _ found)))
  | choice n unequal a b t e iha ihb iht ihe
  | dependentChoice n shape unequal a b t e iha ihb iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, yes, ht, no, he, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (lowerBooleanChoice_choice P literal choice (lowerBooleanChoiceCondition unequal b.isTrueLiteral left right) yes no
        (lowerBooleanChoiceCondition_choice P literal choice unequal b.isTrueLiteral left right
          (iha _ _ hl (fun index member expression found => variables _ _ _ found)
        (fun operand member expression found => operands _ _ _ found))
          (ihb _ _ hr (fun index member expression found => variables _ _ _ found)
        (fun operand member expression found => operands _ _ _ found)))
        (iht _ _ ht (fun index member expression found => variables _ _ _ found)
        (fun operand member expression found => operands _ _ _ found))
        (ihe _ _ he (fun index member expression found => variables _ _ _ found)
        (fun operand member expression found => operands _ _ _ found)))
  | proposition n g t e iht ihe
  | dependentProposition n shape g t e iht ihe =>
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
      (extractGuard_choice P literal binary choice g.value compile hc operands)
  | binding n name nondep value body ihv ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    have first := ihv _ _ hl
      (fun index member expression found => variables _ _ _ found)
      (fun operand member expression found => operands _ _ _ found)
    exact lowerGuardNegations_choice P literal choice n _
      (ihb _ _ hr
        (booleanLetLookup_holds P _ _ _ (first _ _ (literal 1) (literal 0))
          (fun index member expression found => variables _ _ _ found))
        (fun operand member expression found => operands _ _ _ found))
  | wordBinding n name nondep value body ihb =>
    simp only [extractBooleanLocal] at compiled
    split at compiled
    · rename_i noLocal
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨word, hv, condition, hb, rfl⟩ := compiled
      exact lowerGuardNegations_choice P literal choice n _
        (ihb _ _ hb (booleanWordLetLookup_holds P _ _ _ variables)
          (fun operand member expression found => operands _ _ _ found))
    · contradiction

end LeanExe.Extract.Core
