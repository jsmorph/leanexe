import LeanExe.Extract.ScalarGuardSyntax
import LeanExe.Extract.ScalarBooleanPropositionLowering

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (Guard CompoundGuard BooleanGuard SavedBooleanGuard)

def lowerSavedBooleanGuard (_guard : SavedBooleanGuard) (value : LeanExe.IR.Expr) : LeanExe.IR.Cond :=
  wordGuard value

theorem lowerSavedBooleanGuard_correct (guard : SavedBooleanGuard)
    {value : LeanExe.IR.Expr} {word : UInt64} {store : LeanExe.IR.ScalarStore}
    (evaluated : value.ScalarEval store word store) :
    (lowerSavedBooleanGuard guard value).ScalarEval store
      (word == 1) store :=
  .eq evaluated .const

theorem lowerSavedBooleanGuard_choice (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (guard : SavedBooleanGuard) (value : LeanExe.IR.Expr) (valid : P value) :
    ∀ t e, P t → P e → P (.ite (lowerSavedBooleanGuard guard value) t e) :=
  fun t e ht he => choice .eq _ _ t e valid (literal 1) ht he

/-- The callback only receives operands of this exact parsed guard. Membership
allows the surrounding source compiler to prove its recursive calls decrease. -/
def extractGuard : (guard : Guard) →
    ((operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr) → Option LeanExe.IR.Cond
  | .literal value, _ => some (lowerGuardLiteral (value.denote))
  | .compare op a b, compile => do
      let left ← compile a (by simp [Guard.operands])
      let right ← compile b (by simp [Guard.operands])
      pure (lowerComparison op left right)
  | .junction n op a b, compile => do
      let left ← extractGuard a (fun operand member => compile operand (List.mem_append_left _ member))
      let right ← extractGuard b (fun operand member => compile operand (List.mem_append_right _ member))
      pure (lowerGuardNegations n (lowerJunction op left right))
  | .boolean m n op a b, compile => do
      let condition ← extractBooleanGuard (.junction n op a b) compile
      pure (lowerGuardNegations m condition)

  | .savedLeft n op a b, compile => do
      let left ← extractBooleanPropositionLeaf a (fun operand member => compile operand (List.mem_append_left _ member))
      let right ← extractGuard b (fun operand member => compile operand (List.mem_append_right _ member))
      pure (lowerGuardNegations n (lowerJunction op left right))
  | .savedRight n op a b, compile => do
      let left ← extractGuard a (fun operand member => compile operand (List.mem_append_left _ member))
      let right ← extractBooleanPropositionLeaf b (fun operand member => compile operand (List.mem_append_right _ member))
      pure (lowerGuardNegations n (lowerJunction op left right))
  | .savedBoth n op a b, compile => do
      let left ← extractBooleanPropositionLeaf a (fun operand member => compile operand (List.mem_append_left _ member))
      let right ← extractBooleanPropositionLeaf b (fun operand member => compile operand (List.mem_append_right _ member))
      pure (lowerGuardNegations n (lowerJunction op left right))

  | .letGuard n binding body, compile => do
      let _ ← compile binding.operand (by simp [Guard.operands])
      let condition ← extractGuard body (fun operand member =>
        compile (binding.wrap operand) (by exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨operand, member, rfl⟩)))
      pure (lowerGuardNegations n condition)
  | .letSaved n binding body, compile => do
      let _ ← compile binding.operand (by simp [Guard.operands])
      let value ← compile (binding.wrap body.operand) (by simp [Guard.operands])
      pure (lowerGuardNegations n (lowerSavedBooleanGuard body value))
  | .localNegation n value, compile => do
      let condition ← extractBooleanPropositionLeaf value compile
      pure (lowerGuardNegations (n + 1) condition)

theorem extractGuard_accepts (guard : Guard)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    (total : ∀ operand member, ∃ target, compile operand member = some target) :
    ∃ target, extractGuard guard compile = some target := by
  induction guard with
  | literal value => exact ⟨_, rfl⟩
  | compare op a b =>
    obtain ⟨left, hl⟩ := total a (by simp [Guard.operands])
    obtain ⟨right, hr⟩ := total b (by simp [Guard.operands])
    exact ⟨lowerComparison op left right, by simp [extractGuard, hl, hr]⟩
  | junction n op a b iha ihb =>
    obtain ⟨left, hl⟩ := iha (fun operand member => compile operand (List.mem_append_left _ member))
      (fun operand member => total operand _)
    obtain ⟨right, hr⟩ := ihb (fun operand member => compile operand (List.mem_append_right _ member))
      (fun operand member => total operand _)
    exact ⟨lowerGuardNegations n (lowerJunction op left right), by simp [extractGuard, hl, hr]⟩
  | boolean m n op a b =>
    obtain ⟨condition, hc⟩ := extractBooleanGuard_accepts (.junction n op a b) compile total
    exact ⟨lowerGuardNegations m condition, by simp [extractGuard, hc]⟩

  | savedLeft n op a b ihb =>
    obtain ⟨left, hl⟩ := extractBooleanPropositionLeaf_accepts a
      (fun operand member => compile operand (List.mem_append_left _ member)) (fun operand member => total operand _)
    obtain ⟨right, hr⟩ := ihb (fun operand member => compile operand (List.mem_append_right _ member))
      (fun operand member => total operand _)
    exact ⟨lowerGuardNegations n (lowerJunction op left right), by simp [extractGuard, hl, hr]⟩
  | savedRight n op a b iha =>
    obtain ⟨left, hl⟩ := iha (fun operand member => compile operand (List.mem_append_left _ member))
      (fun operand member => total operand _)
    obtain ⟨right, hr⟩ := extractBooleanPropositionLeaf_accepts b
      (fun operand member => compile operand (List.mem_append_right _ member)) (fun operand member => total operand _)
    exact ⟨lowerGuardNegations n (lowerJunction op left right), by simp [extractGuard, hl, hr]⟩
  | savedBoth n op a b =>
    obtain ⟨left, hl⟩ := extractBooleanPropositionLeaf_accepts a
      (fun operand member => compile operand (List.mem_append_left _ member)) (fun operand member => total operand _)
    obtain ⟨right, hr⟩ := extractBooleanPropositionLeaf_accepts b
      (fun operand member => compile operand (List.mem_append_right _ member)) (fun operand member => total operand _)
    exact ⟨lowerGuardNegations n (lowerJunction op left right), by simp [extractGuard, hl, hr]⟩

  | letGuard n binding body ih =>
    obtain ⟨bound, hb⟩ := total binding.operand (by simp [Guard.operands])
    obtain ⟨condition, hc⟩ := ih (fun operand member =>
      compile (binding.wrap operand) (by exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨operand, member, rfl⟩)))
      (fun operand member => total _ _)
    exact ⟨lowerGuardNegations n condition, by simp [extractGuard, hb, hc]⟩
  | letSaved n binding body =>
    obtain ⟨bound, hb⟩ := total binding.operand (by simp [Guard.operands])
    obtain ⟨value, hv⟩ := total (binding.wrap body.operand) (by simp [Guard.operands])
    exact ⟨lowerGuardNegations n (lowerSavedBooleanGuard body value), by simp [extractGuard, hb, hv]⟩
  | localNegation n value =>
    obtain ⟨condition, found⟩ := extractBooleanPropositionLeaf_accepts value compile total
    exact ⟨lowerGuardNegations (n + 1) condition, by simp [extractGuard, found]⟩

theorem extractGuard_operands (guard : Guard)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    {target : LeanExe.IR.Cond} (compiled : extractGuard guard compile = some target) :
    ∀ operand member, ∃ expression, compile operand member = some expression := by
  induction guard generalizing target with
  | literal value =>
    intro operand member
    simp [Guard.operands] at member
  | compare op a b =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro operand member
    simp only [Guard.operands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨left, hl⟩
    · exact ⟨right, hr⟩
  | junction n op a b iha ihb =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro operand member
    rcases List.mem_append.mp member with first | second
    · exact iha _ hl operand first
    · exact ihb _ hr operand second
  | boolean m n op a b =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, _⟩ := compiled
    exact extractBooleanGuard_operands (.junction n op a b) compile hc

  | savedLeft n op a b ihb =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro operand member
    rcases List.mem_append.mp member with member | member
    · exact extractBooleanPropositionLeaf_operands a _ hl operand member
    · exact ihb _ hr operand member
  | savedRight n op a b iha =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro operand member
    rcases List.mem_append.mp member with member | member
    · exact iha _ hl operand member
    · exact extractBooleanPropositionLeaf_operands b _ hr operand member
  | savedBoth n op a b =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro operand member
    rcases List.mem_append.mp member with member | member
    · exact extractBooleanPropositionLeaf_operands a _ hl operand member
    · exact extractBooleanPropositionLeaf_operands b _ hr operand member

  | letGuard n binding body ih =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨bound, hb, condition, hc, _⟩ := compiled
    intro operand member
    simp only [Guard.operands, List.mem_cons, List.mem_map] at member
    rcases member with rfl | ⟨inner, innerMember, rfl⟩
    · exact ⟨bound, hb⟩
    · exact ih _ hc inner innerMember
  | letSaved n binding body =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨bound, hb, value, hv, _⟩ := compiled
    intro operand member
    simp only [Guard.operands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨bound, hb⟩
    · exact ⟨value, hv⟩
  | localNegation n value =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, found, _⟩ := compiled
    exact extractBooleanPropositionLeaf_operands value compile found

theorem extractGuard_correct (guard : Guard)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    (native : Lean.Expr → UInt64) {target : LeanExe.IR.Cond} {store : LeanExe.IR.ScalarStore}
    (compiled : extractGuard guard compile = some target)
    (meanings : ∀ operand member expression, compile operand member = some expression →
      expression.ScalarEval store (native operand) store) :
    target.ScalarEval store (guard.denote native) store := by
  induction guard generalizing native target with
  | literal value =>
    simp only [extractGuard, Option.some.injEq] at compiled
    subst target
    exact lowerGuardLiteral_correct _ _
  | compare op a b =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact lowerComparison_correct op (meanings _ _ _ hl) (meanings _ _ _ hr)
  | junction n op a b iha ihb =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact lowerGuardNegations_correct n (lowerJunction_correct op
      (iha _ native hl (fun operand member expression found => meanings _ _ _ found))
      (ihb _ native hr (fun operand member expression found => meanings _ _ _ found)))
  | boolean m n op a b =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    exact lowerGuardNegations_correct m
      (extractBooleanGuard_correct (.junction n op a b) compile native hc meanings)

  | savedLeft n op a b ihb =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact lowerGuardNegations_correct n (lowerJunction_correct op
      (extractBooleanPropositionLeaf_correct a _ native hl (fun operand member expression found => meanings _ _ _ found))
      (ihb _ native hr (fun operand member expression found => meanings _ _ _ found)))
  | savedRight n op a b iha =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact lowerGuardNegations_correct n (lowerJunction_correct op
      (iha _ native hl (fun operand member expression found => meanings _ _ _ found))
      (extractBooleanPropositionLeaf_correct b _ native hr (fun operand member expression found => meanings _ _ _ found)))
  | savedBoth n op a b =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact lowerGuardNegations_correct n (lowerJunction_correct op
      (extractBooleanPropositionLeaf_correct a _ native hl (fun operand member expression found => meanings _ _ _ found))
      (extractBooleanPropositionLeaf_correct b _ native hr (fun operand member expression found => meanings _ _ _ found)))

  | letGuard n binding body ih =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨bound, hb, condition, hc, rfl⟩ := compiled
    exact lowerGuardNegations_correct n
      (ih _ (fun operand => native (binding.wrap operand)) hc
        (fun operand member expression found => meanings _ _ _ found))
  | letSaved n binding body =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨bound, hb, value, hv, rfl⟩ := compiled
    exact lowerGuardNegations_correct n (lowerSavedBooleanGuard_correct body (meanings _ _ _ hv))
  | localNegation n value =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, found, rfl⟩ := compiled
    exact lowerGuardNegations_correct (n + 1)
      (extractBooleanPropositionLeaf_correct value compile native found meanings)

theorem extractGuard_choice (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (guard : Guard)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    {target : LeanExe.IR.Cond} (compiled : extractGuard guard compile = some target)
    (operands : ∀ operand member expression, compile operand member = some expression → P expression) :
    ∀ t e, P t → P e → P (.ite target t e) := by
  induction guard generalizing target with
  | literal value =>
    simp only [extractGuard, Option.some.injEq] at compiled
    subst target
    exact lowerGuardLiteral_choice P literal choice _
  | compare op a b =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact fun t e ht he => choice op _ _ _ _ (operands _ _ _ hl) (operands _ _ _ hr) ht he
  | junction n op a b iha ihb =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (lowerJunction_choice P literal binary choice op left right
        (iha _ hl (fun operand member expression found => operands _ _ _ found))
        (ihb _ hr (fun operand member expression found => operands _ _ _ found)))
  | boolean m n op a b =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice m _
      (extractBooleanGuard_choice P literal binary choice (.junction n op a b) compile hc operands)

  | savedLeft n op a b ihb =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (lowerJunction_choice P literal binary choice op left right
        (extractBooleanPropositionLeaf_choice P literal choice a _ hl (fun operand member expression found => operands _ _ _ found))
        (ihb _ hr (fun operand member expression found => operands _ _ _ found)))
  | savedRight n op a b iha =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (lowerJunction_choice P literal binary choice op left right
        (iha _ hl (fun operand member expression found => operands _ _ _ found))
        (extractBooleanPropositionLeaf_choice P literal choice b _ hr (fun operand member expression found => operands _ _ _ found)))
  | savedBoth n op a b =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (lowerJunction_choice P literal binary choice op left right
        (extractBooleanPropositionLeaf_choice P literal choice a _ hl (fun operand member expression found => operands _ _ _ found))
        (extractBooleanPropositionLeaf_choice P literal choice b _ hr (fun operand member expression found => operands _ _ _ found)))

  | letGuard n binding body ih =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨bound, hb, condition, hc, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (ih _ hc (fun operand member expression found => operands _ _ _ found))
  | letSaved n binding body =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨bound, hb, value, hv, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (lowerSavedBooleanGuard_choice P literal choice body value (operands _ _ _ hv))
  | localNegation n value =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, found, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice (n + 1) _
      (extractBooleanPropositionLeaf_choice P literal choice value compile found operands)

end LeanExe.Extract.Core
