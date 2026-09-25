import LeanExe.Extract.ScalarGuard
import LeanExe.Source.ScalarBooleanLet

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Resolve the local flag before looking up captured Boolean bindings. -/
def booleanLetLookup (indices : List Nat) (value : LeanExe.IR.Expr)
    (outer : (index : Nat) → index ∈ booleanLetVariables indices → Option LeanExe.IR.Expr) :
    (index : Nat) → index ∈ indices → Option LeanExe.IR.Expr
  | 0, _ => some value
  | index + 1, member => outer index ((mem_booleanLetVariables indices index).mpr member)

theorem booleanLetLookup_accepts (indices : List Nat) (value : LeanExe.IR.Expr)
    (outer : (index : Nat) → index ∈ booleanLetVariables indices → Option LeanExe.IR.Expr)
    (total : ∀ index member, ∃ target, outer index member = some target) :
    ∀ index member, ∃ target, booleanLetLookup indices value outer index member = some target := by
  intro index member
  cases index with
  | zero => exact ⟨value, rfl⟩
  | succ index => exact total index _

theorem booleanLetLookup_external (indices : List Nat) (value : LeanExe.IR.Expr)
    (outer : (index : Nat) → index ∈ booleanLetVariables indices → Option LeanExe.IR.Expr)
    (total : ∀ index member, ∃ target, booleanLetLookup indices value outer index member = some target) :
    ∀ index member, ∃ target, outer index member = some target := by
  intro index member
  exact total (index + 1) ((mem_booleanLetVariables indices index).mp member)

theorem booleanLetLookup_correct (indices : List Nat) (value : LeanExe.IR.Expr)
    (outer : (index : Nat) → index ∈ booleanLetVariables indices → Option LeanExe.IR.Expr)
    (flag : Bool) (booleans : Nat → Bool) (store : LeanExe.IR.ScalarStore)
    (localMeaning : value.ScalarEval store flag.toUInt64 store)
    (outerMeanings : ∀ index member expression, outer index member = some expression →
      expression.ScalarEval store (booleans index).toUInt64 store) :
    ∀ index member expression, booleanLetLookup indices value outer index member = some expression →
      expression.ScalarEval store (booleanLetBooleans flag booleans index).toUInt64 store := by
  intro index member expression found
  cases index with
  | zero => cases found; exact localMeaning
  | succ index => exact outerMeanings index _ expression found

theorem booleanLetLookup_holds (P : LeanExe.IR.Expr → Prop) (indices : List Nat) (value : LeanExe.IR.Expr)
    (outer : (index : Nat) → index ∈ booleanLetVariables indices → Option LeanExe.IR.Expr)
    (localHolds : P value)
    (outerHolds : ∀ index member expression, outer index member = some expression → P expression) :
    ∀ index member expression, booleanLetLookup indices value outer index member = some expression → P expression := by
  intro index member expression found
  cases index with
  | zero => cases found; exact localHolds
  | succ index => exact outerHolds index _ expression found

end LeanExe.Extract.Core
