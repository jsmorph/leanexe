import Lean

namespace LeanExe.Source.ExprEquality

/-! Kernel-checked structural equality for elaborated syntax. Lean's usual Expr
BEq is an opaque alpha-equivalence primitive, so it cannot justify the operand
identity needed when checking a comparison's explicit decision procedure. -/

deriving instance DecidableEq for String.Pos.Raw
deriving instance DecidableEq for Substring.Raw
deriving instance DecidableEq for Lean.SourceInfo
deriving instance DecidableEq for Lean.Syntax.Preresolved

mutual
  private def syntaxDecEq (a b : Lean.Syntax) : Decidable (a = b) := by
    cases a with
    | missing =>
      cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; contradiction)
    | node info kind args =>
      cases b <;> try exact isFalse (by intro h; contradiction)
      rename_i info' kind' args'
      letI : Decidable (args.toList = args'.toList) := syntaxListDecEq args.toList args'.toList
      letI : Decidable (args = args') := decidable_of_iff (args.toList = args'.toList)
        (by constructor <;> intro h; exact Array.ext' h; exact congrArg Array.toList h)
      exact decidable_of_iff (info = info' ∧ kind = kind' ∧ args = args') (by simp)
    | atom info value =>
      cases b <;> try exact isFalse (by intro h; contradiction)
      rename_i info' value'
      exact decidable_of_iff (info = info' ∧ value = value') (by simp)
    | ident info raw value resolved =>
      cases b <;> try exact isFalse (by intro h; contradiction)
      rename_i info' raw' value' resolved'
      exact decidable_of_iff
        (info = info' ∧ raw = raw' ∧ value = value' ∧ resolved = resolved') (by simp)
  termination_by sizeOf a
  decreasing_by
    simp_wf
    have smaller : sizeOf args.toList < sizeOf args := by
      cases args
      simp
    omega

  private def syntaxListDecEq (a b : List Lean.Syntax) : Decidable (a = b) := by
    cases a with
    | nil => cases b <;> simp only [reduceCtorEq] <;> infer_instance
    | cons head tail =>
      cases b with
      | nil => exact isFalse (by intro h; cases h)
      | cons head' tail' =>
        letI : Decidable (head = head') := syntaxDecEq head head'
        letI : Decidable (tail = tail') := syntaxListDecEq tail tail'
        exact decidable_of_iff (head = head' ∧ tail = tail') (by simp)
  termination_by sizeOf a
  decreasing_by all_goals simp_wf; omega
end

instance : DecidableEq Lean.Syntax := syntaxDecEq

deriving instance DecidableEq for Lean.DataValue
deriving instance DecidableEq for Lean.KVMap
deriving instance DecidableEq for Lean.LevelMVarId
deriving instance DecidableEq for Lean.Level
deriving instance DecidableEq for Lean.Literal
deriving instance DecidableEq for Lean.BinderInfo
deriving instance DecidableEq for Lean.FVarId
deriving instance DecidableEq for Lean.MVarId
deriving instance DecidableEq for Lean.Expr

def same (a b : Lean.Expr) : Bool := decide (a = b)

@[simp] theorem same_eq_true {a b : Lean.Expr} : same a b = true ↔ a = b := by
  simp [same]

@[simp] theorem same_self (a : Lean.Expr) : same a a = true := by
  simp [same]

end LeanExe.Source.ExprEquality
