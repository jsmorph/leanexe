import LeanExe.Source.ScalarExtremum
import LeanExe.Extract.ScalarComparison

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (Extremum Comparison)

def lowerExtremum : Extremum → LeanExe.IR.Expr → LeanExe.IR.Expr → LeanExe.IR.Expr
  | .minimum, a, b => .ite (lowerComparison .le a b) a b
  | .maximum, a, b => .ite (lowerComparison .le a b) b a

theorem lowerExtremum_correct (op : Extremum) {a b : LeanExe.IR.Expr}
    {store : LeanExe.IR.ScalarStore} {x y : UInt64}
    (left : a.ScalarEval store x store) (right : b.ScalarEval store y store) :
    (lowerExtremum op a b).ScalarEval store (op.denote x y) store := by
  have condition := lowerComparison_correct .le left right
  cases op with
  | minimum =>
    change (LeanExe.IR.Expr.ite (lowerComparison .le a b) a b).ScalarEval store
      (if x ≤ y then x else y) store
    by_cases h : x ≤ y
    · simp only [h, ↓reduceIte]
      exact .iteTrue (by simpa [Comparison.denote, h] using condition) left
    · simp only [h, ↓reduceIte]
      exact .iteFalse (by simpa [Comparison.denote, h] using condition) right
  | maximum =>
    change (LeanExe.IR.Expr.ite (lowerComparison .le a b) b a).ScalarEval store
      (if x ≤ y then y else x) store
    by_cases h : x ≤ y
    · simp only [h, ↓reduceIte]
      exact .iteTrue (by simpa [Comparison.denote, h] using condition) right
    · simp only [h, ↓reduceIte]
      exact .iteFalse (by simpa [Comparison.denote, h] using condition) left

theorem lowerExtremum_invariant (P : LeanExe.IR.Expr → Prop)
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (op : Extremum) (a b : LeanExe.IR.Expr) (left : P a) (right : P b) :
    P (lowerExtremum op a b) := by
  cases op
  · exact choice .le a b a b left right left right
  · exact choice .le a b b a left right right left

end LeanExe.Extract.Core
