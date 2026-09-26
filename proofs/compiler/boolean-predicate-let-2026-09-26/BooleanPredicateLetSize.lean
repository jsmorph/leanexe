import LeanExe.Extract.ScalarExprCore
open LeanExe.Source.Scalar
#reduce sizeOf (Lean.Expr.app (.const ``Bool.toUInt64 []) (.bvar 0))
#reduce sizeOf (Lean.Expr.letE .anonymous (.const ``Bool []) (.bvar 0) (.bvar 0) false)

namespace LetMeasureScratch

noncomputable def extractionSize : Lean.Expr → Nat
  | .app (.const ``Bool.toUInt64 []) value => sizeOf value
  | expression => sizeOf expression

theorem extractionSize_le (expression : Lean.Expr) : extractionSize expression ≤ sizeOf expression := by
  unfold extractionSize
  split <;> simp_all <;> omega

@[simp] theorem extractionSize_conversion (value : Lean.Expr) :
    extractionSize (.app (.const ``Bool.toUInt64 []) value) = sizeOf value := rfl

theorem let_value_size (name : Lean.Name) (value body : Lean.Expr) (nondep : Bool) :
    extractionSize (.app (.const ``Bool.toUInt64 []) value) <
      extractionSize (.letE name (.const ``Bool []) value body nondep) := by
  simp [extractionSize]
  omega

end LetMeasureScratch
