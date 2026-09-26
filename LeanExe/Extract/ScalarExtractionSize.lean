import Lean

namespace LeanExe.Extract.Core

/-- Boolean extraction measures the expression inside its word conversion. -/
noncomputable def scalarExtractionSize : Lean.Expr → Nat
  | .app (.const ``Bool.toUInt64 []) value => sizeOf value
  | expression => sizeOf expression

theorem scalarExtractionSize_le (expression : Lean.Expr) :
    scalarExtractionSize expression ≤ sizeOf expression := by
  unfold scalarExtractionSize
  split <;> simp_all <;> omega

@[simp] theorem scalarExtractionSize_conversion (value : Lean.Expr) :
    scalarExtractionSize (.app (.const ``Bool.toUInt64 []) value) = sizeOf value := rfl

end LeanExe.Extract.Core
