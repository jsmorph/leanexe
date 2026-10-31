import Verified.WGSL.Scalar

namespace Verified.WGSL

structure Cell (t : Ty) where
  type : LeanExe.WGSL.Source.ScalarType
  encode : t.denote → type.denote
  read : Nat → Rep t
  input : Rep t → LeanExe.WGSL.Source.Expr type
  readBound : ∀ j, (read j).locals ≤ j + 1
  inputHolds : ∀ rep locals arrays x, rep.Holds locals arrays x →
    (input rep).denote locals arrays = some (encode x)
  readHolds : ∀ locals arrays j x, locals j = some (type.value (encode x)) →
    (read j).Holds locals arrays x

def Cell.word : Cell .word where
  type := .u64
  encode := id
  read := fun j => .word (.get j)
  input := Rep.wordExpr
  readBound := fun _ => Nat.le_refl _
  inputHolds := by intro rep locals arrays x h; cases rep; exact h
  readHolds := by intro locals arrays j x h; simp [Rep.Holds, LeanExe.WGSL.Source.Expr.denote, h]

def Cell.bool : Cell .bool where
  type := .u64
  encode := boolWord
  read := fun j => .bool (.ne (.get j) (.const 0))
  input := fun rep => .ite rep.boolExpr (.const 1) (.const 0)
  readBound := fun _ => Nat.le_refl _
  inputHolds := by
    intro rep locals arrays x h
    cases rep
    simp only [Rep.Holds] at h
    cases x <;> simp [LeanExe.WGSL.Source.Expr.denote, Rep.boolExpr, h, boolWord]
  readHolds := by
    intro locals arrays j x h
    cases x <;> simp [Rep.Holds, LeanExe.WGSL.Source.Expr.denote, h, boolWord]

def Cell.float32 : Cell .float32 where
  type := .f32
  encode := Float32.toBits
  read := fun j => .float32 (.getF32 j)
  input := Rep.float32Expr
  readBound := fun _ => Nat.le_refl _
  inputHolds := by intro rep locals arrays x h; cases rep; exact h
  readHolds := by intro locals arrays j x h; simp [Rep.Holds, LeanExe.WGSL.Source.Expr.denote, h]

def Cell.ofTy : (t : Ty) → Option (Cell t)
  | .word => some .word
  | .bool => some .bool
  | .float32 => some .float32
  | _ => none

end Verified.WGSL
