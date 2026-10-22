import Verified.WGSL.Scalar

namespace Verified.WGSL

structure Output (e : Elem) where
  word : Rep (.elem e) → LeanExe.IR.Expr .u64
  encode : e.denote → UInt64
  bound : ∀ r, (word r).denoteLocals ≤ r.locals
  correct : ∀ rep locals arrays x, rep.Holds locals arrays x →
    (word rep).denote locals arrays = some (encode x)

def Demos.Drone.Output.wordOutput : Output .word where
  word := Rep.wordExpr
  encode := id
  bound := by intro r; cases r; exact Nat.le_refl _
  correct := by intro r locals arrays x h; cases r; exact h

def Demos.Drone.Output.boolOutput : Output .bool where
  word := fun rep => .ite rep.boolExpr (.const 1) (.const 0)
  encode := boolWord
  bound := by intro r; cases r; simp [Rep.boolExpr, LeanExe.IR.Expr.denoteLocals, Rep.locals]
  correct := by
    intro r locals arrays x h
    cases r
    simp only [Rep.Holds] at h
    cases x <;> simp [Rep.boolExpr, LeanExe.IR.Expr.denote, h, boolWord]

def Demos.Drone.Output.float32Output : Output .float32 where
  word := fun rep => .toBits32 rep.float32Expr
  encode := fun x => x.toBits.toUInt64
  bound := by intro r; cases r; exact Nat.le_refl _
  correct := by
    intro r locals arrays x h
    cases r
    simp only [Rep.Holds] at h
    simp [Rep.float32Expr, LeanExe.IR.Expr.denote, h]

def Demos.Drone.Output.ofElem : (e : Elem) → Option (Output e)
  | .word => some .wordOutput
  | .bool => some .boolOutput
  | .float32 => some .float32Output
  | _ => none

end Verified.WGSL
