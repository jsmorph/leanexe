import LeanExe.Examples.LidarOblique
import LeanExe.WGSL.Lidar

namespace LeanExe.WGSL.LidarOblique
open UInt LeanExe.Examples.Lidar

def positive (x0 y0 x1 y1 x y range : Expr) : Expr :=
  let ex := Expr.mul (.lit 100) (.sub x0 x)
  let ey := Expr.mul (.lit 75) (.sub y0 y)
  let entry := Expr.choose (.le ex ey) ey ex
  let exit := Expr.min (.mul (.lit 100) (.sub x1 x)) (.mul (.lit 75) (.sub y1 y))
  .choose (.both (.le x x1) (.both (.le y y1) (.both (.le entry exit) (.le entry range))))
    entry (.add range (.lit 1))

def box (i : Nat) : Expr :=
  let negativeX := Expr.choose (.eq .direction (.lit 1)) (.lit 1) (.eq .direction (.lit 3))
  let negativeY := Expr.choose (.eq .direction (.lit 2)) (.lit 1) (.eq .direction (.lit 3))
  let x0 := Expr.read .scene (4*i)
  let y0 := Expr.read .scene (4*i+1)
  let x1 := Expr.read .scene (4*i+2)
  let y1 := Expr.read .scene (4*i+3)
  let x := Expr.read .params 0
  let y := Expr.read .params 1
  positive
    (.choose negativeX (.sub (.lit world) x1) x0)
    (.choose negativeY (.sub (.lit world) y1) y0)
    (.choose negativeX (.sub (.lit world) x0) x1)
    (.choose negativeY (.sub (.lit world) y0) y1)
    (.choose negativeX (.sub (.lit world) x) x)
    (.choose negativeY (.sub (.lit world) y) y)
    (.read .params 2)

def kernel : Expr := .min (box 0) (.min (box 1) (.min (box 2) (box 3)))

theorem eval_positive (input : Input) (x0 y0 x1 y1 x y range : Expr) :
    (positive x0 y0 x1 y1 x y range).eval input =
      LeanExe.Examples.LidarOblique.positiveDistance
        ⟨x0.eval input, y0.eval input, x1.eval input, y1.eval input⟩
        (x.eval input) (y.eval input) (range.eval input) := by
  by_cases h : 100*(x0.eval input-x.eval input) ≤ 75*(y0.eval input-y.eval input)
  · by_cases he : 75*(y0.eval input-y.eval input) ≤
        Nat.min (100*(x1.eval input-x.eval input)) (75*(y1.eval input-y.eval input)) <;>
      by_cases hr : 75*(y0.eval input-y.eval input) ≤ range.eval input <;>
      simp [positive, Expr.eval, LeanExe.Examples.LidarOblique.positiveDistance,
        LeanExe.Examples.LidarOblique.entry, LeanExe.Examples.LidarOblique.exit, Nat.max_def, h, he, hr]
  · by_cases he : 100*(x0.eval input-x.eval input) ≤
        Nat.min (100*(x1.eval input-x.eval input)) (75*(y1.eval input-y.eval input)) <;>
      by_cases hr : 100*(x0.eval input-x.eval input) ≤ range.eval input <;>
      simp [positive, Expr.eval, LeanExe.Examples.LidarOblique.positiveDistance,
        LeanExe.Examples.LidarOblique.entry, LeanExe.Examples.LidarOblique.exit, Nat.max_def, h, he, hr]

theorem eval_box (input : Input) (i : Nat) :
    (box i).eval input = LeanExe.Examples.LidarOblique.boxDistance (Lidar.boxAt input i)
      (input.params 0) (input.params 1) input.direction (input.params 2) := by
  by_cases h1 : input.direction = 1 <;> by_cases h2 : input.direction = 2 <;>
    by_cases h3 : input.direction = 3 <;>
    simp [box, eval_positive, Expr.eval, Lidar.boxAt,
      LeanExe.Examples.LidarOblique.boxDistance, LeanExe.Examples.LidarOblique.reflected,
      LeanExe.Examples.LidarOblique.originX, LeanExe.Examples.LidarOblique.originY, h1, h2, h3]

/-- Coordinates are grid units; the bounded range word and answers are ticks. -/
theorem checked : kernel.Checked 4095 := by decide

theorem exact (input : Input) (bounded : input.Bounded 4095) :
    kernel.eval32 input = kernel.eval input := exact32 _ _ _ bounded checked

end LeanExe.WGSL.LidarOblique
