import LeanExe.Examples.Lidar
import LeanExe.WGSL.UInt

namespace LeanExe.WGSL.Lidar
open UInt
open LeanExe.Examples.Lidar

def axis (lo hi low high origin transverse range : Expr) : Expr :=
  let distance := .sub lo origin
  let miss := .add range (.lit 1)
  .choose (.both (.le low transverse) (.both (.le transverse high) (.le origin hi)))
    (.choose (.le distance range) distance miss) miss

def box (i : Nat) : Expr :=
  let x0 := Expr.read .scene (4*i)
  let y0 := Expr.read .scene (4*i+1)
  let x1 := Expr.read .scene (4*i+2)
  let y1 := Expr.read .scene (4*i+3)
  let x := Expr.read .params 0
  let y := Expr.read .params 1
  let range := Expr.read .params 2
  .choose (.eq .direction (.lit 0)) (axis x0 x1 y0 y1 x y range)
    (.choose (.eq .direction (.lit 1))
      (axis (.sub (.lit world) x1) (.sub (.lit world) x0) y0 y1 (.sub (.lit world) x) y range)
      (.choose (.eq .direction (.lit 2)) (axis y0 y1 x0 x1 y x range)
        (axis (.sub (.lit world) y1) (.sub (.lit world) y0) x0 x1 (.sub (.lit world) y) x range)))

def kernel : Expr := .min (box 0) (.min (box 1) (.min (box 2) (box 3)))

def boxAt (input : Input) (i : Nat) : Rect :=
  ⟨input.scene (4*i), input.scene (4*i+1), input.scene (4*i+2), input.scene (4*i+3)⟩

theorem eval_axis (input : Input) (lo hi low high origin transverse range : Expr) :
    (axis lo hi low high origin transverse range).eval input =
      axisDistance (lo.eval input) (hi.eval input) (low.eval input) (high.eval input)
        (origin.eval input) (transverse.eval input) (range.eval input) := by
  simp [axis, Expr.eval, axisDistance]

theorem eval_box (input : Input) (i : Nat) :
    (box i).eval input = boxDistance (boxAt input i)
      (input.params 0) (input.params 1) input.direction (input.params 2) := by
  by_cases h0 : input.direction = 0 <;> by_cases h1 : input.direction = 1 <;>
    by_cases h2 : input.direction = 2 <;>
    simp [box, Expr.eval, eval_axis, boxAt, boxDistance, h0, h1, h2]

theorem checked : kernel.Checked 4095 := by decide

theorem kernel_exact (input : Input) (bounded : input.Bounded 4095) :
    kernel.eval32 input =
      Nat.min (boxDistance (boxAt input 0) (input.params 0) (input.params 1) input.direction (input.params 2))
      (Nat.min (boxDistance (boxAt input 1) (input.params 0) (input.params 1) input.direction (input.params 2))
      (Nat.min (boxDistance (boxAt input 2) (input.params 0) (input.params 1) input.direction (input.params 2))
      (boxDistance (boxAt input 3) (input.params 0) (input.params 1) input.direction (input.params 2)))) := by
  rw [exact32 kernel input 4095 bounded checked]
  simp only [kernel, Expr.eval, eval_box]

end LeanExe.WGSL.Lidar
