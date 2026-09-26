import Project.Lidar.Oblique
import Project.Lidar.Shader
import LeanExe.WGSL.LidarOblique

namespace Project.Lidar.ObliqueShader
open LeanExe.WGSL LeanExe.Examples.Lidar

theorem kernel_trace_math (input : UInt.Input) :
    LidarOblique.kernel.eval input = LeanExe.Examples.LidarOblique.trace (Shader.boxes input)
      (input.params 0) (input.params 1) input.direction (input.params 2) := by
  have h := Oblique.positive_first
    (LeanExe.Examples.LidarOblique.reflected (Lidar.boxAt input 3) input.direction)
    (LeanExe.Examples.LidarOblique.originX (input.params 0) input.direction)
    (LeanExe.Examples.LidarOblique.originY (input.params 1) input.direction) (input.params 2)
  have hb := h.1
  change LeanExe.Examples.LidarOblique.boxDistance (Lidar.boxAt input 3)
    (input.params 0) (input.params 1) input.direction (input.params 2) ≤ input.params 2+1 at hb
  simp only [LidarOblique.kernel, UInt.Expr.eval, LidarOblique.eval_box,
    Shader.boxes, LeanExe.Examples.LidarOblique.trace]
  rw [Nat.min_eq_left hb]

theorem kernel_trace (input : UInt.Input) (bounded : input.Bounded 4095) :
    LidarOblique.kernel.eval32 input = LeanExe.Examples.LidarOblique.trace (Shader.boxes input)
      (input.params 0) (input.params 1) input.direction (input.params 2) := by
  rw [LidarOblique.exact input bounded]
  exact kernel_trace_math input

theorem certified_correct (source : String) (certified : UInt.Certified source LidarOblique.kernel)
    (input : UInt.Input) (bounded : input.Bounded 4095)
    (directions : input.direction < 4) (valid : ∀ b ∈ Shader.boxes input, b.Valid) :
    UInt.Executes source input (LidarOblique.kernel.eval32 input) ∧
    Continuous.FirstHit (fun ticks => ∃ b ∈ Shader.boxes input,
      Oblique.GeometricHit b (input.params 0) (input.params 1) input.direction (ticks/60))
      (input.params 2) (LidarOblique.kernel.eval32 input) := by
  refine ⟨UInt.certified_executes certified input, ?_⟩
  rw [kernel_trace input bounded]
  exact Oblique.geometric_first _ _ _ _ _ valid (bounded.2.1 0) (bounded.2.1 1) directions

#print axioms certified_correct
end Project.Lidar.ObliqueShader
