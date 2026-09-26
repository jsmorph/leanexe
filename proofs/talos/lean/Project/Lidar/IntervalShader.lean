import Project.Lidar.IntervalBounds
import Project.Lidar.ObliqueShader
import LeanExe.WGSL.LidarInterval

namespace Project.Lidar.IntervalShader
open LeanExe.WGSL LeanExe.Examples.Lidar

theorem inner_box (input : UInt.Input) (i : Nat) :
    Lidar.boxAt (input.mapScene LidarInterval.innerWord) i =
      LeanExe.Examples.LidarInterval.inner (Lidar.boxAt input i) := by
  simp [Lidar.boxAt, UInt.Input.mapScene, LidarInterval.innerWord, UInt.Expr.eval,
    LeanExe.Examples.LidarInterval.inner, Nat.add_mod, Nat.mul_mod]

theorem outer_box (input : UInt.Input) (i : Nat) :
    Lidar.boxAt (input.mapScene LidarInterval.outerWord) i =
      LeanExe.Examples.LidarInterval.outer (Lidar.boxAt input i) := by
  simp [Lidar.boxAt, UInt.Input.mapScene, LidarInterval.outerWord, UInt.Expr.eval,
    LeanExe.Examples.LidarInterval.outer, Nat.add_mod, Nat.mul_mod]

theorem inner_boxes (input : UInt.Input) :
    Shader.boxes (input.mapScene LidarInterval.innerWord) =
      (Shader.boxes input).map LeanExe.Examples.LidarInterval.inner := by
  simp [Shader.boxes, inner_box]

theorem outer_boxes (input : UInt.Input) :
    Shader.boxes (input.mapScene LidarInterval.outerWord) =
      (Shader.boxes input).map LeanExe.Examples.LidarInterval.outer := by
  simp [Shader.boxes, outer_box]

theorem inner_first (input : UInt.Input) (bounded : input.Bounded 4095)
    (directions : input.direction < 4)
    (domain : ∀ b ∈ Shader.boxes input, LeanExe.Examples.LidarInterval.Domain b) :
    Continuous.FirstHit (fun ticks => ∃ b ∈ (Shader.boxes input).map LeanExe.Examples.LidarInterval.inner,
      Oblique.GeometricHit b (input.params 0) (input.params 1) input.direction (ticks/60))
      (input.params 2) (LidarInterval.inner.eval32 input) := by
  rw [LidarInterval.inner_exact input bounded, ObliqueShader.kernel_trace_math, inner_boxes]
  apply Oblique.geometric_first
  · intro target present
    obtain ⟨original,originalPresent,rfl⟩ := List.mem_map.mp present
    exact LeanExe.Examples.LidarInterval.inner_valid original (domain original originalPresent)
  · exact bounded.2.1 0
  · exact bounded.2.1 1
  · exact directions

theorem outer_first (input : UInt.Input) (bounded : input.Bounded 4095)
    (directions : input.direction < 4)
    (domain : ∀ b ∈ Shader.boxes input, LeanExe.Examples.LidarInterval.Domain b) :
    Continuous.FirstHit (fun ticks => ∃ b ∈ (Shader.boxes input).map LeanExe.Examples.LidarInterval.outer,
      Oblique.GeometricHit b (input.params 0) (input.params 1) input.direction (ticks/60))
      (input.params 2) (LidarInterval.outer.eval32 input) := by
  rw [LidarInterval.outer_exact input bounded, ObliqueShader.kernel_trace_math, outer_boxes]
  apply Oblique.geometric_first
  · intro target present
    obtain ⟨original,originalPresent,rfl⟩ := List.mem_map.mp present
    exact LeanExe.Examples.LidarInterval.outer_valid original (domain original originalPresent)
  · exact bounded.2.1 0
  · exact bounded.2.1 1
  · exact directions

#print axioms inner_first
#print axioms outer_first
end Project.Lidar.IntervalShader
