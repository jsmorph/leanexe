import Project.Lidar.Cardinal
import Project.Lidar.Continuous
import LeanExe.WGSL.Lidar
import LeanExe.WGSL.UIntCertificate

namespace Project.Lidar.Shader
open LeanExe.WGSL LeanExe.Examples.Lidar

def boxes (input : UInt.Input) : List Rect :=
  [Lidar.boxAt input 0, Lidar.boxAt input 1, Lidar.boxAt input 2, Lidar.boxAt input 3]

theorem kernel_trace (input : UInt.Input) (bounded : input.Bounded 4095)
    (valid : ∀ b ∈ boxes input, b.Valid) :
    Lidar.kernel.eval32 input = trace (boxes input)
      (input.params 0) (input.params 1) input.direction (input.params 2) := by
  rw [Lidar.kernel_exact input bounded]
  have h := box_first (Lidar.boxAt input 3) (input.params 0) (input.params 1)
    input.direction (input.params 2) (valid _ (by simp [boxes]))
  have hb := h.1
  simp only [boxes, trace]
  rw [Nat.min_eq_left hb]

/-- Composition from the actual parsed shader to nearest-hit geometry.
Each of four invocations owns a distinct output word. Host buffer ownership,
dispatch completion and WebGPU conformance are explicit external obligations. -/
theorem correct (source : String) (parsed : UInt.parse source = some Lidar.kernel)
    (input : UInt.Input) (bounded : input.Bounded 4095)
    (valid : ∀ b ∈ boxes input, b.Valid) :
    ∃ answer, UInt.Executes source input answer ∧
      FirstHit (fun t => ∃ b ∈ boxes input,
        BoxHit b (input.params 0) (input.params 1) input.direction t) (input.params 2) answer := by
  refine ⟨_, UInt.parsed_executes parsed input, ?_⟩
  rw [kernel_trace input bounded valid]
  exact trace_first _ _ _ _ _ valid

theorem distinct_writes (a b : Fin 4) (different : a ≠ b) : a.val ≠ b.val := by
  intro same
  exact different (Fin.ext same)

theorem certified_correct (source : String) (certified : UInt.Certified source Lidar.kernel)
    (input : UInt.Input) (bounded : input.Bounded 4095)
    (directions : input.direction < 4) (valid : ∀ b ∈ boxes input, b.Valid) :
    UInt.Executes source input (Lidar.kernel.eval32 input) ∧
    Continuous.FirstHit (fun t => ∃ b ∈ boxes input,
      Continuous.GeometricHit b (input.params 0) (input.params 1) input.direction t)
      (input.params 2) (Lidar.kernel.eval32 input) := by
  refine ⟨UInt.certified_executes certified input, ?_⟩
  rw [kernel_trace input bounded valid]
  have h := Continuous.trace_first (boxes input) (input.params 0) (input.params 1)
    input.direction (input.params 2) valid
  have same : (fun t => ∃ b ∈ boxes input,
      Continuous.BoxHit b (input.params 0) (input.params 1) input.direction t) =
      (fun t => ∃ b ∈ boxes input,
      Continuous.GeometricHit b (input.params 0) (input.params 1) input.direction t) := by
    funext t
    apply propext
    constructor <;> rintro ⟨b,hb,hh⟩ <;> refine ⟨b,hb,?_⟩
    · exact (Continuous.geometric_iff b _ _ _ _ (valid b hb)
        (bounded.2.1 0) (bounded.2.1 1) directions).mp hh
    · exact (Continuous.geometric_iff b _ _ _ _ (valid b hb)
        (bounded.2.1 0) (bounded.2.1 1) directions).mpr hh
  rwa [same] at h

#print axioms correct
#print axioms certified_correct
end Project.Lidar.Shader
