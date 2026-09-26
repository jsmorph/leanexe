import Shader
import Summary
import Controller
import ControllerResult
import Project.Lidar.ObliqueShader
import Project.Lidar.Summary
import Project.Lidar.Controller

namespace Project.Lidar.Application
open LeanExe.WGSL

/-- The continuous nearest-hit property with 60 ticks per distance unit of the exact certified scan artifact. -/
theorem scan (input : UInt.Input) (bounded : input.Bounded 4095)
    (directions : input.direction < 4)
    (valid : ∀ b ∈ Shader.boxes input, b.Valid) :
    UInt.Executes Artifact.shaderText input (LidarOblique.kernel.eval32 input) ∧
    Continuous.FirstHit (fun t => ∃ b ∈ Shader.boxes input,
      Oblique.GeometricHit b (input.params 0) (input.params 1) input.direction (t/60))
      (input.params 2) (LidarOblique.kernel.eval32 input) :=
  ObliqueShader.certified_correct _ Artifact.certified input bounded directions valid

/-- The exact summary artifact returns the encoded requested summary. -/
theorem summary (input : UInt.Input) (bounded : input.Bounded 4096)
    (mask : input.params 3 < 16) :
    UInt.Executes SummaryArtifact.shaderText input
      (Summary.count input * 8192 + Summary.nearest input) := by
  rw [← Summary.correct input bounded mask]
  exact UInt.certified_executes SummaryArtifact.certified input

/-- The actual emitted controller bytes decode, validate and execute according
to the original elaborated source expression's scalar semantics. -/
theorem controller : Project.Compiler.ArithmeticModule.Correct Unit
    ControllerArtifact.source "parameters" 4 ControllerArtifact.bytes :=
  ControllerArtifact.correct

/-- Integral interpretation of the host's four field extractions. -/
def unpack (word : UInt64) : Nat → Nat
  | 0 => word.toNat % 4096
  | 1 => word.toNat / 4096 % 4096
  | 2 => word.toNat / 16777216 % 4096
  | 3 => word.toNat / 68719476736 % 16
  | _ => 0

theorem unpacked (x y range mask : UInt64)
    (hx : x ≤ 4095) (hy : y ≤ 4095) (hr : range ≤ 4095) (hm : mask ≤ 15) :
    let fields := unpack (LeanExe.Examples.Lidar.parameters x y range mask)
    fields 0 = x.toNat ∧ fields 1 = y.toNat ∧
      fields 2 = range.toNat ∧ fields 3 = mask.toNat := by
  simp only [unpack, Controller.packed_nat x y range mask hx hy hr hm]
  change x.toNat ≤ 4095 at hx
  change y.toNat ≤ 4095 at hy
  change range.toNat ≤ 4095 at hr
  change mask.toNat ≤ 15 at hm
  exact (Controller.fields _ _ _ _ (by omega) (by omega) (by omega) (by omega)).2

/-- The emitted WASM result supplies the parameters of the exact shader whose
continuous nearest-hit property with 60 ticks per distance unit is proved here. Correct host transfer and
WebGPU conformance remain external assumptions. -/
theorem pipeline (x y range mask : UInt64)
    (hx : x ≤ 4095) (hy : y ≤ 4095) (hr : range ≤ 4095) (hm : mask ≤ 15)
    (scene : Nat → Nat) (sceneBound : ∀ i, scene i ≤ 4095)
    (direction : Nat) (hd : direction < 4)
    (valid : ∀ b ∈ Shader.boxes
      ⟨scene, unpack (LeanExe.Examples.Lidar.parameters x y range mask), direction⟩, b.Valid)
    (host : Wasm.HostEnv Unit) (store : Wasm.Store Unit) :
    let word := LeanExe.Examples.Lidar.parameters x y range mask
    let input : UInt.Input := ⟨scene, unpack word, direction⟩
    ∃ raw, Wasm.Binary.decode ControllerArtifact.bytes = .ok raw ∧
      (Wasm.Binary.Translation.module raw).findExport "parameters" = some 0 ∧
      (∃ N, ∀ fuel ≥ N, Wasm.run fuel (Wasm.Binary.Translation.module raw) 0 store
        ([x,y,range,mask].map Wasm.Value.i64).reverse host = .Success [.i64 word] store) ∧
      UInt.Executes Artifact.shaderText input (LidarOblique.kernel.eval32 input) ∧
      Continuous.FirstHit (fun t => ∃ b ∈ Shader.boxes input,
        Oblique.GeometricHit b x.toNat y.toNat direction (t/60))
        range.toNat (LidarOblique.kernel.eval32 input) := by
  obtain ⟨raw, decoded, exported, executed⟩ := ControllerResult.correct x y range mask host store
  refine ⟨raw, decoded, exported, executed, ?_⟩
  let word := LeanExe.Examples.Lidar.parameters x y range mask
  let input : UInt.Input := ⟨scene, unpack word, direction⟩
  have fields := unpacked x y range mask hx hy hr hm
  change x.toNat ≤ 4095 at hx
  change y.toNat ≤ 4095 at hy
  change range.toNat ≤ 4095 at hr
  change mask.toNat ≤ 15 at hm
  have bounded : input.Bounded 4095 := by
    refine ⟨sceneBound, ?_, ?_⟩
    swap
    · change direction ≤ 4095
      omega
    intro i
    change unpack word i ≤ 4095
    match i with
    | 0 => rw [fields.1]; exact hx
    | 1 => rw [fields.2.1]; exact hy
    | 2 => rw [fields.2.2.1]; exact hr
    | 3 => rw [fields.2.2.2]; omega
    | _+4 => simp [unpack]
  obtain ⟨exec, nearest⟩ := scan input bounded hd valid
  refine ⟨exec, ?_⟩
  change Continuous.FirstHit (fun t => ∃ b ∈ Shader.boxes input,
    Oblique.GeometricHit b (unpack word 0) (unpack word 1) direction (t/60))
    (unpack word 2) (LidarOblique.kernel.eval32 input) at nearest
  rwa [fields.1, fields.2.1, fields.2.2.1] at nearest

#print axioms scan
#print axioms summary
#print axioms controller
#print axioms pipeline
#print axioms ControllerResult.correct
#print axioms Controller.packed_nat
#print axioms Controller.fields
end Project.Lidar.Application
