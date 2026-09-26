import Shader
import Inner
import Summary
import Controller
import ControllerResult
import Project.Lidar.IntervalQuery
import Project.Lidar.Controller

namespace Project.Lidar.Application
open LeanExe.WGSL

/-- The host's quotient/remainder interpretation of the actual summary word. -/
def SummaryWord (input : UInt.Input) : Prop :=
  let word := Summary.count input*8192+Summary.nearest input
  UInt.Executes SummaryArtifact.shaderText input word ∧
    word / 8192 = Summary.count input ∧ word % 8192 = Summary.nearest input

theorem summary_word (input : UInt.Input) (bounded : input.Bounded 4095)
    (mask : input.params 3 < 16)
    (domain : ∀ b ∈ Shader.boxes input, LeanExe.Examples.LidarInterval.Domain b)
    (inner : Bool) :
    SummaryWord (IntervalQuery.results (if inner then LidarInterval.inner else LidarInterval.outer) input) := by
  have first := IntervalQuery.nearest_first input bounded domain inner
  have hr := bounded.2.1 2
  refine ⟨?_, Summary.decode _ (by have bound := first.1; omega)⟩
  rw [← Summary.correct _ (IntervalQuery.results_bounded input bounded domain inner) mask]
  exact UInt.certified_executes SummaryArtifact.certified _

/-- All modeled GPU executions, including the requested summary, and the
physical-distance contract for every real scene within the input bounds. -/
def Verified (input : UInt.Input) (actual : List Interval.RealRect) : Prop :=
  (∀ i, i < 4 → UInt.Executes Artifact.shaderText (IntervalQuery.lane input i)
    (LidarInterval.outer.eval32 (IntervalQuery.lane input i)) ∧
    UInt.Executes InnerArtifact.shaderText (IntervalQuery.lane input i)
    (LidarInterval.inner.eval32 (IntervalQuery.lane input i))) ∧
  (let outer := IntervalQuery.results LidarInterval.outer input
   let inner := IntervalQuery.results LidarInterval.inner input
   SummaryWord outer ∧ SummaryWord inner ∧
   IntervalQuery.Result (IntervalQuery.Hit input actual) (input.params 2)
     (Summary.nearest outer) (Summary.nearest inner))

theorem verified (input : UInt.Input) (bounded : input.Bounded 4095)
    (mask : input.params 3 < 16)
    (domain : ∀ b ∈ Shader.boxes input, LeanExe.Examples.LidarInterval.Domain b)
    (actual : List Interval.RealRect)
    (approx : List.Forall₂ Interval.Approx (Shader.boxes input) actual) : Verified input actual := by
  exact ⟨fun i _ => ⟨UInt.certified_executes Artifact.certified _,
      UInt.certified_executes InnerArtifact.certified _⟩,
    summary_word input bounded mask domain false,
    summary_word input bounded mask domain true,
    IntervalQuery.correct input bounded domain actual approx⟩

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

/-- The actual emitted WASM controller supplies the fields used by the
certified scan and summary artifacts, with an explicit real-distance bound. -/
theorem pipeline (x y range mask : UInt64)
    (hx : x ≤ 4095) (hy : y ≤ 4095) (hr : range ≤ 4095) (hm : mask ≤ 15)
    (scene : Nat → Nat) (sceneBound : ∀ i, scene i ≤ 4095)
    (actual : List Interval.RealRect)
    (domain : ∀ b ∈ Shader.boxes
      ⟨scene, unpack (LeanExe.Examples.Lidar.parameters x y range mask), 0⟩,
      LeanExe.Examples.LidarInterval.Domain b)
    (approx : List.Forall₂ Interval.Approx (Shader.boxes
      ⟨scene, unpack (LeanExe.Examples.Lidar.parameters x y range mask), 0⟩) actual)
    (host : Wasm.HostEnv Unit) (store : Wasm.Store Unit) :
    let word := LeanExe.Examples.Lidar.parameters x y range mask
    let input : UInt.Input := ⟨scene, unpack word, 0⟩
    ∃ raw, Wasm.Binary.decode ControllerArtifact.bytes = .ok raw ∧
      (Wasm.Binary.Translation.module raw).findExport "parameters" = some 0 ∧
      (∃ N, ∀ fuel ≥ N, Wasm.run fuel (Wasm.Binary.Translation.module raw) 0 store
        ([x,y,range,mask].map Wasm.Value.i64).reverse host = .Success [.i64 word] store) ∧
      input.params 0 = x.toNat ∧ input.params 1 = y.toNat ∧
      input.params 2 = range.toNat ∧ input.params 3 = mask.toNat ∧ Verified input actual := by
  obtain ⟨raw, decoded, exported, executed⟩ := ControllerResult.correct x y range mask host store
  let word := LeanExe.Examples.Lidar.parameters x y range mask
  let input : UInt.Input := ⟨scene, unpack word, 0⟩
  have fields := unpacked x y range mask hx hy hr hm
  refine ⟨raw, decoded, exported, executed, fields.1, fields.2.1, fields.2.2.1, fields.2.2.2, ?_⟩
  change x.toNat ≤ 4095 at hx
  change y.toNat ≤ 4095 at hy
  change range.toNat ≤ 4095 at hr
  change mask.toNat ≤ 15 at hm
  have bounded : input.Bounded 4095 := by
    refine ⟨sceneBound, ?_, by change 0 ≤ 4095; omega⟩
    intro i
    change unpack word i ≤ 4095
    match i with
    | 0 => rw [fields.1]; exact hx
    | 1 => rw [fields.2.1]; exact hy
    | 2 => rw [fields.2.2.1]; exact hr
    | 3 => rw [fields.2.2.2]; omega
    | _+4 => simp [unpack]
  apply verified input bounded _ domain actual approx
  change unpack word 3 < 16
  rw [fields.2.2.2]
  omega

#print axioms verified
#print axioms pipeline
#print axioms ControllerResult.correct
end Project.Lidar.Application
