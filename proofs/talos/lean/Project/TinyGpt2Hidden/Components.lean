import Project.TinyGpt2Hidden.Program
import Project.TinyGpt2.Model
import Project.LayerNorm.Execution
import Project.SoftmaxWide.Execution
import Project.GeluWide.Execution
import Project.FunctionRegion.Exec

namespace Project.TinyGpt2Hidden.Spec
open Wasm

set_option maxHeartbeats 2000000

private theorem normalizationRegion :
    Project.FunctionRegion.Shift Project.LayerNorm.module Project.TinyGpt2Hidden.module
      (fun i => i+7) (fun i => i+7) (fun i => 2 ≤ i ∧ i ≤ 5) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i hi
  obtain ⟨hlo, hhi⟩ := hi
  interval_cases i
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num

theorem normalization_exact (env : HostEnv Unit) (initial : Store Unit)
    (x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3 : UInt64) :
    TerminatesWith env Project.TinyGpt2Hidden.module 12 initial
      (LayerNorm.Spec.arguments x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3)
      (fun final values => final = initial ∧ values =
        LayerNorm.Spec.resultWords (LayerNorm.compute x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3)) :=
  Project.FunctionRegion.terminatesWith normalizationRegion 5 (by norm_num)
    (LayerNorm.Spec.compute_exact env initial x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3)

set_option maxRecDepth 4096 in
private theorem softmaxRegion :
    Project.FunctionRegion.Shift Project.SoftmaxWide.module Project.TinyGpt2Hidden.module
      (fun i => i+32) (fun i => i+32) (fun i => i ≤ 12) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i hi
  interval_cases i
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num

theorem softmax_exact (env : HostEnv Unit) (initial : Store Unit) (n a b c d : UInt64) :
    TerminatesWith env Project.TinyGpt2Hidden.module 44 initial
      [.i64 d, .i64 c, .i64 b, .i64 a, .i64 n]
      (fun final values => final = initial ∧
        values = Softmax.Spec.resultWords (SoftmaxWide.compute n a b c d)) :=
  Project.FunctionRegion.terminatesWith softmaxRegion 12 (by norm_num)
    (SoftmaxWide.Spec.compute_exact env initial n a b c d)

private def geluIndex (i : Nat) : Nat :=
  if i = 0 then 59 else if i ≤ 4 then i+58 else if i ≤ 10 then i+30 else i+52

set_option maxRecDepth 4096 in
private theorem geluRegion :
    Project.FunctionRegion.Shift Project.GeluWide.module Project.TinyGpt2Hidden.module
      geluIndex geluIndex (fun i => i ≤ 12 ∧ i ≠ 1) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i hi
  obtain ⟨hu, hn⟩ := hi
  interval_cases i
  all_goals first | omega | skip
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num

theorem gelu_all_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.TinyGpt2Hidden.module 64 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (GeluWide.evaluateAll x)]) :=
  Project.FunctionRegion.terminatesWith geluRegion 12 (by norm_num)
    (GeluWide.Spec.evaluateAll_exact env initial x)

#print axioms normalization_exact
#print axioms softmax_exact
#print axioms gelu_all_exact
end Project.TinyGpt2Hidden.Spec
