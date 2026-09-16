import Project.TinyGpt2Hidden.Program
import Project.TinyGpt2.Model
import Project.LayerNorm.Execution
import Project.Softmax.Execution
import Project.Gelu.Execution
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

private theorem softmaxRegion :
    Project.FunctionRegion.Shift Project.Softmax.module Project.TinyGpt2Hidden.module
      (fun i => i+30) (fun i => i+30) (fun i => 2 ≤ i ∧ i ≤ 10) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i hi
  obtain ⟨hlo, hhi⟩ := hi
  interval_cases i
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num

theorem softmax_exact (env : HostEnv Unit) (initial : Store Unit) (n a b c d : UInt64) :
    TerminatesWith env Project.TinyGpt2Hidden.module 40 initial
      [.i64 d, .i64 c, .i64 b, .i64 a, .i64 n]
      (fun final values => final = initial ∧
        values = Softmax.Spec.resultWords (Softmax.compute n a b c d)) :=
  Project.FunctionRegion.terminatesWith softmaxRegion 10 (by norm_num)
    (Softmax.Spec.compute_exact env initial n a b c d)

private def geluIndex (i : Nat) : Nat :=
  if i < 4 then i+55 else if i < 6 then i+31 else i+53

private theorem geluRegion :
    Project.FunctionRegion.Shift Project.Gelu.module Project.TinyGpt2Hidden.module
      geluIndex geluIndex (fun i => i ≤ 7) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i hi
  interval_cases i
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num

private theorem gelu_domain_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.TinyGpt2Hidden.module 56 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (if Gelu.inDomain x then 1 else 0)]) :=
  Project.FunctionRegion.terminatesWith geluRegion 1 (by norm_num)
    (Gelu.Spec.domain_exact env initial x)

private theorem gelu_evaluate_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.TinyGpt2Hidden.module 60 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (Gelu.evaluate x)]) :=
  Project.FunctionRegion.terminatesWith geluRegion 7 (by norm_num)
    (Gelu.Spec.evaluate_exact env initial x)

theorem gelu_all_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.TinyGpt2Hidden.module 61 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (Gelu.evaluateAll x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func61Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func61 _ initial (func61Def.toLocals [.i64 x]) env
  unfold func61
  wp_fixed_frame [func61Def]
  refine wp_call_tw (gelu_domain_exact env initial x) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases hd : Gelu.inDomain x <;> by_cases hs : x < 0x8000000000000000
  all_goals
    repeat first
      | wp_fixed_frame [func61Def, reduceIte, hd, hs]
      | (refine wp_call_tw (gelu_evaluate_exact env initial x) ?_
         rintro st values ⟨hst, rfl⟩
         subst st)
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [hd, hs])
  all_goals simp [Gelu.evaluateAll, hd, hs]

#print axioms normalization_exact
#print axioms softmax_exact
#print axioms gelu_all_exact
end Project.TinyGpt2Hidden.Spec
