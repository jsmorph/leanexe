import Project.Gelu.Program
import Project.Gelu.Model
import Project.ExpWide.Execution
import Project.FunctionRegion.Exec
import Project.ProofKit.FixedFrame

namespace Project.Gelu.Spec
open Wasm Project.ProofKit.F64Order

set_option maxHeartbeats 2000000

private theorem exponentialRegion :
    Project.FunctionRegion.Shift Project.ExpWide.module Project.Gelu.module
      (fun i => i+3) (fun i => i+3) (fun i => i = 1 ∨ i = 2) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i hi
  rcases hi with rfl | rfl
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num

private theorem exponential_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.Gelu.module 5 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (ExpWide.evaluate x)]) :=
  Project.FunctionRegion.terminatesWith exponentialRegion 2 (Or.inr rfl)
    (Project.ExpWide.Spec.evaluate_exact env initial x)

theorem absolute_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.Gelu.module 0 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (absBits x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func0Def) rfl ?_ (by decide)
  change wp Project.Gelu.module func0 _ initial (func0Def.toLocals [.i64 x]) env
  unfold func0
  wp_fixed_frame [func0Def]
  simp [absBits]

theorem domain_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.Gelu.module 1 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (if inDomain x then 1 else 0)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_ (by decide)
  change wp Project.Gelu.module func1 _ initial (func1Def.toLocals [.i64 x]) env
  unfold func1
  wp_fixed_frame [func1Def]
  refine wp_call_tw (absolute_exact env initial x) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  by_cases h : absBits x ≤ 0x4008000000000000
  all_goals
    repeat first
      | wp_fixed_frame [func1Def, h, reduceIte]
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [h])
  all_goals simp [inDomain, h]

theorem negative_absolute_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.Gelu.module 2 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (negativeAbsBits x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func2Def) rfl ?_ (by decide)
  change wp Project.Gelu.module func2 _ initial (func2Def.toLocals [.i64 x]) env
  unfold func2
  wp_fixed_frame [func2Def]
  refine wp_call_tw (absolute_exact env initial x) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func2Def]
  simp [negativeAbsBits]

theorem argument_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.Gelu.module 3 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (argumentMagnitude x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func3Def) rfl ?_ (by decide)
  change wp Project.Gelu.module func3 _ initial (func3Def.toLocals [.i64 x]) env
  unfold func3
  wp_fixed_frame [func3Def]
  simp [argumentMagnitude, Wasm.f64Mul, Wasm.f64Add]

theorem positive_part_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.Gelu.module 6 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (positivePart x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func6Def) rfl ?_ (by decide)
  change wp Project.Gelu.module func6 _ initial (func6Def.toLocals [.i64 x]) env
  unfold func6
  repeat first
    | wp_fixed_frame [func6Def]
    | (refine wp_call_tw (argument_exact env initial _) ?_; rintro st values ⟨hst, rfl⟩; subst st)
    | (refine wp_call_tw (negative_absolute_exact env initial _) ?_; rintro st values ⟨hst, rfl⟩; subst st)
    | (refine wp_call_tw (exponential_exact env initial _) ?_; rintro st values ⟨hst, rfl⟩; subst st)
  simp [positivePart, Wasm.f64Div, Wasm.f64Add]

theorem evaluate_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.Gelu.module 7 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (evaluate x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func7Def) rfl ?_ (by decide)
  change wp Project.Gelu.module func7 _ initial (func7Def.toLocals [.i64 x]) env
  unfold func7
  repeat first
    | wp_fixed_frame [func7Def]
    | (refine wp_call_tw (absolute_exact env initial _) ?_; rintro st values ⟨hst, rfl⟩; subst st)
    | (refine wp_call_tw (positive_part_exact env initial _) ?_; rintro st values ⟨hst, rfl⟩; subst st)
  by_cases h : x < 0x8000000000000000
  all_goals
    repeat first
      | wp_fixed_frame [func7Def, h, reduceIte]
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [h])
  all_goals simp [evaluate, h, Wasm.f64Sub]

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (x : UInt64),
    TerminatesWith env m 8 initial [.i64 x]
      (fun final values => final = initial ∧
        values = [.i64 (gelu x).bits, .i64 (gelu x).status])

theorem gelu_exact : ExactSpecFor Project.Gelu.module := by
  intro env initial x
  refine TerminatesWith.of_wp_entry_for (f := func8Def) rfl ?_ (by decide)
  change wp Project.Gelu.module func8 _ initial (func8Def.toLocals [.i64 x]) env
  unfold func8
  wp_fixed_frame [func8Def]
  refine wp_call_tw (domain_exact env initial x) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases h : inDomain x
  all_goals
    repeat first
      | wp_fixed_frame [func8Def, h, reduceIte]
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [h])
  · simp [gelu, h]
  · refine wp_call_tw (evaluate_exact env initial x) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    wp_fixed_frame [func8Def]
    simp [gelu, h]

#print axioms exponentialRegion
#print axioms gelu_exact
end Project.Gelu.Spec
