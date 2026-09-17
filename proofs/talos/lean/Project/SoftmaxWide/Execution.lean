import Project.SoftmaxWide.Program
import Project.SoftmaxWide.Model
import Project.Softmax.Execution
import Project.ExpNeg.Execution
import Project.FunctionRegion.Exec

namespace Project.SoftmaxWide.Spec
open Wasm Project.Softmax Project.Softmax.Spec

private def sharedIndex (i : Nat) : Nat := if i ≤ 4 then i-2 else i+2

private theorem sharedRegion :
    Project.FunctionRegion.Shift Project.Softmax.module Project.SoftmaxWide.module
      sharedIndex sharedIndex (fun i => i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 8 ∨ i = 9) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num

private theorem rowMaximum_exact (env : HostEnv Unit) (initial : Store Unit) (n a b c d : UInt64) :
    TerminatesWith env Project.SoftmaxWide.module 2 initial [.i64 d, .i64 c, .i64 b, .i64 a, .i64 n]
      (fun final values => final = initial ∧ values = [.i64 (rowMaximum n a b c d)]) :=
  Project.FunctionRegion.terminatesWith sharedRegion 4 (by simp)
    (Project.Softmax.Spec.rowMaximum_exact env initial n a b c d)

private theorem total_exact (env : HostEnv Unit) (initial : Store Unit) (a b c d : UInt64) :
    TerminatesWith env Project.SoftmaxWide.module 10 initial [.i64 d, .i64 c, .i64 b, .i64 a]
      (fun final values => final = initial ∧ values = [.i64 (total a b c d)]) :=
  Project.FunctionRegion.terminatesWith sharedRegion 8 (by simp)
    (Project.Softmax.Spec.total_exact env initial a b c d)

private theorem probability_exact (env : HostEnv Unit) (initial : Store Unit) (n i w den : UInt64) :
    TerminatesWith env Project.SoftmaxWide.module 11 initial [.i64 den, .i64 w, .i64 i, .i64 n]
      (fun final values => final = initial ∧ values = [.i64 (probability n i w den)]) :=
  Project.FunctionRegion.terminatesWith sharedRegion 9 (by simp)
    (Project.Softmax.Spec.probability_exact env initial n i w den)

set_option maxRecDepth 4096 in
private theorem exponentialRegion :
    Project.FunctionRegion.Shift Project.ExpNeg.module Project.SoftmaxWide.module
      (fun i => i+2) (fun i => i+2) (fun i => i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 6) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i hi
  rcases hi with rfl | rfl | rfl | rfl
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num

private theorem exponential_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.SoftmaxWide.module 8 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (ExpNeg.evaluate x)]) :=
  Project.FunctionRegion.terminatesWith exponentialRegion 6 (by simp)
    (Project.ExpNeg.Spec.evaluate_exact env initial x)

theorem weight_exact (env : HostEnv Unit) (initial : Store Unit) (n i x m : UInt64) :
    TerminatesWith env Project.SoftmaxWide.module 9 initial [.i64 m, .i64 x, .i64 i, .i64 n]
      (fun final values => final = initial ∧ values = [.i64 (weight n i x m)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func9Def) rfl ?_ (by decide)
  change wp Project.SoftmaxWide.module func9 _ initial (func9Def.toLocals [.i64 n, .i64 i, .i64 x, .i64 m]) env
  unfold func9
  by_cases h : i < n
  all_goals
    repeat
      first
      | wp_fixed_frame [func9Def, reduceIte, *]
      | (refine wp_call_tw (exponential_exact env initial _) ?_
         rintro st values ⟨hst, rfl⟩
         subst st)
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [*])
  all_goals simp [weight, h, Wasm.f64Sub]

theorem compute_exact (env : HostEnv Unit) (initial : Store Unit) (n a b c d : UInt64) :
    TerminatesWith env Project.SoftmaxWide.module 12 initial [.i64 d, .i64 c, .i64 b, .i64 a, .i64 n]
      (fun final values => final = initial ∧ values = resultWords (compute n a b c d)) := by
  refine TerminatesWith.of_wp_entry_for (f := func12Def) rfl ?_ (by decide)
  change wp Project.SoftmaxWide.module func12 _ initial (func12Def.toLocals [.i64 n, .i64 a, .i64 b, .i64 c, .i64 d]) env
  unfold func12
  wp_fixed_frame [func12Def]
  refine wp_call_tw (rowMaximum_exact env initial _ _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func12Def]
  refine wp_call_tw (weight_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func12Def]
  refine wp_call_tw (weight_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func12Def]
  refine wp_call_tw (weight_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func12Def]
  refine wp_call_tw (weight_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func12Def]
  refine wp_call_tw (total_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func12Def]
  refine wp_call_tw (probability_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func12Def]
  refine wp_call_tw (probability_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func12Def]
  refine wp_call_tw (probability_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func12Def]
  refine wp_call_tw (probability_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func12Def]
  simp [resultWords, compute]

#print axioms sharedRegion
#print axioms exponentialRegion
#print axioms compute_exact
end Project.SoftmaxWide.Spec
