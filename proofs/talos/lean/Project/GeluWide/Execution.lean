import Project.GeluWide.Program
import Project.GeluWide.Model
import Project.ExpNeg.Execution
import Project.FunctionRegion.Exec
import Project.ProofKit.FixedFrame

namespace Project.GeluWide.Spec
open Wasm Project.ProofKit.F64Order

set_option maxRecDepth 4096 in
private theorem exponentialRegion :
    Project.FunctionRegion.Shift Project.ExpNeg.module Project.GeluWide.module
      (fun i => i+4) (fun i => i+4) (fun i => i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 6) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i hi
  rcases hi with rfl | rfl | rfl | rfl
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num

private theorem exponential_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.GeluWide.module 10 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (ExpNeg.evaluate x)]) :=
  Project.FunctionRegion.terminatesWith exponentialRegion 6 (Or.inr (Or.inr (Or.inr rfl)))
    (Project.ExpNeg.Spec.evaluate_exact env initial x)

theorem absolute_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.GeluWide.module 0 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (absBits x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func0Def) rfl ?_ (by decide)
  change wp Project.GeluWide.module func0 _ initial (func0Def.toLocals [.i64 x]) env
  unfold func0
  wp_fixed_frame [func0Def]
  simp [absBits]

theorem finite_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.GeluWide.module 1 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (if finiteBits x then 1 else 0)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_ (by decide)
  change wp Project.GeluWide.module func1 _ initial (func1Def.toLocals [.i64 x]) env
  unfold func1
  wp_fixed_frame [func1Def]
  refine wp_call_tw (absolute_exact env initial x) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  by_cases h : absBits x < 0x7FF0000000000000
  all_goals
    repeat first
      | wp_fixed_frame [func1Def, h, reduceIte]
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [h])
  all_goals simp [finiteBits, h]

theorem negative_absolute_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.GeluWide.module 3 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (negativeAbsBits x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func3Def) rfl ?_ (by decide)
  change wp Project.GeluWide.module func3 _ initial (func3Def.toLocals [.i64 x]) env
  unfold func3
  wp_fixed_frame [func3Def]
  refine wp_call_tw (absolute_exact env initial x) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func3Def]
  simp [negativeAbsBits]

theorem argument_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.GeluWide.module 4 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (Gelu.argumentMagnitude x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func4Def) rfl ?_ (by decide)
  change wp Project.GeluWide.module func4 _ initial (func4Def.toLocals [.i64 x]) env
  unfold func4
  wp_fixed_frame [func4Def]
  simp [Gelu.argumentMagnitude, Wasm.f64Mul, Wasm.f64Add]

theorem core_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.GeluWide.module 2 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (if inCore x then 1 else 0)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func2Def) rfl ?_ (by decide)
  change wp Project.GeluWide.module func2 _ initial (func2Def.toLocals [.i64 x]) env
  unfold func2
  wp_fixed_frame [func2Def]
  refine wp_call_tw (absolute_exact env initial x) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  by_cases h : absBits x ≤ 0x4020000000000000
  all_goals
    repeat first
      | wp_fixed_frame [func2Def, h, reduceIte]
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [h])
  all_goals simp [inCore, h]

theorem evaluate_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.GeluWide.module 11 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (evaluate x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func11Def) rfl ?_ (by decide)
  change wp Project.GeluWide.module func11 _ initial (func11Def.toLocals [.i64 x]) env
  unfold func11
  repeat first
    | wp_fixed_frame [func11Def]
    | (refine wp_call_tw (absolute_exact env initial _) ?_; rintro st values ⟨hst, rfl⟩; subst st)
    | (refine wp_call_tw (argument_exact env initial _) ?_; rintro st values ⟨hst, rfl⟩; subst st)
    | (refine wp_call_tw (negative_absolute_exact env initial _) ?_; rintro st values ⟨hst, rfl⟩; subst st)
    | (refine wp_call_tw (exponential_exact env initial _) ?_; rintro st values ⟨hst, rfl⟩; subst st)
  by_cases h : x < 0x8000000000000000
  all_goals
    repeat first
      | wp_fixed_frame [func11Def, h, reduceIte]
      | (refine wp_iff_cons rfl ?_; simp [h])
      | (refine wp_call_tw (negative_absolute_exact env initial _) ?_; rintro st values ⟨hst, rfl⟩; subst st)
  all_goals simp [evaluate, h, Wasm.f64Mul, Wasm.f64Div, Wasm.f64Add]

theorem evaluateAll_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.GeluWide.module 12 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (evaluateAll x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func12Def) rfl ?_ (by decide)
  change wp Project.GeluWide.module func12 _ initial (func12Def.toLocals [.i64 x]) env
  unfold func12
  wp_fixed_frame [func12Def]
  refine wp_call_tw (core_exact env initial x) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases hd : inCore x
  all_goals
    repeat first
      | wp_fixed_frame [func12Def, hd, reduceIte]
      | (refine wp_iff_cons rfl ?_; simp [hd])
  · by_cases hs : x < 0x8000000000000000
    all_goals
      repeat first
        | wp_fixed_frame [func12Def, hs, reduceIte]
        | (refine wp_iff_cons rfl ?_; simp [hs])
    all_goals simp [evaluateAll, hd, hs]
  · refine wp_call_tw (evaluate_exact env initial x) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    wp_fixed_frame [func12Def]
    simp [evaluateAll, hd]

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (x : UInt64),
    TerminatesWith env m 13 initial [.i64 x]
      (fun final values => final = initial ∧
        values = [.i64 (geluWide x).bits, .i64 (geluWide x).status])

theorem geluWide_exact : ExactSpecFor Project.GeluWide.module := by
  intro env initial x
  refine TerminatesWith.of_wp_entry_for (f := func13Def) rfl ?_ (by decide)
  change wp Project.GeluWide.module func13 _ initial (func13Def.toLocals [.i64 x]) env
  unfold func13
  wp_fixed_frame [func13Def]
  refine wp_call_tw (finite_exact env initial x) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases hd : finiteBits x
  all_goals
    repeat first
      | wp_fixed_frame [func13Def, hd, reduceIte]
      | (refine wp_iff_cons rfl ?_; simp [hd])
  · simp [geluWide, hd]
  · refine wp_call_tw (evaluateAll_exact env initial x) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    wp_fixed_frame [func13Def]
    simp [geluWide, hd]

#print axioms exponentialRegion
#print axioms geluWide_exact
end Project.GeluWide.Spec
