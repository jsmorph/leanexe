import Project.F64Clip.Program
import Project.F64Clip.Model
import Project.ProofKit.FixedFrame
import Project.ProofKit.ExactCall
import Project.TalosCompat

namespace Project.F64Clip.Spec
open Wasm Project.ProofKit.F64Order

theorem absolute_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.F64Clip.module 0 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (absBits x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func0Def) rfl ?_ (by decide)
  change wp Project.F64Clip.module func0 _ initial (func0Def.toLocals [.i64 x]) env
  unfold func0
  wp_fixed_frame [func0Def]
  simp [absBits]

theorem finite_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.F64Clip.module 1 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (if finiteBits x then 1 else 0)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_ (by decide)
  change wp Project.F64Clip.module func1 _ initial (func1Def.toLocals [.i64 x]) env
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
         simp)
  all_goals simp [finiteBits, h]

theorem validBound_exact (env : HostEnv Unit) (initial : Store Unit) (bound : UInt64) :
    TerminatesWith env Project.F64Clip.module 2 initial [.i64 bound]
      (fun final values => final = initial ∧ values = [.i64 (if validBound bound then 1 else 0)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func2Def) rfl ?_ (by decide)
  change wp Project.F64Clip.module func2 _ initial (func2Def.toLocals [.i64 bound]) env
  unfold func2
  cases hf : finiteBits bound
  all_goals by_cases hs : bound < 0x8000000000000000
  all_goals by_cases hz : absBits bound = 0
  all_goals by_cases hb : absBits bound ≤ 0x4024000000000000
  all_goals
    repeat first
      | wp_fixed_frame [func2Def, hf, hs, hz, hb, reduceIte]
      | (refine wp_call_tw (finite_exact env initial _) ?_; rintro st values ⟨hst, rfl⟩; subst st)
      | (refine wp_call_tw (absolute_exact env initial _) ?_; rintro st values ⟨hst, rfl⟩; subst st)
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [hs])
  all_goals simp [validBound, hf, hs, hz, hb]

theorem negative_absolute_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.F64Clip.module 4 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (negativeAbsBits x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func4Def) rfl ?_ (by decide)
  change wp Project.F64Clip.module func4 _ initial (func4Def.toLocals [.i64 x]) env
  unfold func4
  wp_fixed_frame [func4Def]
  refine wp_call_tw (absolute_exact env initial x) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func4Def]
  simp [negativeAbsBits]

theorem clip_exact (env : HostEnv Unit) (initial : Store Unit) (bound x : UInt64) :
    TerminatesWith env Project.F64Clip.module 5 initial [.i64 x, .i64 bound]
      (fun final values => final = initial ∧ values = [.i64 (clip bound x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func5Def) rfl ?_ (by decide)
  change wp Project.F64Clip.module func5 _ initial (func5Def.toLocals [.i64 bound, .i64 x]) env
  unfold func5
  by_cases h : absBits x ≤ absBits bound
  all_goals by_cases hs : x < 0x8000000000000000
  all_goals
    repeat first
      | wp_fixed_frame [func5Def, h, hs, reduceIte]
      | (refine wp_call_tw (absolute_exact env initial _) ?_; rintro st values ⟨hst, rfl⟩; subst st)
      | (refine wp_call_exact_append
          (absolute_exact env initial bound) rfl rfl rfl [.i64 (absBits x)] rfl ?_)
      | (refine wp_call_tw (negative_absolute_exact env initial _) ?_; rintro st values ⟨hst, rfl⟩; subst st)
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [h, hs])
  all_goals simp [clip, h, hs]

#print axioms validBound_exact
#print axioms clip_exact
end Project.F64Clip.Spec
