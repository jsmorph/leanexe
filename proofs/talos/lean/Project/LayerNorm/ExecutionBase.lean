import Project.ProofKit.FixedFrame
import Project.LayerNorm.Program
import Project.LayerNorm.Model
import Project.TalosCompat
import Interpreter.Wasm.Wp.Call

namespace Project.LayerNorm.Spec
open Wasm

set_option maxHeartbeats 2000000

theorem bounded_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.LayerNorm.module 0 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (if bounded x then 1 else 0)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func0Def) rfl ?_ (by decide)
  change wp Project.LayerNorm.module func0 _ initial (func0Def.toLocals [.i64 x]) env
  unfold func0
  by_cases h : x &&& 0x7FFFFFFFFFFFFFFF ≤ (0x4010000000000000 : UInt64)
  all_goals
    repeat
      first
      | wp_fixed_frame [func0Def, reduceIte, *]
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [*])
  all_goals simp [bounded, h]

theorem rowBounded_exact (env : HostEnv Unit) (initial : Store Unit) (a b c d : UInt64) :
    TerminatesWith env Project.LayerNorm.module 1 initial [.i64 d, .i64 c, .i64 b, .i64 a]
      (fun final values => final = initial ∧ values = [.i64 (if rowBounded a b c d then 1 else 0)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_ (by decide)
  change wp Project.LayerNorm.module func1 _ initial (func1Def.toLocals [.i64 a, .i64 b, .i64 c, .i64 d]) env
  unfold func1
  cases ha : bounded a
  all_goals cases hb : bounded b
  all_goals cases hc : bounded c
  all_goals cases hd : bounded d
  all_goals
    repeat
      first
      | wp_fixed_frame [func1Def, reduceIte, *]
      | (refine wp_call_tw (bounded_exact env initial _) ?_
         rintro st values ⟨hst, rfl⟩
         subst st)
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [*])
  all_goals simp [rowBounded, *]

theorem average_exact (env : HostEnv Unit) (initial : Store Unit) (a b c d : UInt64) :
    TerminatesWith env Project.LayerNorm.module 2 initial [.i64 d, .i64 c, .i64 b, .i64 a]
      (fun final values => final = initial ∧ values = [.i64 (average a b c d)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func2Def) rfl ?_ (by decide)
  change wp Project.LayerNorm.module func2 _ initial (func2Def.toLocals [.i64 a, .i64 b, .i64 c, .i64 d]) env
  unfold func2
  wp_fixed_frame [func2Def]
  simp [average, Wasm.f64Add, Wasm.f64Div]

theorem denominator_exact (env : HostEnv Unit) (initial : Store Unit) (a b c d : UInt64) :
    TerminatesWith env Project.LayerNorm.module 3 initial [.i64 d, .i64 c, .i64 b, .i64 a]
      (fun final values => final = initial ∧ values = [.i64 (denominator a b c d)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func3Def) rfl ?_ (by decide)
  change wp Project.LayerNorm.module func3 _ initial (func3Def.toLocals [.i64 a, .i64 b, .i64 c, .i64 d]) env
  unfold func3
  wp_fixed_frame [func3Def]
  refine wp_call_tw (average_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func3Def]
  simp [denominator, Wasm.f64Mul, Wasm.f64Add, Wasm.f64Sqrt]

theorem affine_exact (env : HostEnv Unit) (initial : Store Unit) (x d g b : UInt64) :
    TerminatesWith env Project.LayerNorm.module 4 initial [.i64 b, .i64 g, .i64 d, .i64 x]
      (fun final values => final = initial ∧ values = [.i64 (affine x d g b)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func4Def) rfl ?_ (by decide)
  change wp Project.LayerNorm.module func4 _ initial (func4Def.toLocals [.i64 x, .i64 d, .i64 g, .i64 b]) env
  unfold func4
  wp_fixed_frame [func4Def]
  simp [affine, Wasm.f64Div, Wasm.f64Mul, Wasm.f64Add]

def resultWords (r : Result) : List Value :=
  [.i64 r.y3, .i64 r.y2, .i64 r.y1, .i64 r.y0, .i64 r.status]

#print axioms rowBounded_exact
#print axioms denominator_exact
end Project.LayerNorm.Spec
