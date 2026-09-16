import Project.ProofKit.FixedFrame
import Project.Softmax.Program
import Project.Softmax.Model
import Project.TalosCompat
import Interpreter.Wasm.Wp.Call

namespace Project.Softmax.Spec
open Wasm

set_option maxHeartbeats 2000000

theorem bounded_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.Softmax.module 0 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (if bounded x then 1 else 0)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func0Def) rfl ?_ (by decide)
  change wp Project.Softmax.module func0 _ initial (func0Def.toLocals [.i64 x]) env
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

theorem domain_exact (env : HostEnv Unit) (initial : Store Unit) (n a b c d : UInt64) :
    TerminatesWith env Project.Softmax.module 1 initial [.i64 d, .i64 c, .i64 b, .i64 a, .i64 n]
      (fun final values => final = initial ∧ values = [.i64 (if inDomain n a b c d then 1 else 0)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_ (by decide)
  change wp Project.Softmax.module func1 _ initial (func1Def.toLocals [.i64 n, .i64 a, .i64 b, .i64 c, .i64 d]) env
  unfold func1
  by_cases hn : (0 : UInt64) < n
  all_goals by_cases hn4 : n ≤ (4 : UInt64)
  all_goals cases ha : bounded a
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
  all_goals simp [inDomain, *]

theorem maximum_exact (env : HostEnv Unit) (initial : Store Unit) (a b : UInt64) :
    TerminatesWith env Project.Softmax.module 2 initial [.i64 b, .i64 a]
      (fun final values => final = initial ∧ values = [.i64 (maximum a b)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func2Def) rfl ?_ (by decide)
  change wp Project.Softmax.module func2 _ initial (func2Def.toLocals [.i64 a, .i64 b]) env
  unfold func2
  by_cases ha : a < (0x8000000000000000 : UInt64)
  all_goals by_cases hb : b < (0x8000000000000000 : UInt64)
  all_goals by_cases hab : a ≤ b
  all_goals
    repeat
      first
      | wp_fixed_frame [func2Def, reduceIte, *]
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [*])
  all_goals simp [maximum, *]

theorem activeScore_exact (env : HostEnv Unit) (initial : Store Unit) (n i x first : UInt64) :
    TerminatesWith env Project.Softmax.module 3 initial [.i64 first, .i64 x, .i64 i, .i64 n]
      (fun final values => final = initial ∧ values = [.i64 (activeScore n i x first)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func3Def) rfl ?_ (by decide)
  change wp Project.Softmax.module func3 _ initial (func3Def.toLocals [.i64 n, .i64 i, .i64 x, .i64 first]) env
  unfold func3
  by_cases h : i < n
  all_goals
    repeat
      first
      | wp_fixed_frame [func3Def, reduceIte, *]
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [*])
  all_goals simp [activeScore, h]

theorem polynomial_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.Softmax.module 5 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (ExpSmall.polynomial x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func5Def) rfl ?_ (by decide)
  change wp Project.Softmax.module func5 _ initial (func5Def.toLocals [.i64 x]) env
  unfold func5
  wp_fixed_frame [func5Def]
  simp [ExpSmall.polynomial, Wasm.f64Mul, Wasm.f64Add]

theorem evaluate_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.Softmax.module 6 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (ExpWide.evaluate x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func6Def) rfl ?_ (by decide)
  change wp Project.Softmax.module func6 _ initial (func6Def.toLocals [.i64 x]) env
  unfold func6
  wp_fixed_frame [func6Def]
  refine wp_call_tw (polynomial_exact env initial _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func6Def]
  simp [ExpWide.evaluate, Wasm.f64Mul, Wasm.f64Div]

theorem weight_exact (env : HostEnv Unit) (initial : Store Unit) (n i x m : UInt64) :
    TerminatesWith env Project.Softmax.module 7 initial [.i64 m, .i64 x, .i64 i, .i64 n]
      (fun final values => final = initial ∧ values = [.i64 (weight n i x m)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func7Def) rfl ?_ (by decide)
  change wp Project.Softmax.module func7 _ initial (func7Def.toLocals [.i64 n, .i64 i, .i64 x, .i64 m]) env
  unfold func7
  by_cases h : i < n
  all_goals
    repeat
      first
      | wp_fixed_frame [func7Def, reduceIte, *]
      | (refine wp_call_tw (evaluate_exact env initial _) ?_
         rintro st values ⟨hst, rfl⟩
         subst st)
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [*])
  all_goals simp [weight, h, Wasm.f64Sub]

theorem total_exact (env : HostEnv Unit) (initial : Store Unit) (a b c d : UInt64) :
    TerminatesWith env Project.Softmax.module 8 initial [.i64 d, .i64 c, .i64 b, .i64 a]
      (fun final values => final = initial ∧ values = [.i64 (total a b c d)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func8Def) rfl ?_ (by decide)
  change wp Project.Softmax.module func8 _ initial (func8Def.toLocals [.i64 a, .i64 b, .i64 c, .i64 d]) env
  unfold func8
  wp_fixed_frame [func8Def]
  simp [total, Wasm.f64Add]

theorem probability_exact (env : HostEnv Unit) (initial : Store Unit) (n i w den : UInt64) :
    TerminatesWith env Project.Softmax.module 9 initial [.i64 den, .i64 w, .i64 i, .i64 n]
      (fun final values => final = initial ∧ values = [.i64 (probability n i w den)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func9Def) rfl ?_ (by decide)
  change wp Project.Softmax.module func9 _ initial (func9Def.toLocals [.i64 n, .i64 i, .i64 w, .i64 den]) env
  unfold func9
  by_cases h : i < n
  all_goals
    repeat
      first
      | wp_fixed_frame [func9Def, reduceIte, *]
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [*])
  all_goals simp [probability, h, Wasm.f64Div]

def resultWords (r : Result) : List Value :=
  [.i64 r.p3, .i64 r.p2, .i64 r.p1, .i64 r.p0, .i64 r.status]

#print axioms domain_exact
#print axioms weight_exact
end Project.Softmax.Spec
