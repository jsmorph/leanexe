import Project.ExpNeg.ReduceExecution
import Project.ExpNeg.SquareExecution
import Interpreter.Wasm.Wp.Call

namespace Project.ExpNeg.Spec
open Wasm

theorem domain_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.ExpNeg.module 0 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (if inDomain x then 1 else 0)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func0Def) rfl ?_ (by decide)
  change wp Project.ExpNeg.module func0 _ initial (func0Def.toLocals [.i64 x]) env
  unfold func0
  have hneg : (-4503599627370496 : UInt64) = 0xFFF0000000000000 := by decide
  by_cases hz : x = 0
  all_goals by_cases hl : (0x8000000000000000 : UInt64) ≤ x
  all_goals by_cases hu : x < (0xFFF0000000000000 : UInt64)
  all_goals
    repeat first
      | wp_fixed_frame [func0Def, reduceIte, *]
      | (refine wp_iff_cons rfl ?_; simp [*])
  all_goals simp [inDomain, hz, hl, hu]

set_option maxRecDepth 4096 in
theorem polynomial_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.ExpNeg.module 4 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (polynomial x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func4Def) rfl ?_ (by decide)
  change wp Project.ExpNeg.module func4 _ initial (func4Def.toLocals [.i64 x]) env
  unfold func4
  wp_fixed_frame [func4Def]
  simp only [polynomial, Wasm.f64Mul, Wasm.f64Add, List.append_nil, true_and]

theorem evaluate_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.ExpNeg.module 6 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (evaluate x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func6Def) rfl ?_ (by decide)
  change wp Project.ExpNeg.module func6 _ initial (func6Def.toLocals [.i64 x]) env
  unfold func6
  wp_fixed_frame [func6Def]
  refine wp_iff_cons rfl ?_
  by_cases ht : (0xC050000000000000 : UInt64) < x
  · simp only [ht, ite_true]
    wp_fixed_frame [func6Def]
    simp [evaluate, ht]
  · simp only [ht, ite_false, ne_self_iff_false]
    wp_fixed_frame [func6Def]
    refine wp_call_tw (reduce_exact env initial 6 0 x (by norm_num)) ?_
    rintro st values ⟨hs, rfl⟩
    subst st
    wp_fixed_frame [func6Def]
    refine wp_call_tw (polynomial_exact env initial (reduce 6 x 0).word) ?_
    rintro st values ⟨hs, rfl⟩
    subst st
    wp_fixed_frame [func6Def]
    have hc : (reduce 6 x 0).squares < 2^64 :=
      (reduce_count_le 6 0 x).trans_lt (by norm_num)
    refine wp_call_tw (square_exact env initial (reduce 6 x 0).squares (polynomial (reduce 6 x 0).word) hc) ?_
    rintro st values ⟨hs, rfl⟩
    subst st
    wp_fixed_frame [func6Def]
    simp [evaluate, ht]

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (x : UInt64),
    TerminatesWith env m 7 initial [.i64 x]
      (fun final values => final = initial ∧
        values = [.i64 (expNeg x).bits, .i64 (expNeg x).status])

theorem expNeg_exact : ExactSpecFor Project.ExpNeg.module := by
  intro env initial x
  refine TerminatesWith.of_wp_entry_for (f := func7Def) rfl ?_ (by decide)
  change wp Project.ExpNeg.module func7 _ initial (func7Def.toLocals [.i64 x]) env
  unfold func7
  wp_fixed_frame [func7Def]
  refine wp_call_tw (domain_exact env initial x) ?_
  rintro st values ⟨hs, rfl⟩
  subst st
  cases hd : inDomain x
  all_goals
    repeat first
      | wp_fixed_frame [func7Def, hd, reduceIte]
      | (refine wp_iff_cons rfl ?_; simp [hd])
  · simp [expNeg, hd]
  · refine wp_call_tw (evaluate_exact env initial x) ?_
    rintro st values ⟨hs, rfl⟩
    subst st
    wp_fixed_frame [func7Def]
    simp [expNeg, hd]

#print axioms polynomial_exact
#print axioms evaluate_exact
#print axioms expNeg_exact
end Project.ExpNeg.Spec
