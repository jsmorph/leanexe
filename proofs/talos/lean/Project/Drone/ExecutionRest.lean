import Project.Drone.ExecutionSqrt
import Project.ProofKit.CallRemainder

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone

private theorem restSeconds_eq (dh : UInt64) :
    restSeconds dh =
      let duration := if (3 * dh + 39) / 40 ≤ ceilSqrt ((3 * dh + 1) / 2)
        then ceilSqrt ((3 * dh + 1) / 2) else (3 * dh + 39) / 40
      if 25 ≤ duration then duration else 25 := rfl

set_option maxHeartbeats 2000000 in
theorem restSeconds_exact (env : HostEnv Unit) (initial : Store Unit) (dh : UInt64) :
    TerminatesWith env «module» 8 initial [.i64 dh]
      (fun final values => final = initial ∧ values = [.i64 (restSeconds dh)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func8Def) rfl ?_
  change wp «module» func8 _ initial
    { params := [.i64 dh], locals := List.replicate 4 (.i64 0) } env
  simp only [func8]
  by_cases hInner : (3 * dh + 39) / 40 ≤ ceilSqrt ((3 * dh + 1) / 2)
  · by_cases hOuter : 25 ≤ ceilSqrt ((3 * dh + 1) / 2)
    all_goals
      repeat' ((try wp_fixed_frame [func8Def, hInner, hOuter,
        show (2 : UInt64) ≠ 0 by decide, show (40 : UInt64) ≠ 0 by decide]) <;> first
        | (solve | simp [restSeconds_eq, hInner, hOuter])
        | (refine wp_call_tw ((ceilSqrt_exact env initial _).append_args (f := func7Def) rfl rfl rfl _) ?_;
           rintro final values ⟨out, rfl, hFinal, rfl⟩; subst final)
        | (refine wp_iff_cons rfl ?_; simp [hInner, hOuter]))
    all_goals ((try wp_fixed_frame [func8Def]); simp [restSeconds_eq, hInner, hOuter])
  · by_cases hOuter : 25 ≤ (3 * dh + 39) / 40
    all_goals
      repeat' ((try wp_fixed_frame [func8Def, hInner, hOuter,
        show (2 : UInt64) ≠ 0 by decide, show (40 : UInt64) ≠ 0 by decide]) <;> first
        | (solve | simp [restSeconds_eq, hInner, hOuter])
        | (refine wp_call_tw ((ceilSqrt_exact env initial _).append_args (f := func7Def) rfl rfl rfl _) ?_;
           rintro final values ⟨out, rfl, hFinal, rfl⟩; subst final)
        | (refine wp_iff_cons rfl ?_; simp [hInner, hOuter]))
    all_goals ((try wp_fixed_frame [func8Def]); simp [restSeconds_eq, hInner, hOuter])

#print axioms restSeconds_exact
end Project.Drone.Execution
