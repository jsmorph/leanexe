import Project.Drone.ExecutionEdgePrefix
import Project.ProofKit.ConstIf
import Project.Drone.EdgeSource
import Project.Drone.ExecutionEdgeTail

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone


set_option maxHeartbeats 3000000 in
theorem edgeTicks_moving_exact (env : HostEnv Unit) (initial : Store Unit)
    (r0 r1 z0 z1 u v : UInt64) (hMoving : u + v ≠ 0) :
    TerminatesWith env «module» 9 initial
      [.i64 v, .i64 u, .i64 z1, .i64 z0, .i64 r1, .i64 r0]
      (fun final values => final = initial ∧ values = [.i64 (edgeTicks r0 r1 z0 z1 u v)]) := by
  apply edgeTicks_entry env initial r0 r1 z0 z1 u v
  simp only [func9, List.drop, edgeStartFrame]
  wp_fixed_frame [hMoving]
  apply wp_constIf rfl
  wp_fixed_frame [hMoving]
  apply wp_constIf rfl
  wp_fixed_frame [hMoving]
  refine wp_iff_cons rfl ?_
  simp [hMoving]
  try wp_fixed_frame [hMoving]
  try wp_fixed_frame [hMoving]
  refine wp_call_tw ((distance_exact env initial (u*u) (v*v)).append_args
    (f := func5Def) rfl rfl rfl [.i64 200]) ?_
  rintro final values ⟨out, rfl, hFinal, rfl⟩
  subst final
  wp_fixed_frame [func5Def]
  by_cases hSpeed : 200 < distance (u*u) (v*v)
  · refine wp_iff_cons rfl ?_
    simp [hSpeed]
    try wp_fixed_frame [func9Def]
    simp [edgeTicks_eq, hMoving, hSpeed]
  · refine wp_iff_cons rfl ?_
    simp only [hSpeed, ↓reduceIte, ne_eq, not_true_eq_false]
    change wp «module» (movingTailExpr.program 15 ++ []) _ initial
      ((movingTailState r0 r1 z0 z1 u v (distance z0 z1)).toLocals []) env
    obtain ⟨next, hEval, hParams, hLocals⟩ :=
      movingTail_eval r0 r1 z0 z1 u v (distance z0 z1)
    refine ScalarTransition.Expr.program_spec movingTailExpr 15 _ next _ []
      «module» env initial [] _ hEval ?_
    rw [wp_nil]
    simp [wp_simp, ScalarTransition.State.toLocals, Locals.get, Locals.set?,
      List.getElem?_set, List.length_set, hParams, hLocals, func9Def,
      edgeTicks_eq, hMoving, hSpeed, movingTailValue]

#print axioms edgeTicks_moving_exact
end Project.Drone.Execution
