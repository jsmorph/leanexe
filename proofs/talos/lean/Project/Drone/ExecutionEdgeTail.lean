import Project.Drone.ExecutionEdgeTailModel

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone
open ScalarTransition

macro "finish_edge_eval" : tactic => `(tactic|
  (simp only [movingTailExpr, clearanceExpr, durationExpr, movingTailWords,
    movingTailValue, Expr.evalU64, U64State.get, U64State.set?, U64Op.apply,
    Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
    Option.bind_none, Option.map, List.length, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
    reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true,
    Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true,
    decide_true, decide_false, ite_true, ite_false, show (5 : UInt64) ≠ 0 by decide, *]
   simp))

set_option maxHeartbeats 1000000 in
theorem movingTail_evalU64 (r0 r1 z0 z1 u v dh : UInt64) :
    ∃ next, movingTailExpr.evalU64 15 (movingTailWords r0 r1 z0 z1 u v dh) =
      some (movingTailValue r0 r1 z0 z1 u v dh, next) ∧
      next.params.length = 6 ∧ next.locals.length = 13 := by
  by_cases h1 : 8000 < 3*dh*(u+v)
  · finish_edge_eval
  · by_cases h2 : 160000 < 6*dh*(u+v)*(u+v)
    · finish_edge_eval
    · by_cases hr : r0 ≤ r1
      · by_cases hc : 3*(u+v)*(z0-r0) < 2*u*(r1-r0)
        · finish_edge_eval
        · by_cases hz : (u+v)/5 = 0 <;> finish_edge_eval
      · by_cases hc : 3*(u+v)*(z1-r1) < 2*v*(r0-r1)
        · finish_edge_eval
        · by_cases hz : (u+v)/5 = 0 <;> finish_edge_eval

theorem movingTail_eval (r0 r1 z0 z1 u v dh : UInt64) :
    ∃ next, movingTailExpr.eval 15 (movingTailState r0 r1 z0 z1 u v dh) =
      some (movingTailValue r0 r1 z0 z1 u v dh, next) ∧
      next.params.length = 6 ∧ next.locals.length = 13 := by
  obtain ⟨next, hEval, hParams, hLocals⟩ := movingTail_evalU64 r0 r1 z0 z1 u v dh
  refine ⟨next.toState, ?_, ?_, ?_⟩
  · rw [movingTailState, Expr.eval_toState, hEval]
    rfl
  · simpa [U64State.toState] using hParams
  · simpa [U64State.toState] using hLocals

#print axioms movingTail_evalU64
#print axioms movingTail_eval
end Project.Drone.Execution
