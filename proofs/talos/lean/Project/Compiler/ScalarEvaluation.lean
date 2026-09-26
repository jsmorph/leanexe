import Project.Compiler.ScalarState

namespace Project.Compiler.ScalarLowering

open Project.ProofKit.ScalarTransition (State)
open LeanExe.Wasm.ScalarDescriptor (Expr Cond)

theorem scratch_guard (op : LeanExe.Wasm.ScalarDescriptor.U64Op) :
    (op == .divU || op == .remU) =
      decide (operation op = .divU ∨ operation op = .remU) := by
  cases op <;> decide

mutual
  theorem expression_eval (e : Expr) (scratch : Nat)
      {source : LeanExe.IR.ScalarStore} {state : State} {value : UInt64}
      (evaluation : e.eval source = some value) (agree : Agrees source state)
      (above : source.length ≤ scratch)
      (room : scratch + e.scratchWidth ≤ capacity state) :
      ∃ next, (expression e).eval scratch state = some (value, next) ∧
        Agrees source next ∧ capacity next = capacity state := by
    cases e with
    | get i =>
      refine ⟨state, ?_, agree, rfl⟩
      simpa [expression, Project.ProofKit.ScalarTransition.Expr.eval,
        agree i value evaluation]
    | const v =>
      simp only [Expr.eval, Option.some.injEq] at evaluation
      subst value
      exact ⟨state, by simp [expression, Project.ProofKit.ScalarTransition.Expr.eval], agree, rfl⟩
    | bin op a b =>
      simp only [Expr.eval, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at evaluation
      obtain ⟨x, hx, y, hy, rfl⟩ := evaluation
      by_cases special : operation op = .divU ∨ operation op = .remU
      · simp only [Expr.scratchWidth, scratch_guard, special, decide_true, ite_true] at room
        obtain ⟨sa, ha, aa, ca⟩ := expression_eval a (scratch + 2) hx agree (by omega) (by omega)
        obtain ⟨wa, hwa, awa, cwa⟩ := write_scratch x aa above (by omega)
        obtain ⟨sb, hb, ab, cb⟩ := expression_eval b (scratch + 2) hy awa (by omega) (by omega)
        obtain ⟨wb, hwb, awb, cwb⟩ := write_scratch (index := scratch + 1) y ab (by omega) (by omega)
        refine ⟨wb, ?_, awb, by omega⟩
        simp [expression, Project.ProofKit.ScalarTransition.Expr.eval, special, ha, hwa, hb, hwb]
      · simp only [Expr.scratchWidth, scratch_guard, special, decide_false, Bool.false_eq_true, ite_false] at room
        obtain ⟨sa, ha, aa, ca⟩ := expression_eval a scratch hx agree above (by omega)
        obtain ⟨sb, hb, ab, cb⟩ := expression_eval b scratch hy aa above (by omega)
        refine ⟨sb, ?_, ab, by omega⟩
        simp [expression, Project.ProofKit.ScalarTransition.Expr.eval, special, ha, hb]
    | ite c a b =>
      simp only [Expr.eval, bind, Option.bind_eq_some_iff] at evaluation
      obtain ⟨flag, hc, hv⟩ := evaluation
      simp only [Expr.scratchWidth] at room
      obtain ⟨sc, hec, ac, cc⟩ := condition_eval c scratch hc agree above (by omega)
      cases flag
      · simp only [Bool.false_eq_true, ite_false] at hv
        obtain ⟨sb, hb, ab, cb⟩ := expression_eval b scratch hv ac above (by omega)
        refine ⟨sb, ?_, ab, by omega⟩
        simp [expression, Project.ProofKit.ScalarTransition.Expr.eval, hec, hb]
      · simp only [ite_true] at hv
        obtain ⟨sa, ha, aa, ca⟩ := expression_eval a scratch hv ac above (by omega)
        refine ⟨sa, ?_, aa, by omega⟩
        simp [expression, Project.ProofKit.ScalarTransition.Expr.eval, hec, ha]
  termination_by sizeOf e

  theorem condition_eval (c : Cond) (scratch : Nat)
      {source : LeanExe.IR.ScalarStore} {state : State} {value : Bool}
      (evaluation : c.eval source = some value) (agree : Agrees source state)
      (above : source.length ≤ scratch)
      (room : scratch + c.scratchWidth ≤ capacity state) :
      ∃ next, (condition c).eval scratch state = some (value, next) ∧
        Agrees source next ∧ capacity next = capacity state := by
    cases c with
    | true | false =>
      simp only [Cond.eval, Option.some.injEq] at evaluation
      subst value
      exact ⟨state, by simp [condition, Project.ProofKit.ScalarTransition.Expr.eval], agree, rfl⟩
    | eq a b | ne a b | ltU a b | leU a b =>
      simp only [Cond.eval, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at evaluation
      obtain ⟨x, hx, y, hy, rfl⟩ := evaluation
      simp only [Cond.scratchWidth] at room
      obtain ⟨sa, ha, aa, ca⟩ := expression_eval a scratch hx agree above (by omega)
      obtain ⟨sb, hb, ab, cb⟩ := expression_eval b scratch hy aa above (by omega)
      refine ⟨sb, ?_, ab, by omega⟩
      simp [condition, Project.ProofKit.ScalarTransition.Expr.eval, ha, hb]
    | not c =>
      simp only [Cond.eval, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at evaluation
      obtain ⟨flag, hc, rfl⟩ := evaluation
      obtain ⟨sc, hec, ac, cc⟩ := condition_eval c scratch hc agree above room
      refine ⟨sc, ?_, ac, cc⟩
      simp [condition, Project.ProofKit.ScalarTransition.Expr.eval, hec]
    | and a b | or a b =>
      simp only [Cond.eval, bind, Option.bind_eq_some_iff] at evaluation
      obtain ⟨flag, ha, hv⟩ := evaluation
      simp only [Cond.scratchWidth] at room
      obtain ⟨sa, hea, aa, ca⟩ := condition_eval a scratch ha agree above (by omega)
      cases flag <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure, Option.some.injEq] at hv
      all_goals first
        | (subst value; exact ⟨sa, by simp [condition, Project.ProofKit.ScalarTransition.Expr.eval, hea], aa, ca⟩)
        | (obtain ⟨sb, heb, ab, cb⟩ := condition_eval b scratch hv aa above (by omega)
           exact ⟨sb, by simp [condition, Project.ProofKit.ScalarTransition.Expr.eval, hea, heb], ab, by omega⟩)
  termination_by sizeOf c
end

end Project.Compiler.ScalarLowering
