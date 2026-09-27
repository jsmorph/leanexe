import Project.ProofKit.ScalarTransition

namespace Project.ProofKit.ScalarTransition

open Wasm

def guardedBackEdgeProgram (scratch : Nat) (body : Stmt)
    (condition : Expr .bool) (continuing : Stmt) : Program :=
  body.program scratch ++ condition.program scratch ++ [.br_if 1] ++
    continuing.program scratch ++ [.br 0]

set_option maxHeartbeats 1000000 in
theorem guardedBackEdgeProgram_spec
    (scratch : Nat) (body : Stmt) (condition : Expr .bool)
    (continuing : Stmt) (initial afterBody afterCondition : State)
    (result : Bool) (values : List Value)
    (module_ : Module) (env : HostEnv α) (store : Store α)
    (rest : Program) (Q : Assertion α)
    (hBody : body.eval scratch initial = some afterBody)
    (hCondition : condition.eval scratch afterBody =
      some (result, afterCondition))
    (hExit : result = true →
      Q (.Break 1 store (afterCondition.toLocals values)))
    (hContinue : result = false →
      ∃ afterContinue,
        continuing.eval scratch afterCondition = some afterContinue ∧
        Q (.Break 0 store (afterContinue.toLocals values))) :
    wp module_
      (guardedBackEdgeProgram scratch body condition continuing ++ rest)
      Q store (initial.toLocals values) env := by
  unfold guardedBackEdgeProgram
  simp only [List.append_assoc]
  apply Stmt.program_spec (statement := body) (scratch := scratch)
    (state := initial) (next := afterBody) (values := values)
    (module_ := module_) (env := env) (store := store)
    (rest := condition.program scratch ++
      ([Instruction.br_if 1] ++
        (continuing.program scratch ++ ([Instruction.br 0] ++ rest))))
    (Q := Q) hBody
  apply Expr.program_spec (expression := condition) (scratch := scratch)
    (state := afterBody) (next := afterCondition) (result := result)
    (values := values) (module_ := module_) (env := env) (store := store)
    (rest := [Instruction.br_if 1] ++
      (continuing.program scratch ++ ([Instruction.br 0] ++ rest)))
    (Q := Q) hCondition
  cases result
  · rcases hContinue rfl with ⟨afterContinue, hContinuing, hNext⟩
    simp only [List.cons_append, Wasm.wp_br_if_cons, ScalarType.value]
    simp only [Bool.false_eq_true, ↓reduceIte, State.toLocals, List.nil_append]
    apply Stmt.program_spec (statement := continuing) (scratch := scratch)
      (state := afterCondition) (next := afterContinue) (values := values)
      (module_ := module_) (env := env) (store := store)
      (rest := [Instruction.br 0] ++ rest) (Q := Q) hContinuing
    simpa [wp_simp, State.toLocals] using hNext
  · simpa [wp_simp, State.toLocals, ScalarType.value] using hExit rfl

end Project.ProofKit.ScalarTransition
