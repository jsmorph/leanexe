import Project.Compiler.ScalarLoopTrace

namespace Project.Compiler.ScalarLowering

open Project.ProofKit.ScalarTransition (State WhileTrace)
open LeanExe.Wasm.ScalarDescriptor (Expr Cond Stmt While)

/-- Every finite IR loop execution gives a finite trace of its emitted scalar operations. -/
theorem while_eval {irCondition : LeanExe.IR.Cond} {irBody : LeanExe.IR.Stmt}
    {source nextSource : LeanExe.IR.ScalarStore}
    (evaluated : (LeanExe.IR.Stmt.while irCondition irBody).ScalarEval source nextSource)
    (descriptor : While)
    (matchedCondition : Cond.ofIR irCondition = some descriptor.condition)
    (matchedBody : Stmt.ofIR irBody = some descriptor.body)
    (scratch : Nat) (initial : State) (agree : Agrees source initial)
    (above : source.length ≤ scratch)
    (room : scratch + descriptor.scratchWidth ≤ capacity initial) :
    ∃ final count, WhileTrace (condition descriptor.condition) (statement descriptor.body)
      scratch initial final count ∧ Agrees nextSource final ∧ capacity final = capacity initial := by
  generalize shape : LeanExe.IR.Stmt.while irCondition irBody = ir at evaluated
  induction evaluated generalizing initial with
  | skip | assign | seq | iteTrue | iteFalse => cases shape
  | whileFalse tested =>
    cases shape
    obtain ⟨tested, rfl⟩ := Cond.ofIR_eval tested matchedCondition
    obtain ⟨final, executed, agrees, size⟩ := condition_eval descriptor.condition scratch tested agree above
      (by simp only [While.scratchWidth] at room; omega)
    exact ⟨final, 0, .done executed, agrees, size⟩
  | whileTrue tested executed remaining bodyIH restIH =>
    cases shape
    obtain ⟨tested, rfl⟩ := Cond.ofIR_eval tested matchedCondition
    obtain ⟨afterCondition, conditionEval, conditionAgrees, conditionSize⟩ :=
      condition_eval descriptor.condition scratch tested agree above
        (by simp only [While.scratchWidth] at room; omega)
    have bodyEval := Stmt.ofIR_eval executed matchedBody
    have length := Stmt.eval_length bodyEval
    obtain ⟨afterBody, bodyExecuted, bodyAgrees, bodySize⟩ :=
      statement_eval descriptor.body scratch bodyEval conditionAgrees above (by omega)
        (by simp only [While.scratchWidth] at room; omega)
    obtain ⟨final, count, trace, finalAgrees, finalSize⟩ :=
      restIH afterBody bodyAgrees (by omega) (by omega) rfl
    exact ⟨final, count + 1, .step conditionEval bodyExecuted trace, finalAgrees, by omega⟩

end Project.Compiler.ScalarLowering
