import Project.ProofKit.ScalarFrame

namespace Project.ProofKit.ScalarTransition
open Wasm

def Expr.typedIteProgram (condition : Expr .bool) (thenValue elseValue : Expr .u64)
    (scratch : Nat) (paramTypes resultTypes : List ValueType) : Program :=
  condition.program scratch ++
    [.iff 0 1 (thenValue.program scratch) (elseValue.program scratch) paramTypes resultTypes]

theorem Expr.typedIteProgram_spec (condition : Expr .bool) (thenValue elseValue : Expr .u64)
    (scratch : Nat) (paramTypes resultTypes : List ValueType)
    (state next : State) (result : UInt64) (values : List Value)
    (module_ : Module) (env : HostEnv α) (store : Store α) (rest : Program) (Q : Assertion α)
    (hEval : (Expr.ite condition thenValue elseValue).eval scratch state = some (result, next))
    (hNext : wp module_ rest Q store (next.toLocals (.i64 result :: values)) env) :
    wp module_ (typedIteProgram condition thenValue elseValue scratch paramTypes resultTypes ++ rest)
      Q store (state.toLocals values) env := by
  simp only [Expr.eval] at hEval
  simp only [typedIteProgram, List.append_assoc]
  rcases hCondition : condition.eval scratch state with _ | ⟨conditionValue, afterCondition⟩
  · simp [hCondition] at hEval
  cases conditionValue
  · rcases hElse : elseValue.eval scratch afterCondition with _ | ⟨value, afterValue⟩
    · simp [hCondition, hElse] at hEval
    simp [hCondition, hElse] at hEval
    obtain ⟨rfl, rfl⟩ := hEval
    apply condition.program_spec scratch state afterCondition false values module_ env store _ Q hCondition
    simp only [List.cons_append, List.nil_append, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simp)]
    rw [← List.append_nil (elseValue.program scratch)]
    apply elseValue.program_spec scratch afterCondition afterValue value values module_ env store [] _ hElse
    simpa [wp_simp, State.toLocals, ScalarType.value] using hNext
  · rcases hThen : thenValue.eval scratch afterCondition with _ | ⟨value, afterValue⟩
    · simp [hCondition, hThen] at hEval
    simp [hCondition, hThen] at hEval
    obtain ⟨rfl, rfl⟩ := hEval
    apply condition.program_spec scratch state afterCondition true values module_ env store _ Q hCondition
    simp only [List.cons_append, List.nil_append, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by simp)]
    rw [← List.append_nil (thenValue.program scratch)]
    apply thenValue.program_spec scratch afterCondition afterValue value values module_ env store [] _ hThen
    simpa [wp_simp, State.toLocals, ScalarType.value] using hNext

theorem Stmt.typedIteAssignProgram_frame_spec (index : Nat)
    (condition : Expr .bool) (thenValue elseValue : Expr .u64)
    (scratch : Nat) (paramTypes resultTypes : List ValueType) (frame next : Locals)
    (module_ : Module) (env : HostEnv Unit) (store : Store Unit)
    (hValues : frame.values = []) (hNextValues : next.values = [])
    (hEval : (Stmt.assign index (.ite condition thenValue elseValue)).eval scratch
      (State.ofLocals frame) = some (State.ofLocals next))
    (Q : Assertion Unit) (rest : Program) (hNext : wp module_ rest Q store next env) :
    wp module_ (Expr.typedIteProgram condition thenValue elseValue scratch paramTypes resultTypes ++
      [.localSet index] ++ rest) Q store frame env := by
  have hInitial : (State.ofLocals frame).toLocals [] = frame := by
    apply Project.ProofKit.Frame.ext <;> first | rfl | exact hValues.symm
  have hFinal : (State.ofLocals next).toLocals [] = next := by
    apply Project.ProofKit.Frame.ext <;> first | rfl | exact hNextValues.symm
  simp only [Stmt.eval] at hEval
  rcases hExpression : (Expr.ite condition thenValue elseValue).eval scratch (State.ofLocals frame) with
    _ | ⟨result, afterExpression⟩
  · simp [hExpression] at hEval
  have hSet : afterExpression.set? index (.i64 result) = some (State.ofLocals next) := by
    simpa [hExpression] using hEval
  rw [← hInitial, List.append_assoc]
  apply Expr.typedIteProgram_spec condition thenValue elseValue scratch paramTypes resultTypes
    (State.ofLocals frame) afterExpression result [] module_ env store _ Q hExpression
  apply localSet_spec (rest := rest) hSet
  simpa only [hFinal] using hNext

#print axioms Expr.typedIteProgram_spec
#print axioms Stmt.typedIteAssignProgram_frame_spec

end Project.ProofKit.ScalarTransition
