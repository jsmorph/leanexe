import Project.EulerRiemann.OutputAppendAllocate
import Project.ProofKit.ScalarFrame

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold ScalarTransition

def outputAppendCountsProgram : Wasm.Program := (func99.drop 116).take 12

def outputAppendCountsFrame (frame : Locals) (left right : UInt64) : Locals :=
  resultFrame (resultFrame (resultFrame frame 40 (left + right)) 41 left) 42 right

theorem output_append_counts_shape : outputAppendCountsProgram =
    (Stmt.assign 40 (.bin .add (.get 38) (.get 39))).program 57 ++
      (Stmt.assign 41 (.bin .mul (.get 38) (.const 1))).program 57 ++
      (Stmt.assign 42 (.bin .mul (.get 39) (.const 1))).program 57 := rfl

theorem output_append_counts_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (left right : UInt64) (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hValues : frame.values = []) (hLeft : frame.get 38 = some (.i64 left))
    (hRight : frame.get 39 = some (.i64 right)) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (outputAppendCountsFrame frame left right) env) :
    wp module (outputAppendCountsProgram ++ rest) Q store frame env := by
  let total := resultFrame frame 40 (left + right)
  let leftCount := resultFrame total 41 left
  have hValid (index : Nat) (hi : index < 57) : frame.validIndex index := by
    simpa only [Locals.validIndex, hParams, hLocals] using hi
  have hStateLeft : (State.ofLocals frame).get 38 = some (.i64 left) := hLeft
  have hStateRight : (State.ofLocals frame).get 39 = some (.i64 right) := hRight
  have hTotalLeft : (State.ofLocals total).get 38 = some (.i64 left) :=
    (resultFrame_get_ne frame 40 38 (left + right) (by omega) (by decide)).trans hLeft
  have hCountRight : (State.ofLocals leftCount).get 39 = some (.i64 right) := by
    change leftCount.get 39 = _
    dsimp only [leftCount]
    rw [resultFrame_get_ne _ 41 39 _ (by change frame.params.length ≤ 41; omega) (by decide)]
    dsimp only [total]
    rw [resultFrame_get_ne frame 40 39 _ (by omega) (by decide)]
    exact hRight
  rw [output_append_counts_shape, List.append_assoc, List.append_assoc]
  apply Expr.assign_frame_spec (.bin .add (.get 38) (.get 39)) 57 40 frame (left + right)
    module env store hValues (by omega) (hValid 40 (by decide))
  · simp [Expr.eval, U64Op.apply, hStateLeft, hStateRight]
  apply Expr.assign_frame_spec (.bin .mul (.get 38) (.const 1)) 57 41 total left
    module env store rfl (by change frame.params.length ≤ 41; omega)
    (by simpa only [total, Locals.validIndex, resultFrame_params, resultFrame_locals_length]
      using hValid 41 (by decide))
  · simp [Expr.eval, U64Op.apply, hTotalLeft]
  apply Expr.assign_frame_spec (.bin .mul (.get 39) (.const 1)) 57 42 leftCount right
    module env store rfl (by change frame.params.length ≤ 42; omega)
    (by simpa only [leftCount, total, Locals.validIndex, resultFrame_params, resultFrame_locals_length]
      using hValid 42 (by decide))
  · simp [Expr.eval, U64Op.apply, hCountRight]
  · exact hNext

#print axioms output_append_counts_shape
#print axioms output_append_counts_spec

end Project.EulerRiemann.Execution
