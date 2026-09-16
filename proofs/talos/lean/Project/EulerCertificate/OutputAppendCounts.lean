import Project.EulerCertificate.OutputAppendAllocate
import Project.ProofKit.ScalarFrame

namespace Project.EulerCertificate.Execution
open Project.EulerRiemann Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold ScalarTransition

def outputAppendCountsProgram : Wasm.Program := (func15.drop 269).take 12

def outputAppendCountsFrame (frame : Locals) (left right : UInt64) : Locals :=
  resultFrame (resultFrame (resultFrame frame 52 (left + right)) 53 left) 54 right

theorem output_append_counts_shape : outputAppendCountsProgram =
    (Stmt.assign 52 (.bin .add (.get 50) (.get 51))).program 65 ++
      (Stmt.assign 53 (.bin .mul (.get 50) (.const 1))).program 65 ++
      (Stmt.assign 54 (.bin .mul (.get 51) (.const 1))).program 65 := rfl

theorem output_append_counts_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (left right : UInt64) (hParams : frame.params.length = 17) (hLocals : frame.locals.length = 48)
    (hValues : frame.values = []) (hLeft : frame.get 50 = some (.i64 left))
    (hRight : frame.get 51 = some (.i64 right)) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (outputAppendCountsFrame frame left right) env) :
    wp module (outputAppendCountsProgram ++ rest) Q store frame env := by
  let total := resultFrame frame 52 (left + right)
  let leftCount := resultFrame total 53 left
  have hValid (index : Nat) (hi : index < 65) : frame.validIndex index := by
    simpa only [Locals.validIndex, hParams, hLocals] using hi
  have hStateLeft : (State.ofLocals frame).get 50 = some (.i64 left) := hLeft
  have hStateRight : (State.ofLocals frame).get 51 = some (.i64 right) := hRight
  have hTotalLeft : (State.ofLocals total).get 50 = some (.i64 left) :=
    (resultFrame_get_ne frame 52 50 (left + right) (by omega) (by decide)).trans hLeft
  have hCountRight : (State.ofLocals leftCount).get 51 = some (.i64 right) := by
    change leftCount.get 51 = _
    dsimp only [leftCount]
    rw [resultFrame_get_ne _ 53 51 _ (by change frame.params.length ≤ 53; omega) (by decide)]
    dsimp only [total]
    rw [resultFrame_get_ne frame 52 51 _ (by omega) (by decide)]
    exact hRight
  rw [output_append_counts_shape, List.append_assoc, List.append_assoc]
  apply Expr.assign_frame_spec (.bin .add (.get 50) (.get 51)) 65 52 frame (left + right)
    module env store hValues (by omega) (hValid 52 (by decide))
  · simp [Expr.eval, U64Op.apply, hStateLeft, hStateRight]
  apply Expr.assign_frame_spec (.bin .mul (.get 50) (.const 1)) 65 53 total left
    module env store rfl (by change frame.params.length ≤ 53; omega)
    (by simpa only [total, Locals.validIndex, resultFrame_params, resultFrame_locals_length]
      using hValid 53 (by decide))
  · simp [Expr.eval, U64Op.apply, hTotalLeft]
  apply Expr.assign_frame_spec (.bin .mul (.get 51) (.const 1)) 65 54 leftCount right
    module env store rfl (by change frame.params.length ≤ 54; omega)
    (by simpa only [leftCount, total, Locals.validIndex, resultFrame_params, resultFrame_locals_length]
      using hValid 54 (by decide))
  · simp [Expr.eval, U64Op.apply, hCountRight]
  · exact hNext

#print axioms output_append_counts_shape
#print axioms output_append_counts_spec

end Project.EulerCertificate.Execution
