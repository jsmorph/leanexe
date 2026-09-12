import Project.EulerRiemann.InitialCopyPrefix
import Project.ProofKit.ScalarFrame

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit ScalarTransition FixedArrayFold

def initialAppendCounts : Stmt :=
  .seq (.assign 52 (.bin .add (.get 50) (.get 51)))
    (.seq (.assign 53 (.bin .mul (.get 50) (.const 7)))
      (.assign 54 (.bin .mul (.get 51) (.const 7))))

def initialAppendCountsFrame (frame : Locals) (left right : UInt64) : Locals :=
  resultFrame (resultFrame (resultFrame frame 52 (left + right)) 53 (left * 7)) 54 (right * 7)

theorem initial_append_counts_shape : (initialGrowBody.drop 74).take 12 =
    initialAppendCounts.program 66 := by
  rfl

theorem initial_append_counts_eval (frame : Locals) (left right : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hLeft : frame.get 50 = some (.i64 left)) (hRight : frame.get 51 = some (.i64 right)) :
    initialAppendCounts.eval 66 (State.ofLocals frame) =
      some (State.ofLocals (initialAppendCountsFrame frame left right)) := by
  let total := resultFrame frame 52 (left + right)
  let leftCount := resultFrame total 53 (left * 7)
  have hSetTotal := State.ofLocals_result_set frame 52 (left + right) (by omega)
    (by simp [Locals.validIndex, hParams, hLocals])
  have hSetLeft := State.ofLocals_result_set total 53 (left * 7)
    (by change frame.params.length ≤ 53; omega)
    (by simp [total, Locals.validIndex, resultFrame_params, resultFrame_locals_length, hParams, hLocals])
  have hSetRight := State.ofLocals_result_set leftCount 54 (right * 7)
    (by change frame.params.length ≤ 54; omega)
    (by simp [leftCount, total, Locals.validIndex, resultFrame_params,
      resultFrame_locals_length, hParams, hLocals])
  have hTotalLeft : total.get 50 = some (.i64 left) :=
    (resultFrame_get_ne frame 52 50 (left + right) (by omega) (by decide)).trans hLeft
  have hTotalRight : total.get 51 = some (.i64 right) :=
    (resultFrame_get_ne frame 52 51 (left + right) (by omega) (by decide)).trans hRight
  have hCountRight : leftCount.get 51 = some (.i64 right) :=
    (resultFrame_get_ne total 53 51 (left * 7) (by change frame.params.length ≤ 53; omega)
      (by decide)).trans hTotalRight
  have hStateLeft : (State.ofLocals frame).get 50 = some (.i64 left) := hLeft
  have hStateRight : (State.ofLocals frame).get 51 = some (.i64 right) := hRight
  have hStateTotalLeft : (State.ofLocals total).get 50 = some (.i64 left) := hTotalLeft
  have hStateCountRight : (State.ofLocals leftCount).get 51 = some (.i64 right) := hCountRight
  have hFirst : (Stmt.assign 52 (.bin .add (.get 50) (.get 51))).eval 66 (State.ofLocals frame) =
      some (State.ofLocals total) := by
    simpa [Stmt.eval, Expr.eval, U64Op.apply, hStateLeft, hStateRight] using hSetTotal
  have hSecond : (Stmt.assign 53 (.bin .mul (.get 50) (.const 7))).eval 66 (State.ofLocals total) =
      some (State.ofLocals leftCount) := by
    simpa [Stmt.eval, Expr.eval, U64Op.apply, hStateTotalLeft] using hSetLeft
  have hThird : (Stmt.assign 54 (.bin .mul (.get 51) (.const 7))).eval 66 (State.ofLocals leftCount) =
      some (State.ofLocals (initialAppendCountsFrame frame left right)) := by
    change _ = some (State.ofLocals (resultFrame leftCount 54 (right * 7)))
    simpa [Stmt.eval, Expr.eval, U64Op.apply, hStateCountRight] using hSetRight
  change (do let afterFirst ← (Stmt.assign 52 (.bin .add (.get 50) (.get 51))).eval 66 (State.ofLocals frame)
             let afterSecond ← (Stmt.assign 53 (.bin .mul (.get 50) (.const 7))).eval 66 afterFirst
             (Stmt.assign 54 (.bin .mul (.get 51) (.const 7))).eval 66 afterSecond) = _
  rw [hFirst]
  change ((Stmt.assign 53 (.bin .mul (.get 50) (.const 7))).eval 66 (State.ofLocals total)).bind
    (fun afterSecond => (Stmt.assign 54 (.bin .mul (.get 51) (.const 7))).eval 66 afterSecond) = _
  rw [hSecond]
  exact hThird

theorem initial_append_counts_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (left right : UInt64) (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = []) (hLeft : frame.get 50 = some (.i64 left))
    (hRight : frame.get 51 = some (.i64 right)) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (initialAppendCountsFrame frame left right) env) :
    wp module ((initialGrowBody.drop 74).take 12 ++ rest) Q store frame env := by
  rw [initial_append_counts_shape]
  exact initialAppendCounts.program_frame_spec 66 frame (initialAppendCountsFrame frame left right)
    module env store hValues rfl (initial_append_counts_eval frame left right hParams hLocals hLeft hRight)
    Q rest hNext

#print axioms initial_append_counts_shape
#print axioms initial_append_counts_eval
#print axioms initial_append_counts_spec

end Project.EulerRiemann.Execution
