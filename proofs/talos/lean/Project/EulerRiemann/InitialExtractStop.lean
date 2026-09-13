import Project.EulerRiemann.InitialExtractData
import Project.ProofKit.ScalarConditional

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit ScalarTransition FixedArrayFold

def initialExtractStop : Stmt :=
  .assign 52 (.ite (.ltU (.get 50) (.get 51)) (.get 50) (.get 51))

theorem initial_extract_stop_shape : (initialExtractBody.drop 10).take 5 =
    Expr.typedIteProgram (.ltU (.get 50) (.get 51)) (.get 50) (.get 51) 66 [] [.i64] ++
      [.localSet 52] := by
  rfl

theorem initial_extract_stop_eval (frame : Locals) (size length : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hSize : frame.get 50 = some (.i64 size)) (hLength : frame.get 51 = some (.i64 length))
    (hLe : size ≤ length) :
    initialExtractStop.eval 66 (State.ofLocals frame) =
      some (State.ofLocals (resultFrame frame 52 size)) := by
  have hSet := State.ofLocals_result_set frame 52 size (by omega)
    (by simp [Locals.validIndex, hParams, hLocals])
  have hStateSize : (State.ofLocals frame).get 50 = some (.i64 size) := hSize
  have hStateLength : (State.ofLocals frame).get 51 = some (.i64 length) := hLength
  by_cases hLt : size < length
  · simpa [initialExtractStop, Stmt.eval, Expr.eval, hStateSize, hStateLength, hLt] using hSet
  · have hEq : size = length := UInt64.le_antisymm hLe (UInt64.not_lt.mp hLt)
    subst length
    simpa [initialExtractStop, Stmt.eval, Expr.eval, hStateSize, hStateLength] using hSet

theorem initial_extract_stop_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (size length : UInt64) (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = []) (hSize : frame.get 50 = some (.i64 size))
    (hLength : frame.get 51 = some (.i64 length)) (hLe : size ≤ length)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (resultFrame frame 52 size) env) :
    wp module ((initialExtractBody.drop 10).take 5 ++ rest) Q store frame env := by
  rw [initial_extract_stop_shape]
  exact Stmt.typedIteAssignProgram_frame_spec 52 (.ltU (.get 50) (.get 51)) (.get 50) (.get 51)
    66 [] [.i64] frame (resultFrame frame 52 size) module env store hValues rfl
    (initial_extract_stop_eval frame size length hParams hLocals hSize hLength hLe) Q rest hNext

#print axioms initial_extract_stop_shape
#print axioms initial_extract_stop_eval
#print axioms initial_extract_stop_spec

end Project.EulerRiemann.Execution
