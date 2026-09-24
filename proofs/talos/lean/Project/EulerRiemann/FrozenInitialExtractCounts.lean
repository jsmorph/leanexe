import Project.EulerRiemann.FrozenInitialExtractData
import Project.ProofKit.ScalarFrame

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit ScalarTransition FixedArrayFold

def initialExtractCounts : Stmt :=
  .seq (.assign 54 (.bin .mul (.get 49) (.const 7)))
    (.assign 55 (.bin .mul (.get 53) (.const 7)))

def initialExtractCountsFrame (frame : Locals) (size : UInt64) : Locals :=
  resultFrame (resultFrame frame 54 0) 55 (size * 7)

theorem initial_extract_counts_shape : (initialExtractBody.drop 20).take 8 =
    initialExtractCounts.program 66 := by
  rfl

theorem initial_extract_counts_eval (frame : Locals) (size : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hStart : frame.get 49 = some (.i64 0)) (hSize : frame.get 53 = some (.i64 size)) :
    initialExtractCounts.eval 66 (State.ofLocals frame) =
      some (State.ofLocals (initialExtractCountsFrame frame size)) := by
  have hStartLocal := Frame.internal_getElem_of_get frame 5 44 (.i64 0) hParams
    (by simp [hLocals]) hStart
  have hSizeLocal := Frame.internal_getElem_of_get frame 5 48 (.i64 size) hParams
    (by simp [hLocals]) hSize
  simp [initialExtractCounts, Stmt.eval, Expr.eval, U64Op.apply, State.ofLocals, State.get, State.set?,
    initialExtractCountsFrame, resultFrame, hParams, hLocals, hStartLocal, hSizeLocal]

theorem initial_extract_counts_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (size : UInt64) (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = []) (hStart : frame.get 49 = some (.i64 0))
    (hSize : frame.get 53 = some (.i64 size)) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (initialExtractCountsFrame frame size) env) :
    wp module ((initialExtractBody.drop 20).take 8 ++ rest) Q store frame env := by
  rw [initial_extract_counts_shape]
  exact initialExtractCounts.program_frame_spec 66 frame (initialExtractCountsFrame frame size)
    module env store hValues rfl (initial_extract_counts_eval frame size hParams hLocals hStart hSize)
    Q rest hNext

#print axioms initial_extract_counts_shape
#print axioms initial_extract_counts_eval
#print axioms initial_extract_counts_spec

end Project.EulerRiemann.Frozen.Execution
