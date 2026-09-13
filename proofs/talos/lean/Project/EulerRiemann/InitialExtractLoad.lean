import Project.EulerRiemann.InitialExtractData
import Project.ProofKit.ScalarFrame
import Project.ProofKit.FixedArrayLengthRead

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit ScalarTransition FixedArrayFold

def initialExtractPointers : Stmt :=
  .seq (.assign 48 (.get 4)) (.seq (.assign 49 (.const 0)) (.assign 50 (.get 2)))

def initialExtractPointersFrame (frame : Locals) (source size : UInt64) : Locals :=
  resultFrame (resultFrame (resultFrame frame 48 source) 49 0) 50 size

def initialExtractLoadFrame (frame : Locals) (source size length : UInt64) : Locals :=
  resultFrame (initialExtractPointersFrame frame source size) 51 length

theorem initial_extract_load_shape : initialExtractBody.take 10 =
    initialExtractPointers.program 66 ++ FixedArrayLengthRead.program 48 51 := by
  rfl

theorem initial_extract_pointers_eval (frame : Locals) (source size : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hSource : frame.get 4 = some (.i64 source)) (hSize : frame.get 2 = some (.i64 size)) :
    initialExtractPointers.eval 66 (State.ofLocals frame) =
      some (State.ofLocals (initialExtractPointersFrame frame source size)) := by
  have hP2 := Frame.parameter_getElem_of_get frame 2 (.i64 size) (by simp [hParams]) hSize
  have hP4 := Frame.parameter_getElem_of_get frame 4 (.i64 source) (by simp [hParams]) hSource
  simp [initialExtractPointers, Stmt.eval, Expr.eval, State.ofLocals, State.get, State.set?,
    initialExtractPointersFrame, resultFrame, hParams, hLocals, hP2, hP4]

theorem initial_extract_load_gets (frame : Locals) (source size length : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61) :
    (initialExtractLoadFrame frame source size length).get 48 = some (.i64 source) ∧
    (initialExtractLoadFrame frame source size length).get 49 = some (.i64 0) ∧
    (initialExtractLoadFrame frame source size length).get 50 = some (.i64 size) ∧
    (initialExtractLoadFrame frame source size length).get 51 = some (.i64 length) := by
  simp only [initialExtractLoadFrame, initialExtractPointersFrame, resultFrame_get_ne,
    resultFrame_params, hParams, Nat.reduceLeDiff, ne_eq, Nat.reduceEqDiff, not_false_eq_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply resultFrame_get_result <;>
    simp [Locals.validIndex, resultFrame_params, resultFrame_locals_length, hParams, hLocals]

theorem initial_extract_load_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (source size : UInt64) (grid : Array Traversal.Cell)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = []) (hSource : frame.get 4 = some (.i64 source))
    (hSize : frame.get 2 = some (.i64 size)) (hGrid : Memory.GridAt store source grid)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (initialExtractLoadFrame frame source size (UInt64.ofNat grid.size)) env) :
    wp module (initialExtractBody.take 10 ++ rest) Q store frame env := by
  let pointers := initialExtractPointersFrame frame source size
  rw [initial_extract_load_shape, List.append_assoc]
  apply initialExtractPointers.program_frame_spec 66 frame pointers module env store hValues rfl
    (initial_extract_pointers_eval frame source size hParams hLocals hSource hSize)
  apply FixedArrayLengthRead.program_spec module env store pointers source (UInt64.ofNat grid.size) 48 51 rfl
  · simp only [pointers, initialExtractPointersFrame, resultFrame_get_ne, resultFrame_params,
      hParams, Nat.reduceLeDiff, ne_eq, Nat.reduceEqDiff, not_false_eq_true]
    apply resultFrame_get_result <;> simp [Locals.validIndex, hParams, hLocals]
  · exact hGrid.lengthRead
  · exact hGrid.lengthBound
  · change frame.params.length ≤ 51
    omega
  · simp [pointers, initialExtractPointersFrame, Locals.validIndex, resultFrame_params,
      resultFrame_locals_length, hParams, hLocals]
  · exact hNext

#print axioms initial_extract_load_shape
#print axioms initial_extract_pointers_eval
#print axioms initial_extract_load_gets
#print axioms initial_extract_load_spec

end Project.EulerRiemann.Execution
