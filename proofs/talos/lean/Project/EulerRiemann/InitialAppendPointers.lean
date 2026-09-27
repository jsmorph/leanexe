import Project.EulerRiemann.InitialCopyPrefix
import Project.ProofKit.ScalarFrame

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit ScalarTransition FixedArrayFold

def initialAppendPointers : Stmt :=
  .seq (.assign 35 (.get 50))
    (.seq (.assign 36 (.get 35))
      (.seq (.assign 37 (.get 1))
        (.seq (.assign 38 (.get 2))
          (.seq (.assign 48 (.get 4)) (.assign 49 (.get 36))))))

def initialAppendPointersFrame (frame : Locals) (n size source upper : UInt64) : Locals :=
  resultFrame (resultFrame (resultFrame (resultFrame (resultFrame (resultFrame frame
    35 upper) 36 upper) 37 n) 38 size) 48 source) 49 upper

theorem initial_append_pointers_shape : (initialGrowBody.drop 54).take 12 =
    initialAppendPointers.program 66 := by
  rfl

theorem initial_append_pointers_gets (frame : Locals) (n size source upper : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61) :
    (initialAppendPointersFrame frame n size source upper).get 48 = some (.i64 source) ∧
    (initialAppendPointersFrame frame n size source upper).get 49 = some (.i64 upper) := by
  simp only [initialAppendPointersFrame, resultFrame_get_ne, resultFrame_params, hParams,
    Nat.reduceLeDiff, ne_eq, Nat.reduceEqDiff, not_false_eq_true]
  constructor <;> apply resultFrame_get_result <;>
    simp [Locals.validIndex, resultFrame_params, resultFrame_locals_length, hParams, hLocals]

theorem initial_append_pointers_eval (frame : Locals) (n size source upper : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hN : frame.get 1 = some (.i64 n)) (hSize : frame.get 2 = some (.i64 size))
    (hSource : frame.get 4 = some (.i64 source)) (hUpper : frame.get 50 = some (.i64 upper)) :
    initialAppendPointers.eval 66 (State.ofLocals frame) =
      some (State.ofLocals (initialAppendPointersFrame frame n size source upper)) := by
  have hP1 := Frame.parameter_getElem_of_get frame 1 (.i64 n) (by simp [hParams]) hN
  have hP2 := Frame.parameter_getElem_of_get frame 2 (.i64 size) (by simp [hParams]) hSize
  have hP4 := Frame.parameter_getElem_of_get frame 4 (.i64 source) (by simp [hParams]) hSource
  have hUpperLocal := Frame.internal_getElem_of_get frame 5 45 (.i64 upper) hParams
    (by simp [hLocals]) hUpper
  simp [initialAppendPointers, Stmt.eval, Expr.eval, State.ofLocals, State.get, State.set?,
    initialAppendPointersFrame, resultFrame, hParams, hLocals, hP1, hP2, hP4, hUpperLocal]

theorem initial_append_pointers_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (n size source upper : UInt64) (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = []) (hN : frame.get 1 = some (.i64 n))
    (hSize : frame.get 2 = some (.i64 size)) (hSource : frame.get 4 = some (.i64 source))
    (hUpper : frame.get 50 = some (.i64 upper)) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (initialAppendPointersFrame frame n size source upper) env) :
    wp module ((initialGrowBody.drop 54).take 12 ++ rest) Q store frame env := by
  rw [initial_append_pointers_shape]
  exact initialAppendPointers.program_frame_spec 66 frame
    (initialAppendPointersFrame frame n size source upper) module env store hValues rfl
    (initial_append_pointers_eval frame n size source upper hParams hLocals hN hSize hSource hUpper)
    Q rest hNext

#print axioms initial_append_pointers_shape
#print axioms initial_append_pointers_gets
#print axioms initial_append_pointers_eval
#print axioms initial_append_pointers_spec

end Project.EulerRiemann.Execution
