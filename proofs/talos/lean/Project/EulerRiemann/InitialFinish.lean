import Project.EulerRiemann.InitialLoopFrame

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold

def initialExtractReturnProgram (completed : Bool) : Wasm.Program :=
  if completed then initialDoneBody.drop 70 else initialExtractBody.drop 70

def initialExtractReturnFrame (frame : Locals) (root : UInt64) (completed : Bool) : Locals :=
  let frame := resultFrame frame (if completed then 9 else 47) root
  let frame := resultFrame (resultFrame frame 6 root) 7 root
  if completed then resultFrame frame 8 1 else frame

theorem initial_extract_return_shape (completed : Bool) :
    initialExtractReturnProgram completed =
      [.localGet 56, .localSet (if completed then 9 else 47),
       .localGet (if completed then 9 else 47), .localSet 6,
       .localGet (if completed then 9 else 47), .localSet 7] ++
      (if completed then [.constI64 1, .localSet 8] else []) := by
  cases completed <;> rfl

theorem initial_extract_return_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (root : UInt64) (completed : Bool)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = []) (hRoot : frame.get 56 = some (.i64 root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (initialExtractReturnFrame frame root completed) env) :
    wp module (initialExtractReturnProgram completed ++ rest) Q store frame env := by
  have hRootLocal := Frame.internal_getElem_of_get frame 5 51 (.i64 root) hParams
    (by omega) hRoot
  rw [initial_extract_return_shape]
  cases completed <;>
    simpa [wp_simp, initialExtractReturnFrame, resultFrame, hParams, hLocals,
      hValues, hRootLocal] using hNext

theorem InitialFrameAt.extractReturn {frame : Locals} {fuel : UInt64} {n size : Nat}
    {source tracker output : UInt64} {done : Bool}
    (h : InitialFrameAt frame fuel n size source tracker output done)
    (root : UInt64) (completed : Bool) :
    InitialFrameAt (initialExtractReturnFrame frame root completed) fuel n size source tracker root
      (completed || done) := by
  cases h
  cases completed <;> constructor <;>
    simp_all [initialExtractReturnFrame, resultFrame]

#print axioms initial_extract_return_shape
#print axioms initial_extract_return_spec
#print axioms InitialFrameAt.extractReturn

end Project.EulerRiemann.Execution
