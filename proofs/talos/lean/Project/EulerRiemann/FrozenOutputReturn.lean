import Project.EulerRiemann.FrozenOutputRelease

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit FixedArrayFold

def outputReturnProgram : Wasm.Program := func99.drop 357

def outputReturnFrame (frame : Locals) (root : UInt64) : Locals :=
  { resultFrame (resultFrame frame 34 root) 35 root with values := [.i64 root, .i64 root] }

set_option maxRecDepth 2048 in
theorem output_return_shape : outputReturnProgram =
    [.localGet 31, .localSet 34, .localGet 32, .localSet 35, .localGet 34, .localGet 35] := rfl

theorem output_return_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals) (root : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hValues : frame.values = []) (hOwner : frame.get 31 = some (.i64 root))
    (hPointer : frame.get 32 = some (.i64 root)) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (outputReturnFrame frame root) env) :
    wp module (outputReturnProgram ++ rest) Q store frame env := by
  have h31 := Frame.internal_getElem_of_get frame 5 26 (.i64 root) hParams (by omega) hOwner
  have h32 := Frame.internal_getElem_of_get frame 5 27 (.i64 root) hParams (by omega) hPointer
  rw [output_return_shape]
  simpa [wp_simp, outputReturnFrame, resultFrame, hParams, hLocals, hValues, h31, h32] using hNext

#print axioms output_return_shape
#print axioms output_return_spec

end Project.EulerRiemann.Frozen.Execution
