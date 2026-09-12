import Project.EulerRiemann.InitialAppendPointers
import Project.EulerRiemann.InitialAppendCounts
import Project.ProofKit.FixedArrayLengthRead

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold

def initialAppendInputProgram : Wasm.Program := (initialGrowBody.drop 54).take 32

def initialAppendLengthFrame (frame : Locals) (n size source upper left right : UInt64) : Locals :=
  resultFrame (resultFrame (initialAppendPointersFrame frame n size source upper) 50 left) 51 right

def initialAppendInputFrame (frame : Locals) (n size source upper left right : UInt64) : Locals :=
  initialAppendCountsFrame (initialAppendLengthFrame frame n size source upper left right) left right

theorem initial_append_input_shape : initialAppendInputProgram =
    (initialGrowBody.drop 54).take 12 ++ FixedArrayLengthRead.program 48 50 ++
      FixedArrayLengthRead.program 49 51 ++ (initialGrowBody.drop 74).take 12 := by
  rfl

theorem initial_append_input_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (n size source upper : UInt64) (left right : Array Traversal.Cell)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = []) (hN : frame.get 1 = some (.i64 n))
    (hSize : frame.get 2 = some (.i64 size)) (hSource : frame.get 4 = some (.i64 source))
    (hUpper : frame.get 50 = some (.i64 upper))
    (hLeft : Memory.GridAt store source left) (hRight : Memory.GridAt store upper right)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store
      (initialAppendInputFrame frame n size source upper (UInt64.ofNat left.size) (UInt64.ofNat right.size)) env) :
    wp module (initialAppendInputProgram ++ rest) Q store frame env := by
  let pointers := initialAppendPointersFrame frame n size source upper
  let first := resultFrame pointers 50 (UInt64.ofNat left.size)
  let lengths := resultFrame first 51 (UInt64.ofNat right.size)
  have hPointerParams : pointers.params.length = 5 := hParams
  have hPointerLocals : pointers.locals.length = 61 := by
    simpa only [pointers, initialAppendPointersFrame, resultFrame_locals_length] using hLocals
  have hPointerGets := initial_append_pointers_gets frame n size source upper hParams hLocals
  have hValid50 : pointers.validIndex 50 := by simp [Locals.validIndex, hPointerParams, hPointerLocals]
  have hValid51 : first.validIndex 51 := by
    simp [first, Locals.validIndex, resultFrame_params, resultFrame_locals_length, hPointerParams, hPointerLocals]
  have hFirstUpper : first.get 49 = some (.i64 upper) :=
    (resultFrame_get_ne pointers 50 49 (UInt64.ofNat left.size) (by omega) (by decide)).trans hPointerGets.2
  have hFirstLength := resultFrame_get_result pointers 50 (UInt64.ofNat left.size) (by omega) hValid50
  have hLeftLength : lengths.get 50 = some (.i64 (UInt64.ofNat left.size)) :=
    (resultFrame_get_ne first 51 50 (UInt64.ofNat right.size)
      (by change pointers.params.length ≤ 51; omega) (by decide)).trans hFirstLength
  have hRightLength : lengths.get 51 = some (.i64 (UInt64.ofNat right.size)) :=
    resultFrame_get_result first 51 (UInt64.ofNat right.size)
      (by change pointers.params.length ≤ 51; omega) hValid51
  rw [initial_append_input_shape, List.append_assoc, List.append_assoc, List.append_assoc]
  apply initial_append_pointers_spec env store frame n size source upper hParams hLocals hValues
    hN hSize hSource hUpper
  apply FixedArrayLengthRead.program_spec module env store pointers source (UInt64.ofNat left.size) 48 50
    rfl hPointerGets.1 hLeft.lengthRead hLeft.lengthBound (by omega) hValid50
  apply FixedArrayLengthRead.program_spec module env store first upper (UInt64.ofNat right.size) 49 51
    rfl hFirstUpper hRight.lengthRead hRight.lengthBound
    (by change pointers.params.length ≤ 51; omega) hValid51
  apply initial_append_counts_spec env store lengths (UInt64.ofNat left.size) (UInt64.ofNat right.size)
    hPointerParams
    (by simpa only [lengths, first, resultFrame_locals_length] using hPointerLocals)
    rfl hLeftLength hRightLength
  exact hNext

#print axioms initial_append_input_shape
#print axioms initial_append_input_spec

end Project.EulerRiemann.Execution
