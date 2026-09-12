import Project.EulerRiemann.InitialCopyPrefix
import Project.ProofKit.FixedArrayLengthRead
import Project.ProofKit.FixedArrayFrame

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold

def initialMapInputProgram : Wasm.Program := initialGrowBody.take 12

def initialMapInputFrame (frame : Locals) (source length : UInt64) : Locals :=
  resultFrame (resultFrame (resultFrame (resultFrame frame 48 source) 10 length) 48 source) 49 length

theorem initial_map_input_shape : initialMapInputProgram =
    resultProgram 4 48 ++ FixedArrayLengthRead.program 48 10 ++
      resultProgram 4 48 ++ FixedArrayLengthRead.program 48 49 := by
  rfl

theorem initial_map_input_params (frame : Locals) (source length : UInt64) :
    (initialMapInputFrame frame source length).params = frame.params := rfl

theorem initial_map_input_locals (frame : Locals) (source length : UInt64) :
    (initialMapInputFrame frame source length).locals.length = frame.locals.length := by
  simp only [initialMapInputFrame, resultFrame_locals_length]

theorem initial_map_input_get_other (frame : Locals) (source length : UInt64) (index : Nat)
    (hParams : frame.params.length = 5) (h10 : index ≠ 10) (h48 : index ≠ 48) (h49 : index ≠ 49) :
    (initialMapInputFrame frame source length).get index = frame.get index := by
  unfold initialMapInputFrame
  rw [resultFrame_get_ne _ 49 index length (by change frame.params.length ≤ 49; omega) h49,
    resultFrame_get_ne _ 48 index source (by change frame.params.length ≤ 48; omega) h48,
    resultFrame_get_ne _ 10 index length (by change frame.params.length ≤ 10; omega) h10,
    resultFrame_get_ne frame 48 index source (by omega) h48]

theorem initial_map_input_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (source : UInt64) (grid : Array Traversal.Cell)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = []) (hSource : frame.get 4 = some (.i64 source))
    (hGrid : Memory.GridAt store source grid) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (initialMapInputFrame frame source (UInt64.ofNat grid.size)) env) :
    wp module (initialMapInputProgram ++ rest) Q store frame env := by
  have hRoot32 : source.toNat < 4294967296 := by have := hGrid.1; omega
  have hBound : source.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt hRoot32]
    have := hGrid.2.1
    omega
  have hValid48 : frame.validIndex 48 := by simp [Locals.validIndex, hParams, hLocals]
  have hValid10 : frame.validIndex 10 := by simp [Locals.validIndex, hParams, hLocals]
  have hValid49 : frame.validIndex 49 := by simp [Locals.validIndex, hParams, hLocals]
  let first := resultFrame frame 48 source
  let offset := resultFrame first 10 (UInt64.ofNat grid.size)
  let second := resultFrame offset 48 source
  rw [initial_map_input_shape, List.append_assoc, List.append_assoc, List.append_assoc]
  apply resultProgram_spec 4 48 module env store frame source hValues hSource (by omega) hValid48
  apply FixedArrayLengthRead.program_spec module env store first source (UInt64.ofNat grid.size) 48 10
    rfl (resultFrame_get_result frame 48 source (by omega) hValid48) hGrid.2.2.1 hBound
    (by change frame.params.length ≤ 10; omega)
    (by simpa only [first, Locals.validIndex, resultFrame_params, resultFrame_locals_length] using hValid10)
  have hSourceAgain : offset.get 4 = some (.i64 source) := by
    dsimp only [offset]
    rw [resultFrame_get_ne first 10 4 (UInt64.ofNat grid.size)
      (by change frame.params.length ≤ 10; omega) (by decide)]
    dsimp only [first]
    rw [resultFrame_get_ne frame 48 4 source (by omega) (by decide)]
    exact hSource
  have hOffset48 : offset.validIndex 48 := by
    simpa only [offset, first, Locals.validIndex, resultFrame_params, resultFrame_locals_length] using hValid48
  apply resultProgram_spec 4 48 module env store offset source rfl hSourceAgain
    (by change frame.params.length ≤ 48; omega) hOffset48
  apply FixedArrayLengthRead.program_spec module env store second source (UInt64.ofNat grid.size) 48 49
    rfl (resultFrame_get_result offset 48 source (by change frame.params.length ≤ 48; omega) hOffset48)
    hGrid.2.2.1 hBound (by change frame.params.length ≤ 49; omega)
    (by simpa only [second, offset, first, Locals.validIndex, resultFrame_params,
      resultFrame_locals_length] using hValid49)
  exact hNext

#print axioms initial_map_input_shape
#print axioms initial_map_input_get_other
#print axioms initial_map_input_spec

end Project.EulerRiemann.Execution
