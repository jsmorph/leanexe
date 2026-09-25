import Project.EulerRiemann.FrozenOutputMapAllocate
import Project.ProofKit.FixedArrayLengthRead
import Project.ProofKit.FixedArrayCapacityArithmetic
import Project.ProofKit.I64LocalRange

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayFold FixedArrayCapacity

def outputMapPrepareProgram : Wasm.Program := func99.take 24

def outputMapPreparedFrame (frame : Locals) (source count : UInt64) : Locals :=
  resultFrame (resultFrame (resultFrame frame 36 source) 37 count) 42 (normalizedCapacity count 1)

theorem output_map_prepare_shape : outputMapPrepareProgram =
    resultProgram 4 36 ++ FixedArrayLengthRead.program 36 37 ++ localProgram 37 1 42 := rfl

theorem output_map_prepared_gets (frame : Locals) (source count : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52) :
    (outputMapPreparedFrame frame source count).get 36 = some (.i64 source) ∧
    (outputMapPreparedFrame frame source count).get 37 = some (.i64 count) ∧
    (outputMapPreparedFrame frame source count).get 42 = some (.i64 (normalizedCapacity count 1)) := by
  simp only [outputMapPreparedFrame, resultFrame_get_ne, resultFrame_params, hParams,
    Nat.reduceLeDiff, ne_eq, Nat.reduceEqDiff, not_false_eq_true]
  refine ⟨?_, ?_, ?_⟩ <;> apply resultFrame_get_result <;>
    simp [Locals.validIndex, resultFrame_params, resultFrame_locals_length, hParams, hLocals]

theorem output_map_prepared_get_other (frame : Locals) (source count : UInt64) (index : Nat)
    (hParams : frame.params.length = 5) (h36 : index ≠ 36) (h37 : index ≠ 37) (h42 : index ≠ 42) :
    (outputMapPreparedFrame frame source count).get index = frame.get index := by
  unfold outputMapPreparedFrame
  rw [resultFrame_get_ne _ 42 index _ (by change frame.params.length ≤ 42; omega) h42,
    resultFrame_get_ne _ 37 index _ (by change frame.params.length ≤ 37; omega) h37,
    resultFrame_get_ne frame 36 index source (by omega) h36]

theorem output_map_prepared_scratch (frame : Locals) (source count : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hScratch : I64LocalRange frame 42 57) :
    I64LocalRange (outputMapPreparedFrame frame source count) 42 57 := by
  unfold outputMapPreparedFrame
  repeat' first
    | apply I64LocalRange.result
    | exact hScratch
    | simp [Locals.validIndex, resultFrame_params, resultFrame_locals_length, hParams, hLocals]

theorem output_map_prepare_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (source : UInt64) (grid : Array Traversal.Cell)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hValues : frame.values = []) (hSource : frame.get 4 = some (.i64 source))
    (hGrid : Memory.GridAt store source grid) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store
      (outputMapPreparedFrame frame source (UInt64.ofNat grid.size)) env) :
    wp module (outputMapPrepareProgram ++ rest) Q store frame env := by
  have hValid (index : Nat) (hi : index < 57) : frame.validIndex index := by
    simpa only [Locals.validIndex, hParams, hLocals] using hi
  let sourceFrame := resultFrame frame 36 source
  let countFrame := resultFrame sourceFrame 37 (UInt64.ofNat grid.size)
  rw [output_map_prepare_shape, List.append_assoc, List.append_assoc]
  apply resultProgram_spec 4 36 module env store frame source hValues hSource (by omega)
    (hValid 36 (by decide))
  apply FixedArrayLengthRead.program_spec module env store sourceFrame source (UInt64.ofNat grid.size)
    36 37 rfl (resultFrame_get_result frame 36 source (by omega) (hValid 36 (by decide)))
    hGrid.lengthRead hGrid.lengthBound (by change frame.params.length ≤ 37; omega)
    (by simpa only [sourceFrame, Locals.validIndex, resultFrame_params, resultFrame_locals_length]
      using hValid 37 (by decide))
  apply localProgram_spec 37 (UInt64.ofNat grid.size) 1 42 module env store countFrame
  · apply resultFrame_get_result
    · change frame.params.length ≤ 37
      omega
    · simpa only [sourceFrame, Locals.validIndex, resultFrame_params, resultFrame_locals_length]
        using hValid 37 (by decide)
  · rfl
  · change frame.params.length ≤ 42
    omega
  · simpa only [countFrame, sourceFrame, Locals.validIndex, resultFrame_params, resultFrame_locals_length]
      using hValid 42 (by decide)
  · exact hNext

theorem output_word_capacity (size : Nat) (hSize : size ≤ 1280004) :
    (normalizedCapacity (UInt64.ofNat size) 1).toNat = 8 * (size + 1) := by
  have hWord : (UInt64.ofNat size).toNat = size := by
    exact UInt64.toNat_ofNat_of_lt (by change size < 18446744073709551616; omega)
  have hFit : 8 + (UInt64.ofNat size).toNat * (1 : UInt64).toNat * 8 + 7 < UInt64.size := by
    rw [hWord]
    change 8 + size * 1 * 8 + 7 < 18446744073709551616
    omega
  rw [normalizedCapacity_toNat_of_fits _ _ hFit, hWord]
  change 8 + size * 1 * 8 = 8 * (size + 1)
  omega

#print axioms output_map_prepare_shape
#print axioms output_map_prepared_gets
#print axioms output_map_prepared_get_other
#print axioms output_map_prepared_scratch
#print axioms output_map_prepare_spec
#print axioms output_word_capacity

end Project.EulerRiemann.Frozen.Execution
