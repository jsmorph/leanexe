import Project.EulerRiemann.FrozenOutputAppendCounts
import Project.EulerRiemann.FrozenOutputMapPrepare

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit FixedArrayFold FixedArrayCapacity

def outputAppendSourceLocal (header : Bool) : Nat := if header then 47 else 14
def outputAppendUpperLocal (header : Bool) : Nat := if header then 27 else 24

def outputAppendPrepareProgram (header : Bool) : Wasm.Program :=
  (func99.drop (if header then 280 else 104)).take 42

def outputAppendLengthsFrame (frame : Locals) (source upper left right : UInt64) : Locals :=
  resultFrame (resultFrame (resultFrame (resultFrame frame 36 source) 37 upper) 38 left) 39 right

def outputAppendPreparedFrame (frame : Locals) (source upper left right : UInt64) : Locals :=
  resultFrame (outputAppendCountsFrame (outputAppendLengthsFrame frame source upper left right) left right)
    47 (normalizedCapacity (left + right) 1)

theorem output_append_prepare_shape (header : Bool) : outputAppendPrepareProgram header =
    resultProgram (outputAppendSourceLocal header) 36 ++ resultProgram (outputAppendUpperLocal header) 37 ++
      FixedArrayLengthRead.program 36 38 ++ FixedArrayLengthRead.program 37 39 ++
      outputAppendCountsProgram ++ localProgram 40 1 47 := by
  cases header <;> rfl

theorem output_append_prepared_gets (frame : Locals) (source upper left right : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52) :
    (outputAppendPreparedFrame frame source upper left right).get 36 = some (.i64 source) ∧
    (outputAppendPreparedFrame frame source upper left right).get 37 = some (.i64 upper) ∧
    (outputAppendPreparedFrame frame source upper left right).get 40 = some (.i64 (left + right)) ∧
    (outputAppendPreparedFrame frame source upper left right).get 41 = some (.i64 left) ∧
    (outputAppendPreparedFrame frame source upper left right).get 42 = some (.i64 right) ∧
    (outputAppendPreparedFrame frame source upper left right).get 47 =
      some (.i64 (normalizedCapacity (left + right) 1)) := by
  simp only [outputAppendPreparedFrame, outputAppendCountsFrame, outputAppendLengthsFrame,
    resultFrame_get_ne, resultFrame_params, hParams,
    Nat.reduceLeDiff, ne_eq, Nat.reduceEqDiff, not_false_eq_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply resultFrame_get_result <;>
    simp [Locals.validIndex, resultFrame_params, resultFrame_locals_length, hParams, hLocals]

theorem output_append_prepared_get_other (frame : Locals) (source upper left right : UInt64)
    (index : Nat) (hParams : frame.params.length = 5) (hi : index < 36) :
    (outputAppendPreparedFrame frame source upper left right).get index = frame.get index := by
  unfold outputAppendPreparedFrame outputAppendCountsFrame outputAppendLengthsFrame
  repeat' rw [resultFrame_get_ne _ _ index _
    (by simp only [resultFrame_params, hParams]; omega) (by omega)]

theorem output_append_prepared_scratch (frame : Locals) (source upper left right : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hScratch : I64LocalRange frame 42 57) :
    I64LocalRange (outputAppendPreparedFrame frame source upper left right) 42 57 := by
  unfold outputAppendPreparedFrame outputAppendCountsFrame outputAppendLengthsFrame
  repeat' first
    | apply I64LocalRange.result
    | exact hScratch
    | simp [Locals.validIndex, resultFrame_params, resultFrame_locals_length, hParams, hLocals]

theorem output_append_prepare_spec (header : Bool) (env : HostEnv Unit) (store : Store Unit)
    (frame : Locals) (source upper : UInt64) (left right : Array UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hValues : frame.values = [])
    (hSource : frame.get (outputAppendSourceLocal header) = some (.i64 source))
    (hUpper : frame.get (outputAppendUpperLocal header) = some (.i64 upper))
    (hLeft : UInt64Array.At store source left) (hRight : UInt64Array.At store upper right)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (outputAppendPreparedFrame frame source upper
      (UInt64.ofNat left.size) (UInt64.ofNat right.size)) env) :
    wp module (outputAppendPrepareProgram header ++ rest) Q store frame env := by
  let first := resultFrame frame 36 source
  let pointers := resultFrame first 37 upper
  let loaded := resultFrame pointers 38 (UInt64.ofNat left.size)
  let lengths := resultFrame loaded 39 (UInt64.ofNat right.size)
  let counts := outputAppendCountsFrame lengths (UInt64.ofNat left.size) (UInt64.ofNat right.size)
  have hValid (index : Nat) (hi : index < 57) : frame.validIndex index := by
    simpa only [Locals.validIndex, hParams, hLocals] using hi
  have hPointerParams : pointers.params.length = 5 := hParams
  have hPointerLocals : pointers.locals.length = 52 := by
    simpa only [pointers, first, resultFrame_locals_length] using hLocals
  have hPointerSource : pointers.get 36 = some (.i64 source) := by
    dsimp only [pointers]
    rw [resultFrame_get_ne _ 37 36 _ (by change frame.params.length ≤ 37; omega) (by decide)]
    exact resultFrame_get_result frame 36 source (by omega) (hValid 36 (by decide))
  have hPointerUpper : pointers.get 37 = some (.i64 upper) := resultFrame_get_result first 37 upper
    (by change frame.params.length ≤ 37; omega)
    (by simpa only [first, Locals.validIndex, resultFrame_params, resultFrame_locals_length]
      using hValid 37 (by decide))
  have hLoadedUpper : loaded.get 37 = some (.i64 upper) :=
    (resultFrame_get_ne pointers 38 37 _ (by omega) (by decide)).trans hPointerUpper
  have hLeftLength : lengths.get 38 = some (.i64 (UInt64.ofNat left.size)) := by
    dsimp only [lengths]
    rw [resultFrame_get_ne _ 39 38 _ (by change frame.params.length ≤ 39; omega) (by decide)]
    exact resultFrame_get_result pointers 38 _ (by omega)
      (by simp [Locals.validIndex, hPointerParams, hPointerLocals])
  have hRightLength : lengths.get 39 = some (.i64 (UInt64.ofNat right.size)) :=
    resultFrame_get_result loaded 39 _ (by change frame.params.length ≤ 39; omega)
      (by simp [loaded, Locals.validIndex, resultFrame_params, resultFrame_locals_length,
        hPointerParams, hPointerLocals])
  have hTotal : counts.get 40 = some (.i64 (UInt64.ofNat left.size + UInt64.ofNat right.size)) := by
    dsimp only [counts, outputAppendCountsFrame]
    rw [resultFrame_get_ne _ 42 40 _ (by change frame.params.length ≤ 42; omega) (by decide),
      resultFrame_get_ne _ 41 40 _ (by change frame.params.length ≤ 41; omega) (by decide)]
    apply resultFrame_get_result
    · change frame.params.length ≤ 40
      omega
    · simp [lengths, loaded, pointers, first, Locals.validIndex,
        resultFrame_params, resultFrame_locals_length, hParams, hLocals]
  rw [output_append_prepare_shape]
  simp only [List.append_assoc]
  apply resultProgram_spec (outputAppendSourceLocal header) 36 module env store frame source hValues hSource
    (by omega) (hValid 36 (by decide))
  apply resultProgram_spec (outputAppendUpperLocal header) 37 module env store first upper rfl
    ((resultFrame_get_ne frame 36 _ source (by omega) (by cases header <;> decide)).trans hUpper)
    (by change frame.params.length ≤ 37; omega)
    (by simpa only [first, Locals.validIndex, resultFrame_params, resultFrame_locals_length]
      using hValid 37 (by decide))
  apply FixedArrayLengthRead.program_spec module env store pointers source (UInt64.ofNat left.size) 36 38
    rfl hPointerSource hLeft.lengthRead hLeft.lengthBound (by omega)
    (by simp [Locals.validIndex, hPointerParams, hPointerLocals])
  apply FixedArrayLengthRead.program_spec module env store loaded upper (UInt64.ofNat right.size) 37 39
    rfl hLoadedUpper hRight.lengthRead hRight.lengthBound (by change frame.params.length ≤ 39; omega)
    (by simp [loaded, Locals.validIndex, resultFrame_params, resultFrame_locals_length,
      hPointerParams, hPointerLocals])
  apply output_append_counts_spec env store lengths (UInt64.ofNat left.size) (UInt64.ofNat right.size)
    hParams (by simpa only [lengths, loaded, resultFrame_locals_length] using hPointerLocals)
    rfl hLeftLength hRightLength
  apply localProgram_spec 40 (UInt64.ofNat left.size + UInt64.ofNat right.size) 1 47 module env store counts
    hTotal rfl (by change frame.params.length ≤ 47; omega)
    (by simp [counts, outputAppendCountsFrame, lengths, loaded, pointers, first, Locals.validIndex,
      resultFrame_params, resultFrame_locals_length, hParams, hLocals])
  exact hNext

#print axioms output_append_prepare_shape
#print axioms output_append_prepared_gets
#print axioms output_append_prepared_get_other
#print axioms output_append_prepared_scratch
#print axioms output_append_prepare_spec

end Project.EulerRiemann.Frozen.Execution
