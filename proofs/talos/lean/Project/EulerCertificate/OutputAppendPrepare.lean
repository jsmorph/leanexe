import Project.EulerCertificate.OutputAppendCounts
import Project.EulerRiemann.OutputMapPrepare

namespace Project.EulerCertificate.Execution
open Project.EulerRiemann Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold FixedArrayCapacity

def outputAppendSourceLocal : Nat := 25
def outputAppendUpperLocal : Nat := 40

def outputAppendPrepareProgram : Wasm.Program :=
  (func15.drop 257).take 42

def outputAppendLengthsFrame (frame : Locals) (source upper left right : UInt64) : Locals :=
  resultFrame (resultFrame (resultFrame (resultFrame frame 48 source) 49 upper) 50 left) 51 right

def outputAppendPreparedFrame (frame : Locals) (source upper left right : UInt64) : Locals :=
  resultFrame (outputAppendCountsFrame (outputAppendLengthsFrame frame source upper left right) left right)
    59 (normalizedCapacity (left + right) 1)

theorem output_append_prepare_shape : outputAppendPrepareProgram =
    resultProgram (outputAppendSourceLocal) 48 ++ resultProgram (outputAppendUpperLocal) 49 ++
      FixedArrayLengthRead.program 48 50 ++ FixedArrayLengthRead.program 49 51 ++
      outputAppendCountsProgram ++ localProgram 52 1 59 := rfl

theorem output_append_prepared_gets (frame : Locals) (source upper left right : UInt64)
    (hParams : frame.params.length = 17) (hLocals : frame.locals.length = 48) :
    (outputAppendPreparedFrame frame source upper left right).get 48 = some (.i64 source) ∧
    (outputAppendPreparedFrame frame source upper left right).get 49 = some (.i64 upper) ∧
    (outputAppendPreparedFrame frame source upper left right).get 52 = some (.i64 (left + right)) ∧
    (outputAppendPreparedFrame frame source upper left right).get 53 = some (.i64 left) ∧
    (outputAppendPreparedFrame frame source upper left right).get 54 = some (.i64 right) ∧
    (outputAppendPreparedFrame frame source upper left right).get 59 =
      some (.i64 (normalizedCapacity (left + right) 1)) := by
  simp only [outputAppendPreparedFrame, outputAppendCountsFrame, outputAppendLengthsFrame,
    resultFrame_get_ne, resultFrame_params, hParams,
    Nat.reduceLeDiff, ne_eq, Nat.reduceEqDiff, not_false_eq_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply resultFrame_get_result <;>
    simp [Locals.validIndex, resultFrame_params, resultFrame_locals_length, hParams, hLocals]

theorem output_append_prepared_get_other (frame : Locals) (source upper left right : UInt64)
    (index : Nat) (hParams : frame.params.length = 17) (hi : index < 48) :
    (outputAppendPreparedFrame frame source upper left right).get index = frame.get index := by
  unfold outputAppendPreparedFrame outputAppendCountsFrame outputAppendLengthsFrame
  repeat' rw [resultFrame_get_ne _ _ index _
    (by simp only [resultFrame_params, hParams]; omega) (by omega)]

theorem output_append_prepared_scratch (frame : Locals) (source upper left right : UInt64)
    (hParams : frame.params.length = 17) (hLocals : frame.locals.length = 48)
    (hScratch : I64LocalRange frame 48 65) :
    I64LocalRange (outputAppendPreparedFrame frame source upper left right) 48 65 := by
  unfold outputAppendPreparedFrame outputAppendCountsFrame outputAppendLengthsFrame
  repeat' first
    | apply I64LocalRange.result
    | exact hScratch
    | simp [Locals.validIndex, resultFrame_params, resultFrame_locals_length, hParams, hLocals]

theorem output_append_prepare_spec (env : HostEnv Unit) (store : Store Unit)
    (frame : Locals) (source upper : UInt64) (left right : Array UInt64)
    (hParams : frame.params.length = 17) (hLocals : frame.locals.length = 48)
    (hValues : frame.values = [])
    (hSource : frame.get (outputAppendSourceLocal) = some (.i64 source))
    (hUpper : frame.get (outputAppendUpperLocal) = some (.i64 upper))
    (hLeft : UInt64Array.At store source left) (hRight : UInt64Array.At store upper right)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (outputAppendPreparedFrame frame source upper
      (UInt64.ofNat left.size) (UInt64.ofNat right.size)) env) :
    wp module (outputAppendPrepareProgram ++ rest) Q store frame env := by
  let first := resultFrame frame 48 source
  let pointers := resultFrame first 49 upper
  let loaded := resultFrame pointers 50 (UInt64.ofNat left.size)
  let lengths := resultFrame loaded 51 (UInt64.ofNat right.size)
  let counts := outputAppendCountsFrame lengths (UInt64.ofNat left.size) (UInt64.ofNat right.size)
  have hValid (index : Nat) (hi : index < 65) : frame.validIndex index := by
    simpa only [Locals.validIndex, hParams, hLocals] using hi
  have hPointerParams : pointers.params.length = 17 := hParams
  have hPointerLocals : pointers.locals.length = 48 := by
    simpa only [pointers, first, resultFrame_locals_length] using hLocals
  have hPointerSource : pointers.get 48 = some (.i64 source) := by
    dsimp only [pointers]
    rw [resultFrame_get_ne _ 49 48 _ (by change frame.params.length ≤ 49; omega) (by decide)]
    exact resultFrame_get_result frame 48 source (by omega) (hValid 48 (by decide))
  have hPointerUpper : pointers.get 49 = some (.i64 upper) := resultFrame_get_result first 49 upper
    (by change frame.params.length ≤ 49; omega)
    (by simpa only [first, Locals.validIndex, resultFrame_params, resultFrame_locals_length]
      using hValid 49 (by decide))
  have hLoadedUpper : loaded.get 49 = some (.i64 upper) :=
    (resultFrame_get_ne pointers 50 49 _ (by omega) (by decide)).trans hPointerUpper
  have hLeftLength : lengths.get 50 = some (.i64 (UInt64.ofNat left.size)) := by
    dsimp only [lengths]
    rw [resultFrame_get_ne _ 51 50 _ (by change frame.params.length ≤ 51; omega) (by decide)]
    exact resultFrame_get_result pointers 50 _ (by omega)
      (by simp [Locals.validIndex, hPointerParams, hPointerLocals])
  have hRightLength : lengths.get 51 = some (.i64 (UInt64.ofNat right.size)) :=
    resultFrame_get_result loaded 51 _ (by change frame.params.length ≤ 51; omega)
      (by simp [loaded, Locals.validIndex, resultFrame_params, resultFrame_locals_length,
        hPointerParams, hPointerLocals])
  have hTotal : counts.get 52 = some (.i64 (UInt64.ofNat left.size + UInt64.ofNat right.size)) := by
    dsimp only [counts, outputAppendCountsFrame]
    rw [resultFrame_get_ne _ 54 52 _ (by change frame.params.length ≤ 54; omega) (by decide),
      resultFrame_get_ne _ 53 52 _ (by change frame.params.length ≤ 53; omega) (by decide)]
    apply resultFrame_get_result
    · change frame.params.length ≤ 52
      omega
    · simp [lengths, loaded, pointers, first, Locals.validIndex,
        resultFrame_params, resultFrame_locals_length, hParams, hLocals]
  rw [output_append_prepare_shape]
  simp only [List.append_assoc]
  apply resultProgram_spec (outputAppendSourceLocal) 48 module env store frame source hValues hSource
    (by omega) (hValid 48 (by decide))
  apply resultProgram_spec (outputAppendUpperLocal) 49 module env store first upper rfl
    ((resultFrame_get_ne frame 48 _ source (by omega) (by decide)).trans hUpper)
    (by change frame.params.length ≤ 49; omega)
    (by simpa only [first, Locals.validIndex, resultFrame_params, resultFrame_locals_length]
      using hValid 49 (by decide))
  apply FixedArrayLengthRead.program_spec module env store pointers source (UInt64.ofNat left.size) 48 50
    rfl hPointerSource hLeft.lengthRead hLeft.lengthBound (by omega)
    (by simp [Locals.validIndex, hPointerParams, hPointerLocals])
  apply FixedArrayLengthRead.program_spec module env store loaded upper (UInt64.ofNat right.size) 49 51
    rfl hLoadedUpper hRight.lengthRead hRight.lengthBound (by change frame.params.length ≤ 51; omega)
    (by simp [loaded, Locals.validIndex, resultFrame_params, resultFrame_locals_length,
      hPointerParams, hPointerLocals])
  apply output_append_counts_spec env store lengths (UInt64.ofNat left.size) (UInt64.ofNat right.size)
    hParams (by simpa only [lengths, loaded, resultFrame_locals_length] using hPointerLocals)
    rfl hLeftLength hRightLength
  apply localProgram_spec 52 (UInt64.ofNat left.size + UInt64.ofNat right.size) 1 59 module env store counts
    hTotal rfl (by change frame.params.length ≤ 59; omega)
    (by simp [counts, outputAppendCountsFrame, lengths, loaded, pointers, first, Locals.validIndex,
      resultFrame_params, resultFrame_locals_length, hParams, hLocals])
  exact hNext

#print axioms output_append_prepare_shape
#print axioms output_append_prepared_gets
#print axioms output_append_prepared_get_other
#print axioms output_append_prepared_scratch
#print axioms output_append_prepare_spec

end Project.EulerCertificate.Execution
