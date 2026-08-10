import Project.ProofKit.Array
import Project.ProofKit.FixedArrayResult

namespace Project.ProofKit.FixedArrayFold

open Wasm

def setupLocals (arrayLocal lengthLocal indexLocal stopScratchLocal stopLocal
    accumulatorLocal releaseReadyLocal effectiveStopLocal : Nat) : List Nat :=
  [arrayLocal, lengthLocal, indexLocal, stopScratchLocal, stopLocal,
    accumulatorLocal, releaseReadyLocal, effectiveStopLocal]

def forwardSetupProgram (arrayLocal lengthLocal indexLocal stopScratchLocal
    stopLocal accumulatorLocal releaseReadyLocal effectiveStopLocal : Nat)
    (initial : UInt64) : Wasm.Program :=
  [
  .localGet 0,
  .localSet arrayLocal,
  .localGet arrayLocal,
  .wrapI64,
  .load64 0,
  .localSet lengthLocal,
  .constI64 0,
  .localSet indexLocal,
  .localGet 0,
  .localSet stopScratchLocal,
  .localGet stopScratchLocal,
  .wrapI64,
  .load64 0,
  .localSet stopLocal,
  .constI64 initial,
  .localSet accumulatorLocal,
  .constI64 0,
  .localSet releaseReadyLocal,
  .localGet stopLocal,
  .localGet lengthLocal,
  .ltUI64,
  .iff 0 1 [.localGet stopLocal] [.localGet lengthLocal],
  .localSet effectiveStopLocal
  ]

def forwardSetupFrame (frame : Locals) (inputPtr : UInt64)
    (inputSize : Nat) (arrayLocal lengthLocal indexLocal stopScratchLocal
      stopLocal accumulatorLocal releaseReadyLocal effectiveStopLocal : Nat)
    (initial : UInt64) : Locals :=
  { frame with
    locals := (((((((frame.locals.set (arrayLocal - 1) (.i64 inputPtr)).set
      (lengthLocal - 1) (.i64 (UInt64.ofNat inputSize))).set
      (indexLocal - 1) (.i64 0)).set
      (stopScratchLocal - 1) (.i64 inputPtr)).set
      (stopLocal - 1) (.i64 (UInt64.ofNat inputSize))).set
      (accumulatorLocal - 1) (.i64 initial)).set
      (releaseReadyLocal - 1) (.i64 0)).set
      (effectiveStopLocal - 1) (.i64 (UInt64.ofNat inputSize))
    values := [] }

theorem forwardSetupFrame_params (frame : Locals) (inputPtr : UInt64)
    (inputSize : Nat) (arrayLocal lengthLocal indexLocal stopScratchLocal
      stopLocal accumulatorLocal releaseReadyLocal effectiveStopLocal : Nat)
    (initial : UInt64) :
    (forwardSetupFrame frame inputPtr inputSize arrayLocal lengthLocal
      indexLocal stopScratchLocal stopLocal accumulatorLocal releaseReadyLocal
      effectiveStopLocal initial).params = frame.params := rfl

theorem forwardSetupFrame_locals_length (frame : Locals) (inputPtr : UInt64)
    (inputSize : Nat) (arrayLocal lengthLocal indexLocal stopScratchLocal
      stopLocal accumulatorLocal releaseReadyLocal effectiveStopLocal : Nat)
    (initial : UInt64) :
    (forwardSetupFrame frame inputPtr inputSize arrayLocal lengthLocal
      indexLocal stopScratchLocal stopLocal accumulatorLocal releaseReadyLocal
      effectiveStopLocal initial).locals.length = frame.locals.length := by
  simp [forwardSetupFrame]

theorem forwardSetupFrame_values (frame : Locals) (inputPtr : UInt64)
    (inputSize : Nat) (arrayLocal lengthLocal indexLocal stopScratchLocal
      stopLocal accumulatorLocal releaseReadyLocal effectiveStopLocal : Nat)
    (initial : UInt64) :
    (forwardSetupFrame frame inputPtr inputSize arrayLocal lengthLocal
      indexLocal stopScratchLocal stopLocal accumulatorLocal releaseReadyLocal
      effectiveStopLocal initial).values = [] := rfl

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem forwardSetupProgram_spec
    (arrayLocal lengthLocal indexLocal stopScratchLocal stopLocal
      accumulatorLocal releaseReadyLocal effectiveStopLocal : Nat)
    (initial : UInt64)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr : UInt64) (input : Array UInt64)
    (hParams : frame.params = [.i64 inputPtr])
    (hValues : frame.values = [])
    (hWritable : ∀ slot,
      slot ∈ setupLocals arrayLocal lengthLocal indexLocal stopScratchLocal
        stopLocal accumulatorLocal releaseReadyLocal effectiveStopLocal →
      0 < slot ∧ slot < 1 + frame.locals.length)
    (hDistinct : (setupLocals arrayLocal lengthLocal indexLocal
      stopScratchLocal stopLocal accumulatorLocal releaseReadyLocal
      effectiveStopLocal).Nodup)
    (hInput : UInt64Array.At st inputPtr input)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st
      (forwardSetupFrame frame inputPtr input.size arrayLocal lengthLocal
        indexLocal stopScratchLocal stopLocal accumulatorLocal
        releaseReadyLocal effectiveStopLocal initial) env) :
    wp module_
      (forwardSetupProgram arrayLocal lengthLocal indexLocal stopScratchLocal
        stopLocal accumulatorLocal releaseReadyLocal effectiveStopLocal initial ++
        rest) Q st frame env := by
  have hArray := hWritable arrayLocal (by simp [setupLocals])
  have hLength := hWritable lengthLocal (by simp [setupLocals])
  have hIndex := hWritable indexLocal (by simp [setupLocals])
  have hStopScratch := hWritable stopScratchLocal (by simp [setupLocals])
  have hStop := hWritable stopLocal (by simp [setupLocals])
  have hAccumulator := hWritable accumulatorLocal (by simp [setupLocals])
  have hRelease := hWritable releaseReadyLocal (by simp [setupLocals])
  have hEffective := hWritable effectiveStopLocal (by simp [setupLocals])
  rcases hArray with ⟨hArrayPositive, hArrayBound⟩
  rcases hLength with ⟨hLengthPositive, hLengthBoundLocal⟩
  rcases hIndex with ⟨hIndexPositive, hIndexBound⟩
  rcases hStopScratch with ⟨hStopScratchPositive, hStopScratchBound⟩
  rcases hStop with ⟨hStopPositive, hStopBound⟩
  rcases hAccumulator with ⟨hAccumulatorPositive, hAccumulatorBound⟩
  rcases hRelease with ⟨hReleasePositive, hReleaseBound⟩
  rcases hEffective with ⟨hEffectivePositive, hEffectiveBound⟩
  have hArrayNotParam : ¬arrayLocal < 1 := by omega
  have hLengthNotParam : ¬lengthLocal < 1 := by omega
  have hIndexNotParam : ¬indexLocal < 1 := by omega
  have hStopScratchNotParam : ¬stopScratchLocal < 1 := by omega
  have hStopNotParam : ¬stopLocal < 1 := by omega
  have hAccumulatorNotParam : ¬accumulatorLocal < 1 := by omega
  have hReleaseNotParam : ¬releaseReadyLocal < 1 := by omega
  have hEffectiveNotParam : ¬effectiveStopLocal < 1 := by omega
  have hArrayIndex : arrayLocal - 1 < frame.locals.length := by omega
  have hLengthIndex : lengthLocal - 1 < frame.locals.length := by omega
  have hIndexIndex : indexLocal - 1 < frame.locals.length := by omega
  have hStopScratchIndex : stopScratchLocal - 1 < frame.locals.length := by
    omega
  have hStopIndex : stopLocal - 1 < frame.locals.length := by omega
  have hAccumulatorIndex : accumulatorLocal - 1 < frame.locals.length := by
    omega
  have hReleaseIndex : releaseReadyLocal - 1 < frame.locals.length := by
    omega
  have hEffectiveIndex : effectiveStopLocal - 1 < frame.locals.length := by
    omega
  have hLengthNeIndex : lengthLocal ≠ indexLocal := by
    intro hEq
    subst indexLocal
    simp [setupLocals] at hDistinct
  have hLengthNeStopScratch : lengthLocal ≠ stopScratchLocal := by
    intro hEq
    subst stopScratchLocal
    simp [setupLocals] at hDistinct
  have hLengthNeStop : lengthLocal ≠ stopLocal := by
    intro hEq
    subst stopLocal
    simp [setupLocals] at hDistinct
  have hLengthNeAccumulator : lengthLocal ≠ accumulatorLocal := by
    intro hEq
    subst accumulatorLocal
    simp [setupLocals] at hDistinct
  have hLengthNeRelease : lengthLocal ≠ releaseReadyLocal := by
    intro hEq
    subst releaseReadyLocal
    simp [setupLocals] at hDistinct
  have hStopNeAccumulator : stopLocal ≠ accumulatorLocal := by
    intro hEq
    subst accumulatorLocal
    simp [setupLocals] at hDistinct
  have hStopNeRelease : stopLocal ≠ releaseReadyLocal := by
    intro hEq
    subst releaseReadyLocal
    simp [setupLocals] at hDistinct
  have hReleaseIndexNeStopIndex :
      releaseReadyLocal - 1 ≠ stopLocal - 1 := by omega
  have hAccumulatorIndexNeStopIndex :
      accumulatorLocal - 1 ≠ stopLocal - 1 := by omega
  have hReleaseIndexNeLengthIndex :
      releaseReadyLocal - 1 ≠ lengthLocal - 1 := by omega
  have hAccumulatorIndexNeLengthIndex :
      accumulatorLocal - 1 ≠ lengthLocal - 1 := by omega
  have hStopIndexNeLengthIndex : stopLocal - 1 ≠ lengthLocal - 1 := by
    omega
  have hStopScratchIndexNeLengthIndex :
      stopScratchLocal - 1 ≠ lengthLocal - 1 := by omega
  have hIndexIndexNeLengthIndex : indexLocal - 1 ≠ lengthLocal - 1 := by
    omega
  have hLengthRead := hInput.lengthRead
  have hLengthBound := hInput.generatedLengthBound
  have hInputAddress := hInput.pointerAddress_eq
  unfold forwardSetupProgram
  simp only [List.cons_append, List.nil_append]
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Wasm.Locals.get, Wasm.Locals.set?, List.length_set, hParams, hValues,
    hArrayBound, hLengthBoundLocal, hIndexBound, hStopScratchBound,
    hStopBound, hAccumulatorBound, hReleaseBound,
    hArrayNotParam, hLengthNotParam, hIndexNotParam,
    hStopScratchNotParam, hStopNotParam, hAccumulatorNotParam,
    hReleaseNotParam, hArrayIndex, hLengthIndex, hStopScratchIndex,
    hStopIndex,
    hReleaseIndexNeStopIndex, hAccumulatorIndexNeStopIndex,
    hReleaseIndexNeLengthIndex, hAccumulatorIndexNeLengthIndex,
    hStopIndexNeLengthIndex, hStopScratchIndexNeLengthIndex,
    hIndexIndexNeLengthIndex,
    hLengthRead, hInputAddress]
  rw [if_neg (Nat.not_lt.mpr hLengthBound)]
  rw [if_neg (Nat.not_lt.mpr hLengthBound)]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  simpa [forwardSetupFrame, hParams, hValues, hArrayPositive, hArrayBound,
    hLengthPositive, hLengthBoundLocal, hIndexPositive, hIndexBound,
    hStopScratchPositive, hStopScratchBound, hStopPositive, hStopBound,
    hAccumulatorPositive, hAccumulatorBound, hReleasePositive,
    hReleaseBound, hEffectivePositive, hEffectiveBound,
    hArrayNotParam, hLengthNotParam, hIndexNotParam,
    hStopScratchNotParam, hStopNotParam, hAccumulatorNotParam,
    hReleaseNotParam, hEffectiveNotParam, hLengthNeIndex,
    hLengthNeStopScratch, hLengthNeStop, hLengthNeAccumulator,
    hLengthNeRelease, hStopNeAccumulator, hStopNeRelease,
    hArrayIndex, hLengthIndex, hIndexIndex, hStopScratchIndex,
    hStopIndex, hAccumulatorIndex, hReleaseIndex, hEffectiveIndex,
    hReleaseIndexNeStopIndex, hAccumulatorIndexNeStopIndex,
    hReleaseIndexNeLengthIndex, hAccumulatorIndexNeLengthIndex,
    hStopIndexNeLengthIndex, hStopScratchIndexNeLengthIndex,
    hIndexIndexNeLengthIndex,
    List.length_set, List.getElem?_set] using hNext

def resultProgram (accumulatorLocal resultLocal : Nat) : Wasm.Program :=
  [.localGet accumulatorLocal, .localSet resultLocal]

def resultFrame (frame : Locals) (resultLocal : Nat) (value : UInt64) : Locals :=
  { frame with
    locals := frame.locals.set (resultLocal - frame.params.length) (.i64 value),
    values := [] }

theorem resultFrame_params (frame : Locals) (resultLocal : Nat)
    (value : UInt64) :
    (resultFrame frame resultLocal value).params = frame.params := rfl

theorem resultFrame_locals_length (frame : Locals) (resultLocal : Nat)
    (value : UInt64) :
    (resultFrame frame resultLocal value).locals.length = frame.locals.length := by
  simp [resultFrame]

theorem resultFrame_values (frame : Locals) (resultLocal : Nat)
    (value : UInt64) :
    (resultFrame frame resultLocal value).values = [] := rfl

@[simp]
theorem resultFrame_get_result (frame : Locals) (resultLocal : Nat)
    (value : UInt64) (hResultLocal : frame.params.length ≤ resultLocal)
    (hResultValid : frame.validIndex resultLocal) :
    (resultFrame frame resultLocal value).get resultLocal =
      some (.i64 value) := by
  have hNotParam : ¬resultLocal < frame.params.length :=
    Nat.not_lt.mpr hResultLocal
  have hResultBound :
      resultLocal < frame.params.length + frame.locals.length := hResultValid
  have hResultIndex :
      resultLocal - frame.params.length < frame.locals.length := by
    omega
  simp [resultFrame, Wasm.Locals.get, hNotParam, hResultBound,
    hResultIndex]

@[simp]
theorem resultFrame_get_of_ne (frame : Locals) (resultLocal readLocal : Nat)
    (value : UInt64) (found : Value)
    (hResultLocal : frame.params.length ≤ resultLocal)
    (hReadLocal : frame.params.length ≤ readLocal)
    (hReadValid : frame.validIndex readLocal)
    (hNe : readLocal ≠ resultLocal)
    (hRead : frame.get readLocal = some found) :
    (resultFrame frame resultLocal value).get readLocal = some found := by
  have hReadNotParam : ¬readLocal < frame.params.length :=
    Nat.not_lt.mpr hReadLocal
  have hReadBound :
      readLocal < frame.params.length + frame.locals.length := hReadValid
  have hIndexNe :
      readLocal - frame.params.length ≠
        resultLocal - frame.params.length := by
    omega
  simp only [resultFrame, Wasm.Locals.get, List.length_set,
    hReadNotParam, hReadBound, if_false, if_true]
  rw [List.getElem?_set]
  simp only [hIndexNe.symm, if_false]
  simpa [Wasm.Locals.get, hReadNotParam, hReadBound] using hRead

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem resultProgram_spec
    (accumulatorLocal resultLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (value : UInt64)
    (hValues : frame.values = [])
    (hAccumulator : frame.get accumulatorLocal = some (.i64 value))
    (hResultLocal : frame.params.length ≤ resultLocal)
    (hResultValid : frame.validIndex resultLocal)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st (resultFrame frame resultLocal value) env) :
    wp module_ (resultProgram accumulatorLocal resultLocal ++ rest)
      Q st frame env := by
  have hNotParam : ¬resultLocal < frame.params.length :=
    Nat.not_lt.mpr hResultLocal
  have hResultBound :
      resultLocal < frame.params.length + frame.locals.length := hResultValid
  unfold resultProgram
  simp only [List.cons_append, List.nil_append, wp_simp, hValues,
    hAccumulator]
  simpa [Wasm.Locals.set?, hNotParam, hResultBound, resultFrame] using hNext

def singletonResultProgram (accumulatorLocal resultLocal rootLocal
    destinationLocal returnLocal : Nat) : Wasm.Program :=
  resultProgram accumulatorLocal resultLocal ++
    FixedArrayResult.payloadStoreProgram rootLocal resultLocal 0 ++
    FixedArrayResult.finishProgram rootLocal destinationLocal returnLocal

def singletonResultPost (returnLocal : Nat) (root value : UInt64) :
    Assertion Unit :=
  fun continuation => match continuation with
  | .Fallthrough st frame =>
      frame.get returnLocal = some (.i64 root) ∧
        UInt64Array.At st root #[value]
  | _ => False

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem singletonResultProgram_spec
    (accumulatorLocal resultLocal rootLocal destinationLocal returnLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (root value : UInt64)
    (hValues : frame.values = [])
    (hAccumulator : frame.get accumulatorLocal = some (.i64 value))
    (hResultLocal : frame.params.length ≤ resultLocal)
    (hResultValid : frame.validIndex resultLocal)
    (hRoot : (resultFrame frame resultLocal value).get rootLocal =
      some (.i64 root))
    (hResult : (resultFrame frame resultLocal value).get resultLocal =
      some (.i64 value))
    (hPayloadBound :
      (FixedArrayResult.payloadAddress root 0).toUInt32.toNat + 8 ≤
        st.mem.pages * 65536)
    (hDestinationLower :
      (resultFrame frame resultLocal value).params.length ≤ destinationLocal)
    (hDestinationValid :
      (resultFrame frame resultLocal value).validIndex destinationLocal)
    (hReturnLower :
      (resultFrame frame resultLocal value).params.length ≤ returnLocal)
    (hReturnValid :
      (resultFrame frame resultLocal value).validIndex returnLocal)
    (hOutput : UInt64Array.At
      (FixedArrayResult.writePayload st root 0 value) root #[value]) :
    wp module_
      (singletonResultProgram accumulatorLocal resultLocal rootLocal
        destinationLocal returnLocal)
      (singletonResultPost returnLocal root value) st frame env := by
  rw [singletonResultProgram, List.append_assoc]
  apply resultProgram_spec
  · exact hValues
  · exact hAccumulator
  · exact hResultLocal
  · exact hResultValid
  · apply FixedArrayResult.payloadStore_spec
    · exact hRoot
    · exact hResult
    · exact hPayloadBound
    · apply FixedArrayResult.finishProgram_spec
      · rfl
      · exact hRoot
      · exact hDestinationLower
      · exact hDestinationValid
      · exact hReturnLower
      · exact hReturnValid
      · simp only [Wasm.wp_nil, singletonResultPost]
        exact ⟨FixedArrayResult.finishFrame_return_get _ _ _ _
          hReturnLower hReturnValid, hOutput⟩

end Project.ProofKit.FixedArrayFold
