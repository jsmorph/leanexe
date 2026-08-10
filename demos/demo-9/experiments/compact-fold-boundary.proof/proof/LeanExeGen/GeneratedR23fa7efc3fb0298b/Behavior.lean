import LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec
import LeanExeGen.GeneratedR23fa7efc3fb0298b.Program
import LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.Control
import Project.ProofKit.FixedArrayCapacity
import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArrayFold
import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArrayTraversalInput
import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayResult
import Project.ProofKit.Frame

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior

open Wasm Project.ProofKit

def foldInvariant (current : Store Unit) (inputPtr root : UInt64)
    (input : Array UInt64) (st : Store Unit) (frame : Locals) : Prop :=
  st = current ∧
  ∃ index : Nat,
    index ≤ input.size ∧
    frame.params = [.i64 inputPtr] ∧
    frame.locals.length = 20 ∧
    frame.values = [] ∧
    frame.get 7 = some (.i64 root) ∧
    frame.get 11 = some (.i64 inputPtr) ∧
    frame.get 13 = some (.i64 (UInt64.ofNat index)) ∧
    frame.get 15 = some (.i64 (UInt64.ofNat input.size)) ∧
    frame.get 1 = some (.i64
      (ArrayFold.foldPrefix input (fun sum element => sum + element) 0 index))

def foldMeasure (inputSize : Nat) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 13 with
  | some (.i64 index) => inputSize - index.toNat
  | _ => 0

def foldUpdateProgram : Wasm.Program :=
  [
  .localGet 1,
  .localGet 2,
  .addI64,
  .localSet 3,
  .localGet 3,
  .localSet 17,
  .constI64 0,
  .localSet 16,
  .localGet 17,
  .localSet 1,
  .constI64 1,
  .localSet 18,
  .localGet 16,
  .constI64 0,
  .neI64,
  .br_if 1,
  .localGet 13,
  .constI64 1,
  .addI64,
  .localSet 13,
  .br 0
  ]

def foldUpdateFrame (frame : Locals) (sum nextIndex : UInt64) : Locals :=
  { frame with
    locals := (((((frame.locals.set 2 (.i64 sum)).set 16 (.i64 sum)).set
      15 (.i64 0)).set 0 (.i64 sum)).set 17 (.i64 1)).set
      12 (.i64 nextIndex)
    values := [] }

theorem foldUpdateFrame_get_index (frame : Locals) (sum nextIndex : UInt64)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 20) :
    (foldUpdateFrame frame sum nextIndex).get 13 =
      some (.i64 nextIndex) := by
  simp [foldUpdateFrame, Wasm.Locals.get, hParams, hLocals]

theorem finishFrame_get_six (frame : Locals) (destination : Nat)
    (root : UInt64) (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 20) :
    (FixedArrayResult.finishFrame frame destination 6 root).get 6 =
      some (.i64 root) := by
  simp [FixedArrayResult.finishFrame, Wasm.Locals.get, hParams, hLocals]

theorem finishFrame_get_six_reset (frame : Locals) (destination : Nat)
    (root : UInt64) (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 20) :
    ({ FixedArrayResult.finishFrame frame destination 6 root with values := [] } :
        Locals).get 6 = some (.i64 root) := by
  simpa only [Wasm.Locals.get] using
    finishFrame_get_six frame destination root hParams hLocals

set_option Elab.async false in
theorem foldUpdateProgram_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (accumulator item index : UInt64)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 20)
    (hValues : frame.values = [])
    (hAccumulator : frame.get 1 = some (.i64 accumulator))
    (hItem : frame.get 2 = some (.i64 item))
    (hIndex : frame.get 13 = some (.i64 index))
    (Q : Assertion Unit)
    (hNext : Q (.Break 0 st
      (foldUpdateFrame frame (accumulator + item) (index + 1)))) :
    wp module_ foldUpdateProgram Q st frame env := by
  have hAccumulatorLocal := Frame.internal_getElem_of_get frame 1 0
    (.i64 accumulator) hParams (by omega) (by simpa using hAccumulator)
  have hItemLocal := Frame.internal_getElem_of_get frame 1 1
    (.i64 item) hParams (by omega) (by simpa using hItem)
  have hIndexLocal := Frame.internal_getElem_of_get frame 1 12
    (.i64 index) hParams (by omega) (by simpa using hIndex)
  unfold foldUpdateProgram
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Wasm.Locals.get, Wasm.Locals.set?, Wasm.Locals.validIndex,
    List.length_set, List.getElem?_set, hParams, hLocals, hValues,
    hAccumulatorLocal, hItemLocal, hIndexLocal]
  simpa [foldUpdateFrame, hValues] using hNext

theorem artifact_behavior :
    LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec.ArtifactSpec LeanExeGen.GeneratedR23fa7efc3fb0298b.«module» := by
  refine ⟨0, rfl, ?_⟩
  intro env initial inputPtr input hInput
  rcases hInput with
    ⟨hArray, heapTop, allocs, retains, releases, frees, hGlobals,
      hInputBelow, hOutputFit32, hOutputFitMemory,
      hHeapFit32, hHeapFitMemory, hPages⟩
  change UInt64Array.At initial inputPtr input at hArray
  have hLengthRead := hArray.lengthRead
  have hLengthBound := hArray.generatedLengthBound
  have hInputAddress := hArray.pointerAddress_eq
  have hHeapTop : initial.globals.globals[0]? = some (.i64 heapTop) := by
    simp [hGlobals]
  have hFreeList : initial.globals.globals[1]? = some (.i64 0) := by
    simp [hGlobals]
  have hAllocs : initial.globals.globals[2]? = some (.i64 allocs) := by
    simp [hGlobals]
  apply Wasm.TerminatesWith.of_wp_entry_for (f := func0Def) rfl
  wp_fixed_array_length_le_dispatch_from hArray at 7, 8
  · simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  · simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  · norm_num
  · simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  · norm_num [UInt64.size]
  · intro hSize
    change wp module
      (FixedArrayCapacity.constantProgram 1 1 11 ++ _) _ initial _ env
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [func0Def, Function.toLocals, Function.numParams,
        ValueType.zero, FixedArrayLengthDispatch.branchFrame]
    · norm_num [func0Def, Function.toLocals, Function.numParams,
        ValueType.zero, FixedArrayLengthDispatch.branchFrame,
        Wasm.Locals.validIndex]
    · change wp module
        (FixedArrayAllocatorWindow.region 2 1 ++ _) _ initial _ env
      apply FixedArrayAllocatorWindow.region_spec_withTail 2 4
        (heapTop := heapTop) (capacity := 16) (allocs := allocs)
      · norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero]
      · norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero]
      · rfl
      · norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity]
        <;> native_decide
      · norm_num [FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity]
        <;> native_decide
      · simpa [FormalSpec.expected, hSize,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity] using hOutputFitMemory
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · have hFit : heapTop.toNat + 48 + 16 ≤
            initial.mem.pages * 65536 := by
          simpa [FormalSpec.expected, hSize] using hOutputFitMemory
        have hFacts := Allocation.bumpFacts heapTop 16 initial.mem.pages
          hFit hPages
        have hInputAlloc := FixedArrayPairResult.input_preserved_by_alloc
          initial heapTop 16 1 allocs inputPtr input hArray hInputBelow
          hFit hPages
        have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
            (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs).mem.pages *
              65536 := by
          rw [show (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 by
            simpa using hFacts.wordAddress_toNat 0 (by native_decide)]
          rw [FixedArrayAllocator.allocStore_pages]
          omega
        have hInputCurrent : UInt64Array.At
            (FixedArrayResult.writeLength
              (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
              (heapTop + 48) 1) inputPtr input := by
          simpa [FixedArrayResult.writeLength] using
            (hInputAlloc.write64After
              (address := (heapTop + 48).toUInt32) (value := 1)
              (by
                rw [show (heapTop + 48).toUInt32.toNat =
                    heapTop.toNat + 48 by
                  simpa using hFacts.wordAddress_toNat 0 (by native_decide)]
                omega))
        change wp module
          (FixedArrayResult.lengthStoreProgram 7 1 ++ _) _ _ _ env
        apply FixedArrayResult.lengthStore_spec
          (root := heapTop + 48) (rootLocal := 7)
        · rfl
        · norm_num [Wasm.Locals.get,
            FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Function.toLocals, Function.numParams, ValueType.zero]
          <;> native_decide
        · exact hRootBound
        · change wp module
            (FixedArrayFold.forwardSetupProgram
              11 12 13 16 14 1 18 15 0 ++ _) _ _ _ env
          apply FixedArrayFold.forwardSetupProgram_spec
            (hInput := hInputCurrent)
          · norm_num [FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Function.toLocals, Function.numParams, ValueType.zero]
          · rfl
          · intro slot hSlot
            have hLocals :
                (FixedArrayAllocatorWindow.allocFrame 2
                  (FixedArrayCapacity.capacityFrame
                    (FixedArrayLengthDispatch.branchFrame 7
                      (func0Def.toLocals
                        (List.take func0Def.numParams
                          [Value.i64 inputPtr]).reverse)
                      inputPtr)
                    11 (FixedArrayCapacity.normalizedCapacity 1 1))
                  heapTop 16).locals.length = 20 := by
              norm_num [FixedArrayAllocatorWindow.allocFrame,
                FixedArrayCapacity.capacityFrame,
                FixedArrayLengthDispatch.branchFrame, func0Def,
                Function.toLocals, Function.numParams, ValueType.zero]
            simp [FixedArrayFold.setupLocals] at hSlot
            omega
          · native_decide
          · apply Wasm.wp_block_cons
            apply Wasm.wp_loop_cons
              (Inv := foldInvariant
                (FixedArrayResult.writeLength
                  (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                  (heapTop + 48) 1)
                inputPtr (heapTop + 48) input)
              (μ := foldMeasure input.size)
            · refine ⟨rfl, 0, by omega, ?_, ?_, rfl,
                ?_, ?_, ?_, ?_, ?_⟩
              all_goals
                norm_num [FixedArrayFold.forwardSetupFrame,
                  FixedArrayAllocatorWindow.allocFrame,
                  FixedArrayCapacity.capacityFrame,
                  FixedArrayLengthDispatch.branchFrame, func0Def,
                  Function.toLocals, Function.numParams, ValueType.zero,
                  Wasm.Locals.get, ArrayFold.foldPrefix]
                <;> native_decide
            · rintro loopStore loopFrame hInv
              rcases hInv with
                ⟨rfl, index, hIndex, hParamsLoop, hLocalsLoop,
                  hValuesLoop, hRootLoop, hArrayLoop, hIndexLoop,
                  hStopLoop, hAccumulatorLoop⟩
              have hItem : loopFrame.validIndex 2 := by
                simp [Wasm.Locals.validIndex, hParamsLoop, hLocalsLoop]
              by_cases hContinue : index < input.size
              · have hIndex64 : index < UInt64.size := by
                  exact lt_trans hContinue hInputCurrent.size_lt
                have hContinue64 :
                    UInt64.ofNat index < UInt64.ofNat input.size := by
                  rw [UInt64.lt_iff_toNat_lt,
                    UInt64.toNat_ofNat_of_lt' hIndex64,
                    UInt64.toNat_ofNat_of_lt' hInputCurrent.size_lt]
                  exact hContinue
                change wp module
                  (FixedArrayTraversalInput.continuingProgram 11 13 15 2 ++ _)
                  _ _ loopFrame env
                apply FixedArrayTraversalInput.continuingProgram_spec
                  (inputPtr := inputPtr) (indexValue := UInt64.ofNat index)
                  (stopValue := UInt64.ofNat input.size)
                  (input := input) (index := index) (hItem := hItem)
                · exact hValuesLoop
                · exact hArrayLoop
                · exact hIndexLoop
                · exact hStopLoop
                · rfl
                · exact hContinue64
                · exact hInputCurrent
                · have hIndexSucc :
                      UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by
                    change UInt64.ofNat index + UInt64.ofNat 1 =
                      UInt64.ofNat (index + 1)
                    rw [← UInt64.ofNat_add]
                  have hIndexSucc64 : index + 1 < UInt64.size := by
                    exact lt_of_le_of_lt (Nat.succ_le_iff.mpr hContinue)
                      hInputCurrent.size_lt
                  have hFoldStep := ArrayFold.foldPrefix_succ input
                    (fun sum element : UInt64 => sum + element) 0 index
                    hContinue
                  change wp module foldUpdateProgram _ _ _ env
                  apply foldUpdateProgram_spec
                    (accumulator := ArrayFold.foldPrefix input
                      (fun sum element => sum + element) 0 index)
                    (item := input[index]) (index := UInt64.ofNat index)
                  · simpa [FixedArrayTraversalInput.dynamicResultFrame,
                      hParamsLoop]
                  · simpa [FixedArrayTraversalInput.dynamicResultFrame,
                      Wasm.Locals.set, hParamsLoop, hLocalsLoop]
                  · simp [FixedArrayTraversalInput.dynamicResultFrame,
                      Wasm.Locals.set, hParamsLoop, hValuesLoop]
                  · simpa [FixedArrayTraversalInput.dynamicResultFrame,
                      Wasm.Locals.get, Wasm.Locals.set?, hItem,
                      hParamsLoop, hLocalsLoop] using hAccumulatorLoop
                  · simp [FixedArrayTraversalInput.dynamicResultFrame,
                      Wasm.Locals.get, Wasm.Locals.set?, hItem,
                      hParamsLoop, hLocalsLoop]
                  · simpa [FixedArrayTraversalInput.dynamicResultFrame,
                      Wasm.Locals.get, Wasm.Locals.set?, hItem,
                      hParamsLoop, hLocalsLoop] using hIndexLoop
                  · simp only [hValuesLoop, List.take_zero, List.drop_zero,
                    List.nil_append]
                    change foldInvariant
                        (FixedArrayResult.writeLength
                          (FixedArrayAllocator.allocStore
                            initial heapTop 16 1 allocs)
                          (heapTop + 48) 1)
                        inputPtr (heapTop + 48) input
                        (FixedArrayResult.writeLength
                          (FixedArrayAllocator.allocStore
                            initial heapTop 16 1 allocs)
                          (heapTop + 48) 1)
                        (foldUpdateFrame
                          (FixedArrayTraversalInput.dynamicResultFrame
                            loopFrame 2 input[index] hItem)
                          (ArrayFold.foldPrefix input
                            (fun sum element => sum + element) 0 index +
                              input[index])
                          (UInt64.ofNat index + 1)) ∧
                      foldMeasure input.size
                          (FixedArrayResult.writeLength
                            (FixedArrayAllocator.allocStore
                              initial heapTop 16 1 allocs)
                            (heapTop + 48) 1)
                          (foldUpdateFrame
                            (FixedArrayTraversalInput.dynamicResultFrame
                              loopFrame 2 input[index] hItem)
                            (ArrayFold.foldPrefix input
                              (fun sum element => sum + element) 0 index +
                                input[index])
                            (UInt64.ofNat index + 1)) <
                        foldMeasure input.size
                          (FixedArrayResult.writeLength
                            (FixedArrayAllocator.allocStore
                              initial heapTop 16 1 allocs)
                            (heapTop + 48) 1)
                          loopFrame
                    have hNextIndex :
                        (foldUpdateFrame
                          (FixedArrayTraversalInput.dynamicResultFrame
                            loopFrame 2 input[index] hItem)
                          (ArrayFold.foldPrefix input
                            (fun sum element => sum + element) 0 index +
                              input[index])
                          (UInt64.ofNat index + 1)).get 13 =
                            some (.i64 (UInt64.ofNat (index + 1))) := by
                      apply Eq.trans (foldUpdateFrame_get_index _ _ _
                        (by
                          simp [FixedArrayTraversalInput.dynamicResultFrame,
                            Wasm.Locals.set, hParamsLoop])
                        (by
                          simp [FixedArrayTraversalInput.dynamicResultFrame,
                            Wasm.Locals.set, hParamsLoop, hLocalsLoop]))
                      exact congrArg
                        (fun value : UInt64 => some (Value.i64 value))
                        hIndexSucc
                    constructor
                    · refine ⟨rfl, index + 1, by omega, ?_, ?_, rfl,
                        ?_, ?_, ?_, ?_, ?_⟩
                      · simp [foldUpdateFrame,
                          FixedArrayTraversalInput.dynamicResultFrame,
                          Wasm.Locals.set, hParamsLoop]
                      · simp [foldUpdateFrame,
                          FixedArrayTraversalInput.dynamicResultFrame,
                          Wasm.Locals.set, hParamsLoop, hLocalsLoop]
                      · simpa [foldUpdateFrame,
                          FixedArrayTraversalInput.dynamicResultFrame,
                          Wasm.Locals.get, Wasm.Locals.set, hParamsLoop,
                          hLocalsLoop] using hRootLoop
                      · simpa [foldUpdateFrame,
                          FixedArrayTraversalInput.dynamicResultFrame,
                          Wasm.Locals.get, Wasm.Locals.set, hParamsLoop,
                          hLocalsLoop] using hArrayLoop
                      · exact hNextIndex
                      · simpa [foldUpdateFrame,
                          FixedArrayTraversalInput.dynamicResultFrame,
                          Wasm.Locals.get, Wasm.Locals.set, hParamsLoop,
                          hLocalsLoop] using hStopLoop
                      · simp [foldUpdateFrame,
                          FixedArrayTraversalInput.dynamicResultFrame,
                          Wasm.Locals.get, Wasm.Locals.set, hParamsLoop,
                          hLocalsLoop, hFoldStep]
                    · simp only [foldMeasure, hNextIndex, hIndexLoop]
                      rw [UInt64.toNat_ofNat_of_lt' hIndexSucc64,
                        UInt64.toNat_ofNat_of_lt' hIndex64]
                      omega
              · have hIndexEq : index = input.size := by omega
                subst index
                change wp module
                  (FixedArrayTraversalInput.continuingProgram 11 13 15 2 ++ _)
                  _ _ loopFrame env
                apply FixedArrayTraversalInput.continuingProgram_exit_spec
                  (index := UInt64.ofNat input.size)
                · exact hValuesLoop
                · exact hIndexLoop
                · exact hStopLoop
                · simp only [FixedArrayFold.forwardSetupFrame_values,
                    List.take_zero, List.drop_zero, List.nil_append]
                  have hLoopFrameEmpty :
                      ({ loopFrame with values := [] } : Locals) =
                        loopFrame := by
                    cases loopFrame
                    simp_all
                  rw [hLoopFrameEmpty]
                  have hAccumulatorFinal : loopFrame.get 1 = some (.i64
                      (input.foldl (fun sum element => sum + element) 0)) := by
                    simpa [ArrayFold.foldPrefix_size] using hAccumulatorLoop
                  have hFit32 : heapTop.toNat + 48 + 16 ≤ 4294967296 := by
                    simpa [FormalSpec.expected, hSize] using hOutputFit32
                  have hPayloadBound :
                      (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat + 8 ≤
                        (FixedArrayResult.writeLength
                          (FixedArrayAllocator.allocStore
                            initial heapTop 16 1 allocs)
                          (heapTop + 48) 1).mem.pages * 65536 := by
                    rw [show
                      (FixedArrayResult.payloadAddress
                        (heapTop + 48) 0).toUInt32.toNat =
                          heapTop.toNat + 48 + 8 by
                      simpa [FixedArrayResult.payloadAddress] using
                        hFacts.wordAddress_toNat 1 (by native_decide)]
                    rw [FixedArrayResult.writeLength_pages,
                      FixedArrayAllocator.allocStore_pages]
                    omega
                  have hOutput : UInt64Array.At
                      (FixedArrayResult.singletonStore
                        (FixedArrayAllocator.allocStore
                          initial heapTop 16 1 allocs)
                        (heapTop + 48)
                        (input.foldl (fun sum element => sum + element) 0))
                      (heapTop + 48)
                      #[input.foldl (fun sum element => sum + element) 0] := by
                    apply FixedArrayResult.singletonStore_at
                    · rw [hFacts.rootToNat]
                      exact hFit32
                    · rw [hFacts.rootToNat,
                        FixedArrayAllocator.allocStore_pages]
                      exact hFit
                  change wp module
                    (FixedArrayFold.resultProgram 1 10 ++ _) _ _ loopFrame env
                  apply FixedArrayFold.resultProgram_spec
                    (value := input.foldl
                      (fun sum element => sum + element) 0)
                  · exact hValuesLoop
                  · exact hAccumulatorFinal
                  · simp [hParamsLoop]
                  · simp [Wasm.Locals.validIndex,
                      hParamsLoop, hLocalsLoop]
                  · change wp module
                      (FixedArrayResult.payloadStoreProgram 7 10 0 ++
                        FixedArrayResult.finishProgram 7 4 6) _ _ _ env
                    apply FixedArrayResult.payloadStore_spec
                      (root := heapTop + 48)
                      (value := input.foldl
                        (fun sum element => sum + element) 0)
                    · simpa [FixedArrayFold.resultFrame,
                        Wasm.Locals.get, hParamsLoop, hLocalsLoop] using
                        hRootLoop
                    · simp [FixedArrayFold.resultFrame,
                        Wasm.Locals.get, hParamsLoop, hLocalsLoop]
                    · exact hPayloadBound
                    · change wp module
                        (FixedArrayResult.finishProgram 7 4 6 ++ []) _ _ _ env
                      have hResultParams :
                          (FixedArrayFold.resultFrame loopFrame 10
                            (input.foldl
                              (fun sum element => sum + element) 0)).params.length =
                            1 := by
                        simp [FixedArrayFold.resultFrame, hParamsLoop]
                      have hResultLocals :
                          (FixedArrayFold.resultFrame loopFrame 10
                            (input.foldl
                              (fun sum element => sum + element) 0)).locals.length =
                            20 := by
                        simp [FixedArrayFold.resultFrame, hLocalsLoop]
                      apply FixedArrayResult.finishProgram_spec
                        (root := heapTop + 48)
                      · rfl
                      · simpa [FixedArrayFold.resultFrame,
                          Wasm.Locals.get, hParamsLoop, hLocalsLoop] using
                          hRootLoop
                      · simp [FixedArrayFold.resultFrame, hParamsLoop]
                      · simp [Wasm.Locals.validIndex,
                          FixedArrayFold.resultFrame,
                          hParamsLoop, hLocalsLoop]
                      · simp [FixedArrayFold.resultFrame, hParamsLoop]
                      · simp [Wasm.Locals.validIndex,
                          FixedArrayFold.resultFrame,
                          hParamsLoop, hLocalsLoop]
                      · rw [wp_nil]
                        simp only [FixedArrayEqNode.branchPost]
                        simp only [wp_simp]
                        rw [finishFrame_get_six_reset _ _ _ hResultParams
                          hResultLocals]
                        refine ⟨heapTop + 48, ?_, ?_⟩
                        · simp [func0Def, Function.numParams]
                        · simpa [FormalSpec.expected, hSize,
                            FormalSpec.UInt64ArrayAt, UInt64Array.At,
                            FixedArrayResult.singletonStore] using hOutput
  · intro hSize
    change wp module
      (FixedArrayCapacity.constantProgram 0 1 11 ++ _) _ initial _ env
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [func0Def, Function.toLocals, Function.numParams,
        ValueType.zero, FixedArrayLengthDispatch.branchFrame]
    · norm_num [func0Def, Function.toLocals, Function.numParams,
        ValueType.zero, FixedArrayLengthDispatch.branchFrame,
        Wasm.Locals.validIndex]
    · change wp module
        (FixedArrayAllocatorWindow.region 2 1 ++ _) _ initial _ env
      apply FixedArrayAllocatorWindow.region_spec_withTail 2 4
        (heapTop := heapTop) (capacity := 8) (allocs := allocs)
      · norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero]
      · norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero]
      · rfl
      · norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity]
        <;> native_decide
      · norm_num [FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity]
        <;> native_decide
      · simpa [FormalSpec.expected, hSize,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity] using hOutputFitMemory
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · have hFit : heapTop.toNat + 48 + 8 ≤
            initial.mem.pages * 65536 := by
          simpa [FormalSpec.expected, hSize] using hOutputFitMemory
        have hFit32 : heapTop.toNat + 48 + 8 ≤ 4294967296 := by
          simpa [FormalSpec.expected, hSize] using hOutputFit32
        have hFacts := Allocation.bumpFacts heapTop 8 initial.mem.pages
          hFit hPages
        have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
            (FixedArrayAllocator.allocStore initial heapTop 8 1 allocs).mem.pages *
              65536 := by
          rw [show (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 by
            simpa using hFacts.wordAddress_toNat 0 (by native_decide)]
          rw [FixedArrayAllocator.allocStore_pages]
          omega
        have hOutput : UInt64Array.At
            (FixedArrayResult.writeLength
              (FixedArrayAllocator.allocStore initial heapTop 8 1 allocs)
              (heapTop + 48) 0) (heapTop + 48) #[] := by
          apply FixedArrayResult.emptyStore_at
          · rw [hFacts.rootToNat]
            exact hFit32
          · rw [hFacts.rootToNat,
              FixedArrayAllocator.allocStore_pages]
            exact hFit
        change wp module
          (FixedArrayResult.lengthStoreProgram 7 0 ++
            FixedArrayResult.finishProgram 7 5 6) _ _ _ env
        apply FixedArrayResult.lengthStore_spec
          (root := heapTop + 48) (rootLocal := 7)
        · rfl
        · norm_num [Wasm.Locals.get,
            FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Function.toLocals, Function.numParams, ValueType.zero]
          <;> native_decide
        · exact hRootBound
        · let invalidFrame : Locals :=
            FixedArrayAllocatorWindow.allocFrame 2
              (FixedArrayCapacity.capacityFrame
                (FixedArrayLengthDispatch.branchFrame 7
                  (func0Def.toLocals
                    (List.take func0Def.numParams
                      [Value.i64 inputPtr]).reverse)
                  inputPtr)
                11 (FixedArrayCapacity.normalizedCapacity 0 1))
              heapTop 8
          change wp module
            (FixedArrayResult.finishProgram 7 5 6 ++ []) _ _ invalidFrame env
          have hInvalidParams : invalidFrame.params.length = 1 := by
            norm_num [invalidFrame, FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Function.toLocals, Function.numParams, ValueType.zero]
          have hInvalidLocals : invalidFrame.locals.length = 20 := by
            norm_num [invalidFrame, FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Function.toLocals, Function.numParams, ValueType.zero]
          apply FixedArrayResult.finishProgram_spec
            (root := heapTop + 48)
          · rfl
          · norm_num [invalidFrame, Wasm.Locals.get,
              FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Function.toLocals, Function.numParams, ValueType.zero]
            <;> native_decide
          · omega
          · simpa [Wasm.Locals.validIndex] using
              (show 5 < invalidFrame.params.length +
                  invalidFrame.locals.length by omega)
          · omega
          · simpa [Wasm.Locals.validIndex] using
              (show 6 < invalidFrame.params.length +
                  invalidFrame.locals.length by omega)
          · rw [wp_nil]
            simp only [FixedArrayEqNode.branchPost]
            simp only [wp_simp]
            rw [finishFrame_get_six_reset _ _ _ hInvalidParams
              hInvalidLocals]
            refine ⟨heapTop + 48, ?_, ?_⟩
            · simp [func0Def, Function.numParams]
            · simpa [FormalSpec.expected, hSize,
                FormalSpec.UInt64ArrayAt, UInt64Array.At] using hOutput

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior
