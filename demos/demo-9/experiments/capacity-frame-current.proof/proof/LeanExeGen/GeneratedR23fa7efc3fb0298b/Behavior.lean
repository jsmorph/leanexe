import LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec
import LeanExeGen.GeneratedR23fa7efc3fb0298b.Program
import LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches
import Project.ProofKit.Allocation
import Project.ProofKit.Array
import Project.ProofKit.Control
import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayCapacity
import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArrayFold
import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArrayPairResult
import Project.ProofKit.FixedArrayResult
import Project.ProofKit.FixedArrayTraversalInput

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior

open Wasm Project.ProofKit

def sumInvariant (baseStore : Store Unit) (inputPtr outputPtr : UInt64)
    (input : Array UInt64) (store : Store Unit) (frame : Locals) : Prop :=
  store = baseStore ∧
    ∃ index : Nat,
      index ≤ input.size ∧
      frame.params = [.i64 inputPtr] ∧
      frame.locals.length = 20 ∧
      frame.values = [] ∧
      frame.get 7 = some (.i64 outputPtr) ∧
      frame.get 11 = some (.i64 inputPtr) ∧
      frame.get 13 = some (.i64 (UInt64.ofNat index)) ∧
      frame.get 15 = some (.i64 (UInt64.ofNat input.size)) ∧
      frame.get 1 = some (.i64
        (ArrayFold.foldPrefix input (fun sum element => sum + element) 0 index))

def sumMeasure (input : Array UInt64) (frame : Locals) : Nat :=
  match frame.get 13 with
  | some (.i64 index) => input.size - index.toNat
  | _ => 0

theorem sumExitProgram_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (frame : Locals) (index : UInt64)
    (hValues : frame.values = [])
    (hIndex : frame.get 13 = some (.i64 index))
    (hStop : frame.get 15 = some (.i64 index))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : Q (.Break 1 store { frame with values := [] })) :
    wp module_
      (FixedArrayTraversalInput.continuingProgram 11 13 15 2 ++ rest)
      Q store frame env := by
  have hStopAfter (values : List Value) :
      ({ frame with values := values } : Locals).get 15 = some (.i64 index) := by
    simpa only [Wasm.Locals.get] using hStop
  unfold FixedArrayTraversalInput.continuingProgram
  rw [List.append_assoc]
  simp only [List.cons_append, List.nil_append, wp_simp, hValues, hIndex,
    hStopAfter]
  rw [if_pos (by simp)]
  simpa [hValues] using hNext

def sumContinueProgram : Wasm.Program :=
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

def sumContinueFrame (frame : Locals) (sum item index : UInt64) : Locals :=
  { frame with
    locals := (((((frame.locals.set 2 (.i64 (sum + item))).set 16
      (.i64 (sum + item))).set 15 (.i64 0)).set 0
      (.i64 (sum + item))).set 17 (.i64 1)).set 12 (.i64 (index + 1))
    values := [] }

theorem sumContinueFrame_get_index
    (frame : Locals) (sum item index : UInt64)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 20) :
    (sumContinueFrame frame sum item index).get 13 =
      some (.i64 (index + 1)) := by
  wp_alloc_window [sumContinueFrame, hParams, hLocals]

theorem sumContinueFrame_get_accumulator
    (frame : Locals) (sum item index : UInt64)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 20) :
    (sumContinueFrame frame sum item index).get 1 =
      some (.i64 (sum + item)) := by
  wp_alloc_window [sumContinueFrame, hParams, hLocals]

theorem sumContinueProgram_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (frame : Locals) (inputPtr sum item index : UInt64)
    (hParams : frame.params = [.i64 inputPtr])
    (hLocals : frame.locals.length = 20)
    (hValues : frame.values = [])
    (hSum : frame.get 1 = some (.i64 sum))
    (hItem : frame.get 2 = some (.i64 item))
    (hIndex : frame.get 13 = some (.i64 index))
    (Q : Assertion Unit)
    (hNext : Q (.Break 0 store (sumContinueFrame frame sum item index))) :
    wp module_ sumContinueProgram Q store frame env := by
  have hSumOption : frame.locals[0]? = some (.i64 sum) := by
    simpa [Wasm.Locals.get, hParams, hLocals] using hSum
  have hSumElem : frame.locals[0] = .i64 sum := by
    rw [List.getElem?_eq_getElem (by omega)] at hSumOption
    exact Option.some.inj hSumOption
  have hItemOption : frame.locals[1]? = some (.i64 item) := by
    simpa [Wasm.Locals.get, hParams, hLocals] using hItem
  have hItemElem : frame.locals[1] = .i64 item := by
    rw [List.getElem?_eq_getElem (by omega)] at hItemOption
    exact Option.some.inj hItemOption
  have hIndexOption : frame.locals[12]? = some (.i64 index) := by
    simpa [Wasm.Locals.get, hParams, hLocals] using hIndex
  have hIndexElem : frame.locals[12] = .i64 index := by
    rw [List.getElem?_eq_getElem (by omega)] at hIndexOption
    exact Option.some.inj hIndexOption
  unfold sumContinueProgram
  wp_alloc_window [sumContinueFrame, hParams, hLocals, hValues, hSumElem,
    hItemElem, hIndexElem]
  simpa [sumContinueFrame, hParams] using hNext

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
  · rfl
  · rfl
  · omega
  · norm_num [func0Def, Function.toLocals]
  · norm_num [UInt64.size]
  · intro hSize
    change wp module
      (AnnotationMatches.function_0_length_dispatch_0_valid_capacity_program ++ _)
      _ initial _ env
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals]
    · norm_num [Wasm.Locals.validIndex,
        FixedArrayLengthDispatch.branchFrame, func0Def, Function.toLocals]
    · have hAllocFit : heapTop.toNat + 48 + (16 : UInt64).toNat ≤
          initial.mem.pages * 65536 := by
        simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
      have hFacts := Allocation.bumpFacts heapTop 16 initial.mem.pages
        hAllocFit hPages
      change wp module
        (FixedArrayAllocatorWindow.region 2 1 ++ _) _ initial _ env
      apply FixedArrayAllocatorWindow.region_spec_withTail
        (offset := 2) (tail := 4) (heapTop := heapTop) (capacity := 16)
        (stride := 1) (allocs := allocs)
      · rfl
      · norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def, Function.toLocals]
      · rfl
      · wp_alloc_window [FixedArrayCapacity.capacityFrame,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity,
          FixedArrayLengthDispatch.branchFrame, func0Def, Function.toLocals]
        rfl
      · decide
      · exact hAllocFit
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · change wp module
          (FixedArrayResult.lengthStoreProgram 7 1 ++ _) _ _ _ env
        apply FixedArrayResult.lengthStore_spec (root := heapTop + 48)
        · rfl
        · wp_alloc_window [FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayCapacity.normalizedCapacity,
            FixedArrayCapacity.unnormalizedCapacity,
            FixedArrayLengthDispatch.branchFrame, func0Def, Function.toLocals]
          rfl
        · have hRootNat : (heapTop + 48).toUInt32.toNat =
              heapTop.toNat + 48 := by
            simpa using hFacts.wordAddress_toNat 0 (by decide)
          rw [hRootNat, FixedArrayAllocator.allocStore_pages]
          norm_num at hAllocFit
          omega
        · have hArrayAlloc :=
            FixedArrayPairResult.input_preserved_by_alloc initial heapTop 16 1
              allocs inputPtr input hArray hInputBelow hAllocFit hPages
          have hRootNat : (heapTop + 48).toUInt32.toNat =
              heapTop.toNat + 48 := by
            simpa using hFacts.wordAddress_toNat 0 (by decide)
          have hArrayStored : UInt64Array.At
              (FixedArrayResult.writeLength
                (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                (heapTop + 48) 1) inputPtr input := by
            unfold FixedArrayResult.writeLength
            apply hArrayAlloc.write64After
            rw [hRootNat]
            omega
          change wp module
            (AnnotationMatches.function_0_array_fold_0_setup_program ++ _)
            _ _ _ env
          apply FixedArrayFold.forwardSetupProgram_spec
            (inputPtr := inputPtr) (input := input) (hInput := hArrayStored)
          · rfl
          · rfl
          · wp_alloc_window [FixedArrayFold.setupLocals,
              FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayCapacity.normalizedCapacity,
              FixedArrayCapacity.unnormalizedCapacity,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Function.toLocals]
          · decide
          · wp_block_loop invariant
              (sumInvariant
                (FixedArrayResult.writeLength
                  (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                  (heapTop + 48) 1)
                inputPtr (heapTop + 48) input)
              decreasing (fun _ frame => sumMeasure input frame)
            · unfold sumInvariant
              refine ⟨rfl, 0, by omega, ?_⟩
              wp_alloc_window [FixedArrayFold.forwardSetupFrame,
                FixedArrayAllocatorWindow.allocFrame,
                FixedArrayCapacity.capacityFrame,
                FixedArrayCapacity.normalizedCapacity,
                FixedArrayCapacity.unnormalizedCapacity,
                FixedArrayLengthDispatch.branchFrame, func0Def,
                Function.toLocals, ArrayFold.foldPrefix]
              simp
            · intro st frame hInv
              rcases hInv with
                ⟨rfl, index, hIndex, hParams, hLocals, hValues,
                  hOutputLocal, hArrayLocal, hIndexLocal, hStopLocal,
                  hAccumulator⟩
              have hOutputOption : frame.locals[6]? =
                  some (.i64 (heapTop + 48)) := by
                simpa [Wasm.Locals.get, hParams, hLocals] using hOutputLocal
              have hOutputElem : frame.locals[6] = .i64 (heapTop + 48) := by
                rw [List.getElem?_eq_getElem (by omega)] at hOutputOption
                exact Option.some.inj hOutputOption
              have hArrayOption : frame.locals[10]? =
                  some (.i64 inputPtr) := by
                simpa [Wasm.Locals.get, hParams, hLocals] using hArrayLocal
              have hArrayElem : frame.locals[10] = .i64 inputPtr := by
                rw [List.getElem?_eq_getElem (by omega)] at hArrayOption
                exact Option.some.inj hArrayOption
              have hIndexOption : frame.locals[12]? =
                  some (.i64 (UInt64.ofNat index)) := by
                simpa [Wasm.Locals.get, hParams, hLocals] using hIndexLocal
              have hIndexElem : frame.locals[12] =
                  .i64 (UInt64.ofNat index) := by
                rw [List.getElem?_eq_getElem (by omega)] at hIndexOption
                exact Option.some.inj hIndexOption
              have hStopOption : frame.locals[14]? =
                  some (.i64 (UInt64.ofNat input.size)) := by
                simpa [Wasm.Locals.get, hParams, hLocals] using hStopLocal
              have hStopElem : frame.locals[14] =
                  .i64 (UInt64.ofNat input.size) := by
                rw [List.getElem?_eq_getElem (by omega)] at hStopOption
                exact Option.some.inj hStopOption
              have hAccumulatorOption : frame.locals[0]? = some (.i64
                  (ArrayFold.foldPrefix input
                    (fun sum element => sum + element) 0 index)) := by
                simpa [Wasm.Locals.get, hParams, hLocals] using hAccumulator
              have hAccumulatorElem : frame.locals[0] = .i64
                  (ArrayFold.foldPrefix input
                    (fun sum element => sum + element) 0 index) := by
                rw [List.getElem?_eq_getElem (by omega)] at hAccumulatorOption
                exact Option.some.inj hAccumulatorOption
              by_cases hDone : index = input.size
              · subst index
                change wp module
                  (AnnotationMatches.function_0_array_fold_0_continuing_program ++ _)
                  _ _ frame env
                apply sumExitProgram_spec
                · exact hValues
                · exact hIndexLocal
                · exact hStopLocal
                · have hFrameEq : ({ frame with values := [] } : Locals) =
                      frame := by
                    cases frame
                    simp_all
                  simp only [List.take_zero, List.drop_zero, List.nil_append,
                    hValues, hFrameEq]
                  rw [ArrayFold.foldPrefix_size] at hAccumulator
                  change wp module
                    (AnnotationMatches.function_0_array_fold_0_result_program ++ _)
                    _ _ { frame with values := [] } env
                  rw [hFrameEq]
                  apply FixedArrayFold.resultProgram_spec
                    (value := input.foldl
                      (fun sum element => sum + element) 0)
                  · exact hValues
                  · exact hAccumulator
                  · simpa [hParams]
                  · simpa [Wasm.Locals.validIndex, hParams, hLocals]
                  · change wp module
                      (FixedArrayResult.payloadStoreProgram 7 10 0 ++ _)
                      _ _ _ env
                    apply FixedArrayResult.payloadStore_spec
                      (root := heapTop + 48)
                      (value := input.foldl
                        (fun sum element => sum + element) 0)
                    · wp_alloc_window [FixedArrayFold.resultFrame, hParams,
                        hLocals, hOutputElem]
                    · wp_alloc_window [FixedArrayFold.resultFrame, hParams,
                        hLocals]
                    · have hPayloadNat :
                          (FixedArrayResult.payloadAddress
                              (heapTop + 48) 0).toUInt32.toNat =
                            heapTop.toNat + 56 := by
                        simpa [FixedArrayResult.payloadAddress] using
                          hFacts.wordAddress_toNat 1 (by decide)
                      change
                        (FixedArrayResult.payloadAddress
                            (heapTop + 48) 0).toUInt32.toNat + 8 ≤
                          (FixedArrayResult.writeLength
                            (FixedArrayAllocator.allocStore initial heapTop
                              16 1 allocs) (heapTop + 48) 1).mem.pages * 65536
                      rw [hPayloadNat, FixedArrayResult.writeLength_pages,
                        FixedArrayAllocator.allocStore_pages]
                      simpa [FormalSpec.expected, hSize] using
                        hOutputFitMemory
                    · have hResult : UInt64Array.At
                          (FixedArrayResult.singletonStore
                            (FixedArrayAllocator.allocStore initial heapTop
                              16 1 allocs)
                            (heapTop + 48)
                            (input.foldl
                              (fun sum element => sum + element) 0))
                          (heapTop + 48)
                          #[input.foldl
                            (fun sum element => sum + element) 0] := by
                        apply FixedArrayResult.singletonStore_at
                        · rw [hFacts.rootToNat]
                          have hBound := hOutputFit32
                          simp [FormalSpec.expected, hSize] at hBound
                          omega
                        · rw [FixedArrayAllocator.allocStore_pages]
                          rw [hFacts.rootToNat]
                          have hBound := hOutputFitMemory
                          simp [FormalSpec.expected, hSize] at hBound
                          omega
                      have hResultFormal : FormalSpec.UInt64ArrayAt
                          (FixedArrayResult.singletonStore
                            (FixedArrayAllocator.allocStore initial heapTop
                              16 1 allocs)
                            (heapTop + 48)
                            (input.foldl
                              (fun sum element => sum + element) 0))
                          (heapTop + 48)
                          #[input.foldl
                            (fun sum element => sum + element) 0] := by
                        change UInt64Array.At
                          (FixedArrayResult.singletonStore
                            (FixedArrayAllocator.allocStore initial heapTop
                              16 1 allocs)
                            (heapTop + 48)
                            (input.foldl
                              (fun sum element => sum + element) 0))
                          (heapTop + 48)
                          #[input.foldl
                            (fun sum element => sum + element) 0]
                        exact hResult
                      change wp module
                        (FixedArrayResult.finishProgram 7 4 6) _
                        (FixedArrayResult.singletonStore
                          (FixedArrayAllocator.allocStore initial heapTop
                            16 1 allocs)
                          (heapTop + 48)
                          (input.foldl
                            (fun sum element => sum + element) 0))
                        (FixedArrayFold.resultFrame frame 10
                          (input.foldl
                            (fun sum element => sum + element) 0)) env
                      wp_alloc_window [FixedArrayResult.finishProgram,
                        FixedArrayEqNode.branchPost,
                        FixedArrayFold.resultFrame, hParams, hLocals,
                        hOutputLocal, func0Def, Function.toLocals,
                        FormalSpec.expected, hSize]
                      exact ⟨heapTop + 48, hOutputElem, hResultFormal⟩
              · have hIndexLt : index < input.size := by omega
                have hIndex64 : index < UInt64.size :=
                  lt_trans hIndexLt hArrayStored.size_lt
                have hContinue : UInt64.ofNat index <
                    UInt64.ofNat input.size := by
                  rw [UInt64.lt_iff_toNat_lt,
                    UInt64.toNat_ofNat_of_lt' hIndex64,
                    UInt64.toNat_ofNat_of_lt' hArrayStored.size_lt]
                  exact hIndexLt
                have hItem : frame.validIndex 2 := by
                  simpa [Wasm.Locals.validIndex, hParams, hLocals]
                change wp module
                  (AnnotationMatches.function_0_array_fold_0_continuing_program ++ _)
                  _ _ frame env
                apply FixedArrayTraversalInput.continuingProgram_spec
                  (inputPtr := inputPtr) (indexValue := UInt64.ofNat index)
                  (stopValue := UInt64.ofNat input.size) (input := input)
                  (index := index) (hValues := hValues)
                  (hArrayLocal := hArrayLocal) (hIndexLocal := hIndexLocal)
                  (hStopLocal := hStopLocal) (hIndexValue := rfl)
                  (hContinue := hContinue) (hItem := hItem)
                  (hInput := hArrayStored) (hIndex := hIndexLt)
                have hIndexSucc : UInt64.ofNat index + 1 =
                    UInt64.ofNat (index + 1) := by
                  change UInt64.ofNat index + UInt64.ofNat 1 = _
                  rw [← UInt64.ofNat_add]
                have hIndexSucc64 : index + 1 < UInt64.size := by
                  exact lt_of_le_of_lt (by omega) hArrayStored.size_lt
                have hFoldSucc :
                    ArrayFold.foldPrefix input
                        (fun sum element => sum + element) 0 (index + 1) =
                      ArrayFold.foldPrefix input
                          (fun sum element => sum + element) 0 index +
                        input[index] := by
                  simpa using ArrayFold.foldPrefix_succ input
                    (fun sum element => sum + element) 0 index hIndexLt
                change wp module sumContinueProgram _ _ _ env
                apply sumContinueProgram_spec
                  (inputPtr := inputPtr)
                  (sum := ArrayFold.foldPrefix input
                    (fun sum element => sum + element) 0 index)
                  (item := input[index])
                  (index := UInt64.ofNat index)
                · wp_alloc_window [
                    FixedArrayTraversalInput.dynamicResultFrame, hParams,
                    hLocals]
                · wp_alloc_window [
                    FixedArrayTraversalInput.dynamicResultFrame, hParams,
                    hLocals]
                · wp_alloc_window [
                    FixedArrayTraversalInput.dynamicResultFrame, hParams,
                    hLocals, hValues]
                · wp_alloc_window [
                    FixedArrayTraversalInput.dynamicResultFrame, hParams,
                    hLocals, hAccumulatorElem]
                · wp_alloc_window [
                    FixedArrayTraversalInput.dynamicResultFrame, hParams,
                    hLocals]
                · wp_alloc_window [
                    FixedArrayTraversalInput.dynamicResultFrame, hParams,
                    hLocals, hIndexElem]
                · refine ⟨?_, ?_⟩
                  simp only [List.take_zero, List.drop_zero, List.nil_append,
                    hValues]
                  · unfold sumInvariant
                    refine ⟨rfl, index + 1, by omega, ?_⟩
                    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                    · wp_alloc_window [sumContinueFrame,
                        FixedArrayTraversalInput.dynamicResultFrame, hParams,
                        hLocals]
                    · wp_alloc_window [sumContinueFrame,
                        FixedArrayTraversalInput.dynamicResultFrame, hParams,
                        hLocals]
                    · rfl
                    · wp_alloc_window [sumContinueFrame,
                        FixedArrayTraversalInput.dynamicResultFrame, hParams,
                        hLocals, hOutputElem]
                    · wp_alloc_window [sumContinueFrame,
                        FixedArrayTraversalInput.dynamicResultFrame, hParams,
                        hLocals, hArrayElem]
                    · have hNextIndex := sumContinueFrame_get_index
                        (FixedArrayTraversalInput.dynamicResultFrame frame 2
                          input[index] hItem)
                        (ArrayFold.foldPrefix input
                          (fun sum element => sum + element) 0 index)
                        input[index] (UInt64.ofNat index)
                        (by simpa [FixedArrayTraversalInput.dynamicResultFrame,
                          hParams])
                        (by wp_alloc_window [
                          FixedArrayTraversalInput.dynamicResultFrame,
                          hParams, hLocals])
                      rw [hIndexSucc] at hNextIndex
                      exact hNextIndex
                    · wp_alloc_window [sumContinueFrame,
                        FixedArrayTraversalInput.dynamicResultFrame, hParams,
                        hLocals, hStopElem]
                    · have hNextAccumulator :=
                        sumContinueFrame_get_accumulator
                          (FixedArrayTraversalInput.dynamicResultFrame frame 2
                            input[index] hItem)
                          (ArrayFold.foldPrefix input
                            (fun sum element => sum + element) 0 index)
                          input[index] (UInt64.ofNat index)
                          (by simpa [
                            FixedArrayTraversalInput.dynamicResultFrame,
                            hParams])
                          (by wp_alloc_window [
                            FixedArrayTraversalInput.dynamicResultFrame,
                            hParams, hLocals])
                      simpa [hFoldSucc] using hNextAccumulator
                  · simp only [List.take_zero, List.drop_zero,
                      List.nil_append, hValues]
                    have hMeasureIndex := sumContinueFrame_get_index
                      (FixedArrayTraversalInput.dynamicResultFrame frame 2
                        input[index] hItem)
                      (ArrayFold.foldPrefix input
                        (fun sum element => sum + element) 0 index)
                      input[index] (UInt64.ofNat index)
                      (by simpa [FixedArrayTraversalInput.dynamicResultFrame,
                        hParams])
                      (by wp_alloc_window [
                        FixedArrayTraversalInput.dynamicResultFrame,
                        hParams, hLocals])
                    rw [hIndexSucc] at hMeasureIndex
                    change sumMeasure input
                        (sumContinueFrame
                          (FixedArrayTraversalInput.dynamicResultFrame frame 2
                            input[index] hItem)
                          (ArrayFold.foldPrefix input
                            (fun sum element => sum + element) 0 index)
                          input[index] (UInt64.ofNat index)) <
                      sumMeasure input frame
                    unfold sumMeasure
                    rw [hMeasureIndex, hIndexLocal]
                    change input.size - (UInt64.ofNat (index + 1)).toNat <
                      input.size - (UInt64.ofNat index).toNat
                    rw [
                      UInt64.toNat_ofNat_of_lt' hIndexSucc64,
                      UInt64.toNat_ofNat_of_lt' hIndex64]
                    omega
  · intro hSize
    change wp module
      (AnnotationMatches.function_0_length_dispatch_0_invalid_capacity_program ++ _)
      _ initial _ env
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals]
    · norm_num [Wasm.Locals.validIndex,
        FixedArrayLengthDispatch.branchFrame, func0Def, Function.toLocals]
    · have hAllocFit : heapTop.toNat + 48 + (8 : UInt64).toNat ≤
          initial.mem.pages * 65536 := by
        simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
      have hFacts := Allocation.bumpFacts heapTop 8 initial.mem.pages
        hAllocFit hPages
      change wp module
        (FixedArrayAllocatorWindow.region 2 1 ++ _) _ initial _ env
      apply FixedArrayAllocatorWindow.region_spec_withTail
        (offset := 2) (tail := 4) (heapTop := heapTop) (capacity := 8)
        (stride := 1) (allocs := allocs)
      · rfl
      · norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def, Function.toLocals]
      · rfl
      · wp_alloc_window [FixedArrayCapacity.capacityFrame,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity,
          FixedArrayLengthDispatch.branchFrame, func0Def, Function.toLocals]
        rfl
      · decide
      · exact hAllocFit
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · change wp module
          (FixedArrayResult.lengthStoreProgram 7 0 ++ _) _ _ _ env
        apply FixedArrayResult.lengthStore_spec (root := heapTop + 48)
        · rfl
        · wp_alloc_window [FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayCapacity.normalizedCapacity,
            FixedArrayCapacity.unnormalizedCapacity,
            FixedArrayLengthDispatch.branchFrame, func0Def, Function.toLocals]
          rfl
        · have hRootNat : (heapTop + 48).toUInt32.toNat =
              heapTop.toNat + 48 := by
            simpa using hFacts.wordAddress_toNat 0 (by decide)
          rw [hRootNat, FixedArrayAllocator.allocStore_pages]
          norm_num at hAllocFit
          omega
        · have hRootNat : (heapTop + 48).toUInt32.toNat =
              heapTop.toNat + 48 := by
            simpa using hFacts.wordAddress_toNat 0 (by decide)
          have hResult : UInt64Array.At
              (FixedArrayResult.writeLength
                (FixedArrayAllocator.allocStore initial heapTop 8 1 allocs)
                (heapTop + 48) 0) (heapTop + 48) #[] := by
            apply FixedArrayResult.emptyStore_at
            · rw [hFacts.rootToNat]
              exact hFacts.fit32
            · rw [hFacts.rootToNat, FixedArrayAllocator.allocStore_pages]
              norm_num at hAllocFit
              omega
          wp_alloc_window [FixedArrayEqNode.branchPost,
            FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayCapacity.normalizedCapacity,
            FixedArrayCapacity.unnormalizedCapacity,
            FixedArrayLengthDispatch.branchFrame, func0Def, Function.toLocals,
            FormalSpec.expected, hSize, hResult]
          have hResultFormal : FormalSpec.UInt64ArrayAt
              (FixedArrayResult.writeLength
                (FixedArrayAllocator.allocStore initial heapTop 8 1 allocs)
                (heapTop + 48) 0) (heapTop + 48) #[] := by
            change UInt64Array.At
              (FixedArrayResult.writeLength
                (FixedArrayAllocator.allocStore initial heapTop 8 1 allocs)
                (heapTop + 48) 0) (heapTop + 48) #[]
            exact hResult
          simpa using hResultFormal

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior
