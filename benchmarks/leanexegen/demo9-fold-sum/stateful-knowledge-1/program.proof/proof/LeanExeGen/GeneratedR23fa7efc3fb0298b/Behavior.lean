import LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec
import LeanExeGen.GeneratedR23fa7efc3fb0298b.Program
import LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.Control
import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayCapacity
import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArrayFold
import Project.ProofKit.FixedArrayFoldBody
import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArrayTraversalInput
import Project.ProofKit.Frame
import Project.ProofKit.ScalarTransition

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior

open Wasm Project.ProofKit

private def sumStep (sum element : UInt64) : UInt64 := sum + element

private def sumFrame (inputPtr root : UInt64) (input : Array UInt64)
    (index : Nat) (item temporary done staged releaseReady : UInt64) : Locals :=
  AnnotationMatches.function_0_array_fold_0_continuing_frame
    inputPtr (ArrayFold.foldPrefix input sumStep 0 index)
    item temporary 0 0 0 root 0 0 0 inputPtr (UInt64.ofNat input.size)
    (UInt64.ofNat index) (UInt64.ofNat input.size) (UInt64.ofNat input.size)
    done staged releaseReady 0 0

private def sumInvariant (loopStore : Store Unit) (inputPtr root : UInt64)
    (input : Array UInt64) : AssertionF Unit :=
  fun st frame => ∃ index item temporary staged releaseReady,
    ∃ done, index ≤ input.size ∧ st = loopStore ∧
      frame = sumFrame inputPtr root input index item temporary done staged
        releaseReady

private def sumMeasure (input : Array UInt64) (_st : Store Unit)
    (frame : Locals) : Nat :=
  match frame.get 13 with
  | some (.i64 index) => input.size - index.toNat
  | _ => 0

@[simp] private theorem sumFrame_values (inputPtr root : UInt64)
    (input : Array UInt64) (index : Nat)
    (item temporary done staged releaseReady : UInt64) :
    (sumFrame inputPtr root input index item temporary done staged
      releaseReady).values = [] := by
  simp only [sumFrame,
    AnnotationMatches.function_0_array_fold_0_continuing_frame_values]

@[simp] private theorem sumFrame_get_index (inputPtr root : UInt64)
    (input : Array UInt64) (index : Nat)
    (item temporary done staged releaseReady : UInt64) :
    (sumFrame inputPtr root input index item temporary done staged
      releaseReady).get 13 = some (.i64 (UInt64.ofNat index)) := by
  simp only [sumFrame,
    AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13]

private def sumLoadedState (inputPtr root stop index accumulator element
    temporary done staged releaseReady : UInt64) :
    ScalarTransition.U64State :=
  AnnotationMatches.function_0_array_fold_0_state
    inputPtr accumulator element temporary 0 0 0 root 0 0 0 inputPtr stop
    index stop stop done staged releaseReady 0 0

private def sumAdvancedState (inputPtr root stop index next element : UInt64) :
    ScalarTransition.U64State :=
  AnnotationMatches.function_0_array_fold_0_state
    inputPtr next element next 0 0 0 root 0 0 0 inputPtr stop index stop stop
    0 next 1 0 0

private def sumContinuedState (inputPtr root stop index next element : UInt64) :
    ScalarTransition.U64State :=
  AnnotationMatches.function_0_array_fold_0_state
    inputPtr next element next 0 0 0 root 0 0 0 inputPtr stop (index + 1)
    stop stop 0 next 1 0 0

set_option maxHeartbeats 8000000 in
private theorem sumFrame_initial (inputPtr heapTop : UInt64)
    (input : Array UInt64) :
    FixedArrayFold.forwardSetupFrame
      (FixedArrayAllocatorWindow.allocFrame 2
        (FixedArrayCapacity.capacityFrame
          (FixedArrayLengthDispatch.branchFrame 7
            (LeanExeGen.GeneratedR23fa7efc3fb0298b.func0Def.toLocals
              (List.take
                LeanExeGen.GeneratedR23fa7efc3fb0298b.func0Def.numParams
                [.i64 inputPtr]).reverse)
            inputPtr)
          11 (FixedArrayCapacity.normalizedCapacity 1 1))
        heapTop (FixedArrayCapacity.normalizedCapacity 1 1))
      inputPtr input.size 11 12 13 16 14 1 18 15 0 =
        sumFrame inputPtr (heapTop + 48) input 0 0 0 inputPtr 0 0 := by
  simp [FixedArrayFold.forwardSetupFrame,
    FixedArrayAllocatorWindow.allocFrame,
    FixedArrayCapacity.capacityFrame,
    FixedArrayLengthDispatch.branchFrame,
    LeanExeGen.GeneratedR23fa7efc3fb0298b.func0Def,
    Wasm.Function.toLocals, Wasm.Function.numParams, ValueType.zero,
    sumFrame, ArrayFold.foldPrefix,
    AnnotationMatches.function_0_array_fold_0_continuing_frame,
    AnnotationMatches.function_0_array_fold_0_state,
    ScalarTransition.U64State.toState]

set_option maxHeartbeats 8000000 in
private theorem sumFrame_step (module_ : Wasm.Module) (env : HostEnv Unit)
    (store : Store Unit) (inputPtr root : UInt64) (input : Array UInt64)
    (index : Nat) (item temporary done staged releaseReady : UInt64)
    (hInput : UInt64Array.At store inputPtr input)
    (hIndex : index < input.size) (Q : Assertion Unit)
    (hNext : Q (.Break 0 store
      (sumFrame inputPtr root input (index + 1) input[index]
        (ArrayFold.foldPrefix input sumStep 0 (index + 1)) 0
        (ArrayFold.foldPrefix input sumStep 0 (index + 1)) 1))) :
    wp module_
      (AnnotationMatches.function_0_array_fold_0_continuing_program ++
        AnnotationMatches.function_0_array_fold_0_step_program)
      Q store
        (sumFrame inputPtr root input index item temporary done staged
          releaseReady) env := by
  let accumulator := ArrayFold.foldPrefix input sumStep 0 index
  let element := input[index]
  let next := sumStep accumulator element
  let stop := UInt64.ofNat input.size
  let encodedIndex := UInt64.ofNat index
  have hIndex64 : index < UInt64.size := by
    have hSize := hInput.size_lt
    omega
  have hIndexNat : encodedIndex.toNat = index := by
    exact UInt64.toNat_ofNat_of_lt' hIndex64
  have hContinue : encodedIndex < stop := by
    rw [UInt64.lt_iff_toNat_lt, hIndexNat]
    dsimp only [stop]
    rw [UInt64.toNat_ofNat_of_lt' hInput.size_lt]
    exact hIndex
  have hIndexSucc : encodedIndex + 1 = UInt64.ofNat (index + 1) := by
    have hSucc64 : index + 1 < UInt64.size := by
      have hSize := hInput.size_lt
      omega
    apply UInt64.toNat.inj
    rw [UInt64.toNat_add, hIndexNat,
      UInt64.toNat_ofNat_of_lt' hSucc64]
    have hOne : (1 : UInt64).toNat = 1 := rfl
    rw [hOne, Nat.mod_eq_of_lt hSucc64]
  have hPrefixSucc :=
    ArrayFold.foldPrefix_succ input sumStep 0 index hIndex
  have hItemValid :
      (sumFrame inputPtr root input index item temporary done staged
        releaseReady).validIndex 2 := by
    simpa [sumFrame, accumulator, stop, encodedIndex] using
      AnnotationMatches.function_0_array_fold_0_continuing_item_valid
        inputPtr accumulator item temporary 0 0 0 root 0 0 0 inputPtr stop
        encodedIndex stop stop done staged releaseReady 0 0
  have hLoaded :
      FixedArrayTraversalInput.dynamicResultFrame
          (sumFrame inputPtr root input index item temporary done staged
            releaseReady) 2 input[index] hItemValid =
        (sumLoadedState inputPtr root stop encodedIndex accumulator element
          temporary done staged releaseReady).toState.toLocals [] := by
    change FixedArrayTraversalInput.dynamicResultFrame
        (AnnotationMatches.function_0_array_fold_0_continuing_frame
          inputPtr accumulator item temporary 0 0 0 root 0 0 0 inputPtr stop
          encodedIndex stop stop done staged releaseReady 0 0)
        2 element hItemValid =
      AnnotationMatches.function_0_array_fold_0_continuing_frame
        inputPtr accumulator element temporary 0 0 0 root 0 0 0 inputPtr stop
        encodedIndex stop stop done staged releaseReady 0 0
    simpa using
      AnnotationMatches.function_0_array_fold_0_continuing_loaded_frame_eq
        inputPtr accumulator item temporary 0 0 0 root 0 0 0 inputPtr stop
        encodedIndex stop stop done staged releaseReady 0 0 element
  apply FixedArrayFoldBody.continuingGuardedProgram_spec
    (arrayLocal := 11) (indexLocal := 13) (stopLocal := 15)
    (itemLocal := 2) (scratch := 11)
    (body := AnnotationMatches.function_0_array_fold_0_body)
    (condition := AnnotationMatches.function_0_array_fold_0_condition)
    (continuing := AnnotationMatches.function_0_array_fold_0_step_continuing)
    (inputPtr := inputPtr) (indexValue := encodedIndex) (stopValue := stop)
    (input := input) (index := index)
    (stepProgram := AnnotationMatches.function_0_array_fold_0_step_program)
    (initial := (sumLoadedState inputPtr root stop encodedIndex accumulator
      element temporary done staged releaseReady).toState)
    (afterBody := (sumAdvancedState inputPtr root stop encodedIndex next
      element).toState)
    (afterCondition := (sumAdvancedState inputPtr root stop encodedIndex next
      element).toState)
    (result := false)
    (hValues := by simp only [sumFrame,
      AnnotationMatches.function_0_array_fold_0_continuing_frame_values])
    (hArrayLocal := by simp only [sumFrame,
      AnnotationMatches.function_0_array_fold_0_continuing_frame_get_11])
    (hIndexLocal := by simp only [sumFrame,
      AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13,
      encodedIndex])
    (hStopLocal := by simp only [sumFrame,
      AnnotationMatches.function_0_array_fold_0_continuing_frame_get_15,
      stop])
    (hIndexValue := rfl) (hContinueGuard := hContinue)
    (hItem := hItemValid) (hInput := hInput) (hIndex := hIndex)
    (hLoaded := hLoaded) (hStepProgram := rfl)
  · simpa [sumLoadedState, sumAdvancedState,
      AnnotationMatches.function_0_array_fold_0_bodyTransition, next,
      sumStep, ScalarTransition.U64Op.apply] using
      AnnotationMatches.function_0_array_fold_0_body_eval
        inputPtr accumulator element temporary 0 0 0 root 0 0 0 inputPtr
        stop encodedIndex stop stop done staged releaseReady 0 0
  · simpa [sumAdvancedState,
      AnnotationMatches.function_0_array_fold_0_conditionTransition] using
      AnnotationMatches.function_0_array_fold_0_condition_eval
        inputPtr next element next 0 0 0 root 0 0 0 inputPtr stop
        encodedIndex stop stop 0 next 1 0 0
  · intro hFalse
    contradiction
  · intro _
    refine ⟨(sumContinuedState inputPtr root stop encodedIndex next
      element).toState, ?_, ?_⟩
    · simpa [sumAdvancedState, sumContinuedState,
        AnnotationMatches.function_0_array_fold_0_step_continuingTransition,
        ScalarTransition.U64Op.apply]
        using AnnotationMatches.function_0_array_fold_0_step_continuing_eval
          inputPtr next element next 0 0 0 root 0 0 0 inputPtr stop
          encodedIndex stop stop 0 next 1 0 0
    · have hNextSum :
          next = ArrayFold.foldPrefix input sumStep 0 (index + 1) := by
        simpa only [next, accumulator, element] using hPrefixSucc.symm
      have hContinuedFrame :
          (sumContinuedState inputPtr root stop encodedIndex next
            element).toState.toLocals [] =
          sumFrame inputPtr root input (index + 1) input[index]
            (ArrayFold.foldPrefix input sumStep 0 (index + 1)) 0
            (ArrayFold.foldPrefix input sumStep 0 (index + 1)) 1 := by
        change AnnotationMatches.function_0_array_fold_0_continuing_frame
            inputPtr next element next 0 0 0 root 0 0 0 inputPtr stop
              (encodedIndex + 1) stop stop 0 next 1 0 0 =
          AnnotationMatches.function_0_array_fold_0_continuing_frame
            inputPtr (ArrayFold.foldPrefix input sumStep 0 (index + 1))
              input[index] (ArrayFold.foldPrefix input sumStep 0 (index + 1))
              0 0 0 root 0 0 0 inputPtr (UInt64.ofNat input.size)
              (UInt64.ofNat (index + 1)) (UInt64.ofNat input.size)
              (UInt64.ofNat input.size) 0
              (ArrayFold.foldPrefix input sumStep 0 (index + 1)) 1 0 0
        rw [hIndexSucc, hNextSum]
      rw [hContinuedFrame]
      exact hNext

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
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedR23fa7efc3fb0298b.func0Def) rfl
  wp_fixed_array_length_le_dispatch_from hArray at 7, 8
  all_goals try rfl
  all_goals try decide
  · norm_num [LeanExeGen.GeneratedR23fa7efc3fb0298b.func0Def,
      Wasm.Function.toLocals, Wasm.Function.numParams, ValueType.zero]
  · intro hSize
    change wp _
      (FixedArrayCapacity.constantProgram 1 1 11 ++
        (FixedArrayAllocatorWindow.region 2 1 ++ _)) _ _ _ _
    apply FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail
      (length := 1) (stride := 1) (offset := 2) (tail := 4)
      (heapTop := heapTop) (allocs := allocs)
    · rfl
    · rfl
    · rfl
    · simpa [FormalSpec.heapReserveBytes, hSize,
        FixedArrayCapacity.normalizedCapacity,
        FixedArrayCapacity.unnormalizedCapacity] using hHeapFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · let startFrame : Locals :=
        LeanExeGen.GeneratedR23fa7efc3fb0298b.func0Def.toLocals
          (List.take LeanExeGen.GeneratedR23fa7efc3fb0298b.func0Def.numParams
            [.i64 inputPtr]).reverse
      let baseFrame : Locals :=
        FixedArrayCapacity.capacityFrame
          (FixedArrayLengthDispatch.branchFrame 7 startFrame inputPtr) 11
          (FixedArrayCapacity.normalizedCapacity 1 1)
      let outputFrame : Locals :=
        FixedArrayAllocatorWindow.allocFrame 2 baseFrame heapTop
          (FixedArrayCapacity.normalizedCapacity 1 1)
      let outputStore : Store Unit :=
        FixedArrayAllocator.allocStore initial heapTop
          (FixedArrayCapacity.normalizedCapacity 1 1) 1 allocs
      let foldStore : Store Unit :=
        FixedArrayResult.writeLength outputStore (heapTop + 48) 1
      change wp _
        (FixedArrayResult.lengthStoreProgram 7 1 ++ _) _ outputStore
          outputFrame _
      have hCapacityMemory :
          heapTop.toNat + 48 +
              (FixedArrayCapacity.normalizedCapacity 1 1).toNat ≤
            initial.mem.pages * 65536 := by
        simpa [FormalSpec.heapReserveBytes, hSize,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity] using hHeapFitMemory
      have hBump := Allocation.bumpFacts heapTop
        (FixedArrayCapacity.normalizedCapacity 1 1) initial.mem.pages
        hCapacityMemory hPages
      have hRootAddress :
          (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
        simpa using hBump.wordAddress_toNat 0
          (FixedArrayCapacity.normalizedCapacity_toNat_ge_eight 1 1)
      have hBaseParams : baseFrame.params.length = 1 := by
        norm_num [baseFrame, startFrame,
          FixedArrayCapacity.capacityFrame_params,
          FixedArrayLengthDispatch.branchFrame_params,
          LeanExeGen.GeneratedR23fa7efc3fb0298b.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams, ValueType.zero]
      have hBaseLocals : baseFrame.locals.length = 20 := by
        norm_num [baseFrame, startFrame,
          FixedArrayCapacity.capacityFrame_locals_length,
          FixedArrayLengthDispatch.branchFrame_locals_length,
          LeanExeGen.GeneratedR23fa7efc3fb0298b.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams, ValueType.zero]
      have hOutputParams : outputFrame.params.length = 1 := by
        simpa [outputFrame, FixedArrayAllocatorWindow.allocFrame_params]
          using hBaseParams
      have hOutputParamsValue : outputFrame.params = [.i64 inputPtr] := by
        norm_num [outputFrame, baseFrame, startFrame,
          FixedArrayAllocatorWindow.allocFrame_params,
          FixedArrayCapacity.capacityFrame_params,
          FixedArrayLengthDispatch.branchFrame_params,
          LeanExeGen.GeneratedR23fa7efc3fb0298b.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams, ValueType.zero]
      have hOutputLocals : outputFrame.locals.length = 20 := by
        simpa [outputFrame,
          FixedArrayAllocatorWindow.allocFrame_locals_length] using hBaseLocals
      have hOutputValues : outputFrame.values = [] := by
        simp [outputFrame, baseFrame,
          FixedArrayAllocatorWindow.allocFrame_values,
          FixedArrayCapacity.capacityFrame_values]
      have hRoot : outputFrame.get 7 = some (.i64 (heapTop + 48)) := by
        exact FixedArrayAllocatorWindow.allocFrame_get_root 2 4 baseFrame
          heapTop (FixedArrayCapacity.normalizedCapacity 1 1)
          hBaseParams hBaseLocals
      have hLengthStoreBound :
          (heapTop + 48).toUInt32.toNat + 8 ≤
            outputStore.mem.pages * 65536 := by
        dsimp only [outputStore]
        rw [hRootAddress, FixedArrayAllocator.allocStore_pages]
        omega
      have hInputAllocated : UInt64Array.At outputStore inputPtr input := by
        exact FixedArrayPairResult.input_preserved_by_alloc initial heapTop
          (FixedArrayCapacity.normalizedCapacity 1 1) 1 allocs inputPtr input
          hArray hInputBelow hCapacityMemory hPages
      have hInputFold : UInt64Array.At foldStore inputPtr input := by
        dsimp only [foldStore]
        apply hInputAllocated.write64After
        rw [hRootAddress]
        omega
      have hCapacityValue :
          FixedArrayCapacity.normalizedCapacity 1 1 = 16 := by
        native_decide
      have hCapacityMemory16 :
          heapTop.toNat + 64 ≤ initial.mem.pages * 65536 := by
        simpa [hCapacityValue] using hCapacityMemory
      have hOutputPages : outputStore.mem.pages = initial.mem.pages := by
        dsimp only [outputStore]
        exact FixedArrayAllocator.allocStore_pages initial heapTop
          (FixedArrayCapacity.normalizedCapacity 1 1) 1 allocs
      have hFoldPages : foldStore.mem.pages = initial.mem.pages := by
        dsimp only [foldStore]
        rw [FixedArrayResult.writeLength_pages, hOutputPages]
      have hPayloadAddress :
          (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat =
            heapTop.toNat + 56 := by
        simpa [FixedArrayResult.payloadAddress] using
          hBump.wordAddress_toNat 1 (by
            rw [hCapacityValue]
            decide)
      have hPayloadBound :
          (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat +
              8 ≤ foldStore.mem.pages * 65536 := by
        rw [hPayloadAddress]
        rw [hFoldPages]
        exact hCapacityMemory16
      have hSingletonFit32 :
          (heapTop + 48).toNat + 16 ≤ 4294967296 := by
        rw [hBump.rootToNat]
        simpa [hCapacityValue] using hBump.fit32
      have hSingletonFitMemory :
          (heapTop + 48).toNat + 16 ≤ outputStore.mem.pages * 65536 := by
        rw [hBump.rootToNat, hOutputPages]
        exact hCapacityMemory16
      have hSingleton (value : UInt64) : UInt64Array.At
          (FixedArrayResult.writePayload foldStore (heapTop + 48) 0 value)
          (heapTop + 48) #[value] := by
        simpa [foldStore, FixedArrayResult.singletonStore] using
          (FixedArrayResult.singletonStore_at outputStore (heapTop + 48)
            value hSingletonFit32 hSingletonFitMemory)
      apply FixedArrayResult.lengthStore_spec (root := heapTop + 48)
      · exact hOutputValues
      · exact hRoot
      · exact hLengthStoreBound
      · change wp _
          (FixedArrayFold.forwardSetupProgram 11 12 13 16 14 1 18 15 0 ++ _)
            _ foldStore outputFrame _
        apply FixedArrayFold.forwardSetupProgram_spec
          (inputPtr := inputPtr) (input := input)
        · exact hOutputParamsValue
        · exact hOutputValues
        · intro slot hSlot
          simp [FixedArrayFold.setupLocals] at hSlot
          omega
        · decide
        · exact hInputFold
        · wp_block_loop
            invariant (sumInvariant foldStore inputPtr (heapTop + 48) input)
            decreasing (sumMeasure input)
          · refine ⟨0, 0, 0, 0, 0, inputPtr, Nat.zero_le _, rfl, ?_⟩
            exact sumFrame_initial inputPtr heapTop input
          · intro st frame hInvariant
            rcases hInvariant with
              ⟨index, item, temporary, staged, releaseReady, done,
                hIndex, hStore, hFrame⟩
            subst st
            subst frame
            change wp _
              (AnnotationMatches.function_0_array_fold_0_continuing_program ++
                AnnotationMatches.function_0_array_fold_0_step_program) _ _ _ _
            by_cases hDone : index = input.size
            · subst index
              apply FixedArrayTraversalInput.continuingProgram_exit_spec
                (index := UInt64.ofNat input.size)
              · simp only [sumFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_values]
              · simp only [sumFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13]
              · simp only [sumFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_get_15]
              · change wp _
                  AnnotationMatches.function_0_array_fold_0_singleton_result_program
                  _ foldStore
                    (sumFrame inputPtr (heapTop + 48) input input.size item
                      temporary done staged releaseReady) _
                apply
                  AnnotationMatches.function_0_array_fold_0_singleton_result_spec
                · exact hPayloadBound
                · have hReturn :
                      (FixedArrayResult.finishFrame
                        (FixedArrayFold.resultFrame
                          (sumFrame inputPtr (heapTop + 48) input input.size
                            item temporary done staged releaseReady)
                          10 (ArrayFold.foldPrefix input sumStep 0 input.size))
                        4 6 (heapTop + 48)).get 6 =
                          some (.i64 (heapTop + 48)) := by
                    apply FixedArrayResult.finishFrame_return_get
                    · simp only [FixedArrayFold.resultFrame_params, sumFrame,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
                      norm_num
                    · simp [Wasm.Locals.validIndex,
                        FixedArrayFold.resultFrame_params,
                        FixedArrayFold.resultFrame_locals_length, sumFrame,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame_params,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
                  simp only [FixedArrayEqNode.branchPost]
                  simp only [wp_localGet_cons, Frame.withValues_get, hReturn,
                    Wasm.wp_nil]
                  refine ⟨heapTop + 48, rfl, ?_⟩
                  change UInt64Array.At
                    (FixedArrayResult.writePayload foldStore (heapTop + 48) 0
                      (ArrayFold.foldPrefix input sumStep 0 input.size))
                    (heapTop + 48) (FormalSpec.expected input)
                  rw [FormalSpec.expected, if_pos hSize]
                  change UInt64Array.At
                    (FixedArrayResult.writePayload foldStore (heapTop + 48) 0
                      (ArrayFold.foldPrefix input sumStep 0 input.size))
                    (heapTop + 48) #[input.foldl sumStep 0]
                  simpa only [ArrayFold.foldPrefix_size] using
                    hSingleton (ArrayFold.foldPrefix input sumStep 0 input.size)
            · have hIndexLt : index < input.size := by omega
              apply sumFrame_step
                (module_ := LeanExeGen.GeneratedR23fa7efc3fb0298b.«module»)
                (env := env) (store := foldStore) (inputPtr := inputPtr)
                (root := heapTop + 48) (input := input) (index := index)
                (item := item) (temporary := temporary) (done := done)
                (staged := staged) (releaseReady := releaseReady)
                hInputFold hIndexLt
              simp only [List.take_zero, List.drop_zero, sumFrame_values,
                List.nil_append]
              constructor
              · refine ⟨index + 1, input[index],
                  ArrayFold.foldPrefix input sumStep 0 (index + 1),
                  ArrayFold.foldPrefix input sumStep 0 (index + 1),
                  1, 0, ?_, rfl, rfl⟩
                omega
              · have hCurrentNat :
                    (UInt64.ofNat index).toNat = index := by
                  apply UInt64.toNat_ofNat_of_lt'
                  have hSize := hInputFold.size_lt
                  omega
                have hNextNat :
                    (UInt64.ofNat (index + 1)).toNat = index + 1 := by
                  apply UInt64.toNat_ofNat_of_lt'
                  have hSize := hInputFold.size_lt
                  omega
                simp only [sumMeasure, Frame.withValues_get,
                  sumFrame_get_index]
                rw [hCurrentNat, hNextNat]
                omega
  · intro hSize
    change wp _
      (FixedArrayCapacity.constantProgram 0 1 11 ++
        (FixedArrayAllocatorWindow.region 2 1 ++ _)) _ _ _ _
    apply FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail
      (length := 0) (stride := 1) (offset := 2) (tail := 4)
      (heapTop := heapTop) (allocs := allocs)
    · rfl
    · rfl
    · rfl
    · simpa [FormalSpec.heapReserveBytes, hSize,
        FixedArrayCapacity.normalizedCapacity,
        FixedArrayCapacity.unnormalizedCapacity] using hHeapFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · let startFrame : Locals :=
        LeanExeGen.GeneratedR23fa7efc3fb0298b.func0Def.toLocals
          (List.take LeanExeGen.GeneratedR23fa7efc3fb0298b.func0Def.numParams
            [.i64 inputPtr]).reverse
      let baseFrame : Locals :=
        FixedArrayCapacity.capacityFrame
          (FixedArrayLengthDispatch.branchFrame 7 startFrame inputPtr) 11
          (FixedArrayCapacity.normalizedCapacity 0 1)
      let outputFrame : Locals :=
        FixedArrayAllocatorWindow.allocFrame 2 baseFrame heapTop
          (FixedArrayCapacity.normalizedCapacity 0 1)
      let outputStore : Store Unit :=
        FixedArrayAllocator.allocStore initial heapTop
          (FixedArrayCapacity.normalizedCapacity 0 1) 1 allocs
      change wp _
        (FixedArrayResult.lengthStoreProgram 7 0 ++
          FixedArrayResult.finishProgram 7 5 6) _ outputStore outputFrame _
      have hCapacityMemory :
          heapTop.toNat + 48 +
              (FixedArrayCapacity.normalizedCapacity 0 1).toNat ≤
            initial.mem.pages * 65536 := by
        simpa [FormalSpec.heapReserveBytes, hSize,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity] using hHeapFitMemory
      have hBump := Allocation.bumpFacts heapTop
        (FixedArrayCapacity.normalizedCapacity 0 1) initial.mem.pages
        hCapacityMemory hPages
      have hRootAddress :
          (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
        simpa using hBump.wordAddress_toNat 0
          (FixedArrayCapacity.normalizedCapacity_toNat_ge_eight 0 1)
      have hBaseParams : baseFrame.params.length = 1 := by
        norm_num [baseFrame, startFrame,
          FixedArrayCapacity.capacityFrame_params,
          FixedArrayLengthDispatch.branchFrame_params,
          LeanExeGen.GeneratedR23fa7efc3fb0298b.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams, ValueType.zero]
      have hBaseLocals : baseFrame.locals.length = 20 := by
        norm_num [baseFrame, startFrame,
          FixedArrayCapacity.capacityFrame_locals_length,
          FixedArrayLengthDispatch.branchFrame_locals_length,
          LeanExeGen.GeneratedR23fa7efc3fb0298b.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams, ValueType.zero]
      have hOutputParams : outputFrame.params.length = 1 := by
        simpa [outputFrame, FixedArrayAllocatorWindow.allocFrame_params]
          using hBaseParams
      have hOutputLocals : outputFrame.locals.length = 20 := by
        simpa [outputFrame,
          FixedArrayAllocatorWindow.allocFrame_locals_length] using hBaseLocals
      have hOutputValues : outputFrame.values = [] := by
        simp [outputFrame, baseFrame,
          FixedArrayAllocatorWindow.allocFrame_values,
          FixedArrayCapacity.capacityFrame_values]
      have hRoot : outputFrame.get 7 = some (.i64 (heapTop + 48)) := by
        exact FixedArrayAllocatorWindow.allocFrame_get_root 2 4 baseFrame
          heapTop (FixedArrayCapacity.normalizedCapacity 0 1)
          hBaseParams hBaseLocals
      have hLengthStoreBound :
          (heapTop + 48).toUInt32.toNat + 8 ≤
            outputStore.mem.pages * 65536 := by
        dsimp only [outputStore]
        rw [hRootAddress, FixedArrayAllocator.allocStore_pages]
        simpa [FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity] using hCapacityMemory
      have hEmptyFit32 :
          (heapTop + 48).toNat + 8 ≤ 4294967296 := by
        rw [hBump.rootToNat]
        simpa [FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity] using hBump.fit32
      have hEmptyFitMemory :
          (heapTop + 48).toNat + 8 ≤
            outputStore.mem.pages * 65536 := by
        rw [hBump.rootToNat]
        simpa [outputStore, FixedArrayAllocator.allocStore_pages,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity] using hCapacityMemory
      have hEmpty : UInt64Array.At
          (FixedArrayResult.writeLength outputStore (heapTop + 48) 0)
          (heapTop + 48) #[] :=
        FixedArrayResult.emptyStore_at outputStore (heapTop + 48)
          hEmptyFit32 hEmptyFitMemory
      apply FixedArrayResult.lengthStore_spec (root := heapTop + 48)
      · exact hOutputValues
      · exact hRoot
      · exact hLengthStoreBound
      · apply FixedArrayResult.finishProgram_spec (root := heapTop + 48)
        · exact hOutputValues
        · exact hRoot
        · omega
        · simp [Wasm.Locals.validIndex, hOutputParams, hOutputLocals]
        · omega
        · simp [Wasm.Locals.validIndex, hOutputParams, hOutputLocals]
        · have hReturn :
              (FixedArrayResult.finishFrame outputFrame 5 6
                (heapTop + 48)).get 6 = some (.i64 (heapTop + 48)) := by
            apply FixedArrayResult.finishFrame_return_get
            · omega
            · simp [Wasm.Locals.validIndex, hOutputParams, hOutputLocals]
          simp only [Wasm.wp_nil, FixedArrayEqNode.branchPost]
          simp only [wp_localGet_cons, Frame.withValues_get, hReturn,
            Wasm.wp_nil]
          refine ⟨heapTop + 48, ?_, ?_⟩
          · rfl
          · change UInt64Array.At
              (FixedArrayResult.writeLength outputStore (heapTop + 48) 0)
              (heapTop + 48) (FormalSpec.expected input)
            rw [FormalSpec.expected, if_neg hSize]
            exact hEmpty

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior
