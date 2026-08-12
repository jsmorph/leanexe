import LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec
import LeanExeGen.GeneratedR23fa7efc3fb0298b.Program
import LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.Control
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

def foldFrame (inputPtr root : UInt64) (input : Array UInt64)
    (index : Nat) (item temp done staged releaseReady : UInt64) : Wasm.Locals :=
  AnnotationMatches.function_0_array_fold_0_continuing_frame
    inputPtr
    (ArrayFold.foldPrefix input (fun sum element => sum + element) 0 index)
    item temp 0 0 0 root 0 0 0 inputPtr (UInt64.ofNat input.size)
    (UInt64.ofNat index) (UInt64.ofNat input.size) (UInt64.ofNat input.size)
    done staged releaseReady 0 0

def foldInv (foldStore : Wasm.Store Unit) (inputPtr root : UInt64)
    (input : Array UInt64) (st : Wasm.Store Unit) (frame : Wasm.Locals) : Prop :=
  st = foldStore ∧
    ∃ index item temp done staged releaseReady, index ≤ input.size ∧
      frame = foldFrame inputPtr root input index item temp done staged releaseReady

def foldIndex (frame : Wasm.Locals) : Nat :=
  match frame.get 13 with
  | some (.i64 value) => value.toNat
  | _ => 0

def foldMeasure (input : Array UInt64) (_st : Wasm.Store Unit)
    (frame : Wasm.Locals) : Nat :=
  input.size - foldIndex frame

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
  change Wasm.wp _ func0 _ _ _ _
  rw [AnnotationMatches.function_0_length_dispatch_0_function_eq]
  wp_fixed_array_length_le_dispatch_from hArray at 7, 8
  · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  · norm_num
  · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  · norm_num [UInt64.size]
  · intro hSize
    have hAllocFit :
        heapTop.toNat + 48 + 16 ≤ initial.mem.pages * 65536 := by
      simpa [FormalSpec.expected, hSize] using hOutputFitMemory
    have hFacts := Allocation.bumpFacts heapTop 16 initial.mem.pages
      hAllocFit hPages
    change Wasm.wp _
      (FixedArrayCapacity.constantProgram 1 1 11 ++
        FixedArrayAllocatorWindow.region 2 1 ++ _) _ _ _ _
    apply FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail
        (length := 1) (stride := 1) (offset := 2) (tail := 4)
        (heapTop := heapTop) (allocs := allocs)
    · norm_num [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · norm_num [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · rfl
    · simpa [FixedArrayCapacity.normalizedCapacity,
        FixedArrayCapacity.unnormalizedCapacity] using hAllocFit
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · change Wasm.wp _ (FixedArrayResult.lengthStoreProgram 7 1 ++ _) _ _ _ _
      have hInputAlloc := FixedArrayPairResult.input_preserved_by_alloc
        initial heapTop 16 1 allocs inputPtr input hArray hInputBelow
          hAllocFit hPages
      have hRootAddress :
          (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
        simpa using hFacts.wordAddress_toNat 0 (by native_decide)
      have hInputLength : UInt64Array.At
          (FixedArrayResult.writeLength
            (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
            (heapTop + 48) 1) inputPtr input := by
        apply hInputAlloc.write64After
        rw [hRootAddress]
        omega
      apply FixedArrayResult.lengthStore_spec
        (root := heapTop + 48) (length := 1) (rootLocal := 7)
      · rfl
      · norm_num [FixedArrayAllocatorWindow.allocFrame,
          FixedArrayCapacity.capacityFrame,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero,
          Wasm.Locals.get]
      · rw [hRootAddress, FixedArrayAllocator.allocStore_pages]
        omega
      · change Wasm.wp _
          (AnnotationMatches.function_0_array_fold_0_setup_program ++ _)
          _ _ _ _
        apply FixedArrayFold.forwardSetupProgram_spec
          (inputPtr := inputPtr) (input := input)
        · norm_num [FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Function.toLocals, Function.numParams, ValueType.zero]
        · rfl
        · norm_num [FixedArrayFold.setupLocals,
            FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Function.toLocals, Function.numParams, ValueType.zero]
        · native_decide
        · exact hInputLength
        · change Wasm.wp _
            ([.block 0 0 [.loop 0 0
              (AnnotationMatches.function_0_array_fold_0_continuing_program ++
                AnnotationMatches.function_0_array_fold_0_step_program)]] ++
              AnnotationMatches.function_0_array_fold_0_singleton_result_program)
            _ _ _ _
          apply Wasm.wp_block_cons
          apply Wasm.wp_loop_cons
            (Inv := foldInv
              (FixedArrayResult.writeLength
                (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                (heapTop + 48) 1)
              inputPtr (heapTop + 48) input)
            (μ := foldMeasure input)
          · refine ⟨rfl, 0, 0, 0, inputPtr, 0, 0, by omega, ?_⟩
            simp [foldFrame, ArrayFold.foldPrefix,
              FixedArrayFold.forwardSetupFrame,
              FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayCapacity.normalizedCapacity,
              FixedArrayCapacity.unnormalizedCapacity,
              FixedArrayLengthDispatch.branchFrame,
              AnnotationMatches.function_0_array_fold_0_continuing_frame,
              AnnotationMatches.function_0_array_fold_0_state,
              ScalarTransition.U64State.toState, func0Def,
              Function.toLocals, Function.numParams, ValueType.zero]
          · rintro st frame
              ⟨rfl, index, item, temp, done, staged, releaseReady, hIndex, rfl⟩
            by_cases hDone : index = input.size
            · subst index
              apply FixedArrayTraversalInput.continuingProgram_exit_spec
                (index := UInt64.ofNat input.size)
              · simp only [foldFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_values]
              · simp only [foldFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13]
              · simp only [foldFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_get_15]
              · simp only [List.take_zero, List.drop_zero, List.nil_append,
                  Wasm.wp_nil]
                change Wasm.wp module
                  AnnotationMatches.function_0_array_fold_0_singleton_result_program
                  _
                  (FixedArrayResult.writeLength
                    (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                    (heapTop + 48) 1)
                  (foldFrame inputPtr (heapTop + 48) input input.size
                    item temp done staged releaseReady) env
                simp only [foldFrame]
                apply AnnotationMatches.function_0_array_fold_0_singleton_result_spec
                · have hPayloadAddress :
                      (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat =
                        heapTop.toNat + 56 := by
                    simpa [FixedArrayResult.payloadAddress] using
                      hFacts.wordAddress_toNat 1 (by native_decide)
                  rw [hPayloadAddress, FixedArrayResult.writeLength_pages,
                    FixedArrayAllocator.allocStore_pages]
                  omega
                · have hRootFit32 :
                      (heapTop + 48).toNat + 16 ≤ 4294967296 := by
                    rw [hFacts.rootToNat]
                    simpa [FormalSpec.expected, hSize] using hOutputFit32
                  have hRootFitMemory :
                      (heapTop + 48).toNat + 16 ≤
                        (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs).mem.pages *
                          65536 := by
                    rw [hFacts.rootToNat,
                      FixedArrayAllocator.allocStore_pages]
                    exact hAllocFit
                  have hSingleton := FixedArrayResult.singletonStore_at
                    (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                    (heapTop + 48)
                    (ArrayFold.foldPrefix input
                      (fun sum element => sum + element) 0 input.size)
                    hRootFit32 hRootFitMemory
                  simp only [FixedArrayEqNode.branchPost]
                  unfold AnnotationMatches.function_0_length_dispatch_0_suffix_program
                  wp_run
                  refine ⟨heapTop + 48, ?_, ?_⟩
                  · norm_num [func0Def, Function.numParams]
                  · simpa [FixedArrayResult.singletonStore,
                      FormalSpec.UInt64ArrayAt, UInt64Array.At,
                      FormalSpec.expected, hSize,
                      ArrayFold.foldPrefix_size] using hSingleton
            · have hIndexLt : index < input.size := by omega
              have hIndexEncoded :
                  UInt64.ofNat index < UInt64.ofNat input.size := by
                rw [UInt64.lt_iff_toNat_lt,
                  UInt64.toNat_ofNat_of_lt' (by
                    have hInputSize := hInputLength.size_lt
                    omega),
                  UInt64.toNat_ofNat_of_lt' hInputLength.size_lt]
                exact hIndexLt
              let sum := ArrayFold.foldPrefix input
                (fun sum element => sum + element) 0 index
              let element := input[index]
              let next := sum + element
              let loadedState :=
                AnnotationMatches.function_0_array_fold_0_state
                  inputPtr sum element temp 0 0 0 (heapTop + 48) 0 0 0
                  inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                  (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                  done staged releaseReady 0 0
              let steppedState :=
                AnnotationMatches.function_0_array_fold_0_state
                  inputPtr next element next 0 0 0 (heapTop + 48) 0 0 0
                  inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                  (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                  0 next 1 0 0
              let nextState :=
                AnnotationMatches.function_0_array_fold_0_state
                  inputPtr next element next 0 0 0 (heapTop + 48) 0 0 0
                  inputPtr (UInt64.ofNat input.size)
                  (UInt64.ofNat (index + 1))
                  (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                  0 next 1 0 0
              have hValues :
                  (foldFrame inputPtr (heapTop + 48) input index item temp
                    done staged releaseReady).values = [] := by
                simp only [foldFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_values]
              have hArrayLocal :
                  (foldFrame inputPtr (heapTop + 48) input index item temp
                    done staged releaseReady).get 11 = some (.i64 inputPtr) := by
                simp only [foldFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_get_11]
              have hIndexLocal :
                  (foldFrame inputPtr (heapTop + 48) input index item temp
                    done staged releaseReady).get 13 = some (.i64 (UInt64.ofNat index)) := by
                simp only [foldFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13]
              have hStopLocal :
                  (foldFrame inputPtr (heapTop + 48) input index item temp
                    done staged releaseReady).get 15 =
                      some (.i64 (UInt64.ofNat input.size)) := by
                simp only [foldFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_get_15]
              have hItem :
                  (foldFrame inputPtr (heapTop + 48) input index item temp
                    done staged releaseReady).validIndex 2 := by
                simpa only [foldFrame] using
                  (AnnotationMatches.function_0_array_fold_0_continuing_item_valid
                    inputPtr sum item temp 0 0 0 (heapTop + 48) 0 0 0
                    inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    done staged releaseReady 0 0)
              have hLoaded :
                  FixedArrayTraversalInput.dynamicResultFrame
                      (foldFrame inputPtr (heapTop + 48) input index item temp
                        done staged releaseReady)
                      2 input[index] hItem = loadedState.toState.toLocals [] := by
                simpa only [foldFrame, loadedState, sum, element,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame] using
                  (AnnotationMatches.function_0_array_fold_0_continuing_loaded_frame_eq
                    inputPtr sum item temp 0 0 0 (heapTop + 48) 0 0 0
                    inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    done staged releaseReady 0 0 input[index])
              have hBody :
                  AnnotationMatches.function_0_array_fold_0_body.eval 11
                      loadedState.toState = some steppedState.toState := by
                simpa [loadedState, steppedState, sum, element, next,
                  AnnotationMatches.function_0_array_fold_0_bodyTransition,
                  ScalarTransition.U64Op.apply] using
                  (AnnotationMatches.function_0_array_fold_0_body_eval
                    inputPtr sum element temp 0 0 0 (heapTop + 48) 0 0 0
                    inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    done staged releaseReady 0 0)
              have hCondition :
                  AnnotationMatches.function_0_array_fold_0_condition.eval 11
                      steppedState.toState = some (false, steppedState.toState) := by
                simpa [steppedState,
                  AnnotationMatches.function_0_array_fold_0_conditionTransition] using
                  (AnnotationMatches.function_0_array_fold_0_condition_eval
                    inputPtr next element next 0 0 0 (heapTop + 48) 0 0 0
                    inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    0 next 1 0 0)
              apply FixedArrayFoldBody.continuingGuardedProgram_spec
                (arrayLocal := 11) (indexLocal := 13) (stopLocal := 15)
                (itemLocal := 2) (scratch := 11)
                (body := AnnotationMatches.function_0_array_fold_0_body)
                (condition := AnnotationMatches.function_0_array_fold_0_condition)
                (continuing :=
                  AnnotationMatches.function_0_array_fold_0_step_continuing)
                (module_ := module) (env := env)
                (st := FixedArrayResult.writeLength
                  (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                  (heapTop + 48) 1)
                (frame := foldFrame inputPtr (heapTop + 48) input index
                  item temp done staged releaseReady)
                (inputPtr := inputPtr) (indexValue := UInt64.ofNat index)
                (stopValue := UInt64.ofNat input.size)
                (input := input) (index := index)
                (stepProgram :=
                  AnnotationMatches.function_0_array_fold_0_step_program)
                (initial := loadedState.toState)
                (afterBody := steppedState.toState)
                (afterCondition := steppedState.toState)
                (result := false)
                (hValues := hValues) (hArrayLocal := hArrayLocal)
                (hIndexLocal := hIndexLocal) (hStopLocal := hStopLocal)
                (hIndexValue := rfl) (hContinueGuard := hIndexEncoded)
                (hItem := hItem) (hInput := hInputLength)
                (hIndex := hIndexLt) (hLoaded := hLoaded)
                (hStepProgram := rfl) (hBody := hBody)
                (hCondition := hCondition)
              · intro hFalse
                simp at hFalse
              · intro _
                refine ⟨nextState.toState, ?_, ?_⟩
                · simpa [steppedState, nextState,
                    AnnotationMatches.function_0_array_fold_0_step_continuingTransition,
                    ScalarTransition.U64Op.apply, UInt64.ofNat_add] using
                    (AnnotationMatches.function_0_array_fold_0_step_continuing_eval
                      inputPtr next element next 0 0 0 (heapTop + 48) 0 0 0
                      inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      0 next 1 0 0)
                · simp only [List.take_zero, List.drop_zero, List.nil_append]
                  change foldInv
                      (FixedArrayResult.writeLength
                        (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                        (heapTop + 48) 1)
                      inputPtr (heapTop + 48) input
                      (FixedArrayResult.writeLength
                        (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                        (heapTop + 48) 1)
                      (nextState.toState.toLocals []) ∧
                    foldMeasure input
                        (FixedArrayResult.writeLength
                          (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                          (heapTop + 48) 1)
                        (nextState.toState.toLocals []) <
                      foldMeasure input
                        (FixedArrayResult.writeLength
                          (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                          (heapTop + 48) 1)
                        (foldFrame inputPtr (heapTop + 48) input index
                          item temp done staged releaseReady)
                  have hPrefix := ArrayFold.foldPrefix_succ input
                    (fun sum element => sum + element) 0 index hIndexLt
                  have hNextFrame :
                      nextState.toState.toLocals [] =
                        foldFrame inputPtr (heapTop + 48) input (index + 1)
                          element next 0 next 1 := by
                    simp [nextState, foldFrame, next, sum, element,
                      hPrefix,
                      AnnotationMatches.function_0_array_fold_0_continuing_frame,
                      AnnotationMatches.function_0_array_fold_0_state,
                      ScalarTransition.U64State.toState]
                  constructor
                  · refine ⟨rfl, index + 1, element, next, 0, next, 1,
                      ?_, hNextFrame⟩
                    omega
                  · rw [hNextFrame]
                    simp only [foldMeasure, foldIndex, foldFrame,
                      AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13]
                    rw [UInt64.toNat_ofNat_of_lt' (by
                      have hInputSize := hInputLength.size_lt
                      omega),
                      UInt64.toNat_ofNat_of_lt' (by
                        have hInputSize := hInputLength.size_lt
                        omega)]
                    omega
  · intro hSize
    have hAllocFit :
        heapTop.toNat + 48 + 8 ≤ initial.mem.pages * 65536 := by
      simpa [FormalSpec.expected, hSize] using hOutputFitMemory
    have hFacts := Allocation.bumpFacts heapTop 8 initial.mem.pages
      hAllocFit hPages
    change Wasm.wp _
      (FixedArrayCapacity.constantProgram 0 1 11 ++
        FixedArrayAllocatorWindow.region 2 1 ++ _) _ _ _ _
    apply FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail
        (length := 0) (stride := 1) (offset := 2) (tail := 4)
        (heapTop := heapTop) (allocs := allocs)
    · norm_num [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · norm_num [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · rfl
    · simpa [FixedArrayCapacity.normalizedCapacity,
        FixedArrayCapacity.unnormalizedCapacity] using hAllocFit
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · change Wasm.wp _
        (FixedArrayResult.lengthStoreProgram 7 0 ++
          FixedArrayResult.finishProgram 7 5 6) _ _ _ _
      apply FixedArrayResult.lengthStore_spec
        (root := heapTop + 48) (length := 0) (rootLocal := 7)
      · rfl
      · norm_num [FixedArrayAllocatorWindow.allocFrame,
          FixedArrayCapacity.capacityFrame,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero,
          Wasm.Locals.get]
      · have hRootAddress :
            (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
          simpa using hFacts.wordAddress_toNat 0 (by native_decide)
        rw [hRootAddress, FixedArrayAllocator.allocStore_pages]
        exact hAllocFit
      · have hRootFit32 :
            (heapTop + 48).toNat + 8 ≤ 4294967296 := by
          rw [hFacts.rootToNat]
          simpa [FormalSpec.expected, hSize] using hOutputFit32
        have hRootFitMemory :
            (heapTop + 48).toNat + 8 ≤
              (FixedArrayAllocator.allocStore initial heapTop 8 1 allocs).mem.pages *
                65536 := by
          rw [hFacts.rootToNat, FixedArrayAllocator.allocStore_pages]
          exact hAllocFit
        have hEmpty := FixedArrayResult.emptyStore_at
          (FixedArrayAllocator.allocStore initial heapTop 8 1 allocs)
          (heapTop + 48) hRootFit32 hRootFitMemory
        apply FixedArrayResult.finishProgram_spec (root := heapTop + 48)
        · rfl
        · norm_num [FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayCapacity.normalizedCapacity,
            FixedArrayCapacity.unnormalizedCapacity,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Function.toLocals, Function.numParams, ValueType.zero,
            Wasm.Locals.get]
        · norm_num [FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Function.toLocals, Function.numParams, ValueType.zero]
        · norm_num [Wasm.Locals.validIndex,
            FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Function.toLocals, Function.numParams, ValueType.zero]
        · norm_num [FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Function.toLocals, Function.numParams, ValueType.zero]
        · norm_num [Wasm.Locals.validIndex,
            FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Function.toLocals, Function.numParams, ValueType.zero]
        · simp only [Wasm.wp_nil, FixedArrayEqNode.branchPost]
          unfold AnnotationMatches.function_0_length_dispatch_0_suffix_program
          wp_run
          refine ⟨heapTop + 48, ?_, ?_⟩
          · norm_num [func0Def, Function.numParams]
          · simpa [FormalSpec.UInt64ArrayAt, UInt64Array.At,
              FixedArrayCapacity.normalizedCapacity,
              FixedArrayCapacity.unnormalizedCapacity,
              FormalSpec.expected, hSize] using hEmpty

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior
