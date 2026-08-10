import LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec
import LeanExeGen.GeneratedR23fa7efc3fb0298b.Program
import LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.Control
import Project.ProofKit.FixedArrayCapacity
import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArrayFold
import Project.ProofKit.FixedArrayFoldBody
import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArrayPairResult
import Project.ProofKit.FixedArrayResult
import Project.ProofKit.FixedArrayTraversalInput
import Project.ProofKit.Frame
import Project.ProofKit.ScalarTransition

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior

open Wasm Project.ProofKit

def sumPrefix (input : Array UInt64) (index : Nat) : UInt64 :=
  ArrayFold.foldPrefix input (fun sum element => sum + element) 0 index

def foldFrame (inputPtr root : UInt64) (input : Array UInt64) (index : Nat)
    (item temporary scratch staged releaseReady : UInt64) : Wasm.Locals :=
  AnnotationMatches.function_0_array_fold_0_continuing_frame
    inputPtr (sumPrefix input index) item temporary 0 0 0 root 0 0 0
    inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
    (UInt64.ofNat input.size) (UInt64.ofNat input.size) scratch staged
    releaseReady 0 0

def foldInv (foldStore : Wasm.Store Unit) (inputPtr root : UInt64)
    (input : Array UInt64) : Wasm.Store Unit → Wasm.Locals → Prop :=
  fun st frame => ∃ index item temporary scratch staged releaseReady,
    index ≤ input.size ∧ st = foldStore ∧
      frame = foldFrame inputPtr root input index item temporary scratch staged
        releaseReady

def foldMeasure (input : Array UInt64) :
    Wasm.Store Unit → Wasm.Locals → Nat :=
  fun _ frame => match frame.get 13 with
    | some (.i64 index) => input.size - index.toNat
    | _ => input.size + 1

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
    have hExpected : FormalSpec.expected input =
        #[input.foldl (fun sum element => sum + element) 0] := by
      simp [FormalSpec.expected, hSize]
    have hCapacity1 : FixedArrayCapacity.normalizedCapacity 1 1 = 16 := by
      native_decide
    have hFitMemory :
        heapTop.toNat + 48 + 16 ≤
          initial.mem.pages * 65536 := by
      simp [FormalSpec.heapReserveBytes, hSize] at hHeapFitMemory
      omega
    have hFacts := Allocation.bumpFacts heapTop 16 initial.mem.pages
      hFitMemory hPages
    have hRootNat :
        (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
      simpa using hFacts.wordAddress_toNat 0 (by native_decide)
    change Wasm.wp _
      (FixedArrayCapacity.constantProgram 1 1 11 ++ _) _ _ _ _
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · norm_num [Wasm.Locals.validIndex,
        FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · change Wasm.wp _
        (FixedArrayAllocatorWindow.region 2 1 ++ _) _ _ _ _
      apply FixedArrayAllocatorWindow.region_spec_withTail
        (offset := 2) (tail := 4) (heapTop := heapTop)
        (capacity := 16) (stride := 1) (allocs := allocs)
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
          hCapacity1]
      · native_decide
      · exact hFitMemory
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · have hInputAlloc := FixedArrayPairResult.input_preserved_by_alloc
          initial heapTop 16 1 allocs inputPtr input hArray hInputBelow
          hFitMemory hPages
        have hInputLength : UInt64Array.At
            (FixedArrayResult.writeLength
              (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
              (heapTop + 48) 1) inputPtr input := by
          apply hInputAlloc.write64After
          rw [hRootNat]
          omega
        change Wasm.wp _
          (FixedArrayResult.lengthStoreProgram 7 1 ++ _) _ _ _ _
        apply FixedArrayResult.lengthStore_spec
          (root := heapTop + 48) (length := 1) (rootLocal := 7)
        · rfl
        · norm_num [FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Function.toLocals, Function.numParams, ValueType.zero,
            hCapacity1, Wasm.Locals.get]
        · rw [hRootNat, FixedArrayAllocator.allocStore_pages]
          omega
        · change Wasm.wp _
            (AnnotationMatches.function_0_array_fold_0_setup_program ++ _)
            _ _ _ _
          apply FixedArrayFold.forwardSetupProgram_spec
            (inputPtr := inputPtr) (input := input)
          · norm_num [FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Function.toLocals, Function.numParams, ValueType.zero,
              hCapacity1]
          · rfl
          · intro slot hSlot
            simp [FixedArrayFold.setupLocals] at hSlot
            rcases hSlot with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            all_goals norm_num [FixedArrayAllocatorWindow.allocFrame,
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
            · refine ⟨0, 0, 0, inputPtr, 0, 0, by omega, rfl, ?_⟩
              simp [foldFrame, sumPrefix, ArrayFold.foldPrefix,
                FixedArrayFold.forwardSetupFrame,
                FixedArrayAllocatorWindow.allocFrame,
                FixedArrayCapacity.capacityFrame,
                FixedArrayLengthDispatch.branchFrame, func0Def,
                Function.toLocals, Function.numParams, ValueType.zero,
                hCapacity1,
                AnnotationMatches.function_0_array_fold_0_continuing_frame,
                AnnotationMatches.function_0_array_fold_0_state,
                ScalarTransition.U64State.toState]
            · rintro st frame
                ⟨index, item, temporary, scratch, staged, releaseReady,
                  hIndex, rfl, rfl⟩
              by_cases hDone : index = input.size
              · subst index
                apply FixedArrayTraversalInput.continuingProgram_exit_spec
                  (arrayLocal := 11) (indexLocal := 13)
                  (stopLocal := 15) (itemLocal := 2)
                  (index := UInt64.ofNat input.size)
                · rfl
                · simp [foldFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame,
                    AnnotationMatches.function_0_array_fold_0_state,
                    ScalarTransition.U64State.toState, Wasm.Locals.get]
                · simp [foldFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame,
                    AnnotationMatches.function_0_array_fold_0_state,
                    ScalarTransition.U64State.toState, Wasm.Locals.get]
                · simp only [List.take_zero, List.drop_zero, List.nil_append]
                  change Wasm.wp _
                    AnnotationMatches.function_0_array_fold_0_singleton_result_program
                    _ _ (foldFrame inputPtr (heapTop + 48) input input.size
                      item temporary scratch staged releaseReady) _
                  apply Wasm.wp.conseq
                    (Q := FixedArrayFold.singletonResultPost 6
                      (heapTop + 48) (sumPrefix input input.size))
                  · intro continuation hResult
                    cases continuation <;>
                      simp only [FixedArrayFold.singletonResultPost] at hResult
                    rename_i final resultFrame
                    rcases hResult with ⟨hReturn, hOutput⟩
                    simp only [FixedArrayEqNode.branchPost]
                    unfold AnnotationMatches.function_0_length_dispatch_0_suffix_program
                    wp_run
                    change match resultFrame.get 6 with
                      | some value => _
                      | none => False
                    rw [hReturn]
                    refine ⟨heapTop + 48, ?_, ?_⟩
                    · norm_num [func0Def, Function.numParams]
                    · rw [hExpected]
                      change UInt64Array.At final (heapTop + 48)
                        #[input.foldl (fun sum element => sum + element) 0]
                      simpa [sumPrefix, ArrayFold.foldPrefix_size] using hOutput
                  · apply FixedArrayFold.singletonResultProgram_spec
                      (root := heapTop + 48)
                      (value := sumPrefix input input.size)
                      (hValues := by
                        simp only [foldFrame,
                          AnnotationMatches.function_0_array_fold_0_continuing_frame_values])
                      (hAccumulator := by
                        simp only [foldFrame,
                          AnnotationMatches.function_0_array_fold_0_continuing_frame_get_1])
                      (hRoot := by
                        apply FixedArrayFold.resultFrame_get_of_ne
                        · simp only [foldFrame,
                            AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
                          norm_num
                        · simp only [foldFrame,
                            AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
                          norm_num
                        · simp only [Wasm.Locals.validIndex, foldFrame,
                            AnnotationMatches.function_0_array_fold_0_continuing_frame_params,
                            AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
                          norm_num
                        · norm_num
                        · simp only [foldFrame,
                            AnnotationMatches.function_0_array_fold_0_continuing_frame_get_7])
                      (hResult := by
                        apply FixedArrayFold.resultFrame_get_result
                        · simp only [foldFrame,
                            AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
                          norm_num
                        · simp only [Wasm.Locals.validIndex, foldFrame,
                            AnnotationMatches.function_0_array_fold_0_continuing_frame_params,
                            AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
                          norm_num)
                    · simp only [foldFrame,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
                      norm_num
                    · simp only [Wasm.Locals.validIndex, foldFrame,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame_params,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
                      norm_num
                    · have hPayloadNat :
                          (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat =
                            heapTop.toNat + 56 := by
                        simpa [FixedArrayResult.payloadAddress] using
                          hFacts.wordAddress_toNat 1 (by native_decide)
                      rw [hPayloadNat, FixedArrayResult.writeLength_pages,
                        FixedArrayAllocator.allocStore_pages]
                      omega
                    · simp only [FixedArrayFold.resultFrame_params, foldFrame,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
                      norm_num
                    · simp only [Wasm.Locals.validIndex,
                        FixedArrayFold.resultFrame_params,
                        FixedArrayFold.resultFrame_locals_length, foldFrame,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame_params,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
                      norm_num
                    · simp only [FixedArrayFold.resultFrame_params, foldFrame,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
                      norm_num
                    · simp only [Wasm.Locals.validIndex,
                        FixedArrayFold.resultFrame_params,
                        FixedArrayFold.resultFrame_locals_length, foldFrame,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame_params,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
                      norm_num
                    · apply FixedArrayResult.singletonStore_at
                      · rw [hFacts.rootToNat]
                        omega
                      · rw [hFacts.rootToNat,
                          FixedArrayAllocator.allocStore_pages]
                        exact hFitMemory
              · have hContinue : index < input.size := by omega
                have hEight64 : 8 < UInt64.size := by native_decide
                have hIndex64 : index < UInt64.size := by
                  omega
                have hIndexSucc64 : index + 1 < UInt64.size := by omega
                have hContinueGuard :
                    UInt64.ofNat index < UInt64.ofNat input.size := by
                  rw [UInt64.lt_iff_toNat_lt,
                    UInt64.toNat_ofNat_of_lt' hIndex64,
                    UInt64.toNat_ofNat_of_lt' hInputLength.size_lt]
                  exact hContinue
                have hIndexSucc :
                    UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by
                  apply UInt64.toNat.inj
                  rw [UInt64.toNat_add,
                    UInt64.toNat_ofNat_of_lt' hIndex64,
                    UInt64.toNat_ofNat_of_lt' hIndexSucc64]
                  rw [Nat.mod_eq_of_lt (by simpa using hIndexSucc64)]
                  rfl
                have hPrefixSucc :
                    sumPrefix input (index + 1) =
                      sumPrefix input index + input[index] := by
                  simpa [sumPrefix] using ArrayFold.foldPrefix_succ input
                    (fun sum element : UInt64 => sum + element) 0 index
                    hContinue
                let loadedState :=
                  (AnnotationMatches.function_0_array_fold_0_state
                    inputPtr (sumPrefix input index) input[index] temporary
                    0 0 0 (heapTop + 48) 0 0 0 inputPtr
                    (UInt64.ofNat input.size) (UInt64.ofNat index)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    scratch staged releaseReady 0 0).toState
                let bodyState :=
                  (AnnotationMatches.function_0_array_fold_0_state
                    inputPtr (sumPrefix input (index + 1)) input[index]
                    (sumPrefix input (index + 1)) 0 0 0 (heapTop + 48)
                    0 0 0 inputPtr (UInt64.ofNat input.size)
                    (UInt64.ofNat index) (UInt64.ofNat input.size)
                    (UInt64.ofNat input.size) 0
                    (sumPrefix input (index + 1)) 1 0 0).toState
                let nextState :=
                  (AnnotationMatches.function_0_array_fold_0_state
                    inputPtr (sumPrefix input (index + 1)) input[index]
                    (sumPrefix input (index + 1)) 0 0 0 (heapTop + 48)
                    0 0 0 inputPtr (UInt64.ofNat input.size)
                    (UInt64.ofNat (index + 1)) (UInt64.ofNat input.size)
                    (UInt64.ofNat input.size) 0
                    (sumPrefix input (index + 1)) 1 0 0).toState
                refine FixedArrayFoldBody.continuingGuardedProgram_spec
                  (arrayLocal := 11) (indexLocal := 13)
                  (stopLocal := 15) (itemLocal := 2) (scratch := 11)
                  (body := AnnotationMatches.function_0_array_fold_0_body)
                  (condition :=
                    AnnotationMatches.function_0_array_fold_0_condition)
                  (continuing :=
                    AnnotationMatches.function_0_array_fold_0_step_continuing)
                  (module_ := LeanExeGen.GeneratedR23fa7efc3fb0298b.«module»)
                  (env := env)
                  (st := FixedArrayResult.writeLength
                    (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                    (heapTop + 48) 1)
                  (frame := foldFrame inputPtr (heapTop + 48) input index
                    item temporary scratch staged releaseReady)
                  (inputPtr := inputPtr) (indexValue := UInt64.ofNat index)
                  (stopValue := UInt64.ofNat input.size) (input := input)
                  (index := index)
                  (stepProgram :=
                    AnnotationMatches.function_0_array_fold_0_step_program)
                  (initial := loadedState) (afterBody := bodyState)
                  (afterCondition := bodyState) (result := false)
                  (hValues := by
                    simp only [foldFrame,
                      AnnotationMatches.function_0_array_fold_0_continuing_frame_values])
                  (hArrayLocal := by
                    simp only [foldFrame,
                      AnnotationMatches.function_0_array_fold_0_continuing_frame_get_11])
                  (hIndexLocal := by
                    simp only [foldFrame,
                      AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13])
                  (hStopLocal := by
                    simp only [foldFrame,
                      AnnotationMatches.function_0_array_fold_0_continuing_frame_get_15])
                  (hIndexValue := rfl) (hContinueGuard := hContinueGuard)
                  (hItem :=
                    AnnotationMatches.function_0_array_fold_0_continuing_item_valid
                      inputPtr (sumPrefix input index) item temporary 0 0 0
                      (heapTop + 48) 0 0 0 inputPtr
                      (UInt64.ofNat input.size) (UInt64.ofNat index)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      scratch staged releaseReady 0 0)
                  (hInput := hInputLength) (hIndex := hContinue)
                  (hLoaded := by
                    unfold foldFrame loadedState
                    rw [AnnotationMatches.function_0_array_fold_0_continuing_loaded_frame_eq]
                    rfl)
                  (hStepProgram := rfl)
                  (hBody := by
                    simpa [loadedState, bodyState, hPrefixSucc,
                      AnnotationMatches.function_0_array_fold_0_bodyTransition,
                      ScalarTransition.U64Op.apply] using
                      AnnotationMatches.function_0_array_fold_0_body_eval
                        inputPtr (sumPrefix input index) input[index]
                        temporary 0 0 0 (heapTop + 48) 0 0 0 inputPtr
                        (UInt64.ofNat input.size) (UInt64.ofNat index)
                        (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                        scratch staged releaseReady 0 0)
                  (hCondition := by
                    simpa [bodyState,
                      AnnotationMatches.function_0_array_fold_0_conditionTransition]
                      using
                        AnnotationMatches.function_0_array_fold_0_condition_eval
                          inputPtr (sumPrefix input (index + 1)) input[index]
                          (sumPrefix input (index + 1)) 0 0 0 (heapTop + 48)
                          0 0 0 inputPtr (UInt64.ofNat input.size)
                          (UInt64.ofNat index) (UInt64.ofNat input.size)
                          (UInt64.ofNat input.size) 0
                          (sumPrefix input (index + 1)) 1 0 0)
                  (hExit := by simp) (hContinue := ?_)
                intro _
                refine ⟨nextState, ?_, ?_⟩
                · unfold bodyState nextState
                  rw [AnnotationMatches.function_0_array_fold_0_step_continuing_eval
                      inputPtr (sumPrefix input (index + 1)) input[index]
                      (sumPrefix input (index + 1)) 0 0 0 (heapTop + 48)
                      0 0 0 inputPtr (UInt64.ofNat input.size)
                      (UInt64.ofNat index) (UInt64.ofNat input.size)
                      (UInt64.ofNat input.size) 0
                      (sumPrefix input (index + 1)) 1 0 0]
                  simp only [
                    AnnotationMatches.function_0_array_fold_0_step_continuingTransition,
                    Option.map_some, ScalarTransition.U64Op.apply, hIndexSucc]
                · have hNextFrame : nextState.toLocals [] =
                      foldFrame inputPtr (heapTop + 48) input (index + 1)
                        input[index] (sumPrefix input (index + 1)) 0
                        (sumPrefix input (index + 1)) 1 := by
                    rfl
                  simp only [List.take_zero, List.drop_zero, List.nil_append]
                  rw [hNextFrame]
                  constructor
                  · exact ⟨index + 1, input[index],
                      sumPrefix input (index + 1), 0,
                      sumPrefix input (index + 1), 1, by omega, rfl, rfl⟩
                  · change input.size - (UInt64.ofNat (index + 1)).toNat <
                      input.size - (UInt64.ofNat index).toNat
                    rw [UInt64.toNat_ofNat_of_lt' hIndexSucc64,
                      UInt64.toNat_ofNat_of_lt' hIndex64]
                    omega
  · intro hSize
    have hExpected : FormalSpec.expected input = #[] := by
      simp [FormalSpec.expected, hSize]
    have hCapacity0 : FixedArrayCapacity.normalizedCapacity 0 1 = 8 := by
      native_decide
    have hFitMemory :
        heapTop.toNat + 48 + 8 ≤
          initial.mem.pages * 65536 := by
      simp [FormalSpec.heapReserveBytes, hSize] at hHeapFitMemory
      omega
    have hFacts := Allocation.bumpFacts heapTop 8 initial.mem.pages
      hFitMemory hPages
    change Wasm.wp _
      (FixedArrayCapacity.constantProgram 0 1 11 ++ _) _ _ _ _
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · norm_num [Wasm.Locals.validIndex,
        FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · change Wasm.wp _
        (FixedArrayAllocatorWindow.region 2 1 ++ _) _ _ _ _
      apply FixedArrayAllocatorWindow.region_spec_withTail
        (offset := 2) (tail := 4) (heapTop := heapTop)
        (capacity := 8) (stride := 1) (allocs := allocs)
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
          hCapacity0]
      · rfl
      · exact hFitMemory
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · change Wasm.wp _
          (FixedArrayResult.lengthStoreProgram 7 0 ++ _) _ _ _ _
        apply FixedArrayResult.lengthStore_spec
          (root := heapTop + 48) (length := 0) (rootLocal := 7)
        · rfl
        · norm_num [FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Function.toLocals, Function.numParams, ValueType.zero,
            hCapacity0, Wasm.Locals.get]
        · have hRootNat :
              (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
            simpa using hFacts.wordAddress_toNat 0 (by rfl)
          rw [hRootNat, FixedArrayAllocator.allocStore_pages]
          omega
        · change Wasm.wp _
            (FixedArrayResult.finishProgram 7 5 6 ++ []) _ _ _ _
          apply FixedArrayResult.finishProgram_spec
            (root := heapTop + 48) (rootLocal := 7)
            (destinationLocal := 5) (returnLocal := 6)
          · rfl
          · norm_num [FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Function.toLocals, Function.numParams, ValueType.zero,
              hCapacity0, Wasm.Locals.get]
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
            · rw [hExpected]
              apply FixedArrayResult.emptyStore_at
              · rw [hFacts.rootToNat]
                omega
              · rw [hFacts.rootToNat,
                  FixedArrayAllocator.allocStore_pages]
                exact hFitMemory

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior
