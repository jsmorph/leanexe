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
open LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches

private def sumFrame (inputPtr root : UInt64) (input : Array UInt64)
    (index : Nat) (item staged done saved releaseReady : UInt64) : Locals :=
  function_0_array_fold_0_continuing_frame
    inputPtr (ArrayFold.foldPrefix input (fun sum element => sum + element) 0 index)
    item staged 0 0 0 root 0 0 0 inputPtr (UInt64.ofNat input.size)
    (UInt64.ofNat index) (UInt64.ofNat input.size) (UInt64.ofNat input.size)
    done saved releaseReady 0 0

private def sumInv (inputPtr root : UInt64) (input : Array UInt64)
    (resultStore : Store Unit) (st : Store Unit) (frame : Locals) : Prop :=
  ∃ index, index ≤ input.size ∧
    ∃ item staged done saved releaseReady,
      st = resultStore ∧
      frame = sumFrame inputPtr root input index item staged done saved releaseReady

private def sumMeasure (input : Array UInt64) (_st : Store Unit)
    (frame : Locals) : Nat :=
  match frame.get 13 with
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
  wp_fixed_array_length_le_dispatch_from hArray at 7, 8
  · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams]
  · norm_num [func0Def, Wasm.Function.toLocals]
  · norm_num
  · norm_num [func0Def, Wasm.Function.toLocals]
  · norm_num
  · intro hSize
    have hFitMemory : heapTop.toNat + 48 +
        (FixedArrayCapacity.normalizedCapacity 1 1).toNat ≤
          initial.mem.pages * 65536 := by
      simpa [FixedArrayCapacity.normalizedCapacity,
        FixedArrayCapacity.unnormalizedCapacity,
        FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
    have hFacts := Allocation.bumpFacts heapTop
      (FixedArrayCapacity.normalizedCapacity 1 1) initial.mem.pages
      hFitMemory hPages
    have hCapacity : FixedArrayCapacity.normalizedCapacity 1 1 = 16 := by
      native_decide
    have hCapacityNat :
        (FixedArrayCapacity.normalizedCapacity 1 1).toNat = 16 := by
      native_decide
    have hInputAllocated :=
      FixedArrayPairResult.input_preserved_by_alloc initial heapTop
        (FixedArrayCapacity.normalizedCapacity 1 1) 1 allocs inputPtr input
        hArray hInputBelow hFitMemory hPages
    have hInputWritten : UInt64Array.At
        (FixedArrayResult.writeLength
          (FixedArrayAllocator.allocStore initial heapTop
            (FixedArrayCapacity.normalizedCapacity 1 1) 1 allocs)
          (heapTop + 48) 1)
        inputPtr input := by
      change UInt64Array.At
        { FixedArrayAllocator.allocStore initial heapTop
            (FixedArrayCapacity.normalizedCapacity 1 1) 1 allocs with
          mem :=
            (FixedArrayAllocator.allocStore initial heapTop
              (FixedArrayCapacity.normalizedCapacity 1 1) 1 allocs).mem.write64
              (heapTop + 48).toUInt32 1 }
        inputPtr input
      apply hInputAllocated.write64After
      have hRootAddress : (heapTop + 48).toUInt32.toNat =
          heapTop.toNat + 48 := by
        simpa using hFacts.wordAddress_toNat 0
          (FixedArrayCapacity.normalizedCapacity_toNat_ge_eight 1 1)
      rw [hRootAddress]
      omega
    change wp module
      (FixedArrayCapacity.constantProgram 1 1 11 ++
        (FixedArrayAllocatorWindow.region 2 1 ++ _)) _ initial _ env
    apply FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail
      (length := 1) (stride := 1) (offset := 2) (tail := 4)
      (heapTop := heapTop) (allocs := allocs)
    · norm_num [FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams]
    · norm_num [FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals]
    · rfl
    · exact hFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · change wp module
        (FixedArrayResult.lengthStoreProgram 7 1 ++ _) _ _ _ _
      apply FixedArrayResult.lengthStore_spec
        (root := heapTop + 48) (length := 1) (rootLocal := 7)
      · rfl
      · apply FixedArrayAllocatorWindow.allocFrame_get_root 2 4
        · norm_num [FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams]
        · norm_num [FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams]
      · have hRootAddress : (heapTop + 48).toUInt32.toNat =
            heapTop.toNat + 48 := by
          simpa using hFacts.wordAddress_toNat 0
            (FixedArrayCapacity.normalizedCapacity_toNat_ge_eight 1 1)
        rw [hRootAddress]
        rw [FixedArrayAllocator.allocStore_pages]
        omega
      · change wp module
          (FixedArrayFold.forwardSetupProgram 11 12 13 16 14 1 18 15 0 ++ _)
          _ _ _ _
        apply FixedArrayFold.forwardSetupProgram_spec
          (inputPtr := inputPtr) (input := input)
        · simp only [FixedArrayAllocatorWindow.allocFrame_params,
            FixedArrayCapacity.capacityFrame_params,
            FixedArrayLengthDispatch.branchFrame_params]
          norm_num [func0Def, Wasm.Function.toLocals,
            Wasm.Function.numParams]
        · rfl
        · intro slot hSlot
          simp only [FixedArrayAllocatorWindow.allocFrame_locals_length,
            FixedArrayCapacity.capacityFrame_locals_length,
            FixedArrayLengthDispatch.branchFrame_locals_length]
          norm_num [func0Def, Wasm.Function.toLocals,
            Wasm.Function.numParams]
          simp [FixedArrayFold.setupLocals] at hSlot
          omega
        · norm_num [FixedArrayFold.setupLocals]
        · exact hInputWritten
        · wp_block_loop
            invariant (sumInv inputPtr (heapTop + 48) input
              (FixedArrayResult.writeLength
                (FixedArrayAllocator.allocStore initial heapTop
                  (FixedArrayCapacity.normalizedCapacity 1 1) 1 allocs)
                (heapTop + 48) 1))
            decreasing (sumMeasure input)
          · refine ⟨0, by omega, 0, 0, inputPtr, 0, 0, rfl, ?_⟩
            simp (config := { maxSteps := 1000000 }) [sumFrame,
              ArrayFold.foldPrefix, function_0_array_fold_0_continuing_frame,
              function_0_array_fold_0_state,
              ScalarTransition.U64State.toState,
              FixedArrayFold.forwardSetupFrame,
              FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams,
              Wasm.ValueType.zero]
          · intro st frame hInv
            rcases hInv with
              ⟨index, hIndex, item, staged, done, saved, releaseReady,
                rfl, rfl⟩
            by_cases hDone : index = input.size
            · subst index
              change wp module
                (function_0_array_fold_0_continuing_program ++
                  function_0_array_fold_0_step_program) _ _ _ _
              apply FixedArrayTraversalInput.continuingProgram_exit_spec
                (arrayLocal := 11) (indexLocal := 13) (stopLocal := 15)
                (itemLocal := 2) (index := UInt64.ofNat input.size)
              · simp only [sumFrame,
                  function_0_array_fold_0_continuing_frame_values]
              · simp only [sumFrame,
                  function_0_array_fold_0_continuing_frame_get_13]
              · simp only [sumFrame,
                  function_0_array_fold_0_continuing_frame_get_15]
              · simp only [sumFrame,
                  function_0_array_fold_0_continuing_frame_values,
                  FixedArrayFold.forwardSetupFrame_values, List.take_zero,
                  List.drop_zero, List.drop_nil, List.append_nil,
                  Wasm.wp_nil]
                apply function_0_array_fold_0_singleton_result_spec
                · have hPayloadAddress :
                      (FixedArrayResult.payloadAddress
                          (heapTop + 48) 0).toUInt32.toNat =
                        heapTop.toNat + 56 := by
                    simpa [FixedArrayResult.payloadAddress] using
                      hFacts.wordAddress_toNat 1 (by
                        rw [hCapacity]
                        decide)
                  rw [hPayloadAddress, FixedArrayResult.writeLength_pages,
                    FixedArrayAllocator.allocStore_pages]
                  rw [hCapacityNat] at hFitMemory
                  exact hFitMemory
                · have hOutput : UInt64Array.At
                      (FixedArrayResult.writePayload
                        (FixedArrayResult.writeLength
                          (FixedArrayAllocator.allocStore initial heapTop
                            (FixedArrayCapacity.normalizedCapacity 1 1) 1
                            allocs)
                          (heapTop + 48) 1)
                        (heapTop + 48) 0
                        (ArrayFold.foldPrefix input
                          (fun sum element => sum + element) 0 input.size))
                      (heapTop + 48)
                      #[ArrayFold.foldPrefix input
                        (fun sum element => sum + element) 0 input.size] := by
                    change UInt64Array.At
                      (FixedArrayResult.singletonStore
                        (FixedArrayAllocator.allocStore initial heapTop
                          (FixedArrayCapacity.normalizedCapacity 1 1) 1
                          allocs)
                        (heapTop + 48)
                        (ArrayFold.foldPrefix input
                          (fun sum element => sum + element) 0 input.size))
                      (heapTop + 48)
                      #[ArrayFold.foldPrefix input
                        (fun sum element => sum + element) 0 input.size]
                    apply FixedArrayResult.singletonStore_at
                    · rw [hFacts.rootToNat]
                      have hFit32 := hFacts.fit32
                      rw [hCapacityNat] at hFit32
                      exact hFit32
                    · rw [hFacts.rootToNat,
                        FixedArrayAllocator.allocStore_pages]
                      rw [hCapacityNat] at hFitMemory
                      exact hFitMemory
                  let completionFrame :=
                    function_0_array_fold_0_continuing_frame inputPtr
                      (ArrayFold.foldPrefix input
                        (fun sum element => sum + element) 0 input.size)
                      item staged 0 0 0 (heapTop + 48) 0 0 0 inputPtr
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      done saved releaseReady 0 0
                  let resultFrame := FixedArrayFold.resultFrame
                    completionFrame 10
                      (ArrayFold.foldPrefix input
                        (fun sum element => sum + element) 0 input.size)
                  have hResultParams : resultFrame.params.length = 1 := by
                    simp only [resultFrame, FixedArrayFold.resultFrame_params,
                      completionFrame,
                      function_0_array_fold_0_continuing_frame_params,
                      List.length_cons, List.length_nil]
                  have hResultLocals : resultFrame.locals.length = 20 := by
                    simp only [resultFrame,
                      FixedArrayFold.resultFrame_locals_length,
                      completionFrame,
                      function_0_array_fold_0_continuing_frame_locals_length]
                  have hReturn :
                      (FixedArrayResult.finishFrame resultFrame 4 6
                        (heapTop + 48)).get 6 =
                          some (.i64 (heapTop + 48)) := by
                    apply FixedArrayResult.finishFrame_return_get
                    · omega
                    · simp [Wasm.Locals.validIndex, hResultParams,
                        hResultLocals]
                  simp only [resultFrame, completionFrame] at hReturn
                  simp only [FixedArrayEqNode.branchPost]
                  simp only [wp_localGet_cons, Frame.withValues_get, hReturn]
                  simp only [Wasm.wp_nil]
                  refine ⟨heapTop + 48, ?_, ?_⟩
                  · norm_num [func0Def, Wasm.Function.numParams]
                  · change UInt64Array.At _ _ (FormalSpec.expected input)
                    simpa [FormalSpec.expected, hSize,
                      ArrayFold.foldPrefix_size] using hOutput
            · have hIndexLt : index < input.size := by omega
              let accumulator :=
                ArrayFold.foldPrefix input
                  (fun sum element => sum + element) 0 index
              let nextAccumulator := accumulator + input[index]
              let loaded := function_0_array_fold_0_state
                inputPtr accumulator input[index] staged 0 0 0
                (heapTop + 48) 0 0 0 inputPtr (UInt64.ofNat input.size)
                (UInt64.ofNat index) (UInt64.ofNat input.size)
                (UInt64.ofNat input.size) done saved releaseReady 0 0
              let after := function_0_array_fold_0_state
                inputPtr nextAccumulator input[index] nextAccumulator 0 0 0
                (heapTop + 48) 0 0 0 inputPtr (UInt64.ofNat input.size)
                (UInt64.ofNat index) (UInt64.ofNat input.size)
                (UInt64.ofNat input.size) 0 nextAccumulator 1 0 0
              let continued := function_0_array_fold_0_state
                inputPtr nextAccumulator input[index] nextAccumulator 0 0 0
                (heapTop + 48) 0 0 0 inputPtr (UInt64.ofNat input.size)
                (UInt64.ofNat (index + 1)) (UInt64.ofNat input.size)
                (UInt64.ofNat input.size) 0 nextAccumulator 1 0 0
              change wp module
                (function_0_array_fold_0_continuing_program ++
                  function_0_array_fold_0_step_program) _ _ _ _
              have hFrameValues :
                  (sumFrame inputPtr (heapTop + 48) input index item staged
                    done saved releaseReady).values = [] := by
                simp only [sumFrame,
                  function_0_array_fold_0_continuing_frame_values]
              have hArrayLocal :
                  (sumFrame inputPtr (heapTop + 48) input index item staged
                    done saved releaseReady).get 11 = some (.i64 inputPtr) := by
                simp only [sumFrame,
                  function_0_array_fold_0_continuing_frame_get_11]
              have hIndexLocal :
                  (sumFrame inputPtr (heapTop + 48) input index item staged
                    done saved releaseReady).get 13 =
                      some (.i64 (UInt64.ofNat index)) := by
                simp only [sumFrame,
                  function_0_array_fold_0_continuing_frame_get_13]
              have hStopLocal :
                  (sumFrame inputPtr (heapTop + 48) input index item staged
                    done saved releaseReady).get 15 =
                      some (.i64 (UInt64.ofNat input.size)) := by
                simp only [sumFrame,
                  function_0_array_fold_0_continuing_frame_get_15]
              have hContinueGuard :
                  UInt64.ofNat index < UInt64.ofNat input.size := by
                rw [UInt64.lt_iff_toNat_lt,
                  UInt64.toNat_ofNat_of_lt' (by
                    have hInputSize := hInputWritten.size_lt
                    omega),
                  UInt64.toNat_ofNat_of_lt' hInputWritten.size_lt]
                exact hIndexLt
              have hItem :
                  (sumFrame inputPtr (heapTop + 48) input index item staged
                    done saved releaseReady).validIndex 2 := by
                simpa only [sumFrame] using
                  function_0_array_fold_0_continuing_item_valid
                    inputPtr accumulator item staged 0 0 0 (heapTop + 48)
                    0 0 0 inputPtr (UInt64.ofNat input.size)
                    (UInt64.ofNat index) (UInt64.ofNat input.size)
                    (UInt64.ofNat input.size) done saved releaseReady 0 0
              have hLoaded :
                  FixedArrayTraversalInput.dynamicResultFrame
                    (sumFrame inputPtr (heapTop + 48) input index item staged
                      done saved releaseReady) 2 input[index] hItem =
                    loaded.toState.toLocals [] := by
                simpa only [sumFrame, loaded, accumulator,
                  function_0_array_fold_0_continuing_frame] using
                  function_0_array_fold_0_continuing_loaded_frame_eq
                    inputPtr accumulator item staged 0 0 0 (heapTop + 48)
                    0 0 0 inputPtr (UInt64.ofNat input.size)
                    (UInt64.ofNat index) (UInt64.ofNat input.size)
                    (UInt64.ofNat input.size) done saved releaseReady 0 0
                    input[index]
              have hBody : function_0_array_fold_0_body.eval 11 loaded.toState =
                  some after.toState := by
                simpa [loaded, after, nextAccumulator,
                  ScalarTransition.U64Op.apply,
                  function_0_array_fold_0_bodyTransition] using
                  function_0_array_fold_0_body_eval
                    inputPtr accumulator input[index] staged 0 0 0
                    (heapTop + 48) 0 0 0 inputPtr
                    (UInt64.ofNat input.size) (UInt64.ofNat index)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    done saved releaseReady 0 0
              have hCondition :
                  function_0_array_fold_0_condition.eval 11 after.toState =
                    some (false, after.toState) := by
                simpa [after,
                  function_0_array_fold_0_conditionTransition] using
                  function_0_array_fold_0_condition_eval
                    inputPtr nextAccumulator input[index] nextAccumulator
                    0 0 0 (heapTop + 48) 0 0 0 inputPtr
                    (UInt64.ofNat input.size) (UInt64.ofNat index)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    0 nextAccumulator 1 0 0
              apply FixedArrayFoldBody.continuingGuardedProgram_spec
                (arrayLocal := 11) (indexLocal := 13) (stopLocal := 15)
                (itemLocal := 2) (scratch := 11)
                (body := function_0_array_fold_0_body)
                (condition := function_0_array_fold_0_condition)
                (continuing := function_0_array_fold_0_step_continuing)
                (inputPtr := inputPtr) (indexValue := UInt64.ofNat index)
                (stopValue := UInt64.ofNat input.size)
                (input := input) (index := index)
                (stepProgram := function_0_array_fold_0_step_program)
                (initial := loaded.toState) (afterBody := after.toState)
                (afterCondition := after.toState) (result := false)
                (hValues := hFrameValues) (hArrayLocal := hArrayLocal)
                (hIndexLocal := hIndexLocal) (hStopLocal := hStopLocal)
                (hIndexValue := rfl) (hContinueGuard := hContinueGuard)
                (hItem := hItem) (hInput := hInputWritten)
                (hIndex := hIndexLt) (hLoaded := hLoaded)
                (hStepProgram := rfl) (hBody := hBody)
                (hCondition := hCondition)
              · intro hFalse
                contradiction
              · intro _
                refine ⟨continued.toState, ?_, ?_⟩
                · simpa [after, continued,
                    function_0_array_fold_0_step_continuingTransition,
                    ScalarTransition.U64Op.apply,
                    UInt64.ofNat_add] using
                    function_0_array_fold_0_step_continuing_eval
                      inputPtr nextAccumulator input[index] nextAccumulator
                      0 0 0 (heapTop + 48) 0 0 0 inputPtr
                      (UInt64.ofNat input.size) (UInt64.ofNat index)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      0 nextAccumulator 1 0 0
                · have hFold :
                      ArrayFold.foldPrefix input
                          (fun sum element => sum + element) 0 (index + 1) =
                        nextAccumulator := by
                    simpa [accumulator, nextAccumulator] using
                      ArrayFold.foldPrefix_succ input
                        (fun sum element => sum + element) 0 index hIndexLt
                  have hContinuedFrame : continued.toState.toLocals [] =
                      sumFrame inputPtr (heapTop + 48) input (index + 1)
                        input[index] nextAccumulator 0 nextAccumulator 1 := by
                    simp only [continued, sumFrame,
                      function_0_array_fold_0_continuing_frame, hFold]
                  simp only [hFrameValues, List.take_zero, List.drop_zero,
                    List.drop_nil, List.append_nil]
                  rw [hContinuedFrame]
                  constructor
                  · exact ⟨index + 1, by omega, input[index], nextAccumulator,
                      0, nextAccumulator, 1, rfl, rfl⟩
                  · have hIndex64 : index < UInt64.size := by
                      have hInputSize := hInputWritten.size_lt
                      omega
                    have hNextIndex64 : index + 1 < UInt64.size := by
                      have hInputSize := hInputWritten.size_lt
                      omega
                    change input.size - (UInt64.ofNat (index + 1)).toNat <
                      input.size - (UInt64.ofNat index).toNat
                    rw [UInt64.toNat_ofNat_of_lt' hNextIndex64,
                      UInt64.toNat_ofNat_of_lt' hIndex64]
                    omega
  · intro hSize
    have hFitMemory : heapTop.toNat + 48 +
        (FixedArrayCapacity.normalizedCapacity 0 1).toNat ≤
          initial.mem.pages * 65536 := by
      simpa [FixedArrayCapacity.normalizedCapacity,
        FixedArrayCapacity.unnormalizedCapacity,
        FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
    have hFacts := Allocation.bumpFacts heapTop
      (FixedArrayCapacity.normalizedCapacity 0 1) initial.mem.pages
      hFitMemory hPages
    change wp module
      (FixedArrayCapacity.constantProgram 0 1 11 ++
        (FixedArrayAllocatorWindow.region 2 1 ++ _)) _ initial _ env
    apply FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail
      (length := 0) (stride := 1) (offset := 2) (tail := 4)
      (heapTop := heapTop) (allocs := allocs)
    · norm_num [FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams]
    · norm_num [FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals]
    · rfl
    · exact hFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · change wp module
        (FixedArrayResult.lengthStoreProgram 7 0 ++
          FixedArrayResult.finishProgram 7 5 6) _ _ _ _
      apply FixedArrayResult.lengthStore_spec
        (root := heapTop + 48) (length := 0) (rootLocal := 7)
      · rfl
      · apply FixedArrayAllocatorWindow.allocFrame_get_root 2 4
        · norm_num [FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams]
        · norm_num [FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams]
      · have hRootAddress : (heapTop + 48).toUInt32.toNat =
            heapTop.toNat + 48 := by
          simpa using hFacts.wordAddress_toNat 0
            (FixedArrayCapacity.normalizedCapacity_toNat_ge_eight 0 1)
        rw [hRootAddress]
        rw [FixedArrayAllocator.allocStore_pages]
        omega
      · apply FixedArrayResult.finishProgram_spec
        · rfl
        · apply FixedArrayAllocatorWindow.allocFrame_get_root 2 4
          · norm_num [FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams]
          · norm_num [FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams]
        · simp only [FixedArrayAllocatorWindow.allocFrame_params,
            FixedArrayCapacity.capacityFrame_params,
            FixedArrayLengthDispatch.branchFrame_params]
          norm_num [func0Def, Wasm.Function.toLocals,
            Wasm.Function.numParams]
        · simp [Wasm.Locals.validIndex,
            FixedArrayAllocatorWindow.allocFrame_params,
            FixedArrayAllocatorWindow.allocFrame_locals_length,
            FixedArrayCapacity.capacityFrame_params,
            FixedArrayCapacity.capacityFrame_locals_length,
            FixedArrayLengthDispatch.branchFrame_params,
            FixedArrayLengthDispatch.branchFrame_locals_length,
            func0Def, Wasm.Function.toLocals, Wasm.Function.numParams]
        · simp only [FixedArrayAllocatorWindow.allocFrame_params,
            FixedArrayCapacity.capacityFrame_params,
            FixedArrayLengthDispatch.branchFrame_params]
          norm_num [func0Def, Wasm.Function.toLocals,
            Wasm.Function.numParams]
        · simp [Wasm.Locals.validIndex,
            FixedArrayAllocatorWindow.allocFrame_params,
            FixedArrayAllocatorWindow.allocFrame_locals_length,
            FixedArrayCapacity.capacityFrame_params,
            FixedArrayCapacity.capacityFrame_locals_length,
            FixedArrayLengthDispatch.branchFrame_params,
            FixedArrayLengthDispatch.branchFrame_locals_length,
            func0Def, Wasm.Function.toLocals, Wasm.Function.numParams]
        · let frame := FixedArrayAllocatorWindow.allocFrame 2
              (FixedArrayCapacity.capacityFrame
                (FixedArrayLengthDispatch.branchFrame 7
                  (func0Def.toLocals
                    (List.take func0Def.numParams [.i64 inputPtr]).reverse)
                  inputPtr)
                11 (FixedArrayCapacity.normalizedCapacity 0 1))
              heapTop (FixedArrayCapacity.normalizedCapacity 0 1)
          have hFrameParams : frame.params.length = 1 := by
            simp [frame, FixedArrayAllocatorWindow.allocFrame_params,
              FixedArrayCapacity.capacityFrame_params,
              FixedArrayLengthDispatch.branchFrame_params, func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams]
          have hFrameLocals : frame.locals.length = 20 := by
            simp [frame, FixedArrayAllocatorWindow.allocFrame_locals_length,
              FixedArrayCapacity.capacityFrame_locals_length,
              FixedArrayLengthDispatch.branchFrame_locals_length, func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams]
          have hReturn :
              (FixedArrayResult.finishFrame frame 5 6 (heapTop + 48)).get 6 =
                some (.i64 (heapTop + 48)) := by
            apply FixedArrayResult.finishFrame_return_get
            · omega
            · simp [Wasm.Locals.validIndex, hFrameParams, hFrameLocals]
          have hEmpty : UInt64Array.At
              (FixedArrayResult.writeLength
                (FixedArrayAllocator.allocStore initial heapTop
                  (FixedArrayCapacity.normalizedCapacity 0 1) 1 allocs)
                (heapTop + 48) 0)
              (heapTop + 48) #[] := by
            apply FixedArrayResult.emptyStore_at
            · rw [hFacts.rootToNat]
              have hCapacity :=
                FixedArrayCapacity.normalizedCapacity_toNat_ge_eight 0 1
              omega
            · rw [hFacts.rootToNat,
                FixedArrayAllocator.allocStore_pages]
              have hCapacity :=
                FixedArrayCapacity.normalizedCapacity_toNat_ge_eight 0 1
              omega
          change wp module [] _ _
            (FixedArrayResult.finishFrame frame 5 6 (heapTop + 48)) env
          simp only [Wasm.wp_nil, FixedArrayEqNode.branchPost]
          simp only [wp_localGet_cons, Frame.withValues_get, hReturn]
          simp only [Wasm.wp_nil]
          refine ⟨heapTop + 48, ?_, ?_⟩
          · norm_num [func0Def, Wasm.Function.numParams]
          · change UInt64Array.At _ _ (FormalSpec.expected input)
            simpa [FormalSpec.expected, hSize] using hEmpty

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior
