import LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec
import LeanExeGen.GeneratedRa8e90ffc5781d113.Program
import LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches
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

namespace LeanExeGen.GeneratedRa8e90ffc5781d113.Behavior

open Wasm Project.ProofKit

theorem artifact_behavior :
    LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec.ArtifactSpec LeanExeGen.GeneratedRa8e90ffc5781d113.«module» := by
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
  apply Wasm.TerminatesWith.of_wp_entry_for (f := LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def) rfl
  change Wasm.wp _ LeanExeGen.GeneratedRa8e90ffc5781d113.func0 _ _ _ _
  rw [LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_length_dispatch_0_function_eq]
  wp_fixed_array_length_le_dispatch_from hArray at 7, 8
  all_goals
    try norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
      Wasm.Function.toLocals, Wasm.Function.numParams, Wasm.ValueType.zero]
  · intro hSize
    change Wasm.wp _
      (FixedArrayCapacity.constantProgram 1 1 11 ++
        (FixedArrayAllocatorWindow.region 2 1 ++ _)) _ _ _ _
    apply FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail
      (length := 1) (stride := 1) (offset := 2) (tail := 4)
      (heapTop := heapTop) (allocs := allocs)
    · norm_num [FixedArrayLengthDispatch.branchFrame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams, Wasm.ValueType.zero]
    · norm_num [FixedArrayLengthDispatch.branchFrame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams, Wasm.ValueType.zero]
    · rfl
    · simpa [FormalSpec.heapReserveBytes, hSize,
        FixedArrayCapacity.normalizedCapacity,
        FixedArrayCapacity.unnormalizedCapacity] using hHeapFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · let baseFrame := FixedArrayCapacity.capacityFrame
        (FixedArrayLengthDispatch.branchFrame 7
          (LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.toLocals
            (List.take LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.numParams
              [.i64 inputPtr]).reverse) inputPtr)
        11 (FixedArrayCapacity.normalizedCapacity 1 1)
      let allocFrame := FixedArrayAllocatorWindow.allocFrame 2 baseFrame
        heapTop (FixedArrayCapacity.normalizedCapacity 1 1)
      let allocSt := FixedArrayAllocator.allocStore initial heapTop
        (FixedArrayCapacity.normalizedCapacity 1 1) 1 allocs
      let foldSt := FixedArrayResult.writeLength allocSt (heapTop + 48) 1
      change Wasm.wp _
        (FixedArrayResult.lengthStoreProgram 7 1 ++
          (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_setup_program ++
            ([.block 0 0 [.loop 0 0
              (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_program ++
                LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_step_program)]] ++
              LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_singleton_result_program)))
          _ allocSt allocFrame _
      have hBaseParams : baseFrame.params.length = 1 := by
        norm_num [baseFrame, FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      have hBaseLocals : baseFrame.locals.length = 2 + 14 + 4 := by
        norm_num [baseFrame, FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      have hAllocParams : allocFrame.params = [.i64 inputPtr] := by
        simp [allocFrame, baseFrame,
          FixedArrayAllocatorWindow.allocFrame_params,
          FixedArrayCapacity.capacityFrame_params,
          FixedArrayLengthDispatch.branchFrame_params,
          LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      have hAllocLocals : allocFrame.locals.length = 20 := by
        simpa [allocFrame, FixedArrayAllocatorWindow.allocFrame_locals_length]
          using hBaseLocals
      have hAllocValues : allocFrame.values = [] := by
        simp [allocFrame, baseFrame,
          FixedArrayAllocatorWindow.allocFrame_values,
          FixedArrayCapacity.capacityFrame_values]
      have hRoot : allocFrame.get 7 = some (.i64 (heapTop + 48)) := by
        exact FixedArrayAllocatorWindow.allocFrame_get_root 2 4 baseFrame
          heapTop (FixedArrayCapacity.normalizedCapacity 1 1)
          hBaseParams hBaseLocals
      have hFit : heapTop.toNat + 48 + 16 ≤ initial.mem.pages * 65536 := by
        simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
      have hFacts := Allocation.bumpFacts heapTop 16 initial.mem.pages hFit hPages
      have hRootAddress :
          (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
        simpa using hFacts.wordAddress_toNat 0 (by decide)
      have hRootBound :
          (heapTop + 48).toUInt32.toNat + 8 ≤ allocSt.mem.pages * 65536 := by
        rw [hRootAddress]
        simp only [allocSt, FixedArrayAllocator.allocStore_pages]
        omega
      have hInputAlloc : UInt64Array.At allocSt inputPtr input := by
        simpa [allocSt, FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity] using
          (FixedArrayPairResult.input_preserved_by_alloc initial heapTop 16 1
            allocs inputPtr input hArray hInputBelow hFit hPages)
      have hInputFold : UInt64Array.At foldSt inputPtr input := by
        have hPreserved := hInputAlloc.write64After
          (address := (heapTop + 48).toUInt32) (value := 1) (by
            rw [hRootAddress]
            omega)
        simpa [foldSt, FixedArrayResult.writeLength] using hPreserved
      have hAllocFrame : allocFrame =
          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame
            inputPtr 0 0 0 0 0 0 (heapTop + 48) 0 0 0
            (FixedArrayCapacity.normalizedCapacity 1 1) 0 0
            (heapTop + 48 + FixedArrayCapacity.normalizedCapacity 1 1)
            ((heapTop + 48 + FixedArrayCapacity.normalizedCapacity 1 1 - 1) / 65536 + 1)
            (heapTop + 48) 0 0 0 0 := by
        simp [allocFrame, baseFrame,
          FixedArrayAllocatorWindow.allocFrame,
          FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero,
          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
          ScalarTransition.U64State.toState]
      apply FixedArrayResult.lengthStore_spec
        (root := heapTop + 48) (length := 1) (rootLocal := 7)
      · exact hAllocValues
      · exact hRoot
      · exact hRootBound
      · apply FixedArrayFold.forwardSetupProgram_spec
          (arrayLocal := 11) (lengthLocal := 12) (indexLocal := 13)
          (stopScratchLocal := 16) (stopLocal := 14)
          (accumulatorLocal := 1) (releaseReadyLocal := 18)
          (effectiveStopLocal := 15) (initial := 1)
          (inputPtr := inputPtr) (input := input)
        · exact hAllocParams
        · exact hAllocValues
        · intro slot hSlot
          simp [FixedArrayFold.setupLocals] at hSlot
          omega
        · decide
        · exact hInputFold
        · rw [hAllocFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_setup_frame_eq]
          let step : UInt64 → UInt64 → UInt64 := fun product element => product * element
          let Inv : Store Unit → Locals → Prop := fun st frame =>
            st = foldSt ∧
              ∃ index v2 v3 v4 v5 v6 v8 v9 v10 v16 v17 v18 v19 v20,
                index ≤ input.size ∧
                frame =
                  LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame
                    inputPtr (ArrayFold.foldPrefix input step 1 index)
                    v2 v3 v4 v5 v6 (heapTop + 48) v8 v9 v10
                    inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    v16 v17 v18 v19 v20
          let measure : Store Unit → Locals → Nat := fun _ frame =>
            match frame.get 13 with
            | some (.i64 index) => input.size - index.toNat
            | _ => 0
          wp_block_loop invariant Inv decreasing measure
          · refine ⟨rfl, 0, 0, 0, 0, 0, 0, 0, 0, 0,
              inputPtr, 0, 0, 0, 0, ?_, ?_⟩
            · omega
            · simp [ArrayFold.foldPrefix, step]
          · rintro st frame
              ⟨rfl, index, v2, v3, v4, v5, v6, v8, v9, v10,
                v16, v17, v18, v19, v20, hIndexLe, rfl⟩
            by_cases hIndex : index < input.size
            · let acc := ArrayFold.foldPrefix input step 1 index
              let value := input[index]
              let nextAcc := acc * value
              let loaded :=
                (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state
                  inputPtr acc value v3 v4 v5 v6 (heapTop + 48)
                  v8 v9 v10 inputPtr (UInt64.ofNat input.size)
                  (UInt64.ofNat index) (UInt64.ofNat input.size)
                  (UInt64.ofNat input.size) v16 v17 v18 v19 v20).toState
              let afterBody :=
                (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state
                  inputPtr nextAcc value nextAcc v4 v5 v6 (heapTop + 48)
                  v8 v9 v10 inputPtr (UInt64.ofNat input.size)
                  (UInt64.ofNat index) (UInt64.ofNat input.size)
                  (UInt64.ofNat input.size) 0 nextAcc 1 v19 v20).toState
              let afterContinue :=
                (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state
                  inputPtr nextAcc value nextAcc v4 v5 v6 (heapTop + 48)
                  v8 v9 v10 inputPtr (UInt64.ofNat input.size)
                  (UInt64.ofNat index + 1) (UInt64.ofNat input.size)
                  (UInt64.ofNat input.size) 0 nextAcc 1 v19 v20).toState
              have hIndex64 : index < UInt64.size := by
                exact lt_trans hIndex hInputFold.size_lt
              have hIndexEncoded :
                  UInt64.ofNat index < UInt64.ofNat input.size := by
                rw [UInt64.lt_iff_toNat_lt,
                  UInt64.toNat_ofNat_of_lt' hIndex64,
                  UInt64.toNat_ofNat_of_lt' hInputFold.size_lt]
                exact hIndex
              have hFrameValues :=
                LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame_values
                  inputPtr acc v2 v3 v4 v5 v6 (heapTop + 48) v8 v9 v10
                  inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                  (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                  v16 v17 v18 v19 v20
              have hArrayLocal :=
                LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame_get_11
                  inputPtr acc v2 v3 v4 v5 v6 (heapTop + 48) v8 v9 v10
                  inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                  (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                  v16 v17 v18 v19 v20
              have hIndexLocal :=
                LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13
                  inputPtr acc v2 v3 v4 v5 v6 (heapTop + 48) v8 v9 v10
                  inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                  (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                  v16 v17 v18 v19 v20
              have hStopLocal :=
                LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame_get_15
                  inputPtr acc v2 v3 v4 v5 v6 (heapTop + 48) v8 v9 v10
                  inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                  (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                  v16 v17 v18 v19 v20
              have hItem :=
                LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_item_valid
                  inputPtr acc v2 v3 v4 v5 v6 (heapTop + 48) v8 v9 v10
                  inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                  (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                  v16 v17 v18 v19 v20
              have hLoaded :
                  FixedArrayTraversalInput.dynamicResultFrame
                    (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame
                      inputPtr acc v2 v3 v4 v5 v6 (heapTop + 48) v8 v9 v10
                      inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      v16 v17 v18 v19 v20)
                    2 value hItem = loaded.toLocals [] := by
                simpa [loaded,
                  LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame]
                  using
                    (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_loaded_frame_eq
                      inputPtr acc v2 v3 v4 v5 v6 (heapTop + 48) v8 v9 v10
                      inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      v16 v17 v18 v19 v20 value)
              have hBody :
                  LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_body.eval
                    11 loaded = some afterBody := by
                simpa [loaded, afterBody, nextAcc,
                  LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_bodyTransition,
                  ScalarTransition.U64Op.apply]
                  using
                    (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_body_eval
                      inputPtr acc value v3 v4 v5 v6 (heapTop + 48) v8 v9 v10
                      inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      v16 v17 v18 v19 v20)
              have hCondition :
                  LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_condition.eval
                    11 afterBody = some (false, afterBody) := by
                simpa [afterBody,
                  LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_conditionTransition]
                  using
                    (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_condition_eval
                      inputPtr nextAcc value nextAcc v4 v5 v6 (heapTop + 48)
                      v8 v9 v10 inputPtr (UInt64.ofNat input.size)
                      (UInt64.ofNat index) (UInt64.ofNat input.size)
                      (UInt64.ofNat input.size) 0 nextAcc 1 v19 v20)
              apply FixedArrayFoldBody.continuingGuardedProgram_spec
                (arrayLocal := 11) (indexLocal := 13) (stopLocal := 15)
                (itemLocal := 2) (scratch := 11)
                (body := LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_body)
                (condition := LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_condition)
                (continuing := LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_step_continuing)
                (inputPtr := inputPtr) (indexValue := UInt64.ofNat index)
                (stopValue := UInt64.ofNat input.size)
                (input := input) (index := index)
                (stepProgram := LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_step_program)
                (initial := loaded) (afterBody := afterBody)
                (afterCondition := afterBody) (result := false)
                (hValues := hFrameValues) (hArrayLocal := hArrayLocal)
                (hIndexLocal := hIndexLocal) (hStopLocal := hStopLocal)
                (hIndexValue := rfl) (hContinueGuard := hIndexEncoded)
                (hItem := hItem) (hInput := hInputFold) (hIndex := hIndex)
                (hLoaded := hLoaded) (hStepProgram := rfl)
                (hBody := hBody) (hCondition := hCondition)
              · simp
              · intro _
                refine ⟨afterContinue, ?_, ?_⟩
                · simpa [afterBody, afterContinue,
                    LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_step_continuingTransition,
                    ScalarTransition.U64Op.apply]
                    using
                      (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_step_continuing_eval
                        inputPtr nextAcc value nextAcc v4 v5 v6 (heapTop + 48)
                        v8 v9 v10 inputPtr (UInt64.ofNat input.size)
                        (UInt64.ofNat index) (UInt64.ofNat input.size)
                        (UInt64.ofNat input.size) 0 nextAcc 1 v19 v20)
                · change Inv foldSt (afterContinue.toLocals []) ∧
                    measure foldSt (afterContinue.toLocals []) <
                      measure foldSt
                        (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame
                          inputPtr acc v2 v3 v4 v5 v6 (heapTop + 48) v8 v9 v10
                          inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                          (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                          v16 v17 v18 v19 v20)
                  have hNextFrame : afterContinue.toLocals [] =
                      LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame
                        inputPtr (ArrayFold.foldPrefix input step 1 (index + 1))
                        value nextAcc v4 v5 v6 (heapTop + 48) v8 v9 v10
                        inputPtr (UInt64.ofNat input.size) (UInt64.ofNat (index + 1))
                        (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                        0 nextAcc 1 v19 v20 := by
                    simp [afterContinue, nextAcc, acc, value,
                      LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
                      ArrayFold.foldPrefix_succ input step 1 index hIndex,
                      step]
                  constructor
                  · refine ⟨rfl, index + 1, value, nextAcc, v4, v5, v6,
                      v8, v9, v10, 0, nextAcc, 1, v19, v20, ?_, hNextFrame⟩
                    omega
                  · rw [hNextFrame]
                    simp only [measure,
                      LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13]
                    rw [UInt64.toNat_ofNat_of_lt'
                        (lt_of_le_of_lt (Nat.succ_le_iff.mpr hIndex)
                          hInputFold.size_lt),
                      UInt64.toNat_ofNat_of_lt' hIndex64]
                    omega
            · have hIndexEq : index = input.size := by omega
              subst index
              apply FixedArrayTraversalInput.continuingProgram_exit_spec
                (arrayLocal := 11) (indexLocal := 13) (stopLocal := 15)
                (itemLocal := 2) (index := UInt64.ofNat input.size)
              · exact LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame_values
                  inputPtr (ArrayFold.foldPrefix input step 1 input.size)
                  v2 v3 v4 v5 v6 (heapTop + 48) v8 v9 v10 inputPtr
                  (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                  (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                  v16 v17 v18 v19 v20
              · exact LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13
                  inputPtr (ArrayFold.foldPrefix input step 1 input.size)
                  v2 v3 v4 v5 v6 (heapTop + 48) v8 v9 v10 inputPtr
                  (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                  (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                  v16 v17 v18 v19 v20
              · exact LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame_get_15
                  inputPtr (ArrayFold.foldPrefix input step 1 input.size)
                  v2 v3 v4 v5 v6 (heapTop + 48) v8 v9 v10 inputPtr
                  (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                  (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                  v16 v17 v18 v19 v20
              · simp only [
                  LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame_values,
                  List.take_zero, List.drop_zero, List.nil_append]
                change Wasm.wp _
                  LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_singleton_result_program
                  _ foldSt
                  (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame
                    inputPtr (ArrayFold.foldPrefix input step 1 input.size)
                    v2 v3 v4 v5 v6 (heapTop + 48) v8 v9 v10 inputPtr
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    v16 v17 v18 v19 v20) _
                have hPayloadAddress :
                    (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat =
                      heapTop.toNat + 56 := by
                  simpa [FixedArrayResult.payloadAddress] using
                    hFacts.wordAddress_toNat 1 (by decide)
                have hPayloadBound :
                    (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat + 8 ≤
                      foldSt.mem.pages * 65536 := by
                  rw [hPayloadAddress]
                  simp only [foldSt, FixedArrayResult.writeLength_pages,
                    allocSt, FixedArrayAllocator.allocStore_pages]
                  omega
                have hRootFit32 :
                    (heapTop + 48).toNat + 16 ≤ 4294967296 := by
                  rw [hFacts.rootToNat]
                  simpa [FormalSpec.expected, hSize] using hOutputFit32
                have hRootFitMemory :
                    (heapTop + 48).toNat + 16 ≤ allocSt.mem.pages * 65536 := by
                  rw [hFacts.rootToNat]
                  simp only [allocSt, FixedArrayAllocator.allocStore_pages]
                  simpa [FormalSpec.expected, hSize] using hOutputFitMemory
                have hSingleton := FixedArrayResult.singletonStore_at allocSt
                  (heapTop + 48) (ArrayFold.foldPrefix input step 1 input.size)
                  hRootFit32 hRootFitMemory
                let exitFrame :=
                  LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame
                    inputPtr (ArrayFold.foldPrefix input step 1 input.size)
                    v2 v3 v4 v5 v6 (heapTop + 48) v8 v9 v10 inputPtr
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    v16 v17 v18 v19 v20
                let resultFrame := FixedArrayFold.resultFrame exitFrame 10
                  (ArrayFold.foldPrefix input step 1 input.size)
                have hReturnLower : resultFrame.params.length ≤ 6 := by
                  simp [resultFrame, exitFrame,
                    FixedArrayFold.resultFrame_params,
                    LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
                have hReturnValid : resultFrame.validIndex 6 := by
                  simp [resultFrame, exitFrame, Wasm.Locals.validIndex,
                    FixedArrayFold.resultFrame_params,
                    FixedArrayFold.resultFrame_locals_length,
                    LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame_params,
                    LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
                have hFinishRoot :
                    (FixedArrayResult.finishFrame resultFrame 4 6
                      (heapTop + 48)).get 6 = some (.i64 (heapTop + 48)) :=
                  FixedArrayResult.finishFrame_return_get resultFrame 4 6
                    (heapTop + 48) hReturnLower hReturnValid
                apply LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_singleton_result_spec
                  (hPayloadBound := hPayloadBound)
                simp only [FixedArrayEqNode.branchPost]
                simp only [
                  LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_length_dispatch_0_suffix_program,
                  wp_localGet_cons, hFinishRoot, Wasm.wp_nil]
                refine ⟨heapTop + 48, rfl, ?_⟩
                simpa only [FormalSpec.UInt64ArrayAt, UInt64Array.At,
                  FormalSpec.expected, if_pos hSize,
                  ArrayFold.foldPrefix_size, step, foldSt,
                  FixedArrayResult.singletonStore] using hSingleton
  · intro hSize
    have hNotLe : ¬input.size ≤ 8 := by omega
    change Wasm.wp _
      (FixedArrayCapacity.constantProgram 0 1 11 ++
        (FixedArrayAllocatorWindow.region 2 1 ++ _)) _ _ _ _
    apply FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail
      (length := 0) (stride := 1) (offset := 2) (tail := 4)
      (heapTop := heapTop) (allocs := allocs)
    · norm_num [FixedArrayLengthDispatch.branchFrame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams, Wasm.ValueType.zero]
    · norm_num [FixedArrayLengthDispatch.branchFrame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams, Wasm.ValueType.zero]
    · rfl
    · simpa [FormalSpec.heapReserveBytes, hNotLe,
        FixedArrayCapacity.normalizedCapacity,
        FixedArrayCapacity.unnormalizedCapacity] using hHeapFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · let baseFrame := FixedArrayCapacity.capacityFrame
        (FixedArrayLengthDispatch.branchFrame 7
          (LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.toLocals
            (List.take LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.numParams
              [.i64 inputPtr]).reverse) inputPtr)
        11 (FixedArrayCapacity.normalizedCapacity 0 1)
      let allocFrame := FixedArrayAllocatorWindow.allocFrame 2 baseFrame
        heapTop (FixedArrayCapacity.normalizedCapacity 0 1)
      let allocSt := FixedArrayAllocator.allocStore initial heapTop
        (FixedArrayCapacity.normalizedCapacity 0 1) 1 allocs
      change Wasm.wp _
        (FixedArrayResult.lengthStoreProgram 7 0 ++
          FixedArrayResult.finishProgram 7 5 6) _ allocSt allocFrame _
      have hBaseParams : baseFrame.params.length = 1 := by
        norm_num [baseFrame, FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      have hBaseLocals : baseFrame.locals.length = 2 + 14 + 4 := by
        norm_num [baseFrame, FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      have hAllocParams : allocFrame.params.length = 1 := by
        simpa [allocFrame, FixedArrayAllocatorWindow.allocFrame_params]
          using hBaseParams
      have hAllocLocals : allocFrame.locals.length = 20 := by
        simpa [allocFrame, FixedArrayAllocatorWindow.allocFrame_locals_length]
          using hBaseLocals
      have hAllocValues : allocFrame.values = [] := by
        simp [allocFrame, baseFrame,
          FixedArrayAllocatorWindow.allocFrame_values,
          FixedArrayCapacity.capacityFrame_values,
          FixedArrayLengthDispatch.branchFrame_values]
      have hRoot : allocFrame.get 7 = some (.i64 (heapTop + 48)) := by
        exact FixedArrayAllocatorWindow.allocFrame_get_root 2 4 baseFrame
          heapTop (FixedArrayCapacity.normalizedCapacity 0 1)
          hBaseParams hBaseLocals
      have hFit : heapTop.toNat + 48 + 8 ≤ initial.mem.pages * 65536 := by
        simpa [FormalSpec.heapReserveBytes, hNotLe] using hHeapFitMemory
      have hFacts := Allocation.bumpFacts heapTop 8 initial.mem.pages hFit hPages
      have hRootFit32 : (heapTop + 48).toNat + 8 ≤ 4294967296 := by
        rw [hFacts.rootToNat]
        simpa [FormalSpec.expected, hNotLe] using hOutputFit32
      have hRootFitMemory :
          (heapTop + 48).toNat + 8 ≤ allocSt.mem.pages * 65536 := by
        rw [hFacts.rootToNat]
        simp only [allocSt, FixedArrayAllocator.allocStore_pages]
        simpa [FormalSpec.expected, hNotLe] using hOutputFitMemory
      have hRootBound :
          (heapTop + 48).toUInt32.toNat + 8 ≤ allocSt.mem.pages * 65536 := by
        rw [UInt64.toUInt32_toNat, Nat.mod_eq_of_lt]
        · exact hRootFitMemory
        · omega
      have hEmpty := FixedArrayResult.emptyStore_at allocSt (heapTop + 48)
        hRootFit32 hRootFitMemory
      have hDestinationLower : allocFrame.params.length ≤ 5 := by
        omega
      have hDestinationValid : allocFrame.validIndex 5 := by
        simp [Wasm.Locals.validIndex, hAllocParams, hAllocLocals]
      have hReturnLower : allocFrame.params.length ≤ 6 := by
        omega
      have hReturnValid : allocFrame.validIndex 6 := by
        simp [Wasm.Locals.validIndex, hAllocParams, hAllocLocals]
      apply FixedArrayResult.lengthStore_spec
        (root := heapTop + 48) (length := 0) (rootLocal := 7)
      · exact hAllocValues
      · exact hRoot
      · exact hRootBound
      · apply FixedArrayResult.finishProgram_spec
          (root := heapTop + 48) (rootLocal := 7)
          (destinationLocal := 5) (returnLocal := 6)
        · exact hAllocValues
        · exact hRoot
        · exact hDestinationLower
        · exact hDestinationValid
        · exact hReturnLower
        · exact hReturnValid
        · rw [Wasm.wp_nil]
          simp only [FixedArrayEqNode.branchPost]
          simp only [
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_length_dispatch_0_suffix_program,
            wp_localGet_cons,
            FixedArrayResult.finishFrame_return_get _ _ _ _ hReturnLower hReturnValid,
            Wasm.wp_nil]
          refine ⟨heapTop + 48, rfl, ?_⟩
          simpa only [FormalSpec.UInt64ArrayAt, UInt64Array.At,
            FormalSpec.expected, if_neg hNotLe] using hEmpty

end LeanExeGen.GeneratedRa8e90ffc5781d113.Behavior
