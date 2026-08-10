import LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec
import LeanExeGen.GeneratedR23fa7efc3fb0298b.Program
import LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.Allocation
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

def foldInvariant (loopStore : Store Unit) (inputPtr root : UInt64)
    (input : Array UInt64) (st : Store Unit) (frame : Locals) : Prop :=
  ∃ (index : Nat)
      (v2 v3 v4 v5 v6 v8 v9 v10 v16 v17 v18 v19 v20 : UInt64),
    index ≤ input.size ∧
    st = loopStore ∧
    frame =
      AnnotationMatches.function_0_array_fold_0_continuing_frame
        inputPtr
        (ArrayFold.foldPrefix input (fun sum element => sum + element) 0 index)
        v2 v3 v4 v5 v6 root v8 v9 v10 inputPtr
        (UInt64.ofNat input.size) (UInt64.ofNat index)
        (UInt64.ofNat input.size) (UInt64.ofNat input.size)
        v16 v17 v18 v19 v20

def foldMeasure (input : Array UInt64) (_st : Store Unit)
    (frame : Locals) : Nat :=
  match frame.get 13 with
  | some (.i64 index) => input.size - index.toNat
  | _ => 0

def foldProgram : Wasm.Program :=
  AnnotationMatches.function_0_array_fold_0_setup_program ++
    [.block 0 0 [.loop 0 0
      (AnnotationMatches.function_0_array_fold_0_continuing_program ++
        AnnotationMatches.function_0_array_fold_0_step_program)]] ++
    AnnotationMatches.function_0_array_fold_0_singleton_result_program

set_option Elab.async false in
theorem foldProgram_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr root : UInt64) (input : Array UInt64)
    (hParams : frame.params = [.i64 inputPtr])
    (hLocals : frame.locals.length = 20)
    (hValues : frame.values = [])
    (hInput : UInt64Array.At st inputPtr input)
    (hScalarFrame :
      ∃ (v1 v2 v3 v4 v5 v6 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
          v18 v19 v20 : UInt64),
        frame = AnnotationMatches.function_0_array_fold_0_continuing_frame
          inputPtr v1 v2 v3 v4 v5 v6 root v8 v9 v10 v11 v12 v13 v14
          v15 v16 v17 v18 v19 v20)
    (hRoot : frame.get 7 = some (.i64 root))
    (hPayloadBound :
      (FixedArrayResult.payloadAddress root 0).toUInt32.toNat + 8 ≤
        st.mem.pages * 65536)
    (hOutput : UInt64Array.At
      (FixedArrayResult.writePayload st root 0
        (input.foldl (fun sum element => sum + element) 0))
      root #[input.foldl (fun sum element => sum + element) 0]) :
    wp module_ foldProgram
      (FixedArrayFold.singletonResultPost 6 root
        (input.foldl (fun sum element => sum + element) 0))
      st frame env := by
  unfold foldProgram
  apply FixedArrayFold.forwardSetupProgram_spec
  · exact hParams
  · exact hValues
  · intro slot hSlot
    simp [FixedArrayFold.setupLocals] at hSlot
    omega
  · decide
  · exact hInput
  · apply Wasm.wp_block_cons
    apply Wasm.wp_loop_cons
      (Inv := foldInvariant st inputPtr root input)
      (μ := foldMeasure input)
    · rcases hScalarFrame with
        ⟨v1, v2, v3, v4, v5, v6, v8, v9, v10, v11, v12, v13, v14,
          v15, v16, v17, v18, v19, v20, rfl⟩
      refine ⟨0, v2, v3, v4, v5, v6, v8, v9, v10, inputPtr, v17, 0,
        v19, v20, Nat.zero_le _, rfl, ?_⟩
      simp [FixedArrayFold.forwardSetupFrame, ArrayFold.foldPrefix,
        AnnotationMatches.function_0_array_fold_0_continuing_frame,
        AnnotationMatches.function_0_array_fold_0_state,
        ScalarTransition.U64State.toState, Wasm.Locals.set]
    · rintro st' current hInv
      rcases hInv with
        ⟨index, v2, v3, v4, v5, v6, v8, v9, v10, v16, v17, v18, v19,
          v20, hIndexLe, hStore, hFrame⟩
      subst st'
      subst current
      by_cases hDone : index = input.size
      · subst index
        apply FixedArrayTraversalInput.continuingProgram_exit_spec
          (arrayLocal := 11) (indexLocal := 13) (stopLocal := 15)
          (itemLocal := 2) (index := UInt64.ofNat input.size)
        · simp only [
            AnnotationMatches.function_0_array_fold_0_continuing_frame_values]
        · simp only [
            AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13]
        · simp only [
            AnnotationMatches.function_0_array_fold_0_continuing_frame_get_15]
        · simp only [List.take, List.drop, List.nil_append,
            FixedArrayFold.forwardSetupFrame_values]
          change wp module_
            AnnotationMatches.function_0_array_fold_0_singleton_result_program
            (FixedArrayFold.singletonResultPost 6 root
              (input.foldl (fun sum element => sum + element) 0)) st _ env
          apply FixedArrayFold.singletonResultProgram_spec
          · simp only [
              AnnotationMatches.function_0_array_fold_0_continuing_frame_values]
          · rw [ArrayFold.foldPrefix_size]
            simpa only [Wasm.Locals.get] using
              (AnnotationMatches.function_0_array_fold_0_continuing_frame_get_1
                inputPtr (input.foldl (fun sum element => sum + element) 0)
                v2 v3 v4 v5 v6 root v8 v9 v10 inputPtr
                (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                v16 v17 v18 v19 v20)
          · simp only [
              AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
            norm_num
          · simp [Wasm.Locals.validIndex,
              AnnotationMatches.function_0_array_fold_0_continuing_frame_params,
              AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
          · apply FixedArrayFold.resultFrame_get_of_ne
            · simp only [
                AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
              norm_num
            · simp only [
                AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
              norm_num
            · simp [Wasm.Locals.validIndex,
                AnnotationMatches.function_0_array_fold_0_continuing_frame_params,
                AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
            · norm_num
            · simpa only [Wasm.Locals.get] using
                (AnnotationMatches.function_0_array_fold_0_continuing_frame_get_7
                  inputPtr
                  (ArrayFold.foldPrefix input
                    (fun sum element => sum + element) 0 input.size)
                  v2 v3 v4 v5 v6 root v8 v9 v10 inputPtr
                  (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                  (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                  v16 v17 v18 v19 v20)
          · apply FixedArrayFold.resultFrame_get_result
            · simp only [
                AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
              norm_num
            · simp [Wasm.Locals.validIndex,
                AnnotationMatches.function_0_array_fold_0_continuing_frame_params,
                AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
          · exact hPayloadBound
          · simp only [FixedArrayFold.resultFrame_params,
              AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
            norm_num
          · simp [Wasm.Locals.validIndex, FixedArrayFold.resultFrame_params,
              FixedArrayFold.resultFrame_locals_length,
              AnnotationMatches.function_0_array_fold_0_continuing_frame_params,
              AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
          · simp only [FixedArrayFold.resultFrame_params,
              AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
            norm_num
          · simp [Wasm.Locals.validIndex, FixedArrayFold.resultFrame_params,
              FixedArrayFold.resultFrame_locals_length,
              AnnotationMatches.function_0_array_fold_0_continuing_frame_params,
                AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
          · exact hOutput
      · have hIndex : index < input.size := by omega
        have hIndex64 : index < UInt64.size := by
          exact lt_trans hIndex hInput.size_lt
        have hNextIndex64 : index + 1 < UInt64.size := by
          exact lt_of_le_of_lt (Nat.succ_le_of_lt hIndex) hInput.size_lt
        have hContinue :
            UInt64.ofNat index < UInt64.ofNat input.size := by
          rw [UInt64.lt_iff_toNat_lt,
            UInt64.toNat_ofNat_of_lt' hIndex64,
            UInt64.toNat_ofNat_of_lt' hInput.size_lt]
          exact hIndex
        let acc :=
          ArrayFold.foldPrefix input (fun sum element => sum + element) 0 index
        let nextAcc := acc + input[index]
        let loadedState : ScalarTransition.State :=
          (AnnotationMatches.function_0_array_fold_0_state
            inputPtr acc input[index] v3 v4 v5 v6 root v8 v9 v10 inputPtr
            (UInt64.ofNat input.size) (UInt64.ofNat index)
            (UInt64.ofNat input.size) (UInt64.ofNat input.size)
            v16 v17 v18 v19 v20).toState
        let afterBody : ScalarTransition.State :=
          (AnnotationMatches.function_0_array_fold_0_state
            inputPtr nextAcc input[index] nextAcc v4 v5 v6 root v8 v9 v10
            inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
            (UInt64.ofNat input.size) (UInt64.ofNat input.size)
            0 nextAcc 1 v19 v20).toState
        apply FixedArrayFoldBody.continuingGuardedProgram_spec
          (arrayLocal := 11) (indexLocal := 13) (stopLocal := 15)
          (itemLocal := 2) (scratch := 11)
          (body := AnnotationMatches.function_0_array_fold_0_body)
          (condition := AnnotationMatches.function_0_array_fold_0_condition)
          (continuing :=
            AnnotationMatches.function_0_array_fold_0_step_continuing)
          (inputPtr := inputPtr) (indexValue := UInt64.ofNat index)
          (stopValue := UInt64.ofNat input.size)
          (input := input) (index := index)
          (stepProgram :=
            AnnotationMatches.function_0_array_fold_0_step_program)
          (initial := loadedState) (afterBody := afterBody)
          (afterCondition := afterBody) (result := false)
        · simp only [
            AnnotationMatches.function_0_array_fold_0_continuing_frame_values]
        · simp only [
            AnnotationMatches.function_0_array_fold_0_continuing_frame_get_11]
        · simp only [
            AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13]
        · simp only [
            AnnotationMatches.function_0_array_fold_0_continuing_frame_get_15]
        · rfl
        · exact hContinue
        · exact hInput
        · simpa [acc, loadedState,
              AnnotationMatches.function_0_array_fold_0_continuing_frame]
            using
            (AnnotationMatches.function_0_array_fold_0_continuing_loaded_frame_eq
              inputPtr acc v2 v3 v4 v5 v6 root v8 v9 v10 inputPtr
              (UInt64.ofNat input.size) (UInt64.ofNat index)
              (UInt64.ofNat input.size) (UInt64.ofNat input.size)
              v16 v17 v18 v19 v20 input[index])
        · rfl
        · simpa [loadedState, afterBody,
              AnnotationMatches.function_0_array_fold_0_bodyTransition,
              ScalarTransition.U64Op.apply] using
            (AnnotationMatches.function_0_array_fold_0_body_eval
              inputPtr acc input[index] v3 v4 v5 v6 root v8 v9 v10 inputPtr
              (UInt64.ofNat input.size) (UInt64.ofNat index)
              (UInt64.ofNat input.size) (UInt64.ofNat input.size)
              v16 v17 v18 v19 v20)
        · simpa [afterBody,
              AnnotationMatches.function_0_array_fold_0_conditionTransition]
            using
            (AnnotationMatches.function_0_array_fold_0_condition_eval
              inputPtr nextAcc input[index] nextAcc v4 v5 v6 root v8 v9 v10
              inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
              (UInt64.ofNat input.size) (UInt64.ofNat input.size)
              0 nextAcc 1 v19 v20)
        · simp
        · intro _
          let afterContinue : ScalarTransition.State :=
            (AnnotationMatches.function_0_array_fold_0_state
              inputPtr nextAcc input[index] nextAcc v4 v5 v6 root v8 v9 v10
              inputPtr (UInt64.ofNat input.size) (UInt64.ofNat (index + 1))
              (UInt64.ofNat input.size) (UInt64.ofNat input.size)
              0 nextAcc 1 v19 v20).toState
          refine ⟨afterContinue, ?_, ?_⟩
          · simpa [afterBody, afterContinue,
                AnnotationMatches.function_0_array_fold_0_step_continuingTransition,
                ScalarTransition.U64Op.apply, UInt64.ofNat_add] using
              (AnnotationMatches.function_0_array_fold_0_step_continuing_eval
                inputPtr nextAcc input[index] nextAcc v4 v5 v6 root v8 v9 v10
                inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                0 nextAcc 1 v19 v20)
          · change
              foldInvariant st inputPtr root input st
                  (afterContinue.toLocals []) ∧
                foldMeasure input st (afterContinue.toLocals []) <
                  foldMeasure input st
                    (AnnotationMatches.function_0_array_fold_0_continuing_frame
                      inputPtr acc v2 v3 v4 v5 v6 root v8 v9 v10 inputPtr
                      (UInt64.ofNat input.size) (UInt64.ofNat index)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      v16 v17 v18 v19 v20)
            constructor
            · refine ⟨index + 1, input[index], nextAcc, v4, v5, v6, v8,
                v9, v10, 0, nextAcc, 1, v19, v20, ?_, rfl, ?_⟩
              · omega
              · rw [ArrayFold.foldPrefix_succ input
                    (fun sum element => sum + element) 0 index hIndex]
                rfl
            · change input.size - (UInt64.ofNat (index + 1)).toNat <
                input.size - (UInt64.ofNat index).toNat
              rw [UInt64.toNat_ofNat_of_lt' hNextIndex64,
                UInt64.toNat_ofNat_of_lt' hIndex64]
              omega
        · exact
            AnnotationMatches.function_0_array_fold_0_continuing_item_valid
              inputPtr acc v2 v3 v4 v5 v6 root v8 v9 v10 inputPtr
              (UInt64.ofNat input.size) (UInt64.ofNat index)
              (UInt64.ofNat input.size) (UInt64.ofNat input.size)
              v16 v17 v18 v19 v20

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
  change wp _ func0 _ _ _ _
  rw [AnnotationMatches.function_0_length_dispatch_0_function_eq]
  wp_fixed_array_length_le_dispatch_from hArray at 7, 8
  · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  · norm_num
  · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  · norm_num [UInt64.size]
  · intro hSize
    change wp _
      (AnnotationMatches.function_0_length_dispatch_0_valid_capacity_program ++ _)
      _ _ _ _
    apply FixedArrayCapacity.constantProgram_spec
    · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero,
        FixedArrayLengthDispatch.branchFrame]
    · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero,
        FixedArrayLengthDispatch.branchFrame, Wasm.Locals.validIndex]
    · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero,
        FixedArrayLengthDispatch.branchFrame, Wasm.Locals.validIndex]
    change wp _ (FixedArrayAllocatorWindow.region 2 1 ++ _) _ _ _ _
    apply FixedArrayAllocatorWindow.region_spec_withTail
      (offset := 2) (tail := 4) (heapTop := heapTop) (capacity := 16)
      (stride := 1) (allocs := allocs)
    · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero,
        FixedArrayLengthDispatch.branchFrame, FixedArrayCapacity.capacityFrame]
    · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero,
        FixedArrayLengthDispatch.branchFrame, FixedArrayCapacity.capacityFrame]
    · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero,
        FixedArrayLengthDispatch.branchFrame, FixedArrayCapacity.capacityFrame]
    · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero,
        FixedArrayLengthDispatch.branchFrame, FixedArrayCapacity.capacityFrame,
        FixedArrayCapacity.normalizedCapacity,
        FixedArrayCapacity.unnormalizedCapacity] <;> native_decide
    · decide
    · simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · let allocSt :=
        FixedArrayAllocator.allocStore initial heapTop 16 1 allocs
      let allocFrame := FixedArrayAllocatorWindow.allocFrame 2
        (FixedArrayCapacity.capacityFrame
          (FixedArrayLengthDispatch.branchFrame 7
            (func0Def.toLocals
              (List.take func0Def.numParams [.i64 inputPtr]).reverse)
            inputPtr)
          11 (FixedArrayCapacity.normalizedCapacity 1 1))
        heapTop 16
      have hFit :
          heapTop.toNat + 48 + 16 ≤ initial.mem.pages * 65536 := by
        simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
      have hFacts := Allocation.bumpFacts heapTop 16 initial.mem.pages
        hFit hPages
      have hRootAddressNat :
          (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
        simpa using hFacts.wordAddress_toNat 0 (by decide)
      have hPayloadAddressNat :
          (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat =
            heapTop.toNat + 48 + 8 := by
        simpa [FixedArrayResult.payloadAddress] using
          hFacts.wordAddress_toNat 1 (by decide)
      have hAllocValues : allocFrame.values = [] := by
        simp [allocFrame, FixedArrayAllocatorWindow.allocFrame,
          FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero]
      have hAllocParams : allocFrame.params = [.i64 inputPtr] := by
        simp [allocFrame, FixedArrayAllocatorWindow.allocFrame,
          FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero]
      have hAllocLocals : allocFrame.locals.length = 20 := by
        simp [allocFrame, FixedArrayAllocatorWindow.allocFrame,
          FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero]
      have hRoot : allocFrame.get 7 = some (.i64 (heapTop + 48)) := by
        simp [allocFrame, FixedArrayAllocatorWindow.allocFrame,
          FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero,
          Wasm.Locals.get]
      have hScalarFrame :
          ∃ (v1 v2 v3 v4 v5 v6 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
              v18 v19 v20 : UInt64),
            allocFrame =
              AnnotationMatches.function_0_array_fold_0_continuing_frame
                inputPtr v1 v2 v3 v4 v5 v6 (heapTop + 48) v8 v9 v10 v11
                v12 v13 v14 v15 v16 v17 v18 v19 v20 := by
        refine ⟨0, 0, 0, 0, 0, 0, 0, 0, 0,
          FixedArrayCapacity.normalizedCapacity 1 1, 0, 0,
          heapTop + 48 + 16, (heapTop + 48 + 16 - 1) / 65536 + 1,
          heapTop + 48, 0, 0, 0, 0, ?_⟩
        simp [allocFrame, FixedArrayAllocatorWindow.allocFrame,
          FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero,
          AnnotationMatches.function_0_array_fold_0_continuing_frame,
          AnnotationMatches.function_0_array_fold_0_state,
          ScalarTransition.U64State.toState]
      have hInputAlloc : UInt64Array.At allocSt inputPtr input := by
        exact FixedArrayPairResult.input_preserved_by_alloc initial heapTop
          16 1 allocs inputPtr input hArray hInputBelow hFit hPages
      have hInputAfterLength : UInt64Array.At
          (FixedArrayResult.writeLength allocSt (heapTop + 48) 1)
          inputPtr input := by
        exact hInputAlloc.write64After
          (address := (heapTop + 48).toUInt32) (value := 1)
          (by rw [hRootAddressNat]; omega)
      have hRootBound :
          (heapTop + 48).toUInt32.toNat + 8 ≤
            allocSt.mem.pages * 65536 := by
        rw [hRootAddressNat]
        simp only [allocSt, FixedArrayAllocator.allocStore_pages]
        omega
      have hPayloadBound :
          (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat +
              8 ≤
            (FixedArrayResult.writeLength allocSt (heapTop + 48) 1).mem.pages *
              65536 := by
        rw [hPayloadAddressNat]
        simp only [FixedArrayResult.writeLength_pages, allocSt,
          FixedArrayAllocator.allocStore_pages]
        omega
      have hSingleton : UInt64Array.At
          (FixedArrayResult.writePayload
            (FixedArrayResult.writeLength allocSt (heapTop + 48) 1)
            (heapTop + 48) 0
            (input.foldl (fun sum element => sum + element) 0))
          (heapTop + 48)
          #[input.foldl (fun sum element => sum + element) 0] := by
        apply FixedArrayResult.singletonStore_at
        · rw [hFacts.rootToNat]
          exact hFacts.fit32
        · simp only [allocSt, FixedArrayAllocator.allocStore_pages]
          rw [hFacts.rootToNat]
          exact hFit
      change wp module
        (FixedArrayResult.lengthStoreProgram 7 1 ++ foldProgram)
        (FixedArrayEqNode.branchPost module env
          AnnotationMatches.function_0_length_dispatch_0_suffix_program _)
        allocSt allocFrame env
      apply FixedArrayResult.lengthStore_spec
      · exact hAllocValues
      · exact hRoot
      · exact hRootBound
      · apply Wasm.wp.conseq
          (Q := FixedArrayFold.singletonResultPost 6 (heapTop + 48)
            (input.foldl (fun sum element => sum + element) 0))
        · intro continuation hResult
          cases continuation
          case Fallthrough final resultFrame =>
            rcases hResult with ⟨hReturn, hResultArray⟩
            simp only [FixedArrayEqNode.branchPost]
            have hReturn' :
                ({ resultFrame with values := [] } : Locals).get 6 =
                  some (.i64 (heapTop + 48)) := by
              simpa only [Wasm.Locals.get] using hReturn
            unfold
              AnnotationMatches.function_0_length_dispatch_0_suffix_program
            simp only [wp_localGet_cons, hReturn', Wasm.wp_nil]
            refine ⟨heapTop + 48, ?_, ?_⟩
            · norm_num [func0Def, Function.numParams]
            · change UInt64Array.At _ _ _
              simpa [FormalSpec.expected, hSize] using hResultArray
          all_goals
            simp only [FixedArrayFold.singletonResultPost] at hResult
        · exact foldProgram_spec module env
            (FixedArrayResult.writeLength allocSt (heapTop + 48) 1)
            allocFrame inputPtr (heapTop + 48) input hAllocParams
            hAllocLocals hAllocValues hInputAfterLength hScalarFrame hRoot
            hPayloadBound hSingleton
  · intro hSize
    change wp _
      (AnnotationMatches.function_0_length_dispatch_0_invalid_capacity_program ++ _)
      _ _ _ _
    apply FixedArrayCapacity.constantProgram_spec
    · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero,
        FixedArrayLengthDispatch.branchFrame]
    · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero,
        FixedArrayLengthDispatch.branchFrame, Wasm.Locals.validIndex]
    · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero,
        FixedArrayLengthDispatch.branchFrame, Wasm.Locals.validIndex]
    change wp _ (FixedArrayAllocatorWindow.region 2 1 ++ _) _ _ _ _
    apply FixedArrayAllocatorWindow.region_spec_withTail
      (offset := 2) (tail := 4) (heapTop := heapTop) (capacity := 8)
      (stride := 1) (allocs := allocs)
    · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero,
        FixedArrayLengthDispatch.branchFrame, FixedArrayCapacity.capacityFrame]
    · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero,
        FixedArrayLengthDispatch.branchFrame, FixedArrayCapacity.capacityFrame]
    · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero,
        FixedArrayLengthDispatch.branchFrame, FixedArrayCapacity.capacityFrame]
    · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero,
        FixedArrayLengthDispatch.branchFrame, FixedArrayCapacity.capacityFrame,
        FixedArrayCapacity.normalizedCapacity,
        FixedArrayCapacity.unnormalizedCapacity] <;> native_decide
    · decide
    · simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · let allocSt :=
        FixedArrayAllocator.allocStore initial heapTop 8 1 allocs
      let allocFrame := FixedArrayAllocatorWindow.allocFrame 2
        (FixedArrayCapacity.capacityFrame
          (FixedArrayLengthDispatch.branchFrame 7
            (func0Def.toLocals
              (List.take func0Def.numParams [.i64 inputPtr]).reverse)
            inputPtr)
          11 (FixedArrayCapacity.normalizedCapacity 0 1))
        heapTop 8
      have hFit : heapTop.toNat + 48 + 8 ≤ initial.mem.pages * 65536 := by
        simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
      have hFacts := Allocation.bumpFacts heapTop 8 initial.mem.pages hFit hPages
      have hRootAddressNat :
          (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
        simpa using hFacts.wordAddress_toNat 0 (by decide)
      have hAllocValues : allocFrame.values = [] := by
        simp [allocFrame, FixedArrayAllocatorWindow.allocFrame,
          FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero]
      have hAllocParams : allocFrame.params.length = 1 := by
        simp [allocFrame, FixedArrayAllocatorWindow.allocFrame,
          FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero]
      have hAllocLocals : allocFrame.locals.length = 20 := by
        simp [allocFrame, FixedArrayAllocatorWindow.allocFrame,
          FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero]
      have hRoot : allocFrame.get 7 = some (.i64 (heapTop + 48)) := by
        simp [allocFrame, FixedArrayAllocatorWindow.allocFrame,
          FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero,
          Wasm.Locals.get]
      have hRootBound :
          (heapTop + 48).toUInt32.toNat + 8 ≤
            allocSt.mem.pages * 65536 := by
        rw [hRootAddressNat]
        simp only [allocSt, FixedArrayAllocator.allocStore_pages]
        omega
      have hEmpty : UInt64Array.At
          (FixedArrayResult.writeLength allocSt (heapTop + 48) 0)
          (heapTop + 48) #[] := by
        apply FixedArrayResult.emptyStore_at
        · rw [hFacts.rootToNat]
          omega
        · simp only [allocSt, FixedArrayAllocator.allocStore_pages]
          rw [hFacts.rootToNat]
          omega
      change wp module
        (FixedArrayResult.lengthStoreProgram 7 0 ++
          FixedArrayResult.finishProgram 7 5 6) _ allocSt allocFrame env
      apply FixedArrayResult.lengthStore_spec
      · exact hAllocValues
      · exact hRoot
      · exact hRootBound
      · apply FixedArrayResult.finishProgram_spec
        · exact hAllocValues
        · exact hRoot
        · simpa [hAllocParams]
        · simpa [Wasm.Locals.validIndex, hAllocParams, hAllocLocals]
        · simpa [hAllocParams]
        · simpa [Wasm.Locals.validIndex, hAllocParams, hAllocLocals]
        · rw [Wasm.wp_nil]
          simp only [FixedArrayEqNode.branchPost]
          have hReturn := FixedArrayResult.finishFrame_return_get
            allocFrame 5 6 (heapTop + 48) (by simpa [hAllocParams])
            (by simpa [Wasm.Locals.validIndex, hAllocParams, hAllocLocals])
          have hReturn' :
              ({ FixedArrayResult.finishFrame allocFrame 5 6 (heapTop + 48) with
                values := [] } : Locals).get 6 =
                some (.i64 (heapTop + 48)) := by
            simpa only [Wasm.Locals.get] using hReturn
          unfold AnnotationMatches.function_0_length_dispatch_0_suffix_program
          simp only [wp_localGet_cons, hReturn', Wasm.wp_nil]
          refine ⟨heapTop + 48, ?_, ?_⟩
          · norm_num [func0Def, Function.numParams]
          · change UInt64Array.At _ _ _
            simpa [FormalSpec.expected, hSize] using hEmpty

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior
