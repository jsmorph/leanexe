import LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec
import LeanExeGen.GeneratedR23fa7efc3fb0298b.Program
import LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.Allocation
import Project.ProofKit.Control
import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayCapacity
import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArrayFold
import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArrayResult
import Project.ProofKit.FixedArrayTraversalInput
import Project.ProofKit.Frame
import Project.ProofKit.GuardedBackEdge
import Project.ProofKit.ScalarTransition

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior

open Wasm Project.ProofKit

def sumPrefix (input : Array UInt64) (index : Nat) : UInt64 :=
  ArrayFold.foldPrefix input (fun sum element => sum + element) 0 index

def FoldInv (root inputPtr : UInt64) (input : Array UInt64)
    (frame : Locals) : Prop :=
  ∃ index : Nat, ∃ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
      v15 v16 v17 v18 v19 v20 : UInt64,
    index ≤ input.size ∧
    frame = (AnnotationMatches.function_0_array_fold_0_state
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
      v17 v18 v19 v20).toState.toLocals [] ∧
    v0 = inputPtr ∧
    v1 = sumPrefix input index ∧
    v7 = root ∧
    v11 = inputPtr ∧
    v13 = UInt64.ofNat index ∧
    v15 = UInt64.ofNat input.size

def foldMeasure (input : Array UInt64) (frame : Locals) : Nat :=
  match frame.get 13 with
  | some (.i64 index) => input.size - index.toNat
  | _ => 0

theorem input_preserved_by_alloc
    (st : Store Unit) (heapTop capacity stride allocs inputPtr : UInt64)
    (input : Array UInt64)
    (hInput : UInt64Array.At st inputPtr input)
    (hInputBelow : inputPtr.toNat + 8 * (input.size + 1) ≤ heapTop.toNat)
    (hFitMemory : heapTop.toNat + 48 + capacity.toNat ≤
      st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536) :
    UInt64Array.At
      (FixedArrayAllocator.allocStore st heapTop capacity stride allocs)
      inputPtr input := by
  have hFacts := Allocation.bumpFacts heapTop capacity st.mem.pages
    hFitMemory hPages
  apply hInput.frameBefore hInputBelow
  · exact FixedArrayAllocator.allocStore_pages st heapTop capacity stride allocs
  · intro address hAddress
    simp only [FixedArrayAllocator.allocStore, FixedArrayAllocator.headerMem]
    rw [Memory.write64_bytes_before _ _ _ (by simp; omega)]
    rw [Memory.write64_bytes_before _ _ _ (by simp; omega)]
    rw [Memory.write64_bytes_before _ _ _ (by simp; omega)]
    rw [Memory.write64_bytes_before _ _ _ (by simp; omega)]
    rw [Memory.write64_bytes_before _ _ _ (by simp; omega)]
    rw [Memory.write64_bytes_before _ _ _ (by simp; omega)]

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
  · decide
  · simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  · decide
  case hValid =>
    intro hSize
    have hFitMemory16 : heapTop.toNat + 48 + 16 ≤
        initial.mem.pages * 65536 := by
      simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
    have hFacts := Allocation.bumpFacts heapTop 16 initial.mem.pages
      hFitMemory16 hPages
    have hArrayAlloc := input_preserved_by_alloc initial heapTop 16 1 allocs
      inputPtr input hArray hInputBelow hFitMemory16 hPages
    change wp module
      (AnnotationMatches.function_0_length_dispatch_0_valid_capacity_program ++ _)
      _ initial _ env
    unfold AnnotationMatches.function_0_length_dispatch_0_valid_capacity_program
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero,
        Wasm.Locals.validIndex]
    · change wp module (FixedArrayAllocatorWindow.region 2 1 ++ _)
        _ initial _ env
      apply FixedArrayAllocatorWindow.region_spec_withTail
        (offset := 2) (tail := 4) (heapTop := heapTop)
        (capacity := 16) (stride := 1) (allocs := allocs)
      · simp [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero]
      · simp [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero]
      · rfl
      · simp [FixedArrayCapacity.capacityFrame,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero]
      · decide
      · exact hFitMemory16
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · apply FixedArrayResult.lengthStore_spec
          (root := heapTop + 48) (length := 1) (rootLocal := 7)
        · rfl
        · simp [FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayCapacity.normalizedCapacity,
            FixedArrayCapacity.unnormalizedCapacity,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Function.toLocals, Function.numParams, ValueType.zero,
            Wasm.Locals.get]
        · have hRootAddress : (heapTop + 48).toUInt32.toNat =
              heapTop.toNat + 48 := by
            convert hFacts.wordAddress_toNat 0 (by decide) using 1 <;> norm_num
          rw [hRootAddress, FixedArrayAllocator.allocStore_pages]
          omega
        · have hRootAddress : (heapTop + 48).toUInt32.toNat =
              heapTop.toNat + 48 := by
            convert hFacts.wordAddress_toNat 0 (by decide) using 1 <;> norm_num
          have hArrayLength : UInt64Array.At
              (FixedArrayResult.writeLength
                (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                (heapTop + 48) 1) inputPtr input := by
            simpa [FixedArrayResult.writeLength] using
              hArrayAlloc.write64After (address := (heapTop + 48).toUInt32)
                (value := 1) (by rw [hRootAddress]; omega)
          change wp module
            (AnnotationMatches.function_0_array_fold_0_setup_program ++ _)
            _ _ _ env
          unfold AnnotationMatches.function_0_array_fold_0_setup_program
          apply FixedArrayFold.forwardSetupProgram_spec
            (inputPtr := inputPtr) (input := input)
          · simp [FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Function.toLocals, Function.numParams, ValueType.zero]
          · rfl
          · intro slot hSlot
            have hLocals : (FixedArrayAllocatorWindow.allocFrame 2
                (FixedArrayCapacity.capacityFrame
                  (FixedArrayLengthDispatch.branchFrame 7
                    (func0Def.toLocals
                      (List.take func0Def.numParams [.i64 inputPtr]).reverse)
                    inputPtr)
                  11 (FixedArrayCapacity.normalizedCapacity 1 1))
                heapTop 16).locals.length = 20 := by
              simp [FixedArrayAllocatorWindow.allocFrame,
                FixedArrayCapacity.capacityFrame,
                FixedArrayLengthDispatch.branchFrame, func0Def,
                Function.toLocals, Function.numParams, ValueType.zero]
            simp [FixedArrayFold.setupLocals] at hSlot
            omega
          · decide
          · exact hArrayLength
          · apply Wasm.wp_block_cons
            apply Wasm.wp_loop_cons
              (Inv := fun st frame =>
                st = FixedArrayResult.writeLength
                  (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                  (heapTop + 48) 1 ∧ FoldInv (heapTop + 48) inputPtr input frame)
              (μ := fun _ frame => foldMeasure input frame)
            · refine ⟨rfl, ?_⟩
              unfold FoldInv
              refine ⟨0, inputPtr, 0, 0, 0, 0, 0, 0, heapTop + 48,
                0, 0, 0, inputPtr, UInt64.ofNat input.size, 0,
                UInt64.ofNat input.size, UInt64.ofNat input.size, inputPtr,
                0, 0, 0, 0, ?_⟩
              refine ⟨by omega, ?_, rfl, ?_, rfl, rfl, rfl, rfl⟩
              · simp [FixedArrayFold.forwardSetupFrame,
                  AnnotationMatches.function_0_array_fold_0_state,
                  ScalarTransition.U64State.toState,
                  ScalarTransition.State.toLocals,
                  FixedArrayAllocatorWindow.allocFrame,
                  FixedArrayCapacity.capacityFrame,
                  FixedArrayCapacity.normalizedCapacity,
                  FixedArrayCapacity.unnormalizedCapacity,
                  FixedArrayLengthDispatch.branchFrame, func0Def,
                  Function.toLocals, Function.numParams, ValueType.zero]
              · simp [sumPrefix, ArrayFold.foldPrefix]
            · rintro st frame ⟨rfl, hInv⟩
              rcases hInv with
                ⟨index, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10,
                  v11, v12, v13, v14, v15, v16, v17, v18, v19, v20,
                  hIndex, hFrame, hv0, hv1, hv7, hv11, hv13, hv15⟩
              subst frame
              subst v0
              subst v1
              subst v7
              subst v11
              subst v13
              subst v15
              by_cases hDone : index = input.size
              · subst index
                change wp module
                  (AnnotationMatches.function_0_array_fold_0_continuing_program ++ _)
                  _ _ _ env
                unfold AnnotationMatches.function_0_array_fold_0_continuing_program
                apply FixedArrayTraversalInput.continuingProgram_exit_spec
                  (index := UInt64.ofNat input.size)
                · rfl
                · simp [AnnotationMatches.function_0_array_fold_0_state,
                    ScalarTransition.U64State.toState,
                    ScalarTransition.State.toLocals, Wasm.Locals.get]
                · simp [AnnotationMatches.function_0_array_fold_0_state,
                    ScalarTransition.U64State.toState,
                    ScalarTransition.State.toLocals, Wasm.Locals.get]
                · change wp module
                    (AnnotationMatches.function_0_array_fold_0_result_program ++ _)
                    _ _ _ env
                  unfold AnnotationMatches.function_0_array_fold_0_result_program
                  apply FixedArrayFold.resultProgram_spec
                    (value := sumPrefix input input.size)
                  · rfl
                  · simp [AnnotationMatches.function_0_array_fold_0_state,
                      ScalarTransition.U64State.toState,
                      ScalarTransition.State.toLocals, Wasm.Locals.get]
                  · simp [AnnotationMatches.function_0_array_fold_0_state,
                      ScalarTransition.U64State.toState]
                  · simp [Wasm.Locals.validIndex,
                      AnnotationMatches.function_0_array_fold_0_state,
                      ScalarTransition.U64State.toState]
                  · apply FixedArrayResult.payloadStore_spec
                      (root := heapTop + 48)
                      (value := sumPrefix input input.size)
                      (rootLocal := 7) (scratchLocal := 10) (index := 0)
                    · simp [FixedArrayFold.resultFrame,
                        AnnotationMatches.function_0_array_fold_0_state,
                        ScalarTransition.U64State.toState,
                        ScalarTransition.State.toLocals, Wasm.Locals.get]
                    · simp [FixedArrayFold.resultFrame,
                        AnnotationMatches.function_0_array_fold_0_state,
                        ScalarTransition.U64State.toState,
                        ScalarTransition.State.toLocals, Wasm.Locals.get]
                    · have hPayloadAddress :
                          (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat =
                            heapTop.toNat + 56 := by
                        convert hFacts.wordAddress_toNat 1 (by decide) using 1 <;>
                          simp [FixedArrayResult.payloadAddress]
                      rw [hPayloadAddress, FixedArrayResult.writeLength_pages,
                        FixedArrayAllocator.allocStore_pages]
                      omega
                    · have hRootFit32 : (heapTop + 48).toNat + 16 ≤
                          4294967296 := by
                        rw [hFacts.rootToNat]
                        simpa [FormalSpec.expected, hSize] using hOutputFit32
                      have hRootFitMemory : (heapTop + 48).toNat + 16 ≤
                          (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs).mem.pages *
                            65536 := by
                        rw [hFacts.rootToNat,
                          FixedArrayAllocator.allocStore_pages]
                        simpa [FormalSpec.expected, hSize] using hOutputFitMemory
                      have hOutput := FixedArrayResult.singletonStore_at
                        (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                        (heapTop + 48) (sumPrefix input input.size)
                        hRootFit32 hRootFitMemory
                      apply FixedArrayResult.finishProgram_spec
                        (root := heapTop + 48) (rootLocal := 7)
                        (destinationLocal := 4) (returnLocal := 6)
                      · rfl
                      · simp [FixedArrayFold.resultFrame,
                          AnnotationMatches.function_0_array_fold_0_state,
                          ScalarTransition.U64State.toState,
                          ScalarTransition.State.toLocals, Wasm.Locals.get]
                      · simp [FixedArrayFold.resultFrame,
                          AnnotationMatches.function_0_array_fold_0_state,
                          ScalarTransition.U64State.toState]
                      · simp [Wasm.Locals.validIndex, FixedArrayFold.resultFrame,
                          AnnotationMatches.function_0_array_fold_0_state,
                          ScalarTransition.U64State.toState]
                      · simp [FixedArrayFold.resultFrame,
                          AnnotationMatches.function_0_array_fold_0_state,
                          ScalarTransition.U64State.toState]
                      · simp [Wasm.Locals.validIndex, FixedArrayFold.resultFrame,
                          AnnotationMatches.function_0_array_fold_0_state,
                          ScalarTransition.U64State.toState]
                      · rw [wp_nil]
                        simp only [FixedArrayEqNode.branchPost]
                        wp_run
                        simp [FixedArrayResult.finishFrame,
                          FixedArrayFold.resultFrame,
                          AnnotationMatches.function_0_array_fold_0_state,
                          ScalarTransition.U64State.toState,
                          ScalarTransition.State.toLocals, Wasm.Locals.get]
                        refine ⟨heapTop + 48, ?_, ?_⟩
                        · simp [func0Def, Function.numParams]
                        · change UInt64Array.At _ (heapTop + 48)
                            (FormalSpec.expected input)
                          simpa [FormalSpec.expected, hSize, sumPrefix,
                            ArrayFold.foldPrefix_size,
                            FixedArrayResult.singletonStore] using hOutput
              · have hIndexLt : index < input.size := by omega
                change wp module
                  (AnnotationMatches.function_0_array_fold_0_continuing_program ++ _)
                  _ _ _ env
                unfold AnnotationMatches.function_0_array_fold_0_continuing_program
                have hIndex64 : index < UInt64.size := by
                  have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
                  omega
                have hSize64 : input.size < UInt64.size := by
                  have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
                  omega
                have hContinueEncoded :
                    UInt64.ofNat index < UInt64.ofNat input.size := by
                  rw [UInt64.lt_iff_toNat_lt,
                    UInt64.toNat_ofNat_of_lt' hIndex64,
                    UInt64.toNat_ofNat_of_lt' hSize64]
                  exact hIndexLt
                apply FixedArrayTraversalInput.continuingProgram_spec
                  (inputPtr := inputPtr) (input := input) (index := index)
                  (indexValue := UInt64.ofNat index)
                  (stopValue := UInt64.ofNat input.size)
                  (hValues := by rfl)
                  (hArrayLocal := by
                    simp [AnnotationMatches.function_0_array_fold_0_state,
                      ScalarTransition.U64State.toState,
                      ScalarTransition.State.toLocals, Wasm.Locals.get])
                  (hIndexLocal := by
                    simp [AnnotationMatches.function_0_array_fold_0_state,
                      ScalarTransition.U64State.toState,
                      ScalarTransition.State.toLocals, Wasm.Locals.get])
                  (hStopLocal := by
                    simp [AnnotationMatches.function_0_array_fold_0_state,
                      ScalarTransition.U64State.toState,
                      ScalarTransition.State.toLocals, Wasm.Locals.get])
                  (hIndexValue := rfl)
                  (hContinue := hContinueEncoded)
                  (hItem := by change 2 < 21; decide)
                  (hInput := hArrayLength) (hIndex := hIndexLt)
                change wp module
                  (AnnotationMatches.function_0_array_fold_0_step_program ++ _)
                  _ _
                  ((AnnotationMatches.function_0_array_fold_0_state
                    inputPtr (sumPrefix input index) input[index] v3 v4 v5 v6
                    (heapTop + 48) v8 v9 v10 inputPtr v12
                    (UInt64.ofNat index) v14 (UInt64.ofNat input.size)
                    v16 v17 v18 v19 v20).toState.toLocals []) env
                unfold AnnotationMatches.function_0_array_fold_0_step_program
                have hNextValue : UInt64.ofNat index + 1 =
                    UInt64.ofNat (index + 1) := by
                  change UInt64.ofNat index + UInt64.ofNat 1 =
                    UInt64.ofNat (index + 1)
                  rw [← UInt64.ofNat_add]
                let nextSum : UInt64 := sumPrefix input index + input[index]
                let loaded : ScalarTransition.State :=
                  (AnnotationMatches.function_0_array_fold_0_state
                    inputPtr (sumPrefix input index) input[index] v3 v4 v5 v6
                    (heapTop + 48) v8 v9 v10 inputPtr v12
                    (UInt64.ofNat index) v14 (UInt64.ofNat input.size)
                    v16 v17 v18 v19 v20).toState
                let afterBody : ScalarTransition.State :=
                  (AnnotationMatches.function_0_array_fold_0_state
                    inputPtr nextSum input[index] nextSum v4 v5 v6
                    (heapTop + 48) v8 v9 v10 inputPtr v12
                    (UInt64.ofNat index) v14 (UInt64.ofNat input.size)
                    0 nextSum 1 v19 v20).toState
                let afterContinue : ScalarTransition.State :=
                  (AnnotationMatches.function_0_array_fold_0_state
                    inputPtr nextSum input[index] nextSum v4 v5 v6
                    (heapTop + 48) v8 v9 v10 inputPtr v12
                    (UInt64.ofNat (index + 1)) v14 (UInt64.ofNat input.size)
                    0 nextSum 1 v19 v20).toState
                apply ScalarTransition.guardedBackEdgeProgram_spec
                  (initial := loaded) (afterBody := afterBody)
                  (afterCondition := afterBody) (result := false)
                  (values := [])
                · simpa [loaded, afterBody, nextSum,
                    AnnotationMatches.function_0_array_fold_0_bodyTransition,
                    ScalarTransition.U64Op.apply] using
                    (AnnotationMatches.function_0_array_fold_0_body_eval
                      inputPtr (sumPrefix input index) input[index]
                      v3 v4 v5 v6 (heapTop + 48) v8 v9 v10 inputPtr v12
                      (UInt64.ofNat index) v14 (UInt64.ofNat input.size)
                      v16 v17 v18 v19 v20)
                · simpa [afterBody,
                    AnnotationMatches.function_0_array_fold_0_conditionTransition]
                    using
                    (AnnotationMatches.function_0_array_fold_0_condition_eval
                      inputPtr nextSum input[index] nextSum v4 v5 v6
                      (heapTop + 48) v8 v9 v10 inputPtr v12
                      (UInt64.ofNat index) v14 (UInt64.ofNat input.size)
                      0 nextSum 1 v19 v20)
                · simp
                · intro _
                  refine ⟨afterContinue, ?_, ?_⟩
                  · unfold afterBody afterContinue
                    rw [ScalarTransition.Stmt.eval_toState]
                    simp (config := { maxSteps := 1000000 }) only
                      [AnnotationMatches.function_0_array_fold_0_step_continuing,
                        AnnotationMatches.function_0_array_fold_0_state,
                        ScalarTransition.Stmt.evalU64,
                        ScalarTransition.Expr.evalU64,
                        ScalarTransition.U64State.get,
                        ScalarTransition.U64State.set?,
                        ScalarTransition.U64Op.apply, Option.bind,
                        Option.pure_def, Option.bind_eq_bind,
                        Option.bind_some, Option.bind_none, Option.map,
                        List.length, List.getElem?_cons_zero,
                        List.getElem?_cons_succ, List.set, Nat.reduceAdd,
                        Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true,
                        true_or, or_false, false_or, Bool.false_eq_true,
                        Bool.not_eq_true', Bool.not_true, Bool.not_false,
                        beq_self_eq_true,
                        ScalarTransition.u64_one_beq_zero,
                        ScalarTransition.u64_zero_beq_one, decide_true,
                        decide_false, if_true, if_false, hNextValue]
                  · change
                      ((FixedArrayResult.writeLength
                            (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                            (heapTop + 48) 1 =
                          FixedArrayResult.writeLength
                            (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                            (heapTop + 48) 1 ∧
                        FoldInv (heapTop + 48) inputPtr input
                          (afterContinue.toLocals [])) ∧
                        foldMeasure input (afterContinue.toLocals []) <
                          foldMeasure input (loaded.toLocals []))
                    refine ⟨⟨rfl, ?_⟩, ?_⟩
                    · unfold FoldInv
                      refine ⟨index + 1, inputPtr, nextSum, input[index],
                        nextSum, v4, v5, v6, heapTop + 48, v8, v9, v10,
                        inputPtr, v12, UInt64.ofNat (index + 1), v14,
                        UInt64.ofNat input.size, 0, nextSum, 1, v19, v20, ?_⟩
                      refine ⟨by omega, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
                      simpa [nextSum, sumPrefix] using
                        (ArrayFold.foldPrefix_succ input
                          (fun sum element => sum + element) 0 index hIndexLt).symm
                    · have hNext64 : index + 1 < UInt64.size := by
                        have hUInt64Size :
                            UInt64.size = 18446744073709551616 := rfl
                        omega
                      simp [foldMeasure, afterContinue, loaded,
                        AnnotationMatches.function_0_array_fold_0_state,
                        ScalarTransition.U64State.toState,
                        ScalarTransition.State.toLocals,
                        ScalarTransition.State.get,
                        UInt64.toNat_ofNat_of_lt' hIndex64,
                        UInt64.toNat_ofNat_of_lt' hNext64]
                      omega
  case hInvalid =>
    intro hSize
    have hFitMemory8 : heapTop.toNat + 48 + 8 ≤
        initial.mem.pages * 65536 := by
      simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
    have hFacts := Allocation.bumpFacts heapTop 8 initial.mem.pages
      hFitMemory8 hPages
    change wp module
      (AnnotationMatches.function_0_length_dispatch_0_invalid_capacity_program ++ _)
      _ initial _ env
    unfold AnnotationMatches.function_0_length_dispatch_0_invalid_capacity_program
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero,
        Wasm.Locals.validIndex]
    · change wp module (FixedArrayAllocatorWindow.region 2 1 ++ _)
        _ initial _ env
      apply FixedArrayAllocatorWindow.region_spec_withTail
        (offset := 2) (tail := 4) (heapTop := heapTop)
        (capacity := 8) (stride := 1) (allocs := allocs)
      · simp [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero]
      · simp [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero]
      · rfl
      · simp [FixedArrayCapacity.capacityFrame,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Function.toLocals, Function.numParams, ValueType.zero]
      · decide
      · exact hFitMemory8
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · apply FixedArrayResult.lengthStore_spec
          (root := heapTop + 48) (length := 0) (rootLocal := 7)
        · rfl
        · simp [FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayCapacity.normalizedCapacity,
            FixedArrayCapacity.unnormalizedCapacity,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Function.toLocals, Function.numParams, ValueType.zero,
            Wasm.Locals.get]
        · have hRootAddress : (heapTop + 48).toUInt32.toNat =
              heapTop.toNat + 48 := by
            convert hFacts.wordAddress_toNat 0 (by decide) using 1 <;> norm_num
          rw [hRootAddress, FixedArrayAllocator.allocStore_pages]
          exact hFitMemory8
        · have hRootFit32 : (heapTop + 48).toNat + 8 ≤ 4294967296 := by
            rw [hFacts.rootToNat]
            exact hFacts.fit32
          have hRootFitMemory : (heapTop + 48).toNat + 8 ≤
              (FixedArrayAllocator.allocStore initial heapTop 8 1 allocs).mem.pages *
                65536 := by
            rw [hFacts.rootToNat, FixedArrayAllocator.allocStore_pages]
            exact hFitMemory8
          have hOutput := FixedArrayResult.emptyStore_at
            (FixedArrayAllocator.allocStore initial heapTop 8 1 allocs)
            (heapTop + 48) hRootFit32 hRootFitMemory
          apply FixedArrayResult.finishProgram_spec
            (root := heapTop + 48) (rootLocal := 7)
            (destinationLocal := 5) (returnLocal := 6)
          · rfl
          · simp [FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayCapacity.normalizedCapacity,
              FixedArrayCapacity.unnormalizedCapacity,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Function.toLocals, Function.numParams, ValueType.zero,
              Wasm.Locals.get]
          · simp [FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Function.toLocals, Function.numParams, ValueType.zero]
          · simp [Wasm.Locals.validIndex,
              FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Function.toLocals, Function.numParams, ValueType.zero]
          · simp [FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Function.toLocals, Function.numParams, ValueType.zero]
          · simp [Wasm.Locals.validIndex,
              FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Function.toLocals, Function.numParams, ValueType.zero]
          · rw [wp_nil]
            simp only [FixedArrayEqNode.branchPost]
            wp_run
            simp [FixedArrayResult.finishFrame,
              FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayCapacity.normalizedCapacity,
              FixedArrayCapacity.unnormalizedCapacity,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Function.toLocals, Function.numParams, ValueType.zero,
              Wasm.Locals.get]
            change UInt64Array.At _ (heapTop + 48) (FormalSpec.expected input)
            simpa [FormalSpec.expected, hSize] using hOutput

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior
