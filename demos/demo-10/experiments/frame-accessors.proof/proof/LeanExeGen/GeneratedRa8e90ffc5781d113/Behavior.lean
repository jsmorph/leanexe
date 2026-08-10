import LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec
import LeanExeGen.GeneratedRa8e90ffc5781d113.Program
import LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches
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

namespace LeanExeGen.GeneratedRa8e90ffc5781d113.Behavior

open Wasm Project.ProofKit

private def productPrefix (input : Array UInt64) (index : Nat) : UInt64 :=
  Project.ProofKit.ArrayFold.foldPrefix input
    (fun product element => product * element) 1 index

private def productFrame (inputPtr root : UInt64) (input : Array UInt64)
    (index : Nat) (item temporary done staged releaseReady : UInt64) :
    Wasm.Locals :=
  LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame
    inputPtr (productPrefix input index) item temporary 0 0 0 root 0 0 0
    inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
    (UInt64.ofNat input.size) (UInt64.ofNat input.size) done staged
    releaseReady 0 0

private def productInv (foldStore : Wasm.Store Unit) (inputPtr root : UInt64)
    (input : Array UInt64) : Wasm.Store Unit → Wasm.Locals → Prop :=
  fun st frame => st = foldStore ∧
    ∃ index item temporary done staged releaseReady,
      index ≤ input.size ∧
      frame = productFrame inputPtr root input index item temporary done
        staged releaseReady

private def productMeasure (input : Array UInt64) (_st : Wasm.Store Unit)
    (frame : Wasm.Locals) : Nat :=
  match frame.get 13 with
  | some (.i64 index) => input.size - index.toNat
  | _ => 0

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
  apply Wasm.TerminatesWith.of_wp_entry_for (f :=
    LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def) rfl
  change Wasm.wp _ LeanExeGen.GeneratedRa8e90ffc5781d113.func0 _ initial _ env
  rw [LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_length_dispatch_0_function_eq]
  wp_fixed_array_length_le_dispatch_from hArray at 7, 8
  · rfl
  · rfl
  · norm_num
  · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
      Wasm.Function.toLocals, Wasm.Function.numParams, Wasm.ValueType.zero]
  · norm_num [UInt64.size]
  · intro hSize
    change Wasm.wp _
      (Project.ProofKit.FixedArrayCapacity.constantProgram 1 1 11 ++ _)
      _ initial _ env
    apply Project.ProofKit.FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero,
        Project.ProofKit.FixedArrayLengthDispatch.branchFrame]
    · norm_num [Wasm.Locals.validIndex,
        LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero,
        Project.ProofKit.FixedArrayLengthDispatch.branchFrame]
    · change Wasm.wp _
        (Project.ProofKit.FixedArrayAllocatorWindow.region 2 1 ++ _)
        _ initial _ env
      have hFitMemory16 :
          heapTop.toNat + 48 + 16 ≤ initial.mem.pages * 65536 := by
        simpa [LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec.heapReserveBytes,
          hSize] using hHeapFitMemory
      apply Project.ProofKit.FixedArrayAllocatorWindow.region_spec_withTail
        (offset := 2) (tail := 4) (heapTop := heapTop) (capacity := 16)
        (stride := 1) (allocs := allocs)
      · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero,
          Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
          Project.ProofKit.FixedArrayCapacity.capacityFrame]
      · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero,
          Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
          Project.ProofKit.FixedArrayCapacity.capacityFrame]
      · rfl
      · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero,
          Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
          Project.ProofKit.FixedArrayCapacity.capacityFrame,
          Project.ProofKit.FixedArrayCapacity.normalizedCapacity,
          Project.ProofKit.FixedArrayCapacity.unnormalizedCapacity] <;>
          native_decide
      · native_decide
      · exact hFitMemory16
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · let allocSt := Project.ProofKit.FixedArrayAllocator.allocStore
          initial heapTop 16 1 allocs
        let allocFrame :=
          Project.ProofKit.FixedArrayAllocatorWindow.allocFrame 2
            (Project.ProofKit.FixedArrayCapacity.capacityFrame
              (Project.ProofKit.FixedArrayLengthDispatch.branchFrame 7
                (LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.toLocals
                  (List.take
                    LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.numParams
                    [.i64 inputPtr]).reverse)
                inputPtr)
              11 (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 1 1))
            heapTop 16
        have hFacts := Project.ProofKit.Allocation.bumpFacts heapTop 16
          initial.mem.pages (by simpa using hFitMemory16) hPages
        have hRootAddressNat : (heapTop + 48).toUInt32.toNat =
            heapTop.toNat + 48 := by
          simpa using hFacts.wordAddress_toNat 0 (by native_decide)
        have hAllocValues : allocFrame.values = [] := by
          rfl
        have hAllocParams : allocFrame.params = [.i64 inputPtr] := by
          norm_num [allocFrame,
            Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
            Project.ProofKit.FixedArrayCapacity.capacityFrame,
            Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.ValueType.zero]
        have hAllocLocals : allocFrame.locals.length = 20 := by
          norm_num [allocFrame,
            Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
            Project.ProofKit.FixedArrayCapacity.capacityFrame,
            Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.ValueType.zero]
        have hRoot : allocFrame.get 7 = some (.i64 (heapTop + 48)) := by
          simp [allocFrame,
            Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
            Project.ProofKit.FixedArrayCapacity.capacityFrame,
            Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.ValueType.zero, Wasm.Locals.get]
        have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
            allocSt.mem.pages * 65536 := by
          rw [hRootAddressNat]
          simp only [allocSt,
            Project.ProofKit.FixedArrayAllocator.allocStore_pages]
          omega
        have hInputAlloc : Project.ProofKit.UInt64Array.At
            allocSt inputPtr input := by
          exact Project.ProofKit.FixedArrayPairResult.input_preserved_by_alloc
            initial heapTop 16 1 allocs inputPtr input hArray hInputBelow
              (by simpa using hFitMemory16) hPages
        have hInputAfterLength : Project.ProofKit.UInt64Array.At
            (Project.ProofKit.FixedArrayResult.writeLength allocSt
              (heapTop + 48) 1) inputPtr input := by
          exact hInputAlloc.write64After
            (address := (heapTop + 48).toUInt32) (value := 1)
            (by rw [hRootAddressNat]; omega)
        change Wasm.wp _
          (Project.ProofKit.FixedArrayResult.lengthStoreProgram 7 1 ++ _)
          _ allocSt allocFrame env
        apply Project.ProofKit.FixedArrayResult.lengthStore_spec
          (root := heapTop + 48) (length := 1)
        · exact hAllocValues
        · exact hRoot
        · exact hRootBound
        · change Wasm.wp _
            (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_setup_program ++ _)
            _
            (Project.ProofKit.FixedArrayResult.writeLength allocSt
              (heapTop + 48) 1)
            allocFrame env
          apply Project.ProofKit.FixedArrayFold.forwardSetupProgram_spec
            (arrayLocal := 11) (lengthLocal := 12) (indexLocal := 13)
            (stopScratchLocal := 16) (stopLocal := 14)
            (accumulatorLocal := 1) (releaseReadyLocal := 18)
            (effectiveStopLocal := 15) (initial := 1)
            (inputPtr := inputPtr) (input := input)
          · exact hAllocParams
          · exact hAllocValues
          · intro slot hSlot
            simp [Project.ProofKit.FixedArrayFold.setupLocals] at hSlot
            constructor <;> omega
          · native_decide
          · exact hInputAfterLength
          · apply Wasm.wp_block_cons
            apply Wasm.wp_loop_cons
              (Inv := productInv
                (Project.ProofKit.FixedArrayResult.writeLength allocSt
                  (heapTop + 48) 1)
                inputPtr (heapTop + 48) input)
              (μ := productMeasure input)
            · refine ⟨rfl, 0, 0, 0, inputPtr, 0, 0, by omega, ?_⟩
              simp [productFrame, productPrefix,
                Project.ProofKit.ArrayFold.foldPrefix,
                Project.ProofKit.FixedArrayFold.forwardSetupFrame,
                allocFrame,
                Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
                Project.ProofKit.FixedArrayCapacity.capacityFrame,
                Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
                LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
                Wasm.Function.toLocals, Wasm.Function.numParams,
                Wasm.ValueType.zero,
                LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
                LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                Project.ProofKit.ScalarTransition.U64State.toState,
                Project.ProofKit.ScalarTransition.State.toLocals]
            · rintro st frame
                ⟨rfl, index, item, temporary, done, staged, releaseReady,
                  hIndex, rfl⟩
              by_cases hExit : index = input.size
              · subst index
                change Wasm.wp _
                  (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_program ++ _)
                  _ _ _ env
                apply Project.ProofKit.FixedArrayTraversalInput.continuingProgram_exit_spec
                  (arrayLocal := 11) (indexLocal := 13) (stopLocal := 15)
                  (itemLocal := 2) (index := UInt64.ofNat input.size)
                · rfl
                · rfl
                · rfl
                · simp only [List.take_zero, List.drop_zero,
                    List.nil_append]
                  change Wasm.wp _
                    LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_singleton_result_program
                    _
                    (Project.ProofKit.FixedArrayResult.writeLength allocSt
                      (heapTop + 48) 1)
                    (productFrame inputPtr (heapTop + 48) input input.size
                      item temporary done staged releaseReady)
                    env
                  have hPayloadAddressNat :
                      (Project.ProofKit.FixedArrayResult.payloadAddress
                        (heapTop + 48) 0).toUInt32.toNat =
                        heapTop.toNat + 48 + 8 := by
                    simpa [Project.ProofKit.FixedArrayResult.payloadAddress]
                      using hFacts.wordAddress_toNat 1 (by native_decide)
                  have hPayloadBound :
                      (Project.ProofKit.FixedArrayResult.payloadAddress
                        (heapTop + 48) 0).toUInt32.toNat + 8 ≤
                        (Project.ProofKit.FixedArrayResult.writeLength allocSt
                          (heapTop + 48) 1).mem.pages * 65536 := by
                    rw [hPayloadAddressNat,
                      Project.ProofKit.FixedArrayResult.writeLength_pages]
                    simp only [allocSt,
                      Project.ProofKit.FixedArrayAllocator.allocStore_pages]
                    omega
                  have hOutput :=
                    Project.ProofKit.FixedArrayResult.singletonStore_at
                      allocSt (heapTop + 48)
                      (productPrefix input input.size)
                      (by rw [hFacts.rootToNat]; omega)
                      (by
                        simp only [allocSt,
                          Project.ProofKit.FixedArrayAllocator.allocStore_pages]
                        rw [hFacts.rootToNat]
                        omega)
                  apply Wasm.wp.conseq
                    (Q := Project.ProofKit.FixedArrayFold.singletonResultPost
                      6 (heapTop + 48) (productPrefix input input.size))
                  · intro continuation hResult
                    cases continuation <;>
                      simp only [Project.ProofKit.FixedArrayFold.singletonResultPost]
                        at hResult
                    rename_i final resultFrame
                    rcases hResult with ⟨hReturn, hResultArray⟩
                    simp only [Project.ProofKit.FixedArrayEqNode.branchPost]
                    change Wasm.wp _
                      LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_length_dispatch_0_suffix_program
                      _ final { resultFrame with values := [] } env
                    simp only [Wasm.Locals.get] at hReturn
                    unfold LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_length_dispatch_0_suffix_program
                    simp only [Wasm.wp_localGet_cons, Wasm.wp_nil]
                    simp only [Wasm.Locals.get]
                    rw [hReturn]
                    refine ⟨heapTop + 48, rfl, ?_⟩
                    change Project.ProofKit.UInt64Array.At _ _ _
                    rw [LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec.expected,
                      if_pos hSize]
                    simpa [productPrefix,
                      Project.ProofKit.ArrayFold.foldPrefix_size] using
                        hResultArray
                  · apply Project.ProofKit.FixedArrayFold.singletonResultProgram_spec
                    · rfl
                    · rfl
                    · simp [productFrame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                        Project.ProofKit.ScalarTransition.U64State.toState,
                        Project.ProofKit.ScalarTransition.State.toLocals]
                    · simp [Wasm.Locals.validIndex, productFrame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                        Project.ProofKit.ScalarTransition.U64State.toState,
                        Project.ProofKit.ScalarTransition.State.toLocals]
                    · simp [Project.ProofKit.FixedArrayFold.resultFrame,
                        productFrame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                        Project.ProofKit.ScalarTransition.U64State.toState,
                        Project.ProofKit.ScalarTransition.State.toLocals,
                        Wasm.Locals.get]
                    · simp [Project.ProofKit.FixedArrayFold.resultFrame,
                        productFrame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                        Project.ProofKit.ScalarTransition.U64State.toState,
                        Project.ProofKit.ScalarTransition.State.toLocals,
                        Wasm.Locals.get]
                    · exact hPayloadBound
                    · simp [Project.ProofKit.FixedArrayFold.resultFrame,
                        productFrame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                        Project.ProofKit.ScalarTransition.U64State.toState,
                        Project.ProofKit.ScalarTransition.State.toLocals]
                    · simp [Wasm.Locals.validIndex,
                        Project.ProofKit.FixedArrayFold.resultFrame,
                        productFrame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                        Project.ProofKit.ScalarTransition.U64State.toState,
                        Project.ProofKit.ScalarTransition.State.toLocals]
                    · simp [Project.ProofKit.FixedArrayFold.resultFrame,
                        productFrame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                        Project.ProofKit.ScalarTransition.U64State.toState,
                        Project.ProofKit.ScalarTransition.State.toLocals]
                    · simp [Wasm.Locals.validIndex,
                        Project.ProofKit.FixedArrayFold.resultFrame,
                        productFrame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                        Project.ProofKit.ScalarTransition.U64State.toState,
                        Project.ProofKit.ScalarTransition.State.toLocals]
                    · simpa [Project.ProofKit.FixedArrayResult.singletonStore]
                        using hOutput
              · have hIndexLt : index < input.size := by omega
                change Wasm.wp _
                  (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_program ++
                    LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_step_program)
                  _ _ _ env
                let accumulator := productPrefix input index
                let element := input[index]
                let loadedState :=
                  LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state
                    inputPtr accumulator element temporary 0 0 0
                    (heapTop + 48) 0 0 0 inputPtr
                    (UInt64.ofNat input.size) (UInt64.ofNat index)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    done staged releaseReady 0 0
                let steppedState :=
                  LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state
                    inputPtr (accumulator * element) element
                    (accumulator * element) 0 0 0 (heapTop + 48) 0 0 0
                    inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size) 0
                    (accumulator * element) 1 0 0
                apply Project.ProofKit.FixedArrayFoldBody.continuingGuardedProgram_spec
                  (arrayLocal := 11) (indexLocal := 13) (stopLocal := 15)
                  (itemLocal := 2) (scratch := 11)
                  (body := LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_body)
                  (condition := LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_condition)
                  (continuing := LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_step_continuing)
                  (inputPtr := inputPtr) (indexValue := UInt64.ofNat index)
                  (stopValue := UInt64.ofNat input.size) (input := input)
                  (index := index)
                  (stepProgram := LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_step_program)
                  (initial := loadedState.toState)
                  (afterBody := steppedState.toState)
                  (afterCondition := steppedState.toState) (result := false)
                  (hItem :=
                    LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_item_valid
                      inputPtr accumulator item temporary 0 0 0
                      (heapTop + 48) 0 0 0 inputPtr
                      (UInt64.ofNat input.size) (UInt64.ofNat index)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      done staged releaseReady 0 0)
                  (hInput := hInputAfterLength) (hIndex := hIndexLt)
                · rfl
                · rfl
                · rfl
                · rfl
                · rfl
                · rw [UInt64.lt_iff_toNat_lt,
                    UInt64.toNat_ofNat_of_lt' (by
                      exact lt_trans hIndexLt hArray.size_lt),
                    UInt64.toNat_ofNat_of_lt' hArray.size_lt]
                  exact hIndexLt
                · simpa only [productFrame, loadedState, accumulator, element,
                    LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame]
                    using
                      (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_loaded_frame_eq
                        inputPtr accumulator item temporary 0 0 0
                        (heapTop + 48) 0 0 0 inputPtr
                        (UInt64.ofNat input.size) (UInt64.ofNat index)
                        (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                        done staged releaseReady 0 0 element)
                · rfl
                · simpa [loadedState, steppedState, accumulator, element,
                    LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_bodyTransition,
                    Project.ProofKit.ScalarTransition.U64Op.apply]
                    using
                      (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_body_eval
                        inputPtr accumulator element temporary 0 0 0
                        (heapTop + 48) 0 0 0 inputPtr
                        (UInt64.ofNat input.size) (UInt64.ofNat index)
                        (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                        done staged releaseReady 0 0)
                · simpa [steppedState,
                    LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_conditionTransition]
                    using
                      (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_condition_eval
                        inputPtr (accumulator * element) element
                        (accumulator * element) 0 0 0 (heapTop + 48) 0 0 0
                        inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                        (UInt64.ofNat input.size) (UInt64.ofNat input.size) 0
                        (accumulator * element) 1 0 0)
                · intro hFalse
                  simp at hFalse
                · intro _
                  have hIndexWordSucc :
                      UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by
                    change UInt64.ofNat index + UInt64.ofNat 1 = _
                    rw [← UInt64.ofNat_add]
                  have hPrefixSucc :
                      productPrefix input (index + 1) =
                        accumulator * element := by
                    simpa [productPrefix, accumulator, element] using
                      (Project.ProofKit.ArrayFold.foldPrefix_succ input
                        (fun product element => product * element) 1 index
                        hIndexLt)
                  let nextState :=
                    LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state
                      inputPtr (accumulator * element) element
                      (accumulator * element) 0 0 0 (heapTop + 48) 0 0 0
                      inputPtr (UInt64.ofNat input.size)
                      (UInt64.ofNat (index + 1))
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size) 0
                      (accumulator * element) 1 0 0
                  refine ⟨nextState.toState, ?_, ?_⟩
                  · dsimp only [steppedState]
                    rw [LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_step_continuing_eval]
                    unfold LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_step_continuingTransition
                    simp only [Option.map_some,
                      Project.ProofKit.ScalarTransition.U64Op.apply]
                    dsimp only [nextState]
                    rw [hIndexWordSucc]
                  · simp only [List.take_zero, List.drop_zero,
                      List.nil_append]
                    have hNextFrame : nextState.toState.toLocals [] =
                        productFrame inputPtr (heapTop + 48) input
                          (index + 1) element (accumulator * element) 0
                          (accumulator * element) 1 := by
                      simp [nextState, productFrame, hPrefixSucc,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                        Project.ProofKit.ScalarTransition.U64State.toState,
                        Project.ProofKit.ScalarTransition.State.toLocals]
                    constructor
                    · refine ⟨rfl, index + 1, element,
                        accumulator * element, 0, accumulator * element, 1,
                        by omega, ?_⟩
                      exact hNextFrame
                    · rw [hNextFrame]
                      have hIndexBound : index < UInt64.size :=
                        lt_trans hIndexLt hArray.size_lt
                      have hNextIndexBound : index + 1 < UInt64.size := by
                        exact lt_of_le_of_lt (Nat.succ_le_iff.mpr hIndexLt)
                          hArray.size_lt
                      simp [productMeasure, productFrame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                        Project.ProofKit.ScalarTransition.U64State.toState,
                        Project.ProofKit.ScalarTransition.State.toLocals,
                        Wasm.Locals.get,
                        UInt64.toNat_ofNat_of_lt' hIndexBound,
                        UInt64.toNat_ofNat_of_lt' hNextIndexBound]
                      omega
  · intro hSize
    change Wasm.wp _
      (Project.ProofKit.FixedArrayCapacity.constantProgram 0 1 11 ++ _)
      _ initial _ env
    apply Project.ProofKit.FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero,
        Project.ProofKit.FixedArrayLengthDispatch.branchFrame]
    · norm_num [Wasm.Locals.validIndex,
        LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero,
        Project.ProofKit.FixedArrayLengthDispatch.branchFrame]
    · change Wasm.wp _
        (Project.ProofKit.FixedArrayAllocatorWindow.region 2 1 ++ _)
        _ initial _ env
      have hFitMemory8 :
          heapTop.toNat + 48 + 8 ≤ initial.mem.pages * 65536 := by
        simpa [LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec.heapReserveBytes,
          hSize] using hHeapFitMemory
      apply Project.ProofKit.FixedArrayAllocatorWindow.region_spec_withTail
        (offset := 2) (tail := 4) (heapTop := heapTop) (capacity := 8)
        (stride := 1) (allocs := allocs)
      · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero,
          Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
          Project.ProofKit.FixedArrayCapacity.capacityFrame]
      · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero,
          Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
          Project.ProofKit.FixedArrayCapacity.capacityFrame]
      · rfl
      · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero,
          Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
          Project.ProofKit.FixedArrayCapacity.capacityFrame,
          Project.ProofKit.FixedArrayCapacity.normalizedCapacity,
          Project.ProofKit.FixedArrayCapacity.unnormalizedCapacity] <;>
          native_decide
      · native_decide
      · exact hFitMemory8
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · let allocSt := Project.ProofKit.FixedArrayAllocator.allocStore
          initial heapTop 8 1 allocs
        let allocFrame :=
          Project.ProofKit.FixedArrayAllocatorWindow.allocFrame 2
            (Project.ProofKit.FixedArrayCapacity.capacityFrame
              (Project.ProofKit.FixedArrayLengthDispatch.branchFrame 7
                (LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.toLocals
                  (List.take
                    LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.numParams
                    [.i64 inputPtr]).reverse)
                inputPtr)
              11 (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 0 1))
            heapTop 8
        have hFacts := Project.ProofKit.Allocation.bumpFacts heapTop 8
          initial.mem.pages (by simpa using hFitMemory8) hPages
        have hRootAddressNat : (heapTop + 48).toUInt32.toNat =
            heapTop.toNat + 48 := by
          simpa using hFacts.wordAddress_toNat 0 (by native_decide)
        have hAllocValues : allocFrame.values = [] := by
          rfl
        have hAllocParams : allocFrame.params.length = 1 := by
          norm_num [allocFrame,
            Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
            Project.ProofKit.FixedArrayCapacity.capacityFrame,
            Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.ValueType.zero]
        have hAllocLocals : allocFrame.locals.length = 20 := by
          norm_num [allocFrame,
            Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
            Project.ProofKit.FixedArrayCapacity.capacityFrame,
            Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.ValueType.zero]
        have hRoot : allocFrame.get 7 = some (.i64 (heapTop + 48)) := by
          simp [allocFrame,
            Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
            Project.ProofKit.FixedArrayCapacity.capacityFrame,
            Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.ValueType.zero, Wasm.Locals.get]
        have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
            allocSt.mem.pages * 65536 := by
          rw [hRootAddressNat]
          simp only [allocSt,
            Project.ProofKit.FixedArrayAllocator.allocStore_pages]
          omega
        have hEmpty := Project.ProofKit.FixedArrayResult.emptyStore_at
          allocSt (heapTop + 48)
          (by rw [hFacts.rootToNat]; omega)
          (by
            simp only [allocSt,
              Project.ProofKit.FixedArrayAllocator.allocStore_pages]
            rw [hFacts.rootToNat]
            omega)
        change Wasm.wp _
          (Project.ProofKit.FixedArrayResult.lengthStoreProgram 7 0 ++
            Project.ProofKit.FixedArrayResult.finishProgram 7 5 6)
          _ allocSt allocFrame env
        apply Project.ProofKit.FixedArrayResult.lengthStore_spec
          (root := heapTop + 48) (length := 0)
        · exact hAllocValues
        · exact hRoot
        · exact hRootBound
        · apply Project.ProofKit.FixedArrayResult.finishProgram_spec
            (root := heapTop + 48)
          · exact hAllocValues
          · exact hRoot
          · omega
          · simpa [Wasm.Locals.validIndex, hAllocParams, hAllocLocals]
          · omega
          · simpa [Wasm.Locals.validIndex, hAllocParams, hAllocLocals]
          · simp only [Wasm.wp_nil,
              Project.ProofKit.FixedArrayEqNode.branchPost]
            change Wasm.wp _
              LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_length_dispatch_0_suffix_program
              _ _ _ env
            unfold LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_length_dispatch_0_suffix_program
            wp_run
            refine ⟨heapTop + 48, rfl, ?_⟩
            change Project.ProofKit.UInt64Array.At _ _ _
            simpa [LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec.expected,
              hSize] using hEmpty

end LeanExeGen.GeneratedRa8e90ffc5781d113.Behavior
