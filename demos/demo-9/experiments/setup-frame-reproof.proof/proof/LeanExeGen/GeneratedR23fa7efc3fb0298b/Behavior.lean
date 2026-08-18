import LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec
import LeanExeGen.GeneratedR23fa7efc3fb0298b.Program
import LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches
import LeanExeGen.Knowledge.Proposal4f56fd45fe24D4f7d73b3648.Proposed
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

def sumFrame (inputPtr root : UInt64) (input : Array UInt64) (index : Nat)
    (item scratch done staged releaseReady : UInt64) : Locals :=
  AnnotationMatches.function_0_array_fold_0_continuing_frame
    inputPtr
    (ArrayFold.foldPrefix input (fun sum element => sum + element) 0 index)
    item scratch 0 0 0 root 0 0 0 inputPtr (UInt64.ofNat input.size)
    (UInt64.ofNat index) (UInt64.ofNat input.size) (UInt64.ofNat input.size)
    done staged releaseReady 0 0

def sumInv (fixed : Store Unit) (inputPtr root : UInt64)
    (input : Array UInt64) : Store Unit → Locals → Prop :=
  fun st frame => st = fixed ∧
    ∃ index item scratch done staged releaseReady,
      index ≤ input.size ∧
      frame = sumFrame inputPtr root input index item scratch done staged
        releaseReady

def sumMeasure (input : Array UInt64) (_st : Store Unit) (frame : Locals) : Nat :=
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
  · simp [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.ValueType.zero]
  · simp [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.ValueType.zero]
  · omega
  · simp [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.ValueType.zero]
  · norm_num [UInt64.size]
  · intro hSize
    change wp module
      (FixedArrayCapacity.constantProgram 1 1 11 ++
        (FixedArrayAllocatorWindow.region 2 1 ++ _)) _ initial _ env
    apply FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail
      (length := 1) (stride := 1) (offset := 2) (tail := 4)
      (heapTop := heapTop) (allocs := allocs)
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · simpa [FormalSpec.expected, hSize,
        FixedArrayCapacity.normalizedCapacity,
        FixedArrayCapacity.unnormalizedCapacity] using hOutputFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · have hCapacity : FixedArrayCapacity.normalizedCapacity 1 1 = 16 := by
        native_decide
      simp only [hCapacity]
      let baseFrame := FixedArrayCapacity.capacityFrame
        (FixedArrayLengthDispatch.branchFrame 7
          (func0Def.toLocals
            (List.take func0Def.numParams [.i64 inputPtr]).reverse) inputPtr)
        11 16
      let allocSt := FixedArrayAllocator.allocStore initial heapTop 16 1 allocs
      let allocFrame := FixedArrayAllocatorWindow.allocFrame 2 baseFrame heapTop 16
      let foldSt := FixedArrayResult.writeLength allocSt (heapTop + 48) 1
      have hFit : heapTop.toNat + 48 + 16 ≤ initial.mem.pages * 65536 := by
        simpa [FormalSpec.expected, hSize] using hOutputFitMemory
      have hFacts := Allocation.bumpFacts heapTop 16 initial.mem.pages hFit hPages
      have hBaseParams : baseFrame.params.length = 1 := by
        simp [baseFrame, FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      have hBaseLocals : baseFrame.locals.length = 20 := by
        simp [baseFrame, FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      have hAllocValues : allocFrame.values = [] := by
        simp [allocFrame, FixedArrayAllocatorWindow.allocFrame,
          baseFrame, FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      have hRoot : allocFrame.get 7 = some (.i64 (heapTop + 48)) := by
        exact FixedArrayAllocatorWindow.allocFrame_get_root 2 4 baseFrame
          heapTop 16 hBaseParams (by simpa using hBaseLocals)
      have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
          allocSt.mem.pages * 65536 := by
        rw [show (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 by
          simpa using hFacts.wordAddress_toNat 0 (by decide)]
        simp only [allocSt, FixedArrayAllocator.allocStore_pages]
        omega
      have hInputAlloc : UInt64Array.At allocSt inputPtr input := by
        exact FixedArrayPairResult.input_preserved_by_alloc initial heapTop 16
          1 allocs inputPtr input hArray hInputBelow hFit hPages
      have hInputFold : UInt64Array.At foldSt inputPtr input := by
        apply hInputAlloc.write64After
        rw [show (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 by
          simpa using hFacts.wordAddress_toNat 0 (by decide)]
        exact hInputBelow.trans (by omega)
      have hPayloadBound :
          (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat + 8 ≤
            foldSt.mem.pages * 65536 := by
        rw [show
          (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat =
            heapTop.toNat + 48 + 8 by
          simpa [FixedArrayResult.payloadAddress] using
            hFacts.wordAddress_toNat 1 (by decide)]
        simp only [foldSt, FixedArrayResult.writeLength_pages, allocSt,
          FixedArrayAllocator.allocStore_pages]
        omega
      have hSingleton (value : UInt64) : UInt64Array.At
          (FixedArrayResult.writePayload foldSt (heapTop + 48) 0 value)
          (heapTop + 48) #[value] := by
        simpa [foldSt, FixedArrayResult.singletonStore] using
          (FixedArrayResult.singletonStore_at allocSt (heapTop + 48) value
            (by rw [hFacts.rootToNat]; exact hFacts.fit32)
            (by
              simp only [allocSt, FixedArrayAllocator.allocStore_pages]
              rw [hFacts.rootToNat]
              exact hFit))
      have hAllocFrameEq : allocFrame =
          AnnotationMatches.function_0_array_fold_0_continuing_frame
            inputPtr 0 0 0 0 0 0 (heapTop + 48) 0 0 0 16 0 0
            (heapTop + 48 + 16) ((heapTop + 48 + 16 - 1) / 65536 + 1)
            (heapTop + 48) 0 0 0 0 := by
        simp [allocFrame, FixedArrayAllocatorWindow.allocFrame, baseFrame,
          FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero,
          AnnotationMatches.function_0_array_fold_0_continuing_frame,
          AnnotationMatches.function_0_array_fold_0_state,
          ScalarTransition.U64State.toState]
      change wp module
        (FixedArrayResult.lengthStoreProgram 7 1 ++
          (AnnotationMatches.function_0_array_fold_0_setup_program ++ _)) _
        allocSt allocFrame env
      apply FixedArrayResult.lengthStore_spec
        (root := heapTop + 48) (length := 1) (rootLocal := 7)
      · exact hAllocValues
      · exact hRoot
      · exact hRootBound
      · rw [hAllocFrameEq]
        apply FixedArrayFold.forwardSetupProgram_spec
          (inputPtr := inputPtr) (input := input)
        · rfl
        · rfl
        · intro slot hSlot
          simp only [
            AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
          simp [FixedArrayFold.setupLocals] at hSlot
          omega
        · decide
        · exact hInputFold
        · rw [AnnotationMatches.function_0_array_fold_0_setup_frame_eq]
          apply wp_block_cons
          apply wp_loop_cons
            (Inv := sumInv foldSt inputPtr (heapTop + 48) input)
            (μ := sumMeasure input)
          · refine ⟨rfl, 0, 0, 0, inputPtr, 0, 0, by omega, ?_⟩
            simp [sumFrame, ArrayFold.foldPrefix]
          · rintro st frame
              ⟨rfl, index, item, scratch, done, staged, releaseReady,
                hIndex, rfl⟩
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
              · simp only [sumFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_values,
                  List.take_zero, List.drop_zero, List.nil_append]
                change wp module
                  AnnotationMatches.function_0_array_fold_0_singleton_result_program
                  _ foldSt
                  (sumFrame inputPtr (heapTop + 48) input input.size item scratch
                    done staged releaseReady) env
                change wp module
                  (FixedArrayFold.singletonResultProgram 1 10 7 4 6) _ foldSt
                  (sumFrame inputPtr (heapTop + 48) input input.size item scratch
                    done staged releaseReady) env
                apply LeanExeGen.Knowledge.Proposal4f56fd45fe24D4f7d73b3648.Proposed.singletonResultProgram_spec_to_fromFrame
                  (root := heapTop + 48)
                  (value := ArrayFold.foldPrefix input
                    (fun sum element => sum + element) 0 input.size)
                · simp only [sumFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_values]
                · simp only [sumFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_get_1]
                · simp only [sumFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
                  norm_num
                · simp [Wasm.Locals.validIndex, sumFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_params,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
                · simp only [sumFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
                  norm_num
                · simp [Wasm.Locals.validIndex, sumFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_params,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
                · omega
                · simp only [sumFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_get_7]
                · exact hPayloadBound
                · simp only [sumFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
                  norm_num
                · simp [Wasm.Locals.validIndex, sumFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_params,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
                · simp only [sumFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
                  norm_num
                · simp [Wasm.Locals.validIndex, sumFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_params,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
                · simp only [FixedArrayEqNode.branchPost]
                  have hReturn := FixedArrayResult.finishFrame_return_get
                    (FixedArrayFold.resultFrame
                      (sumFrame inputPtr (heapTop + 48) input input.size item
                        scratch done staged releaseReady)
                      10 (ArrayFold.foldPrefix input
                        (fun sum element => sum + element) 0 input.size))
                    4 6 (heapTop + 48) (by
                      simp only [FixedArrayFold.resultFrame_params, sumFrame,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
                      norm_num) (by
                      simp [Wasm.Locals.validIndex,
                        FixedArrayFold.resultFrame_params,
                        FixedArrayFold.resultFrame_locals_length, sumFrame,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame_params,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length])
                  wp_run
                  refine ⟨heapTop + 48, ?_, ?_⟩
                  · rfl
                  · change UInt64Array.At _ _ _
                    rw [FormalSpec.expected, if_pos hSize]
                    simpa [ArrayFold.foldPrefix_size] using
                      hSingleton (ArrayFold.foldPrefix input
                        (fun sum element => sum + element) 0 input.size)
            · have hIndexLt : index < input.size := by omega
              have hIndexNat : (UInt64.ofNat index).toNat = index := by
                apply UInt64.toNat_ofNat_of_lt'
                exact lt_of_lt_of_le hIndexLt hInputFold.size_lt.le
              have hSizeNat : (UInt64.ofNat input.size).toNat = input.size :=
                UInt64.toNat_ofNat_of_lt' hInputFold.size_lt
              have hContinue : UInt64.ofNat index < UInt64.ofNat input.size := by
                rw [UInt64.lt_iff_toNat_lt, hIndexNat, hSizeNat]
                exact hIndexLt
              let acc := ArrayFold.foldPrefix input
                (fun sum element => sum + element) 0 index
              let value := input[index]
              let afterBody :=
                (AnnotationMatches.function_0_array_fold_0_state
                  inputPtr (acc + value) value (acc + value) 0 0 0
                  (heapTop + 48) 0 0 0 inputPtr (UInt64.ofNat input.size)
                  (UInt64.ofNat index) (UInt64.ofNat input.size)
                  (UInt64.ofNat input.size) 0 (acc + value) 1 0 0).toState
              have hItemValid :
                  (sumFrame inputPtr (heapTop + 48) input index item scratch done
                    staged releaseReady).validIndex 2 := by
                simpa [sumFrame, acc] using
                  (AnnotationMatches.function_0_array_fold_0_continuing_item_valid
                    inputPtr acc item scratch 0 0 0 (heapTop + 48) 0 0 0 inputPtr
                    (UInt64.ofNat input.size) (UInt64.ofNat index)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size) done
                    staged releaseReady 0 0)
              change wp module
                (AnnotationMatches.function_0_array_fold_0_continuing_program ++
                  AnnotationMatches.function_0_array_fold_0_step_program) _
                foldSt
                (sumFrame inputPtr (heapTop + 48) input index item scratch done
                  staged releaseReady) env
              apply FixedArrayFoldBody.continuingGuardedProgram_spec
                (arrayLocal := 11) (indexLocal := 13) (stopLocal := 15)
                (itemLocal := 2) (scratch := 11)
                (body := AnnotationMatches.function_0_array_fold_0_body)
                (condition := AnnotationMatches.function_0_array_fold_0_condition)
                (continuing :=
                  AnnotationMatches.function_0_array_fold_0_step_continuing)
                (inputPtr := inputPtr) (indexValue := UInt64.ofNat index)
                (stopValue := UInt64.ofNat input.size) (input := input)
                (index := index)
                (stepProgram := AnnotationMatches.function_0_array_fold_0_step_program)
                (initial :=
                  (AnnotationMatches.function_0_array_fold_0_state
                    inputPtr acc value scratch 0 0 0 (heapTop + 48) 0 0 0
                    inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size) done
                    staged releaseReady 0 0).toState)
                (afterBody := afterBody) (afterCondition := afterBody)
                (result := false)
                (hValues := by simp only [sumFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_values])
                (hArrayLocal := by simp only [sumFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_get_11])
                (hIndexLocal := by simp only [sumFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13])
                (hStopLocal := by simp only [sumFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_get_15])
                (hIndexValue := rfl) (hContinueGuard := hContinue)
                (hItem := hItemValid) (hInput := hInputFold) (hIndex := hIndexLt)
                (hLoaded := by
                  simpa [sumFrame, acc, value,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame] using
                    (AnnotationMatches.function_0_array_fold_0_continuing_loaded_frame_eq
                      inputPtr acc item scratch 0 0 0 (heapTop + 48) 0 0 0
                      inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size) done
                      staged releaseReady 0 0 value))
                (hStepProgram := rfl)
                (hBody := by
                  simpa [afterBody, acc, value,
                    ScalarTransition.U64Op.apply,
                    AnnotationMatches.function_0_array_fold_0_bodyTransition] using
                    (AnnotationMatches.function_0_array_fold_0_body_eval
                      inputPtr acc value scratch 0 0 0 (heapTop + 48) 0 0 0
                      inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size) done
                      staged releaseReady 0 0))
                (hCondition := by
                  simpa [afterBody,
                    AnnotationMatches.function_0_array_fold_0_conditionTransition] using
                    (AnnotationMatches.function_0_array_fold_0_condition_eval
                      inputPtr (acc + value) value (acc + value) 0 0 0
                      (heapTop + 48) 0 0 0 inputPtr (UInt64.ofNat input.size)
                      (UInt64.ofNat index) (UInt64.ofNat input.size)
                      (UInt64.ofNat input.size) 0 (acc + value) 1 0 0))
              · intro hFalse
                contradiction
              · intro _
                let afterContinue :=
                  (AnnotationMatches.function_0_array_fold_0_state
                    inputPtr (acc + value) value (acc + value) 0 0 0
                    (heapTop + 48) 0 0 0 inputPtr (UInt64.ofNat input.size)
                    (UInt64.ofNat (index + 1)) (UInt64.ofNat input.size)
                    (UInt64.ofNat input.size) 0 (acc + value) 1 0 0).toState
                refine ⟨afterContinue, ?_, ?_⟩
                · simpa [afterContinue, afterBody, UInt64.ofNat_add,
                    ScalarTransition.U64Op.apply,
                    AnnotationMatches.function_0_array_fold_0_step_continuingTransition] using
                    (AnnotationMatches.function_0_array_fold_0_step_continuing_eval
                      inputPtr (acc + value) value (acc + value) 0 0 0
                      (heapTop + 48) 0 0 0 inputPtr (UInt64.ofNat input.size)
                      (UInt64.ofNat index) (UInt64.ofNat input.size)
                      (UInt64.ofNat input.size) 0 (acc + value) 1 0 0)
                · change
                    sumInv foldSt inputPtr (heapTop + 48) input foldSt
                        (AnnotationMatches.function_0_array_fold_0_continuing_frame
                          inputPtr (acc + value) value (acc + value) 0 0 0
                          (heapTop + 48) 0 0 0 inputPtr
                          (UInt64.ofNat input.size) (UInt64.ofNat (index + 1))
                          (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                          0 (acc + value) 1 0 0) ∧
                      sumMeasure input foldSt
                          (AnnotationMatches.function_0_array_fold_0_continuing_frame
                            inputPtr (acc + value) value (acc + value) 0 0 0
                            (heapTop + 48) 0 0 0 inputPtr
                            (UInt64.ofNat input.size) (UInt64.ofNat (index + 1))
                            (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                            0 (acc + value) 1 0 0) <
                        sumMeasure input foldSt
                          (sumFrame inputPtr (heapTop + 48) input index item
                            scratch done staged releaseReady)
                  constructor
                  · refine ⟨rfl, index + 1, value, acc + value, 0,
                      acc + value, 1, by omega, ?_⟩
                    simp only [sumFrame]
                    rw [ArrayFold.foldPrefix_succ input
                      (fun sum element => sum + element) 0 index hIndexLt]
                  · have hSuccNat : (UInt64.ofNat (index + 1)).toNat = index + 1 := by
                      apply UInt64.toNat_ofNat_of_lt'
                      exact lt_of_le_of_lt (Nat.succ_le_iff.mpr hIndexLt)
                        hInputFold.size_lt
                    simp only [sumMeasure, sumFrame,
                      AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13]
                    rw [hSuccNat, hIndexNat]
                    omega
  · intro hSize
    change wp module
      (FixedArrayCapacity.constantProgram 0 1 11 ++
        (FixedArrayAllocatorWindow.region 2 1 ++ _)) _ initial _ env
    apply FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail
      (length := 0) (stride := 1) (offset := 2) (tail := 4)
      (heapTop := heapTop) (allocs := allocs)
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · simpa [FormalSpec.expected, hSize,
        FixedArrayCapacity.normalizedCapacity,
        FixedArrayCapacity.unnormalizedCapacity] using hOutputFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · have hCapacity : FixedArrayCapacity.normalizedCapacity 0 1 = 8 := by
        native_decide
      simp only [hCapacity]
      let baseFrame := FixedArrayCapacity.capacityFrame
        (FixedArrayLengthDispatch.branchFrame 7
          (func0Def.toLocals
            (List.take func0Def.numParams [.i64 inputPtr]).reverse) inputPtr)
        11 8
      let allocSt := FixedArrayAllocator.allocStore initial heapTop 8 1 allocs
      let allocFrame := FixedArrayAllocatorWindow.allocFrame 2 baseFrame heapTop 8
      have hFit : heapTop.toNat + 48 + 8 ≤ initial.mem.pages * 65536 := by
        simpa [FormalSpec.expected, hSize] using hOutputFitMemory
      have hFacts := Allocation.bumpFacts heapTop 8 initial.mem.pages hFit hPages
      have hBaseParams : baseFrame.params.length = 1 := by
        simp [baseFrame, FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      have hBaseLocals : baseFrame.locals.length = 20 := by
        simp [baseFrame, FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      have hAllocValues : allocFrame.values = [] := by
        simp [allocFrame, FixedArrayAllocatorWindow.allocFrame,
          baseFrame, FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      have hAllocParams : allocFrame.params.length = 1 := by
        change (FixedArrayAllocatorWindow.allocFrame 2 baseFrame heapTop 8).params.length = 1
        rw [FixedArrayAllocatorWindow.allocFrame_params]
        exact hBaseParams
      have hAllocLocals : allocFrame.locals.length = 20 := by
        change (FixedArrayAllocatorWindow.allocFrame 2 baseFrame heapTop 8).locals.length = 20
        rw [FixedArrayAllocatorWindow.allocFrame_locals_length]
        exact hBaseLocals
      have hRoot : allocFrame.get 7 = some (.i64 (heapTop + 48)) := by
        exact FixedArrayAllocatorWindow.allocFrame_get_root 2 4 baseFrame
          heapTop 8 hBaseParams (by simpa using hBaseLocals)
      have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
          allocSt.mem.pages * 65536 := by
        rw [show (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 by
          simpa using hFacts.wordAddress_toNat 0 (by decide)]
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
        (root := heapTop + 48) (length := 0) (rootLocal := 7)
      · exact hAllocValues
      · exact hRoot
      · exact hRootBound
      · apply FixedArrayResult.finishProgram_spec
          (root := heapTop + 48) (rootLocal := 7)
          (destinationLocal := 5) (returnLocal := 6) (rest := [])
        · exact hAllocValues
        · exact hRoot
        · omega
        · change 5 < allocFrame.params.length + allocFrame.locals.length
          rw [hAllocParams, hAllocLocals]
          omega
        · omega
        · change 6 < allocFrame.params.length + allocFrame.locals.length
          rw [hAllocParams, hAllocLocals]
          omega
        · rw [Wasm.wp_nil]
          simp only [FixedArrayEqNode.branchPost]
          have hReturn := FixedArrayResult.finishFrame_return_get allocFrame
            5 6 (heapTop + 48) (by omega) (by
              change 6 < allocFrame.params.length + allocFrame.locals.length
              rw [hAllocParams, hAllocLocals]
              omega)
          wp_run
          refine ⟨heapTop + 48, ?_, ?_⟩
          · rfl
          · change UInt64Array.At _ _ _
            simpa [FormalSpec.expected, hSize] using hEmpty

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior
