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
import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.Allocation
import Project.ProofKit.FixedArrayResult
import Project.ProofKit.Frame
import Project.ProofKit.ScalarTransition

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRa8e90ffc5781d113.Behavior

open Wasm Project.ProofKit

private def productFrame (inputPtr root : UInt64) (input : Array UInt64)
    (index : Nat) (item temporary done staged releaseReady : UInt64) :
    Wasm.Locals :=
  AnnotationMatches.function_0_array_fold_0_continuing_frame
    inputPtr
    (ArrayFold.foldPrefix input
      (fun product element => product * element) 1 index)
    item temporary 0 0 0 root 0 0 0 inputPtr
    (UInt64.ofNat input.size) (UInt64.ofNat index)
    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
    done staged releaseReady 0 0

private def productInv (loopStore : Wasm.Store Unit)
    (inputPtr root : UInt64) (input : Array UInt64) : Wasm.AssertionF Unit :=
  fun st frame => ∃ index item temporary done staged releaseReady,
    index ≤ input.size ∧ st = loopStore ∧
      frame = productFrame inputPtr root input index item temporary done
        staged releaseReady

private def productMeasure (input : Array UInt64)
    (_ : Wasm.Store Unit) (frame : Wasm.Locals) : Nat :=
  match frame.get 13 with
  | some (.i64 index) => input.size - index.toNat
  | _ => 0

private def productLoopProgram : Wasm.Program :=
  [.block 0 0 [.loop 0 0
    (AnnotationMatches.function_0_array_fold_0_continuing_program ++
      AnnotationMatches.function_0_array_fold_0_step_program)]]

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
  apply Wasm.TerminatesWith.of_wp_entry_for (f := func0Def) rfl
  change Wasm.wp «module» func0 _ initial _ env
  rw [AnnotationMatches.function_0_length_dispatch_0_function_eq]
  wp_fixed_array_length_le_dispatch_from hArray at 7, 8
  · rfl
  · rfl
  · norm_num
  · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.ValueType.zero]
  · norm_num [UInt64.size]
  · intro hSize
    have hExpected : FormalSpec.expected input =
        #[input.foldl (fun product element => product * element) 1] := by
      simp [FormalSpec.expected, hSize]
    have hFitMemory : heapTop.toNat + 48 + 16 ≤
        initial.mem.pages * 65536 := by
      simpa [hExpected] using hOutputFitMemory
    change Wasm.wp «module»
      (FixedArrayCapacity.constantProgram 1 1 11 ++
        (FixedArrayAllocatorWindow.region 2 1 ++ _)) _ initial _ env
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [func0Def, Wasm.Function.toLocals,
        Wasm.Function.numParams, Wasm.Locals.validIndex,
        Wasm.ValueType.zero, FixedArrayLengthDispatch.branchFrame]
    · norm_num [func0Def, Wasm.Function.toLocals,
        Wasm.Function.numParams, Wasm.Locals.validIndex,
        Wasm.ValueType.zero, FixedArrayLengthDispatch.branchFrame]
    · apply FixedArrayAllocatorWindow.region_spec_withTail 2 4
        «module» env initial _ heapTop 16 1 allocs
      · norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      · norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      · rfl
      · norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero, FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity] <;> decide
      · decide
      · exact hFitMemory
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · let allocSt := FixedArrayAllocator.allocStore
          initial heapTop 16 1 allocs
        let allocFrame := FixedArrayAllocatorWindow.allocFrame 2
          (FixedArrayCapacity.capacityFrame
            (FixedArrayLengthDispatch.branchFrame 7
              (func0Def.toLocals
                (List.take func0Def.numParams [.i64 inputPtr]).reverse)
              inputPtr)
            11 16)
          heapTop 16
        let root := heapTop + 48
        let loopStore := FixedArrayResult.writeLength allocSt root 1
        have hBump := Allocation.bumpFacts heapTop 16 initial.mem.pages
          hFitMemory hPages
        have hFit32 : heapTop.toNat + 48 + 16 ≤ 4294967296 := by
          simpa [hExpected] using hOutputFit32
        have hValues : allocFrame.values = [] := by
          rfl
        have hParams : allocFrame.params = [.i64 inputPtr] := by
          rfl
        have hLocalsLength : allocFrame.locals.length = 20 := by
          norm_num [allocFrame, FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.ValueType.zero]
        have hRoot : allocFrame.get 7 = some (.i64 root) := by
          norm_num [root, allocFrame, FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.Locals.get, Wasm.ValueType.zero]
        have hRootToNat : root.toUInt32.toNat = heapTop.toNat + 48 := by
          simpa [root] using hBump.wordAddress_toNat 0 (by decide)
        have hRootBound : root.toUInt32.toNat + 8 ≤
            allocSt.mem.pages * 65536 := by
          rw [hRootToNat]
          simp only [allocSt, FixedArrayAllocator.allocStore_pages]
          omega
        have hInputAlloc := FixedArrayPairResult.input_preserved_by_alloc
          initial heapTop 16 1 allocs inputPtr input hArray hInputBelow
          hFitMemory hPages
        have hInputLoop : UInt64Array.At loopStore inputPtr input := by
          apply hInputAlloc.write64After
          rw [hRootToNat]
          omega
        have hOutput (value : UInt64) : UInt64Array.At
            (FixedArrayResult.writePayload loopStore root 0 value)
            root #[value] := by
          simpa [loopStore, FixedArrayResult.singletonStore] using
            FixedArrayResult.singletonStore_at allocSt root value
              (by rw [show root.toNat = heapTop.toNat + 48 by
                    simpa [root] using hBump.rootToNat]
                  exact hFit32)
              (by
                rw [show root.toNat = heapTop.toNat + 48 by
                  simpa [root] using hBump.rootToNat]
                simp only [allocSt, FixedArrayAllocator.allocStore_pages]
                exact hFitMemory)
        change Wasm.wp «module»
          (FixedArrayResult.lengthStoreProgram 7 1 ++
            (AnnotationMatches.function_0_array_fold_0_setup_program ++
              (productLoopProgram ++
                AnnotationMatches.function_0_array_fold_0_singleton_result_program)))
          _ allocSt allocFrame env
        apply FixedArrayResult.lengthStore_spec
            (root := root) (length := 1) (rootLocal := 7)
        · exact hValues
        · exact hRoot
        · exact hRootBound
        · apply FixedArrayFold.forwardSetupProgram_spec
              (arrayLocal := 11) (lengthLocal := 12)
              (indexLocal := 13) (stopScratchLocal := 16)
              (stopLocal := 14) (accumulatorLocal := 1)
              (releaseReadyLocal := 18) (effectiveStopLocal := 15)
              (initial := 1) (inputPtr := inputPtr) (input := input)
          · exact hParams
          · exact hValues
          · intro slot hSlot
            simp [FixedArrayFold.setupLocals] at hSlot
            rcases hSlot with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            all_goals omega
          · decide
          · exact hInputLoop
          · unfold productLoopProgram
            apply Wasm.wp_block_cons
            apply Wasm.wp_loop_cons
              (Inv := productInv loopStore inputPtr root input)
              (μ := productMeasure input)
            · refine ⟨0, 0, 0, inputPtr, 0, 0, Nat.zero_le _, rfl, ?_⟩
              simp [productFrame, FixedArrayFold.forwardSetupFrame,
                root, allocFrame, FixedArrayAllocatorWindow.allocFrame,
                FixedArrayCapacity.capacityFrame,
                FixedArrayLengthDispatch.branchFrame, func0Def,
                Wasm.Function.toLocals, Wasm.Function.numParams,
                Wasm.ValueType.zero,
                AnnotationMatches.function_0_array_fold_0_continuing_frame,
                AnnotationMatches.function_0_array_fold_0_state,
                ScalarTransition.U64State.toState,
                ScalarTransition.State.toLocals, ArrayFold.foldPrefix]
            · rintro st frame
                ⟨index, item, temporary, done, staged, releaseReady,
                  hIndex, rfl, rfl⟩
              by_cases hDone : index = input.size
              · subst index
                apply FixedArrayTraversalInput.continuingProgram_exit_spec
                    (arrayLocal := 11) (indexLocal := 13)
                    (stopLocal := 15) (itemLocal := 2)
                    (index := UInt64.ofNat input.size)
                · rfl
                · rfl
                · rfl
                · simp only [productFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_values,
                    List.take_zero, List.drop_zero, List.nil_append,
                    Wasm.wp_nil]
                  let value := ArrayFold.foldPrefix input
                    (fun product element => product * element) 1 input.size
                  let exitFrame := productFrame inputPtr root input input.size
                    item temporary done staged releaseReady
                  have hExitParamsLength : exitFrame.params.length = 1 := by
                    rfl
                  have hExitLocalsLength : exitFrame.locals.length = 20 := by
                    rfl
                  have hExitAccumulator : exitFrame.get 1 =
                      some (.i64 value) := by
                    rfl
                  have hExitRoot : exitFrame.get 7 = some (.i64 root) := by
                    rfl
                  have hExitResultLower : exitFrame.params.length ≤ 10 := by
                    omega
                  have hExitResultValid : exitFrame.validIndex 10 := by
                    simpa [Wasm.Locals.validIndex, hExitParamsLength,
                      hExitLocalsLength]
                  have hExitRootLower : exitFrame.params.length ≤ 7 := by
                    omega
                  have hExitRootValid : exitFrame.validIndex 7 := by
                    simpa [Wasm.Locals.validIndex, hExitParamsLength,
                      hExitLocalsLength]
                  have hResultRoot :
                      (FixedArrayFold.resultFrame exitFrame 10 value).get 7 =
                        some (.i64 root) := by
                    exact FixedArrayFold.resultFrame_get_of_ne
                      exitFrame 10 7 value (.i64 root) hExitResultLower
                      hExitRootLower hExitRootValid (by decide) hExitRoot
                  have hResultValue :
                      (FixedArrayFold.resultFrame exitFrame 10 value).get 10 =
                        some (.i64 value) := by
                    exact FixedArrayFold.resultFrame_get_result exitFrame 10
                      value hExitResultLower hExitResultValid
                  have hResultParamsLength :
                      (FixedArrayFold.resultFrame exitFrame 10 value).params.length =
                        1 := by
                    rw [FixedArrayFold.resultFrame_params]
                    exact hExitParamsLength
                  have hResultLocalsLength :
                      (FixedArrayFold.resultFrame exitFrame 10 value).locals.length =
                        20 := by
                    rw [FixedArrayFold.resultFrame_locals_length]
                    exact hExitLocalsLength
                  change Wasm.wp «module»
                    AnnotationMatches.function_0_array_fold_0_singleton_result_program
                    _ loopStore exitFrame env
                  apply Wasm.wp.conseq
                    (Q := FixedArrayFold.singletonResultPost 6 root value)
                  · intro continuation hPost
                    cases continuation
                    case Fallthrough final frame =>
                      rcases hPost with ⟨hReturn, hResultArray⟩
                      simp only [FixedArrayEqNode.branchPost]
                      have hReturn' :
                          ({ frame with values := [] } : Wasm.Locals).get 6 =
                            some (.i64 root) := by
                        simpa only [Wasm.Locals.get] using hReturn
                      unfold AnnotationMatches.function_0_length_dispatch_0_suffix_program
                      simp only [Wasm.wp_localGet_cons, hReturn', Wasm.wp_nil]
                      refine ⟨root, ?_, ?_⟩
                      · norm_num [func0Def, Wasm.Function.numParams]
                      · rw [hExpected]
                        have hComplete := ArrayFold.foldPrefix_size input
                          (fun product element => product * element) 1
                        change UInt64Array.At final root
                          #[input.foldl
                            (fun product element => product * element) 1]
                        simpa [value, hComplete] using hResultArray
                    all_goals
                      simp [FixedArrayFold.singletonResultPost] at hPost
                  · apply FixedArrayFold.singletonResultProgram_spec
                        (accumulatorLocal := 1) (resultLocal := 10)
                        (rootLocal := 7) (destinationLocal := 4)
                        (returnLocal := 6) (root := root) (value := value)
                        (frame := exitFrame) (st := loopStore)
                    · rfl
                    · exact hExitAccumulator
                    · exact hExitResultLower
                    · exact hExitResultValid
                    · exact hResultRoot
                    · exact hResultValue
                    · have hPayloadToNat :
                          (FixedArrayResult.payloadAddress root 0).toUInt32.toNat =
                            heapTop.toNat + 56 := by
                        simpa [root, FixedArrayResult.payloadAddress] using
                          hBump.wordAddress_toNat 1 (by decide)
                      rw [hPayloadToNat]
                      simp only [loopStore, FixedArrayResult.writeLength_pages,
                        allocSt, FixedArrayAllocator.allocStore_pages]
                      omega
                    · omega
                    · simpa [Wasm.Locals.validIndex, hResultParamsLength,
                        hResultLocalsLength]
                    · omega
                    · simpa [Wasm.Locals.validIndex, hResultParamsLength,
                        hResultLocalsLength]
                    · exact hOutput value
              · have hIndexLt : index < input.size := by
                  omega
                have hIndex64 : index < UInt64.size := by
                  exact lt_trans hIndexLt hInputLoop.size_lt
                have hIndexSucc64 : index + 1 < UInt64.size := by
                  exact lt_of_le_of_lt (Nat.succ_le_iff.mpr hIndexLt)
                    hInputLoop.size_lt
                have hIndexNat : (UInt64.ofNat index).toNat = index :=
                  UInt64.toNat_ofNat_of_lt' hIndex64
                have hIndexSuccNat :
                    (UInt64.ofNat (index + 1)).toNat = index + 1 :=
                  UInt64.toNat_ofNat_of_lt' hIndexSucc64
                have hInputSizeNat :
                    (UInt64.ofNat input.size).toNat = input.size :=
                  UInt64.toNat_ofNat_of_lt' hInputLoop.size_lt
                have hIndexEncoded :
                    UInt64.ofNat index < UInt64.ofNat input.size := by
                  rw [UInt64.lt_iff_toNat_lt, hIndexNat, hInputSizeNat]
                  exact hIndexLt
                have hIndexSucc :
                    UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by
                  simpa using (UInt64.ofNat_add index 1).symm
                let accumulator := ArrayFold.foldPrefix input
                  (fun product element => product * element) 1 index
                let nextValue := accumulator * input[index]
                let initialState :=
                  (AnnotationMatches.function_0_array_fold_0_state
                    inputPtr accumulator input[index] temporary 0 0 0 root
                    0 0 0 inputPtr (UInt64.ofNat input.size)
                    (UInt64.ofNat index) (UInt64.ofNat input.size)
                    (UInt64.ofNat input.size) done staged releaseReady 0 0).toState
                let afterState :=
                  (AnnotationMatches.function_0_array_fold_0_state
                    inputPtr nextValue input[index] nextValue 0 0 0 root
                    0 0 0 inputPtr (UInt64.ofNat input.size)
                    (UInt64.ofNat index) (UInt64.ofNat input.size)
                    (UInt64.ofNat input.size) 0 nextValue 1 0 0).toState
                let continuedState :=
                  (AnnotationMatches.function_0_array_fold_0_state
                    inputPtr nextValue input[index] nextValue 0 0 0 root
                    0 0 0 inputPtr (UInt64.ofNat input.size)
                    (UInt64.ofNat index + 1) (UInt64.ofNat input.size)
                    (UInt64.ofNat input.size) 0 nextValue 1 0 0).toState
                apply FixedArrayFoldBody.continuingGuardedProgram_spec
                    (arrayLocal := 11) (indexLocal := 13)
                    (stopLocal := 15) (itemLocal := 2) (scratch := 11)
                    (body := AnnotationMatches.function_0_array_fold_0_body)
                    (condition :=
                      AnnotationMatches.function_0_array_fold_0_condition)
                    (continuing :=
                      AnnotationMatches.function_0_array_fold_0_step_continuing)
                    (module_ := «module») (env := env) (st := loopStore)
                    (frame := productFrame inputPtr root input index item
                      temporary done staged releaseReady)
                    (inputPtr := inputPtr) (indexValue := UInt64.ofNat index)
                    (stopValue := UInt64.ofNat input.size)
                    (input := input) (index := index)
                    (stepProgram :=
                      AnnotationMatches.function_0_array_fold_0_step_program)
                    (initial := initialState) (afterBody := afterState)
                    (afterCondition := afterState) (result := false)
                · rfl
                · rfl
                · rfl
                · rfl
                · rfl
                · exact hIndexEncoded
                · exact hInputLoop
                · simpa only [productFrame, accumulator, initialState,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame]
                    using
                      AnnotationMatches.function_0_array_fold_0_continuing_loaded_frame_eq
                        inputPtr accumulator item temporary 0 0 0 root 0 0 0
                        inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                        (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                        done staged releaseReady 0 0 input[index]
                · rfl
                · simpa [initialState, afterState, nextValue,
                    AnnotationMatches.function_0_array_fold_0_bodyTransition,
                    ScalarTransition.U64Op.apply] using
                      AnnotationMatches.function_0_array_fold_0_body_eval
                        inputPtr accumulator input[index] temporary 0 0 0 root
                        0 0 0 inputPtr (UInt64.ofNat input.size)
                        (UInt64.ofNat index) (UInt64.ofNat input.size)
                        (UInt64.ofNat input.size) done staged releaseReady 0 0
                · simpa [afterState,
                    AnnotationMatches.function_0_array_fold_0_conditionTransition]
                    using
                      AnnotationMatches.function_0_array_fold_0_condition_eval
                        inputPtr nextValue input[index] nextValue 0 0 0 root
                        0 0 0 inputPtr (UInt64.ofNat input.size)
                        (UInt64.ofNat index) (UInt64.ofNat input.size)
                        (UInt64.ofNat input.size) 0 nextValue 1 0 0
                · simp
                · intro _
                  refine ⟨continuedState, ?_, ?_⟩
                  · simpa [afterState, continuedState,
                      AnnotationMatches.function_0_array_fold_0_step_continuingTransition,
                      ScalarTransition.U64Op.apply] using
                        AnnotationMatches.function_0_array_fold_0_step_continuing_eval
                          inputPtr nextValue input[index] nextValue 0 0 0 root
                          0 0 0 inputPtr (UInt64.ofNat input.size)
                          (UInt64.ofNat index) (UInt64.ofNat input.size)
                          (UInt64.ofNat input.size) 0 nextValue 1 0 0
                  · have hContinuedFrame : continuedState.toLocals [] =
                        productFrame inputPtr root input (index + 1)
                          input[index] nextValue 0 nextValue 1 := by
                      simp only [continuedState, productFrame,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame]
                      rw [ArrayFold.foldPrefix_succ input
                        (fun product element => product * element) 1 index
                        hIndexLt]
                      rw [hIndexSucc]
                    change
                      productInv loopStore inputPtr root input loopStore
                          (continuedState.toLocals []) ∧
                        productMeasure input loopStore
                            (continuedState.toLocals []) <
                          productMeasure input loopStore
                            (productFrame inputPtr root input index item
                              temporary done staged releaseReady)
                    constructor
                    · refine ⟨index + 1, input[index], nextValue, 0,
                        nextValue, 1, ?_, rfl, hContinuedFrame⟩
                      omega
                    · rw [hContinuedFrame]
                      simp only [productMeasure, productFrame,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13]
                      rw [hIndexNat, hIndexSuccNat]
                      omega
                · simpa only [productFrame, accumulator] using
                    AnnotationMatches.function_0_array_fold_0_continuing_item_valid
                      inputPtr accumulator item temporary 0 0 0 root 0 0 0
                      inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      done staged releaseReady 0 0
  · intro hSize
    have hExpected : FormalSpec.expected input = #[] := by
      simp [FormalSpec.expected, hSize]
    have hFitMemory : heapTop.toNat + 48 + 8 ≤
        initial.mem.pages * 65536 := by
      simpa [hExpected] using hOutputFitMemory
    change Wasm.wp «module»
      (FixedArrayCapacity.constantProgram 0 1 11 ++
        (FixedArrayAllocatorWindow.region 2 1 ++ _)) _ initial _ env
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [func0Def, Wasm.Function.toLocals,
        Wasm.Function.numParams, Wasm.Locals.validIndex,
        Wasm.ValueType.zero, FixedArrayLengthDispatch.branchFrame]
    · norm_num [func0Def, Wasm.Function.toLocals,
        Wasm.Function.numParams, Wasm.Locals.validIndex,
        Wasm.ValueType.zero, FixedArrayLengthDispatch.branchFrame]
    · apply FixedArrayAllocatorWindow.region_spec_withTail 2 4
        «module» env initial _ heapTop 8 1 allocs
      · norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      · norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      · rfl
      · norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero, FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity] <;> decide
      · decide
      · exact hFitMemory
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · let allocSt := FixedArrayAllocator.allocStore
          initial heapTop 8 1 allocs
        let allocFrame := FixedArrayAllocatorWindow.allocFrame 2
          (FixedArrayCapacity.capacityFrame
            (FixedArrayLengthDispatch.branchFrame 7
              (func0Def.toLocals
                (List.take func0Def.numParams [.i64 inputPtr]).reverse)
              inputPtr)
            11 8)
          heapTop 8
        have hBump := Allocation.bumpFacts heapTop 8 initial.mem.pages
          hFitMemory hPages
        have hValues : allocFrame.values = [] := by
          rfl
        have hParamsLength : allocFrame.params.length = 1 := by
          rfl
        have hLocalsLength : allocFrame.locals.length = 20 := by
          norm_num [allocFrame, FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.ValueType.zero]
        have hRoot : allocFrame.get 7 = some (.i64 (heapTop + 48)) := by
          norm_num [allocFrame, FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.Locals.get, Wasm.ValueType.zero]
        have hDestinationLower : allocFrame.params.length ≤ 5 := by
          omega
        have hDestinationValid : allocFrame.validIndex 5 := by
          simpa [Wasm.Locals.validIndex, hParamsLength, hLocalsLength]
        have hReturnLower : allocFrame.params.length ≤ 6 := by
          omega
        have hReturnValid : allocFrame.validIndex 6 := by
          simpa [Wasm.Locals.validIndex, hParamsLength, hLocalsLength]
        have hRootToNat : (heapTop + 48).toUInt32.toNat =
            heapTop.toNat + 48 := by
          simpa using hBump.wordAddress_toNat 0 (by decide)
        have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
            allocSt.mem.pages * 65536 := by
          rw [hRootToNat]
          simp only [allocSt, FixedArrayAllocator.allocStore_pages]
          omega
        have hOutput : UInt64Array.At
            (FixedArrayResult.writeLength allocSt (heapTop + 48) 0)
            (heapTop + 48) #[] := by
          apply FixedArrayResult.emptyStore_at
          · rw [hBump.rootToNat]
            omega
          · rw [hBump.rootToNat]
            simp only [allocSt, FixedArrayAllocator.allocStore_pages]
            omega
        change Wasm.wp «module»
          (FixedArrayResult.lengthStoreProgram 7 0 ++
            FixedArrayResult.finishProgram 7 5 6) _ allocSt allocFrame env
        apply FixedArrayResult.lengthStore_spec
            (root := heapTop + 48) (length := 0) (rootLocal := 7)
        · exact hValues
        · exact hRoot
        · exact hRootBound
        · apply FixedArrayResult.finishProgram_spec
              (module_ := «module») (env := env)
              (st := FixedArrayResult.writeLength
                allocSt (heapTop + 48) 0)
              (frame := allocFrame)
              (root := heapTop + 48) (rootLocal := 7)
              (destinationLocal := 5) (returnLocal := 6)
          · exact hValues
          · exact hRoot
          · exact hDestinationLower
          · exact hDestinationValid
          · exact hReturnLower
          · exact hReturnValid
          · rw [Wasm.wp_nil]
            simp only [FixedArrayEqNode.branchPost]
            have hReturnGet := FixedArrayResult.finishFrame_return_get
              allocFrame 5 6 (heapTop + 48) hReturnLower hReturnValid
            unfold AnnotationMatches.function_0_length_dispatch_0_suffix_program
            simp only [Wasm.wp_localGet_cons,
              hReturnGet, Wasm.wp_nil]
            refine ⟨heapTop + 48, ?_, ?_⟩
            · norm_num [func0Def, Wasm.Function.numParams]
            · rw [hExpected]
              exact hOutput

end LeanExeGen.GeneratedRa8e90ffc5781d113.Behavior
