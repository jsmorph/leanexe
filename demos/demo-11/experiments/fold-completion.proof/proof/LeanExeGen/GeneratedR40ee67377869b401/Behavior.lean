import LeanExeGen.GeneratedR40ee67377869b401.FormalSpec
import LeanExeGen.GeneratedR40ee67377869b401.Program
import LeanExeGen.GeneratedR40ee67377869b401.AnnotationMatches
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

namespace LeanExeGen.GeneratedR40ee67377869b401.Behavior

open Wasm Project.ProofKit

private def xorLoopProgram : Wasm.Program :=
  [.block 0 0 [.loop 0 0
    (AnnotationMatches.function_0_array_fold_0_continuing_program ++
      AnnotationMatches.function_0_array_fold_0_step_program)]]

private def xorFrame (inputPtr root : UInt64) (input : Array UInt64)
    (index : Nat) (item scratch done staged release : UInt64) : Wasm.Locals :=
  AnnotationMatches.function_0_array_fold_0_continuing_frame
    inputPtr (ArrayFold.foldPrefix input UInt64.xor 0 index)
    item scratch 0 0 0 root 0 0 0 inputPtr
    (UInt64.ofNat input.size) (UInt64.ofNat index)
    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
    done staged release 0 0

private def xorInvariant (loopStore : Wasm.Store Unit)
    (inputPtr root : UInt64) (input : Array UInt64) :
    Wasm.Store Unit → Wasm.Locals → Prop :=
  fun st frame => ∃ index item scratch done staged release,
    index ≤ input.size ∧ st = loopStore ∧
      frame = xorFrame inputPtr root input index item scratch done staged release

private def xorMeasure (input : Array UInt64) :
    Wasm.Store Unit → Wasm.Locals → Nat :=
  fun _ frame =>
    match frame.get 13 with
    | some (.i64 index) => input.size - index.toNat
    | _ => input.size + 1

private def publicPost (inputPtr : UInt64) (input : Array UInt64) :
    Wasm.Assertion Unit :=
  fun continuation => match continuation with
  | .Fallthrough st frame => ∃ outputPtr,
      List.take func0Def.results.length frame.values ++
          List.drop func0Def.numParams [.i64 inputPtr] = [.i64 outputPtr] ∧
        FormalSpec.UInt64ArrayAt st outputPtr (FormalSpec.expected input)
  | .Return st values => ∃ outputPtr,
      List.take func0Def.results.length values ++
          List.drop func0Def.numParams [.i64 inputPtr] = [.i64 outputPtr] ∧
        FormalSpec.UInt64ArrayAt st outputPtr (FormalSpec.expected input)
  | _ => False

theorem artifact_behavior :
    LeanExeGen.GeneratedR40ee67377869b401.FormalSpec.ArtifactSpec LeanExeGen.GeneratedR40ee67377869b401.«module» := by
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
  apply Wasm.wp.conseq (Q := publicPost inputPtr input)
  · intro continuation hPost
    cases continuation <;> simpa [publicPost] using hPost
  rw [AnnotationMatches.function_0_length_dispatch_0_function_eq]
  wp_fixed_array_length_le_dispatch_from hArray at 7, 8
  · rfl
  · rfl
  · norm_num
  · norm_num [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  · norm_num
  · intro hSize
    have hFit16 : heapTop.toNat + 48 + 16 ≤
        initial.mem.pages * 65536 := by
      simpa [FormalSpec.expected, hSize] using hOutputFitMemory
    have hFacts16 := Allocation.bumpFacts heapTop 16 initial.mem.pages
      hFit16 hPages
    change Wasm.wp _ (FixedArrayCapacity.constantProgram 1 1 11 ++ _) _ _ _ _
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · norm_num [Wasm.Locals.validIndex, FixedArrayLengthDispatch.branchFrame,
        func0Def, Function.toLocals, Function.numParams, ValueType.zero]
    · change Wasm.wp _ (FixedArrayAllocatorWindow.region 2 1 ++ _) _ _ _ _
      apply FixedArrayAllocatorWindow.region_spec_withTail 2 4
        (heapTop := heapTop) (capacity := 16) (allocs := allocs)
      · simp only [FixedArrayCapacity.capacityFrame_params,
          FixedArrayLengthDispatch.branchFrame_params]
        norm_num [func0Def, Function.toLocals, Function.numParams,
          ValueType.zero]
      · simp only [FixedArrayCapacity.capacityFrame_locals_length,
          FixedArrayLengthDispatch.branchFrame_locals_length]
        norm_num [func0Def, Function.toLocals, Function.numParams,
          ValueType.zero]
      · rfl
      · norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def, Function.toLocals,
          Function.numParams, ValueType.zero,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity]
        decide
      · decide
      · exact hFit16
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · let allocSt := FixedArrayAllocator.allocStore initial heapTop 16 1 allocs
        let allocFrame := FixedArrayAllocatorWindow.allocFrame 2
          (FixedArrayCapacity.capacityFrame
            (FixedArrayLengthDispatch.branchFrame 7
              (func0Def.toLocals
                (List.take func0Def.numParams [.i64 inputPtr]).reverse)
              inputPtr)
            11 (FixedArrayCapacity.normalizedCapacity 1 1))
          heapTop 16
        let root := heapTop + 48
        let lengthSt := FixedArrayResult.writeLength allocSt root 1
        have hAllocValues : allocFrame.values = [] := by
          rfl
        have hAllocParams : allocFrame.params = [.i64 inputPtr] := by
          rfl
        have hAllocLocals : allocFrame.locals.length = 20 := by
          simp only [allocFrame, FixedArrayAllocatorWindow.allocFrame,
            List.length_set, FixedArrayCapacity.capacityFrame_locals_length,
            FixedArrayLengthDispatch.branchFrame_locals_length]
          norm_num [func0Def, Function.toLocals, Function.numParams,
            ValueType.zero]
        have hRoot : allocFrame.get 7 = some (.i64 root) := by
          norm_num [allocFrame, root, FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Function.toLocals, Function.numParams, ValueType.zero,
            Wasm.Locals.get, FixedArrayCapacity.normalizedCapacity,
            FixedArrayCapacity.unnormalizedCapacity]
        have hRootAddressNat : root.toUInt32.toNat = heapTop.toNat + 48 := by
          simpa [root] using hFacts16.wordAddress_toNat 0 (by decide)
        have hRootNat : root.toNat = heapTop.toNat + 48 := by
          simpa [root] using hFacts16.rootToNat
        have hPayloadAddressNat :
            (FixedArrayResult.payloadAddress root 0).toUInt32.toNat =
              heapTop.toNat + 56 := by
          simpa [root, FixedArrayResult.payloadAddress] using
            hFacts16.wordAddress_toNat 1 (by decide)
        have hRootBound : root.toUInt32.toNat + 8 ≤
            allocSt.mem.pages * 65536 := by
          rw [hRootAddressNat]
          simp only [allocSt, FixedArrayAllocator.allocStore_pages]
          omega
        have hInputAlloc : UInt64Array.At allocSt inputPtr input := by
          exact FixedArrayPairResult.input_preserved_by_alloc initial heapTop
            16 1 allocs inputPtr input hArray hInputBelow hFit16 hPages
        have hInputLength : UInt64Array.At lengthSt inputPtr input := by
          have hAfter : inputPtr.toNat + 8 * (input.size + 1) ≤
              root.toUInt32.toNat := by
            rw [hRootAddressNat]
            omega
          simpa [lengthSt, FixedArrayResult.writeLength] using
            hInputAlloc.write64After hAfter
        have hPayloadBound :
            (FixedArrayResult.payloadAddress root 0).toUInt32.toNat + 8 ≤
              lengthSt.mem.pages * 65536 := by
          rw [hPayloadAddressNat]
          simp only [lengthSt, FixedArrayResult.writeLength_pages, allocSt,
            FixedArrayAllocator.allocStore_pages]
          omega
        have hSingleton (value : UInt64) : UInt64Array.At
            (FixedArrayResult.writePayload lengthSt root 0 value)
            root #[value] := by
          have hFit32 : root.toNat + 16 ≤ 4294967296 := by
            rw [hRootNat]
            simpa [FormalSpec.expected, hSize] using hOutputFit32
          have hFitMemory : root.toNat + 16 ≤
              allocSt.mem.pages * 65536 := by
            rw [hRootNat]
            simp only [allocSt, FixedArrayAllocator.allocStore_pages]
            omega
          simpa [lengthSt, FixedArrayResult.singletonStore] using
            FixedArrayResult.singletonStore_at allocSt root value
              hFit32 hFitMemory
        change Wasm.wp _ (FixedArrayResult.lengthStoreProgram 7 1 ++ _)
          _ allocSt allocFrame _
        apply FixedArrayResult.lengthStore_spec
        · exact hAllocValues
        · exact hRoot
        · exact hRootBound
        · change Wasm.wp _
            (FixedArrayFold.forwardSetupProgram 11 12 13 16 14 1 18 15 0 ++ _)
            _ lengthSt allocFrame _
          apply FixedArrayFold.forwardSetupProgram_spec
          · exact hAllocParams
          · exact hAllocValues
          · intro slot hSlot
            rw [hAllocLocals]
            simp [FixedArrayFold.setupLocals] at hSlot
            omega
          · decide
          · exact hInputLength
          · let setupFrame := FixedArrayFold.forwardSetupFrame allocFrame
              inputPtr input.size 11 12 13 16 14 1 18 15 0
            change Wasm.wp _
              (xorLoopProgram ++
                AnnotationMatches.function_0_array_fold_0_singleton_result_program)
              _ lengthSt setupFrame _
            unfold xorLoopProgram
            simp only [List.cons_append, List.nil_append]
            apply Wasm.wp_block_cons
            apply Wasm.wp_loop_cons
              (Inv := xorInvariant lengthSt inputPtr root input)
              (μ := xorMeasure input)
            · refine ⟨0, 0, 0, inputPtr, 0, 0, by omega, rfl, ?_⟩
              norm_num [setupFrame, xorFrame,
                FixedArrayFold.forwardSetupFrame, allocFrame,
                FixedArrayAllocatorWindow.allocFrame,
                FixedArrayCapacity.capacityFrame,
                FixedArrayLengthDispatch.branchFrame, func0Def,
                Function.toLocals, Function.numParams, ValueType.zero,
                AnnotationMatches.function_0_array_fold_0_continuing_frame,
                AnnotationMatches.function_0_array_fold_0_state,
                ScalarTransition.U64State.toState, ArrayFold.foldPrefix]
              exact ⟨rfl, rfl⟩
            · rintro st frame hInv
              rcases hInv with
                ⟨index, item, scratch, done, staged, release,
                  hIndexLe, hSt, hFrame⟩
              subst st
              subst frame
              by_cases hExit : index = input.size
              · subst index
                apply FixedArrayTraversalInput.continuingProgram_exit_spec
                  (index := UInt64.ofNat input.size)
                · simp only [xorFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_values]
                · simp only [xorFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13]
                · simp only [xorFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_get_15]
                · have hExpected : FormalSpec.expected input =
                      #[ArrayFold.foldPrefix input UInt64.xor 0 input.size] := by
                    simp [FormalSpec.expected, hSize,
                      ArrayFold.foldPrefix_size]
                  have hSuffix : Wasm.wp module
                      AnnotationMatches.function_0_array_fold_0_singleton_result_program
                      (FixedArrayEqNode.branchPost module env
                        AnnotationMatches.function_0_length_dispatch_0_suffix_program
                        (publicPost inputPtr input)) lengthSt
                      (xorFrame inputPtr root input input.size item scratch done
                        staged release) env := by
                    apply AnnotationMatches.function_0_array_fold_0_singleton_result_spec
                    · exact hPayloadBound
                    · simp only [FixedArrayEqNode.branchPost]
                      simp only [
                        AnnotationMatches.function_0_length_dispatch_0_suffix_program,
                        wp_localGet_cons, Wasm.wp_nil, publicPost]
                      refine ⟨root, rfl, ?_⟩
                      change UInt64Array.At _ _ _
                      rw [hExpected]
                      exact hSingleton
                        (ArrayFold.foldPrefix input UInt64.xor 0 input.size)
                  simp only [List.take_zero, List.drop_zero, List.nil_append,
                    setupFrame, FixedArrayFold.forwardSetupFrame_values,
                    xorFrame]
                  convert hSuffix using 1
                  apply Frame.ext <;> rfl
              · have hIndex : index < input.size := by
                  omega
                let accumulator :=
                  ArrayFold.foldPrefix input UInt64.xor 0 index
                let element := input[index]
                let next := accumulator ^^^ element
                let initialState :=
                  AnnotationMatches.function_0_array_fold_0_state
                    inputPtr accumulator element scratch 0 0 0 root 0 0 0
                    inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    done staged release 0 0
                let afterBodyState :=
                  AnnotationMatches.function_0_array_fold_0_state
                    inputPtr next element next 0 0 0 root 0 0 0 inputPtr
                    (UInt64.ofNat input.size) (UInt64.ofNat index)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    0 next 1 0 0
                have hValues :
                    (xorFrame inputPtr root input index item scratch done staged
                      release).values = [] := by
                  simp only [xorFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_values]
                have hArrayLocal :
                    (xorFrame inputPtr root input index item scratch done staged
                      release).get 11 = some (.i64 inputPtr) := by
                  simp only [xorFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_get_11]
                have hIndexLocal :
                    (xorFrame inputPtr root input index item scratch done staged
                      release).get 13 = some (.i64 (UInt64.ofNat index)) := by
                  simp only [xorFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13]
                have hStopLocal :
                    (xorFrame inputPtr root input index item scratch done staged
                      release).get 15 =
                        some (.i64 (UInt64.ofNat input.size)) := by
                  simp only [xorFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_get_15]
                have hGuard : UInt64.ofNat index < UInt64.ofNat input.size := by
                  have hIndexToNat : (UInt64.ofNat index).toNat = index :=
                    UInt64.toNat_ofNat_of_lt' (by
                      have hInputSize := hInputLength.size_lt
                      omega)
                  have hSizeToNat : (UInt64.ofNat input.size).toNat =
                      input.size :=
                    UInt64.toNat_ofNat_of_lt' hInputLength.size_lt
                  rw [UInt64.lt_iff_toNat_lt, hIndexToNat, hSizeToNat]
                  exact hIndex
                have hItemValid :
                    (xorFrame inputPtr root input index item scratch done staged
                      release).validIndex 2 := by
                  simpa only [xorFrame] using
                    AnnotationMatches.function_0_array_fold_0_continuing_item_valid
                      inputPtr accumulator item scratch 0 0 0 root 0 0 0
                      inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      done staged release 0 0
                have hLoaded : FixedArrayTraversalInput.dynamicResultFrame
                    (xorFrame inputPtr root input index item scratch done staged
                      release) 2 element hItemValid =
                      initialState.toState.toLocals [] := by
                  simpa only [initialState, element, accumulator, xorFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame]
                    using
                    AnnotationMatches.function_0_array_fold_0_continuing_loaded_frame_eq
                      inputPtr accumulator item scratch 0 0 0 root 0 0 0
                      inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      done staged release 0 0 element
                have hBody : AnnotationMatches.function_0_array_fold_0_body.eval
                    11 initialState.toState = some afterBodyState.toState := by
                  simpa [afterBodyState, initialState, next,
                    AnnotationMatches.function_0_array_fold_0_bodyTransition,
                    ScalarTransition.U64Op.apply] using
                    AnnotationMatches.function_0_array_fold_0_body_eval
                      inputPtr accumulator element scratch 0 0 0 root 0 0 0
                      inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      done staged release 0 0
                have hCondition :
                    AnnotationMatches.function_0_array_fold_0_condition.eval 11
                      afterBodyState.toState =
                        some (false, afterBodyState.toState) := by
                  simpa [afterBodyState,
                    AnnotationMatches.function_0_array_fold_0_conditionTransition]
                    using
                    AnnotationMatches.function_0_array_fold_0_condition_eval
                      inputPtr next element next 0 0 0 root 0 0 0 inputPtr
                      (UInt64.ofNat input.size) (UInt64.ofNat index)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      0 next 1 0 0
                apply FixedArrayFoldBody.continuingGuardedProgram_spec
                  (arrayLocal := 11) (indexLocal := 13) (stopLocal := 15)
                  (itemLocal := 2) (scratch := 11)
                  (body := AnnotationMatches.function_0_array_fold_0_body)
                  (condition :=
                    AnnotationMatches.function_0_array_fold_0_condition)
                  (continuing :=
                    AnnotationMatches.function_0_array_fold_0_step_continuing)
                  (inputPtr := inputPtr) (indexValue := UInt64.ofNat index)
                  (stopValue := UInt64.ofNat input.size) (input := input)
                  (index := index) (initial := initialState.toState)
                  (afterBody := afterBodyState.toState)
                  (afterCondition := afterBodyState.toState) (result := false)
                  (hValues := hValues) (hArrayLocal := hArrayLocal)
                  (hIndexLocal := hIndexLocal) (hStopLocal := hStopLocal)
                  (hIndexValue := rfl) (hContinueGuard := hGuard)
                  (hItem := hItemValid) (hInput := hInputLength)
                  (hIndex := hIndex) (hLoaded := hLoaded)
                  (hStepProgram := rfl) (hBody := hBody)
                  (hCondition := hCondition)
                · intro hFalse
                  contradiction
                · intro _
                  let afterContinueState :=
                    AnnotationMatches.function_0_array_fold_0_state
                      inputPtr next element next 0 0 0 root 0 0 0 inputPtr
                      (UInt64.ofNat input.size) (UInt64.ofNat index + 1)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      0 next 1 0 0
                  have hStep :
                      AnnotationMatches.function_0_array_fold_0_step_continuing.eval
                        11 afterBodyState.toState =
                          some afterContinueState.toState := by
                    simpa [afterContinueState, afterBodyState,
                      AnnotationMatches.function_0_array_fold_0_step_continuingTransition,
                      ScalarTransition.U64Op.apply] using
                      AnnotationMatches.function_0_array_fold_0_step_continuing_eval
                        inputPtr next element next 0 0 0 root 0 0 0 inputPtr
                        (UInt64.ofNat input.size) (UInt64.ofNat index)
                        (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                        0 next 1 0 0
                  refine ⟨afterContinueState.toState, hStep, ?_⟩
                  simp only [List.take_zero, List.drop_zero, List.nil_append,
                    hValues]
                  change
                    xorInvariant lengthSt inputPtr root input lengthSt
                        (afterContinueState.toState.toLocals []) ∧
                      xorMeasure input lengthSt
                          (afterContinueState.toState.toLocals []) <
                        xorMeasure input lengthSt
                          (xorFrame inputPtr root input index item scratch done
                            staged release)
                  have hNextAccumulator :
                      ArrayFold.foldPrefix input UInt64.xor 0 (index + 1) =
                        next := by
                    rw [ArrayFold.foldPrefix_succ input UInt64.xor 0 index
                      hIndex]
                    rfl
                  have hNextIndex : UInt64.ofNat index + 1 =
                      UInt64.ofNat (index + 1) := by
                    change UInt64.ofNat index + UInt64.ofNat 1 =
                      UInt64.ofNat (index + 1)
                    rw [← UInt64.ofNat_add]
                  have hFrameNext : afterContinueState.toState.toLocals [] =
                      xorFrame inputPtr root input (index + 1) element next 0
                        next 1 := by
                    simp only [afterContinueState, xorFrame,
                      AnnotationMatches.function_0_array_fold_0_continuing_frame,
                      hNextAccumulator, hNextIndex]
                  constructor
                  · refine ⟨index + 1, element, next, 0, next, 1, by omega,
                      rfl, hFrameNext⟩
                  · rw [hFrameNext]
                    simp only [xorMeasure, xorFrame,
                      AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13]
                    have hCurrentToNat : (UInt64.ofNat index).toNat = index :=
                      UInt64.toNat_ofNat_of_lt' (by
                        have hInputSize := hInputLength.size_lt
                        omega)
                    have hNextToNat : (UInt64.ofNat (index + 1)).toNat =
                        index + 1 :=
                      UInt64.toNat_ofNat_of_lt' (by
                        have hInputSize := hInputLength.size_lt
                        omega)
                    rw [hCurrentToNat, hNextToNat]
                    omega
  · intro hSize
    have hFit8 : heapTop.toNat + 48 + 8 ≤
        initial.mem.pages * 65536 := by
      simpa [FormalSpec.expected, hSize] using hOutputFitMemory
    have hFacts8 := Allocation.bumpFacts heapTop 8 initial.mem.pages
      hFit8 hPages
    change Wasm.wp _ (FixedArrayCapacity.constantProgram 0 1 11 ++ _) _ _ _ _
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · norm_num [Wasm.Locals.validIndex, FixedArrayLengthDispatch.branchFrame,
        func0Def, Function.toLocals, Function.numParams, ValueType.zero]
    · change Wasm.wp _ (FixedArrayAllocatorWindow.region 2 1 ++ _) _ _ _ _
      apply FixedArrayAllocatorWindow.region_spec_withTail 2 4
        (heapTop := heapTop) (capacity := 8) (allocs := allocs)
      · simp only [FixedArrayCapacity.capacityFrame_params,
          FixedArrayLengthDispatch.branchFrame_params]
        norm_num [func0Def, Function.toLocals, Function.numParams,
          ValueType.zero]
      · simp only [FixedArrayCapacity.capacityFrame_locals_length,
          FixedArrayLengthDispatch.branchFrame_locals_length]
        norm_num [func0Def, Function.toLocals, Function.numParams,
          ValueType.zero]
      · rfl
      · norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame, func0Def, Function.toLocals,
          Function.numParams, ValueType.zero,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity]
        decide
      · decide
      · exact hFit8
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · let allocSt := FixedArrayAllocator.allocStore initial heapTop 8 1 allocs
        let allocFrame := FixedArrayAllocatorWindow.allocFrame 2
          (FixedArrayCapacity.capacityFrame
            (FixedArrayLengthDispatch.branchFrame 7
              (func0Def.toLocals
                (List.take func0Def.numParams [.i64 inputPtr]).reverse)
              inputPtr)
            11 (FixedArrayCapacity.normalizedCapacity 0 1))
          heapTop 8
        let root := heapTop + 48
        have hAllocValues : allocFrame.values = [] := by
          rfl
        have hAllocParams : allocFrame.params.length = 1 := by
          simp only [allocFrame, FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame_params,
            FixedArrayLengthDispatch.branchFrame_params]
          norm_num [func0Def, Function.toLocals, Function.numParams,
            ValueType.zero]
        have hAllocLocals : allocFrame.locals.length = 20 := by
          simp only [allocFrame, FixedArrayAllocatorWindow.allocFrame,
            List.length_set, FixedArrayCapacity.capacityFrame_locals_length,
            FixedArrayLengthDispatch.branchFrame_locals_length]
          norm_num [func0Def, Function.toLocals, Function.numParams,
            ValueType.zero]
        have hRoot : allocFrame.get 7 = some (.i64 root) := by
          norm_num [allocFrame, root, FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Function.toLocals, Function.numParams, ValueType.zero,
            Wasm.Locals.get, FixedArrayCapacity.normalizedCapacity,
            FixedArrayCapacity.unnormalizedCapacity]
        have hRootAddressNat : root.toUInt32.toNat = heapTop.toNat + 48 := by
          simpa [root] using hFacts8.wordAddress_toNat 0 (by decide)
        have hRootNat : root.toNat = heapTop.toNat + 48 := by
          simpa [root] using hFacts8.rootToNat
        have hRootBound : root.toUInt32.toNat + 8 ≤
            allocSt.mem.pages * 65536 := by
          rw [hRootAddressNat]
          simp only [allocSt, FixedArrayAllocator.allocStore_pages]
          omega
        have hEmpty : UInt64Array.At
            (FixedArrayResult.writeLength allocSt root 0) root #[] := by
          apply FixedArrayResult.emptyStore_at
          · rw [hRootNat]
            simpa [FormalSpec.expected, hSize] using hOutputFit32
          · rw [hRootNat]
            simp only [allocSt, FixedArrayAllocator.allocStore_pages]
            omega
        change Wasm.wp _
          (FixedArrayResult.lengthStoreProgram 7 0 ++
            FixedArrayResult.finishProgram 7 5 6) _ allocSt allocFrame _
        apply FixedArrayResult.lengthStore_spec
        · exact hAllocValues
        · exact hRoot
        · exact hRootBound
        · apply FixedArrayResult.finishProgram_spec
          · exact hAllocValues
          · exact hRoot
          · omega
          · simpa [Wasm.Locals.validIndex, hAllocParams, hAllocLocals]
          · omega
          · simpa [Wasm.Locals.validIndex, hAllocParams, hAllocLocals]
          · have hReturnGet := FixedArrayResult.finishFrame_return_get
                allocFrame 5 6 root (by omega)
                (by simpa [Wasm.Locals.validIndex, hAllocParams, hAllocLocals])
            simp only [Wasm.wp_nil, FixedArrayEqNode.branchPost]
            simp only [AnnotationMatches.function_0_length_dispatch_0_suffix_program,
              wp_localGet_cons, hReturnGet, Wasm.wp_nil]
            refine ⟨root, rfl, ?_⟩
            change UInt64Array.At _ root (FormalSpec.expected input)
            simpa [FormalSpec.expected, hSize] using hEmpty

end LeanExeGen.GeneratedR40ee67377869b401.Behavior
