import LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec
import LeanExeGen.GeneratedRa8e90ffc5781d113.Program
import LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.Control
import Project.ProofKit.FixedArrayCapacity
import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayFold
import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArrayTraversalInput
import Project.ProofKit.Frame
import Project.ProofKit.ScalarTransition

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRa8e90ffc5781d113.Behavior

open Wasm Project.ProofKit

def publicPost (inputPtr : UInt64) (expected : Array UInt64) :
    Wasm.Assertion Unit :=
  fun continuation => match continuation with
  | .Fallthrough final frame =>
      ∃ outputPtr,
        List.take func0Def.results.length frame.values ++
            List.drop func0Def.numParams [.i64 inputPtr] = [.i64 outputPtr] ∧
          FormalSpec.UInt64ArrayAt final outputPtr expected
  | .Return final values =>
      ∃ outputPtr,
        List.take func0Def.results.length values ++
            List.drop func0Def.numParams [.i64 inputPtr] = [.i64 outputPtr] ∧
          FormalSpec.UInt64ArrayAt final outputPtr expected
  | _ => False

def productInv (foldSt : Wasm.Store Unit) (inputPtr root : UInt64)
    (input : Array UInt64) : Wasm.Store Unit → Wasm.Locals → Prop :=
  fun st frame =>
    st = foldSt ∧
      ∃ index v2 v3 v4 v5 v6 v8 v9 v10 v16 v17 v18 v19 v20,
        index ≤ input.size ∧
          frame = AnnotationMatches.function_0_array_fold_0_continuing_frame
            inputPtr
            (ArrayFold.foldPrefix input (fun product element =>
              product * element) 1 index)
            v2 v3 v4 v5 v6 root v8 v9 v10 inputPtr
            (UInt64.ofNat input.size) (UInt64.ofNat index)
            (UInt64.ofNat input.size) (UInt64.ofNat input.size)
            v16 v17 v18 v19 v20

def productMeasure (input : Array UInt64) (_st : Wasm.Store Unit)
    (frame : Wasm.Locals) : Nat :=
  input.size -
    (ScalarTransition.State.ofLocals frame).localU64ToNat 12

theorem productInv_values
    {foldSt st : Wasm.Store Unit} {inputPtr root : UInt64}
    {input : Array UInt64} {frame : Wasm.Locals}
    (hInv : productInv foldSt inputPtr root input st frame) :
    frame.values = [] := by
  rcases hInv with
    ⟨_, index, v2, v3, v4, v5, v6, v8, v9, v10, v16, v17, v18, v19,
      v20, _, rfl⟩
  rfl

theorem productFoldFrame_eq (inputPtr heapTop : UInt64) (inputSize : Nat) :
    FixedArrayFold.forwardSetupFrame
      (FixedArrayAllocatorWindow.allocFrame 2
        (FixedArrayCapacity.capacityFrame
          (FixedArrayLengthDispatch.branchFrame 7
            (func0Def.toLocals
              (List.take func0Def.numParams [.i64 inputPtr]).reverse)
            inputPtr)
          11 (FixedArrayCapacity.normalizedCapacity 1 1))
        heapTop 16)
      inputPtr inputSize 11 12 13 16 14 1 18 15 1 =
      AnnotationMatches.function_0_array_fold_0_continuing_frame
        inputPtr 1 0 0 0 0 0 (heapTop + 48) 0 0 0 inputPtr
        (UInt64.ofNat inputSize) 0 (UInt64.ofNat inputSize)
        (UInt64.ofNat inputSize) inputPtr 0 0 0 0 := by
  rfl

theorem productLoadedFrame_eq
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18
      v19 v20 value : UInt64) :
    FixedArrayTraversalInput.dynamicResultFrame
      (AnnotationMatches.function_0_array_fold_0_continuing_frame
        v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
        v18 v19 v20)
      2 value
      (AnnotationMatches.function_0_array_fold_0_continuing_item_valid
        v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
        v18 v19 v20) =
      AnnotationMatches.function_0_array_fold_0_continuing_frame
        v0 v1 value v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
        v18 v19 v20 := by
  simp [FixedArrayTraversalInput.dynamicResultFrame,
    AnnotationMatches.function_0_array_fold_0_continuing_frame,
    AnnotationMatches.function_0_array_fold_0_state,
    ScalarTransition.U64State.toState, Wasm.Locals.set]

theorem productMeasure_continuing_frame
    (input : Array UInt64) (st : Wasm.Store Unit)
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v16 v17 v18 v19
      v20 : UInt64}
    (index : Nat) (hIndex : index < UInt64.size) :
    productMeasure input st
      (AnnotationMatches.function_0_array_fold_0_continuing_frame
        v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 (UInt64.ofNat index)
        v14 v15 v16 v17 v18 v19 v20) = input.size - index := by
  simp [productMeasure,
    AnnotationMatches.function_0_array_fold_0_continuing_frame,
    AnnotationMatches.function_0_array_fold_0_state,
    ScalarTransition.U64State.toState, ScalarTransition.State.ofLocals,
    ScalarTransition.State.localU64ToNat,
    UInt64.toNat_ofNat_of_lt' hIndex]

set_option Elab.async false in
theorem productLoopBody_spec
    (env : Wasm.HostEnv Unit) (foldSt : Wasm.Store Unit)
    (inputPtr root : UInt64) (input : Array UInt64)
    (st : Wasm.Store Unit) (frame : Wasm.Locals)
    (Q : Wasm.Assertion Unit)
    (hInput : UInt64Array.At foldSt inputPtr input)
    (hInv : productInv foldSt inputPtr root input st frame)
    (hExit : ∀ completedFrame,
      productInv foldSt inputPtr root input foldSt completedFrame →
      completedFrame.get 13 =
        some (.i64 (UInt64.ofNat input.size)) →
      Q (.Break 1 foldSt completedFrame))
    (hRepeat : ∀ nextFrame,
      productInv foldSt inputPtr root input foldSt nextFrame →
      productMeasure input foldSt nextFrame <
        productMeasure input st frame →
      Q (.Break 0 foldSt nextFrame)) :
    Wasm.wp module
      (AnnotationMatches.function_0_array_fold_0_continuing_program ++
        AnnotationMatches.function_0_array_fold_0_step_program)
      Q st frame env := by
  rcases hInv with
    ⟨hStore, index, v2, v3, v4, v5, v6, v8, v9, v10, v16, v17, v18,
      v19, v20, hIndexLe, hFrame⟩
  subst st
  subst frame
  let accumulator := ArrayFold.foldPrefix input
    (fun product element => product * element) 1 index
  let currentFrame :=
    AnnotationMatches.function_0_array_fold_0_continuing_frame
      inputPtr accumulator v2 v3 v4 v5 v6 root v8 v9 v10 inputPtr
      (UInt64.ofNat input.size) (UInt64.ofNat index)
      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
      v16 v17 v18 v19 v20
  have hCurrentInv :
      productInv foldSt inputPtr root input foldSt currentFrame := by
    exact ⟨rfl, index, v2, v3, v4, v5, v6, v8, v9, v10, v16, v17, v18,
      v19, v20, hIndexLe, rfl⟩
  by_cases hDone : index = input.size
  · subst index
    change Wasm.wp module
      (FixedArrayTraversalInput.continuingProgram 11 13 15 2 ++
        AnnotationMatches.function_0_array_fold_0_step_program)
      Q foldSt currentFrame env
    apply FixedArrayTraversalInput.continuingProgram_exit_spec
      (index := UInt64.ofNat input.size)
    · rfl
    · rfl
    · rfl
    · apply hExit currentFrame hCurrentInv
      rfl
  · have hIndexLt : index < input.size := by omega
    have hIndex64 : index < UInt64.size := by
      have hSize := hInput.size_lt
      omega
    have hIndexToNat : (UInt64.ofNat index).toNat = index :=
      UInt64.toNat_ofNat_of_lt' hIndex64
    have hInputSizeToNat :
        (UInt64.ofNat input.size).toNat = input.size :=
      UInt64.toNat_ofNat_of_lt' hInput.size_lt
    have hContinue :
        UInt64.ofNat index < UInt64.ofNat input.size := by
      rw [UInt64.lt_iff_toNat_lt, hIndexToNat, hInputSizeToNat]
      exact hIndexLt
    apply AnnotationMatches.function_0_array_fold_0_continuing_spec
      (input := input) (index := index)
      (hIndexValue := rfl) (hContinue := hContinue)
      (hInput := hInput) (hIndex := hIndexLt)
    rw [productLoadedFrame_eq]
    let item := input[index]
    let nextAccumulator := accumulator * item
    let initialState := AnnotationMatches.function_0_array_fold_0_state
      inputPtr accumulator item v3 v4 v5 v6 root v8 v9 v10 inputPtr
      (UInt64.ofNat input.size) (UInt64.ofNat index)
      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
      v16 v17 v18 v19 v20
    let afterBody := AnnotationMatches.function_0_array_fold_0_state
      inputPtr nextAccumulator item nextAccumulator v4 v5 v6 root v8 v9 v10
      inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
      0 nextAccumulator 1 v19 v20
    let afterContinue := AnnotationMatches.function_0_array_fold_0_state
      inputPtr nextAccumulator item nextAccumulator v4 v5 v6 root v8 v9 v10
      inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index + 1)
      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
      0 nextAccumulator 1 v19 v20
    change Wasm.wp module
      AnnotationMatches.function_0_array_fold_0_step_program Q foldSt
      (initialState.toState.toLocals []) env
    rw [show AnnotationMatches.function_0_array_fold_0_step_program =
        ScalarTransition.guardedBackEdgeProgram 11
          AnnotationMatches.function_0_array_fold_0_body
          AnnotationMatches.function_0_array_fold_0_condition
          AnnotationMatches.function_0_array_fold_0_step_continuing ++ [] by
      simp [AnnotationMatches.function_0_array_fold_0_step_program]]
    apply ScalarTransition.guardedBackEdgeProgram_spec
      (initial := initialState.toState)
      (afterBody := afterBody.toState)
      (afterCondition := afterBody.toState)
      (result := false) (values := []) (rest := [])
    · simpa [initialState, afterBody, nextAccumulator, item,
        AnnotationMatches.function_0_array_fold_0_bodyTransition,
        ScalarTransition.U64Op.apply] using
        (AnnotationMatches.function_0_array_fold_0_body_eval
          inputPtr accumulator item v3 v4 v5 v6 root v8 v9 v10 inputPtr
          (UInt64.ofNat input.size) (UInt64.ofNat index)
          (UInt64.ofNat input.size) (UInt64.ofNat input.size)
          v16 v17 v18 v19 v20)
    · simpa [afterBody,
        AnnotationMatches.function_0_array_fold_0_conditionTransition] using
        (AnnotationMatches.function_0_array_fold_0_condition_eval
          inputPtr nextAccumulator item nextAccumulator v4 v5 v6 root v8 v9
          v10 inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
          (UInt64.ofNat input.size) (UInt64.ofNat input.size)
          0 nextAccumulator 1 v19 v20)
    · simp
    · intro _
      refine ⟨afterContinue.toState, ?_, ?_⟩
      · simpa [afterBody, afterContinue,
          AnnotationMatches.function_0_array_fold_0_step_continuingTransition,
          ScalarTransition.U64Op.apply] using
          (AnnotationMatches.function_0_array_fold_0_step_continuing_eval
            inputPtr nextAccumulator item nextAccumulator v4 v5 v6 root v8 v9
            v10 inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
            (UInt64.ofNat input.size) (UInt64.ofNat input.size)
            0 nextAccumulator 1 v19 v20)
      · have hIndexSucc :
            UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by
          change UInt64.ofNat index + UInt64.ofNat 1 =
            UInt64.ofNat (index + 1)
          exact (UInt64.ofNat_add index 1).symm
        have hAfterContinueFrame :
            afterContinue.toState.toLocals [] =
              AnnotationMatches.function_0_array_fold_0_continuing_frame
                inputPtr nextAccumulator item nextAccumulator v4 v5 v6 root
                v8 v9 v10 inputPtr (UInt64.ofNat input.size)
                (UInt64.ofNat (index + 1)) (UInt64.ofNat input.size)
                (UInt64.ofNat input.size) 0 nextAccumulator 1 v19 v20 := by
          dsimp [afterContinue]
          rw [hIndexSucc]
          rfl
        rw [hAfterContinueFrame]
        apply hRepeat
        · refine ⟨rfl, index + 1, item, nextAccumulator, v4, v5, v6, v8,
            v9, v10, 0, nextAccumulator, 1, v19, v20, by omega, ?_⟩
          dsimp [nextAccumulator, item, accumulator]
          rw [ArrayFold.foldPrefix_succ input
            (fun product element => product * element) 1 index hIndexLt]
        · rw [productMeasure_continuing_frame input foldSt (index + 1) (by
            have hSize := hInput.size_lt
            omega)]
          rw [productMeasure_continuing_frame input foldSt index hIndex64]
          omega

set_option Elab.async false in
theorem productSuffix_spec
    (env : Wasm.HostEnv Unit) (st : Wasm.Store Unit) (frame : Wasm.Locals)
    (inputPtr root value : UInt64) (input : Array UInt64)
    (hExpected : FormalSpec.expected input = #[value])
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 20)
    (hValues : frame.values = [])
    (hAccumulator : frame.get 1 = some (.i64 value))
    (hRoot : frame.get 7 = some (.i64 root))
    (hPayloadBound :
      (FixedArrayResult.payloadAddress root 0).toUInt32.toNat + 8 ≤
        st.mem.pages * 65536)
    (hOutput : UInt64Array.At
      (FixedArrayResult.writePayload st root 0 value) root #[value]) :
    Wasm.wp module
      AnnotationMatches.function_0_array_fold_0_singleton_result_program
      (FixedArrayEqNode.branchPost module env
        AnnotationMatches.function_0_length_dispatch_0_suffix_program
        (publicPost inputPtr (FormalSpec.expected input))) st frame env := by
  change Wasm.wp module
    (FixedArrayFold.singletonResultProgram 1 10 7 4 6) _ st frame env
  apply Wasm.wp.conseq
    (Q := FixedArrayFold.singletonResultPost 6 root value)
  · intro continuation hPost
    cases continuation
    case Fallthrough final resultFrame =>
      rcases hPost with ⟨hReturn, hArray⟩
      have hReturn' :
          ({ resultFrame with values := [] } : Wasm.Locals).get 6 =
            some (.i64 root) := by
        simpa only [Wasm.Locals.get] using hReturn
      simp only [FixedArrayEqNode.branchPost]
      unfold AnnotationMatches.function_0_length_dispatch_0_suffix_program
      simp only [wp_localGet_cons, hReturn', Wasm.wp_nil, publicPost]
      refine ⟨root, rfl, ?_⟩
      rw [hExpected]
      change FormalSpec.UInt64ArrayAt final root #[value] at hArray
      exact hArray
    all_goals simp [FixedArrayFold.singletonResultPost] at hPost
  · have hResultLower : frame.params.length ≤ 10 := by omega
    have hResultValid : frame.validIndex 10 := by
      simp [Wasm.Locals.validIndex, hParams, hLocals]
    have hRoot' :
        (FixedArrayFold.resultFrame frame 10 value).get 7 =
          some (.i64 root) := by
      simpa [FixedArrayFold.resultFrame, Wasm.Locals.get, hParams, hLocals]
        using hRoot
    have hResult :
        (FixedArrayFold.resultFrame frame 10 value).get 10 =
          some (.i64 value) := by
      simp [FixedArrayFold.resultFrame, Wasm.Locals.get, hParams, hLocals]
    have hPlacedParams :
        (FixedArrayFold.resultFrame frame 10 value).params.length = 1 := by
      rw [FixedArrayFold.resultFrame_params, hParams]
    have hPlacedLocals :
        (FixedArrayFold.resultFrame frame 10 value).locals.length = 20 := by
      rw [FixedArrayFold.resultFrame_locals_length, hLocals]
    have hDestinationLower :
        (FixedArrayFold.resultFrame frame 10 value).params.length ≤ 4 := by
      omega
    have hDestinationValid :
        (FixedArrayFold.resultFrame frame 10 value).validIndex 4 := by
      simp [Wasm.Locals.validIndex, hPlacedParams, hPlacedLocals]
    have hReturnLower :
        (FixedArrayFold.resultFrame frame 10 value).params.length ≤ 6 := by
      omega
    have hReturnValid :
        (FixedArrayFold.resultFrame frame 10 value).validIndex 6 := by
      simp [Wasm.Locals.validIndex, hPlacedParams, hPlacedLocals]
    apply FixedArrayFold.singletonResultProgram_spec
    · exact hValues
    · exact hAccumulator
    · exact hResultLower
    · exact hResultValid
    · exact hRoot'
    · exact hResult
    · exact hPayloadBound
    · exact hDestinationLower
    · exact hDestinationValid
    · exact hReturnLower
    · exact hReturnValid
    · exact hOutput

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
  change Wasm.wp _ func0 _ _ _ _
  apply Wasm.wp.conseq
    (Q := publicPost inputPtr (FormalSpec.expected input))
  · intro continuation hPost
    cases continuation <;> simpa [publicPost] using hPost
  rw [AnnotationMatches.function_0_length_dispatch_0_function_eq]
  wp_fixed_array_length_le_dispatch_from hArray at 7, 8
  · rfl
  · rfl
  · norm_num
  · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams]
  · norm_num [UInt64.size]
  · intro hSize
    change Wasm.wp _ (FixedArrayCapacity.constantProgram 1 1 11 ++ _) _ _ _ _
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
        FixedArrayLengthDispatch.branchFrame]
    · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
        FixedArrayLengthDispatch.branchFrame, Wasm.Locals.validIndex]
    · change Wasm.wp _ (FixedArrayAllocatorWindow.region 2 1 ++ _) _ _ _ _
      apply FixedArrayAllocatorWindow.region_spec_withTail
        (offset := 2) (tail := 4) (heapTop := heapTop) (capacity := 16)
        (stride := 1) (allocs := allocs)
      · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
          FixedArrayLengthDispatch.branchFrame, FixedArrayCapacity.capacityFrame]
      · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
          FixedArrayLengthDispatch.branchFrame, FixedArrayCapacity.capacityFrame]
      · rfl
      · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
          FixedArrayLengthDispatch.branchFrame, FixedArrayCapacity.capacityFrame,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity] <;> decide
      · decide
      · simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · let postCapacityFrame := FixedArrayCapacity.capacityFrame
          (FixedArrayLengthDispatch.branchFrame 7
            (func0Def.toLocals
              (List.take func0Def.numParams [.i64 inputPtr]).reverse)
            inputPtr)
          11 (FixedArrayCapacity.normalizedCapacity 1 1)
        let allocFrame := FixedArrayAllocatorWindow.allocFrame 2
          postCapacityFrame heapTop 16
        let allocSt := FixedArrayAllocator.allocStore initial heapTop 16 1 allocs
        let foldSt := FixedArrayResult.writeLength allocSt (heapTop + 48) 1
        have hAllocFit :
            heapTop.toNat + 48 + (16 : UInt64).toNat ≤
              initial.mem.pages * 65536 := by
          simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
        have hFacts := Allocation.bumpFacts heapTop 16 initial.mem.pages
          hAllocFit hPages
        have hRootAddress :
            (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
          simpa using hFacts.wordAddress_toNat 0 (by decide)
        have hAllocValues : allocFrame.values = [] := rfl
        have hAllocParams : allocFrame.params = [.i64 inputPtr] := by
          norm_num [allocFrame, postCapacityFrame,
            FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame,
            func0Def, Wasm.Function.toLocals, Wasm.Function.numParams]
        have hAllocLocals : allocFrame.locals.length = 20 := by
          norm_num [allocFrame, postCapacityFrame,
            FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame,
            func0Def, Wasm.Function.toLocals, Wasm.Function.numParams]
        have hAllocRoot :
            allocFrame.get 7 = some (.i64 (heapTop + 48)) := by
          norm_num [allocFrame, postCapacityFrame,
            FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame,
            FixedArrayCapacity.normalizedCapacity,
            FixedArrayCapacity.unnormalizedCapacity,
            func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.Locals.get] <;> decide
        have hInputAlloc := FixedArrayPairResult.input_preserved_by_alloc
          initial heapTop 16 1 allocs inputPtr input hArray hInputBelow
          hAllocFit hPages
        have hInputFold : UInt64Array.At foldSt inputPtr input := by
          have hWritten := hInputAlloc.write64After
            (address := (heapTop + 48).toUInt32) (value := 1) (by
              rw [hRootAddress]
              omega)
          exact hWritten
        change Wasm.wp module
          (FixedArrayResult.lengthStoreProgram 7 1 ++ _) _ allocSt allocFrame env
        apply FixedArrayResult.lengthStore_spec (root := heapTop + 48)
        · exact hAllocValues
        · exact hAllocRoot
        · rw [hRootAddress]
          simp only [allocSt, FixedArrayAllocator.allocStore_pages]
          omega
        · change Wasm.wp module
            (FixedArrayFold.forwardSetupProgram 11 12 13 16 14 1 18 15 1 ++ _)
            _ foldSt allocFrame env
          apply FixedArrayFold.forwardSetupProgram_spec
            (inputPtr := inputPtr) (input := input)
          · exact hAllocParams
          · exact hAllocValues
          · intro slot hSlot
            simp [FixedArrayFold.setupLocals, hAllocLocals] at hSlot ⊢
            omega
          · decide
          · exact hInputFold
          · let foldFrame := FixedArrayFold.forwardSetupFrame allocFrame
              inputPtr input.size 11 12 13 16 14 1 18 15 1
            change Wasm.wp module
              ([.block 0 0 [.loop 0 0
                (AnnotationMatches.function_0_array_fold_0_continuing_program ++
                  AnnotationMatches.function_0_array_fold_0_step_program)]] ++
                AnnotationMatches.function_0_array_fold_0_singleton_result_program)
              _ foldSt foldFrame env
            apply Wasm.wp_block_cons
            apply Wasm.wp_loop_cons
              (Inv := productInv foldSt inputPtr (heapTop + 48) input)
              (μ := productMeasure input)
            · rw [show foldFrame =
                  AnnotationMatches.function_0_array_fold_0_continuing_frame
                    inputPtr 1 0 0 0 0 0 (heapTop + 48) 0 0 0 inputPtr
                    (UInt64.ofNat input.size) 0 (UInt64.ofNat input.size)
                    (UInt64.ofNat input.size) inputPtr 0 0 0 0 by
                exact productFoldFrame_eq inputPtr heapTop input.size]
              refine ⟨rfl, 0, 0, 0, 0, 0, 0, 0, 0, 0, inputPtr,
                0, 0, 0, 0, by omega, ?_⟩
              simp [ArrayFold.foldPrefix]
            · intro currentSt currentFrame hCurrent
              have hCurrentValues := productInv_values hCurrent
              apply productLoopBody_spec
                (env := env) (foldSt := foldSt) (inputPtr := inputPtr)
                (root := heapTop + 48) (input := input)
                (st := currentSt) (frame := currentFrame)
                (hInput := hInputFold) (hInv := hCurrent)
              · rintro completedFrame
                  ⟨_, index, v2, v3, v4, v5, v6, v8, v9, v10, v16, v17,
                    v18, v19, v20, hIndexLe, hCompletedFrame⟩ hIndexValue
                subst completedFrame
                have hEncoded :
                    UInt64.ofNat index = UInt64.ofNat input.size := by
                  simpa [
                    AnnotationMatches.function_0_array_fold_0_continuing_frame,
                    AnnotationMatches.function_0_array_fold_0_state,
                    ScalarTransition.U64State.toState,
                    ScalarTransition.State.toLocals, Wasm.Locals.get,
                    ScalarTransition.State.get] using hIndexValue
                have hIndex64 : index < UInt64.size := by
                  have hSize64 := hInputFold.size_lt
                  omega
                have hIndexEq : index = input.size := by
                  have hEq := (hInputFold.encodedSize_eq
                    (size := index) hIndex64).mp hEncoded.symm
                  omega
                subst index
                let value := ArrayFold.foldPrefix input
                  (fun product element => product * element) 1 input.size
                have hResultFit32 :
                    (heapTop + 48).toNat + 16 ≤ 4294967296 := by
                  rw [hFacts.rootToNat]
                  simpa using hFacts.fit32
                have hResultFitMemory :
                    (heapTop + 48).toNat + 16 ≤
                      allocSt.mem.pages * 65536 := by
                  rw [hFacts.rootToNat]
                  simpa [allocSt, FixedArrayAllocator.allocStore_pages] using
                    hAllocFit
                have hSingleton := FixedArrayResult.singletonStore_at allocSt
                  (heapTop + 48) value hResultFit32 hResultFitMemory
                have hOutput : UInt64Array.At
                    (FixedArrayResult.writePayload foldSt (heapTop + 48) 0
                      value)
                    (heapTop + 48) #[value] := by
                  simpa [foldSt, FixedArrayResult.singletonStore] using
                    hSingleton
                have hPayloadBound :
                    (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat +
                        8 ≤ foldSt.mem.pages * 65536 := by
                  simpa [FixedArrayResult.payloadAddress,
                    FixedArrayResult.writePayload, Mem.write64_pages] using
                    hOutput.elementBound 0 (by simp)
                change Wasm.wp module
                  AnnotationMatches.function_0_array_fold_0_singleton_result_program
                  (FixedArrayEqNode.branchPost module env
                    AnnotationMatches.function_0_length_dispatch_0_suffix_program
                    (publicPost inputPtr (FormalSpec.expected input)))
                  foldSt
                  (AnnotationMatches.function_0_array_fold_0_continuing_frame
                    inputPtr value v2 v3 v4 v5 v6 (heapTop + 48) v8 v9 v10
                    inputPtr (UInt64.ofNat input.size)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    (UInt64.ofNat input.size) v16 v17 v18 v19 v20)
                  env
                apply productSuffix_spec
                  (inputPtr := inputPtr) (root := heapTop + 48)
                  (value := value) (input := input)
                · simp [FormalSpec.expected, hSize, value,
                    ArrayFold.foldPrefix_size]
                · rfl
                · rfl
                · rfl
                · rfl
                · rfl
                · exact hPayloadBound
                · exact hOutput
              · intro nextFrame hNext hDecrease
                have hNextValues := productInv_values hNext
                have hNextFrameEq :
                    ({ nextFrame with values := [] } : Wasm.Locals) =
                      nextFrame := by
                  cases nextFrame
                  simp_all
                simpa [hCurrentValues, hNextFrameEq] using
                  And.intro hNext hDecrease
  · intro hSize
    change Wasm.wp _ (FixedArrayCapacity.constantProgram 0 1 11 ++ _) _ _ _ _
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
        FixedArrayLengthDispatch.branchFrame]
    · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
        FixedArrayLengthDispatch.branchFrame, Wasm.Locals.validIndex]
    · change Wasm.wp _ (FixedArrayAllocatorWindow.region 2 1 ++ _) _ _ _ _
      apply FixedArrayAllocatorWindow.region_spec_withTail
        (offset := 2) (tail := 4) (heapTop := heapTop) (capacity := 8)
        (stride := 1) (allocs := allocs)
      · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
          FixedArrayLengthDispatch.branchFrame, FixedArrayCapacity.capacityFrame]
      · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
          FixedArrayLengthDispatch.branchFrame, FixedArrayCapacity.capacityFrame]
      · rfl
      · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
          FixedArrayLengthDispatch.branchFrame, FixedArrayCapacity.capacityFrame,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity] <;> decide
      · decide
      · simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · let postCapacityFrame := FixedArrayCapacity.capacityFrame
          (FixedArrayLengthDispatch.branchFrame 7
            (func0Def.toLocals
              (List.take func0Def.numParams [.i64 inputPtr]).reverse)
            inputPtr)
          11 (FixedArrayCapacity.normalizedCapacity 0 1)
        let allocFrame := FixedArrayAllocatorWindow.allocFrame 2
          postCapacityFrame heapTop 8
        let allocSt := FixedArrayAllocator.allocStore initial heapTop 8 1 allocs
        have hAllocFit :
            heapTop.toNat + 48 + (8 : UInt64).toNat ≤
              initial.mem.pages * 65536 := by
          simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
        have hFacts := Allocation.bumpFacts heapTop 8 initial.mem.pages
          hAllocFit hPages
        have hAllocValues : allocFrame.values = [] := rfl
        have hAllocParams : allocFrame.params.length = 1 := by
          norm_num [allocFrame, postCapacityFrame,
            FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame,
            func0Def, Wasm.Function.toLocals, Wasm.Function.numParams]
        have hAllocLocals : allocFrame.locals.length = 20 := by
          norm_num [allocFrame, postCapacityFrame,
            FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame,
            func0Def, Wasm.Function.toLocals, Wasm.Function.numParams]
        have hAllocRoot :
            allocFrame.get 7 = some (.i64 (heapTop + 48)) := by
          norm_num [allocFrame, postCapacityFrame,
            FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayLengthDispatch.branchFrame,
            FixedArrayCapacity.normalizedCapacity,
            FixedArrayCapacity.unnormalizedCapacity,
            func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.Locals.get] <;> decide
        have hDestinationLower : allocFrame.params.length ≤ 5 := by omega
        have hDestinationValid : allocFrame.validIndex 5 := by
          simp [Wasm.Locals.validIndex, hAllocParams, hAllocLocals]
        have hReturnLower : allocFrame.params.length ≤ 6 := by omega
        have hReturnValid : allocFrame.validIndex 6 := by
          simp [Wasm.Locals.validIndex, hAllocParams, hAllocLocals]
        change Wasm.wp module
          (FixedArrayResult.lengthStoreProgram 7 0 ++
            FixedArrayResult.finishProgram 7 5 6) _ allocSt allocFrame env
        apply FixedArrayResult.lengthStore_spec (root := heapTop + 48)
        · exact hAllocValues
        · exact hAllocRoot
        · have hRootAddress :
              (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
            simpa using hFacts.wordAddress_toNat 0 (by decide)
          rw [hRootAddress]
          simpa [allocSt, FixedArrayAllocator.allocStore_pages] using hAllocFit
        · apply FixedArrayResult.finishProgram_spec (root := heapTop + 48)
          · exact hAllocValues
          · exact hAllocRoot
          · exact hDestinationLower
          · exact hDestinationValid
          · exact hReturnLower
          · exact hReturnValid
          · have hOutputFit32' :
                (heapTop + 48).toNat + 8 ≤ 4294967296 := by
              rw [hFacts.rootToNat]
              simpa [FormalSpec.expected, hSize] using hOutputFit32
            have hOutputFitMemory' :
                (heapTop + 48).toNat + 8 ≤ allocSt.mem.pages * 65536 := by
              rw [hFacts.rootToNat]
              simpa [allocSt, FixedArrayAllocator.allocStore_pages,
                FormalSpec.expected, hSize] using hOutputFitMemory
            have hOutput := FixedArrayResult.emptyStore_at allocSt
              (heapTop + 48) hOutputFit32' hOutputFitMemory'
            rw [Wasm.wp_nil]
            simp only [FixedArrayEqNode.branchPost]
            unfold AnnotationMatches.function_0_length_dispatch_0_suffix_program
            simp only [wp_localGet_cons, Wasm.wp_nil]
            refine ⟨heapTop + 48, ?_, ?_⟩
            · rfl
            · change FormalSpec.UInt64ArrayAt
                (FixedArrayResult.writeLength allocSt (heapTop + 48) 0)
                (heapTop + 48) #[] at hOutput
              simpa [FormalSpec.expected, hSize] using hOutput

end LeanExeGen.GeneratedRa8e90ffc5781d113.Behavior
