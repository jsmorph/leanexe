import LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec
import LeanExeGen.GeneratedRa8e90ffc5781d113.Program
import LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.Control
import Project.ProofKit.FixedArrayCapacity
import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArrayFold
import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayPairResult
import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArrayResult
import Project.ProofKit.FixedArrayTraversalInput
import Project.ProofKit.Frame
import Project.ProofKit.ScalarTransition

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRa8e90ffc5781d113.Behavior

open Wasm Project.ProofKit

def productStep (product element : UInt64) : UInt64 :=
  product * element

def productLoopFrame (inputPtr root : UInt64) (inputSize index : Nat)
    (product item scratch conditionScratch staged releaseReady : UInt64) :
    Wasm.Locals :=
  LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame
    inputPtr product item scratch 0 0 0 root 0 0 0 inputPtr
    (UInt64.ofNat inputSize) (UInt64.ofNat index) (UInt64.ofNat inputSize)
    (UInt64.ofNat inputSize) conditionScratch staged releaseReady 0 0

def productLoopInv (loopStore : Wasm.Store Unit) (inputPtr root : UInt64)
    (input : Array UInt64) (st : Wasm.Store Unit) (frame : Wasm.Locals) : Prop :=
  ∃ index item scratch conditionScratch staged releaseReady,
    index ≤ input.size ∧
    st = loopStore ∧
    frame = productLoopFrame inputPtr root input.size index
      (ArrayFold.foldPrefix input productStep 1 index)
      item scratch conditionScratch staged releaseReady

def productLoopIndex (frame : Wasm.Locals) : Nat :=
  match frame.get 13 with
  | some (.i64 index) => index.toNat
  | _ => 0

def productLoopMeasure (input : Array UInt64) (_st : Wasm.Store Unit)
    (frame : Wasm.Locals) : Nat :=
  input.size - productLoopIndex frame

def productLoopPost (loopStore : Wasm.Store Unit) (inputPtr root : UInt64)
    (input : Array UInt64) : Wasm.Assertion Unit :=
  fun continuation => match continuation with
  | .Break 0 st frame =>
      ∃ item scratch conditionScratch staged releaseReady,
        st = loopStore ∧
        frame = productLoopFrame inputPtr root input.size input.size
          (ArrayFold.foldPrefix input productStep 1 input.size)
          item scratch conditionScratch staged releaseReady
  | _ => False

def productOutputPost (root : UInt64) (expected : Array UInt64) :
    Wasm.Assertion Unit :=
  fun continuation => match continuation with
  | .Fallthrough st frame =>
      frame.get 6 = some (.i64 root) ∧ UInt64Array.At st root expected
  | _ => False

theorem productSuffix_spec
    (module_ : Wasm.Module) (env : Wasm.HostEnv Unit) (st : Wasm.Store Unit)
    (inputPtr root product item scratch conditionScratch staged releaseReady :
      UInt64)
    (inputSize : Nat)
    (hPayloadBound :
      (FixedArrayResult.payloadAddress root 0).toUInt32.toNat + 8 ≤
        st.mem.pages * 65536)
    (hOutput : UInt64Array.At
      (FixedArrayResult.writePayload st root 0 product) root #[product]) :
    Wasm.wp module_
      (FixedArrayFold.resultProgram 1 10 ++
        (FixedArrayResult.payloadStoreProgram 7 10 0 ++
          FixedArrayResult.finishProgram 7 4 6))
      (productOutputPost root #[product]) st
      (productLoopFrame inputPtr root inputSize inputSize product
        item scratch conditionScratch staged releaseReady) env := by
  apply FixedArrayFold.resultProgram_spec (value := product)
  · rfl
  · rfl
  · norm_num [productLoopFrame,
      LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
      LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
      ScalarTransition.U64State.toState]
  · norm_num [productLoopFrame,
      LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
      LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
      ScalarTransition.U64State.toState, Wasm.Locals.validIndex]
  · apply FixedArrayResult.payloadStore_spec
      (root := root) (value := product)
      (rootLocal := 7) (scratchLocal := 10) (index := 0)
    · norm_num [FixedArrayFold.resultFrame, productLoopFrame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
        ScalarTransition.U64State.toState, Wasm.Locals.get]
    · norm_num [FixedArrayFold.resultFrame, productLoopFrame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
        ScalarTransition.U64State.toState, Wasm.Locals.get]
    · exact hPayloadBound
    · apply FixedArrayResult.finishProgram_spec
        (root := root) (rootLocal := 7)
        (destinationLocal := 4) (returnLocal := 6)
      · rfl
      · norm_num [FixedArrayFold.resultFrame, productLoopFrame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
          ScalarTransition.U64State.toState, Wasm.Locals.get]
      · norm_num [FixedArrayFold.resultFrame, productLoopFrame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
          ScalarTransition.U64State.toState]
      · norm_num [FixedArrayFold.resultFrame, productLoopFrame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
          ScalarTransition.U64State.toState, Wasm.Locals.validIndex]
      · norm_num [FixedArrayFold.resultFrame, productLoopFrame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
          ScalarTransition.U64State.toState]
      · norm_num [FixedArrayFold.resultFrame, productLoopFrame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
          ScalarTransition.U64State.toState, Wasm.Locals.validIndex]
      · simp only [Wasm.wp_nil, productOutputPost]
        refine ⟨?_, hOutput⟩
        norm_num [FixedArrayResult.finishFrame, FixedArrayFold.resultFrame,
          productLoopFrame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
          ScalarTransition.U64State.toState, Wasm.Locals.get]

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
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def) rfl
  wp_fixed_array_length_le_dispatch_from hArray at 7, 8
  · rfl
  · rfl
  · norm_num
  · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
      Wasm.Function.toLocals, Wasm.Function.numParams, Wasm.ValueType.zero]
  · norm_num [UInt64.size]
  · intro hSize
    have hAllocFit : heapTop.toNat + 48 + (16 : UInt64).toNat ≤
        initial.mem.pages * 65536 := by
      simpa [LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec.heapReserveBytes,
        hSize] using hHeapFitMemory
    have hFacts := Allocation.bumpFacts heapTop 16 initial.mem.pages
      hAllocFit hPages
    have hRootAddress : (heapTop + 48).toUInt32.toNat =
        heapTop.toNat + 48 := by
      simpa using hFacts.wordAddress_toNat 0 (by decide)
    have hExpected :
        LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec.expected input =
          #[input.foldl productStep 1] := by
      rw [LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec.expected,
        if_pos hSize]
      rfl
    have hResultFit32 : (heapTop + 48).toNat + 16 ≤ 4294967296 := by
      rw [hFacts.rootToNat]
      simpa [hExpected] using hOutputFit32
    have hResultFitMemory :
        (heapTop + 48).toNat + 16 ≤ initial.mem.pages * 65536 := by
      rw [hFacts.rootToNat]
      simpa [hExpected] using hOutputFitMemory
    have hPayloadBound :
        (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat + 8 ≤
          (FixedArrayResult.writeLength
            (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
            (heapTop + 48) 1).mem.pages * 65536 := by
      have hPayloadAddress :
          (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat =
            heapTop.toNat + 48 + 8 := by
        simpa [FixedArrayResult.payloadAddress] using
          hFacts.wordAddress_toNat 1 (by decide)
      rw [hPayloadAddress, FixedArrayResult.writeLength_pages,
        FixedArrayAllocator.allocStore_pages]
      rw [hFacts.rootToNat] at hResultFitMemory
      omega
    have hInputAlloc : UInt64Array.At
        (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
        inputPtr input :=
      FixedArrayPairResult.input_preserved_by_alloc initial heapTop 16 1
        allocs inputPtr input hArray hInputBelow hAllocFit hPages
    have hInputAfterLength : UInt64Array.At
        (FixedArrayResult.writeLength
          (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
          (heapTop + 48) 1) inputPtr input := by
      apply UInt64Array.At.write64After
        (h := hInputAlloc)
      rw [hRootAddress]
      omega
    change Wasm.wp _
      (FixedArrayCapacity.constantProgram 1 1 11 ++ _) _ _ _ _
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero, FixedArrayLengthDispatch.branchFrame]
    · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero, Wasm.Locals.validIndex,
        FixedArrayLengthDispatch.branchFrame]
    · change Wasm.wp _
        (FixedArrayAllocatorWindow.region 2 1 ++ _) _ _ _ _
      apply FixedArrayAllocatorWindow.region_spec_withTail 2 4
        (heapTop := heapTop) (capacity := 16) (stride := 1)
        (allocs := allocs)
      · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero, FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame]
      · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero, FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame]
      · rfl
      · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero, FixedArrayCapacity.capacityFrame,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity,
          FixedArrayLengthDispatch.branchFrame]
        decide
      · decide
      · exact hAllocFit
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · change Wasm.wp _
          (FixedArrayResult.lengthStoreProgram 7 1 ++ _) _ _ _ _
        apply FixedArrayResult.lengthStore_spec
          (root := heapTop + 48) (length := 1) (rootLocal := 7)
        · rfl
        · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.ValueType.zero, Wasm.Locals.get,
            FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayCapacity.normalizedCapacity,
            FixedArrayCapacity.unnormalizedCapacity,
            FixedArrayLengthDispatch.branchFrame]
        · rw [hRootAddress, FixedArrayAllocator.allocStore_pages]
          omega
        · change Wasm.wp _
            (FixedArrayFold.forwardSetupProgram
              11 12 13 16 14 1 18 15 1 ++ _) _ _ _ _
          apply FixedArrayFold.forwardSetupProgram_spec
            (inputPtr := inputPtr) (input := input)
          · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams,
              Wasm.ValueType.zero, FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame]
          · rfl
          · intro slot hSlot
            simp only [FixedArrayFold.setupLocals, List.mem_cons,
              List.not_mem_nil, or_false] at hSlot
            rcases hSlot with hSlot | hSlot | hSlot | hSlot | hSlot |
              hSlot | hSlot | hSlot
            all_goals subst slot
            all_goals
              norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
                Wasm.Function.toLocals, Wasm.Function.numParams,
                Wasm.ValueType.zero, FixedArrayAllocatorWindow.allocFrame,
                FixedArrayCapacity.capacityFrame,
                FixedArrayLengthDispatch.branchFrame]
          · decide
          · simpa using hInputAfterLength
          · apply Wasm.wp_block_cons
            apply Wasm.wp.conseq
              (Q := productLoopPost
                (FixedArrayResult.writeLength
                  (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                  (heapTop + 48) 1)
                inputPtr (heapTop + 48) input)
            · intro continuation hComplete
              cases continuation <;>
                simp only [productLoopPost] at hComplete
              rename_i depth final frame
              cases depth with
              | succ depth => exact hComplete.elim
              | zero =>
                  rcases hComplete with
                    ⟨item, scratch, conditionScratch, staged, releaseReady,
                      hFinal, hFrame⟩
                  subst final
                  subst frame
                  apply Wasm.wp.conseq
                    (Q := productOutputPost (heapTop + 48)
                      #[ArrayFold.foldPrefix input productStep 1 input.size])
                  · intro result hResult
                    cases result <;>
                      simp only [productOutputPost] at hResult
                    rename_i final frame
                    rcases hResult with ⟨hReturn, hOutput⟩
                    simp only [FixedArrayEqNode.branchPost]
                    rw [Wasm.wp_localGet_cons]
                    have hReturn' :
                        ({ frame with values := [] } : Wasm.Locals).get 6 =
                          some (.i64 (heapTop + 48)) := by
                      simpa only [Wasm.Locals.get] using hReturn
                    rw [hReturn']
                    simp only [Wasm.wp_nil]
                    refine ⟨heapTop + 48, rfl, ?_⟩
                    change UInt64Array.At _ _ _
                    rw [hExpected]
                    simpa only [ArrayFold.foldPrefix_size] using hOutput
                  · have hOutput : UInt64Array.At
                        (FixedArrayResult.singletonStore
                          (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                          (heapTop + 48)
                          (ArrayFold.foldPrefix input productStep 1 input.size))
                        (heapTop + 48)
                        #[ArrayFold.foldPrefix input productStep 1 input.size] :=
                      FixedArrayResult.singletonStore_at _ _ _
                        hResultFit32 hResultFitMemory
                    apply productSuffix_spec
                      (hPayloadBound := hPayloadBound)
                    simpa [FixedArrayResult.singletonStore] using hOutput
            · apply Wasm.wp_loop_cons (Inv := productLoopInv
                (FixedArrayResult.writeLength
                  (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                  (heapTop + 48) 1)
                inputPtr (heapTop + 48) input)
                (μ := productLoopMeasure input)
              · refine ⟨0, 0, 0, inputPtr, 0, 0, by omega, rfl, ?_⟩
                norm_num [productLoopFrame, productStep,
                  ArrayFold.foldPrefix, FixedArrayFold.forwardSetupFrame,
                  FixedArrayAllocatorWindow.allocFrame,
                  FixedArrayCapacity.capacityFrame,
                  FixedArrayCapacity.normalizedCapacity,
                  FixedArrayCapacity.unnormalizedCapacity,
                  FixedArrayLengthDispatch.branchFrame,
                  LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
                  Wasm.Function.toLocals, Wasm.Function.numParams,
                  Wasm.ValueType.zero,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame,
                  AnnotationMatches.function_0_array_fold_0_state,
                  ScalarTransition.U64State.toState]
                rfl
              · rintro loopStore loopFrame
                  ⟨index, item, scratch, conditionScratch, staged, releaseReady,
                    hIndex, hLoopStore, hLoopFrame⟩
                subst loopStore
                subst loopFrame
                change Wasm.wp module
                  (AnnotationMatches.function_0_array_fold_0_continuing_program ++
                    AnnotationMatches.function_0_array_fold_0_step_program)
                  _
                  (FixedArrayResult.writeLength
                    (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                    (heapTop + 48) 1)
                  (productLoopFrame inputPtr (heapTop + 48) input.size index
                    (ArrayFold.foldPrefix input productStep 1 index)
                    item scratch conditionScratch staged releaseReady) env
                by_cases hDone : index = input.size
                · subst index
                  apply FixedArrayTraversalInput.continuingProgram_exit_spec
                    (arrayLocal := 11) (indexLocal := 13)
                    (stopLocal := 15) (itemLocal := 2)
                    (index := UInt64.ofNat input.size)
                  · rfl
                  · norm_num [productLoopFrame,
                      AnnotationMatches.function_0_array_fold_0_continuing_frame,
                      AnnotationMatches.function_0_array_fold_0_state,
                      ScalarTransition.U64State.toState, Wasm.Locals.get]
                  · norm_num [productLoopFrame,
                      AnnotationMatches.function_0_array_fold_0_continuing_frame,
                      AnnotationMatches.function_0_array_fold_0_state,
                      ScalarTransition.U64State.toState, Wasm.Locals.get]
                  · simp only [productLoopPost]
                    exact ⟨item, scratch, conditionScratch, staged,
                      releaseReady, True.intro, rfl⟩
                · have hIndexLt : index < input.size := by omega
                  have hIndexNat : (UInt64.ofNat index).toNat = index := by
                    apply UInt64.toNat_ofNat_of_lt'
                    have hUInt64Size : UInt64.size =
                        18446744073709551616 := rfl
                    omega
                  have hInputSizeNat :
                      (UInt64.ofNat input.size).toNat = input.size :=
                    UInt64.toNat_ofNat_of_lt' hInputAfterLength.size_lt
                  have hContinue :
                      UInt64.ofNat index < UInt64.ofNat input.size := by
                    rw [UInt64.lt_iff_toNat_lt, hIndexNat, hInputSizeNat]
                    exact hIndexLt
                  apply
                    AnnotationMatches.function_0_array_fold_0_continuing_spec
                      (input := input) (index := index)
                      (hIndexValue := rfl) (hContinue := hContinue)
                      (hInput := hInputAfterLength) (hIndex := hIndexLt)
                  have hIndexSucc :
                      UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by
                    change UInt64.ofNat index + UInt64.ofNat 1 =
                      UInt64.ofNat (index + 1)
                    rw [← UInt64.ofNat_add]
                  let accumulated :=
                    ArrayFold.foldPrefix input productStep 1 index
                  let updated := productStep accumulated input[index]
                  let before :=
                    AnnotationMatches.function_0_array_fold_0_state
                      inputPtr accumulated input[index] scratch 0 0 0
                      (heapTop + 48) 0 0 0 inputPtr
                      (UInt64.ofNat input.size) (UInt64.ofNat index)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      conditionScratch staged releaseReady 0 0
                  let after :=
                    AnnotationMatches.function_0_array_fold_0_state
                      inputPtr updated input[index] updated 0 0 0
                      (heapTop + 48) 0 0 0 inputPtr
                      (UInt64.ofNat input.size) (UInt64.ofNat index)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      0 updated 1 0 0
                  let advanced :=
                    AnnotationMatches.function_0_array_fold_0_state
                      inputPtr updated input[index] updated 0 0 0
                      (heapTop + 48) 0 0 0 inputPtr
                      (UInt64.ofNat input.size) (UInt64.ofNat index + 1)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      0 updated 1 0 0
                  change Wasm.wp module
                    (AnnotationMatches.function_0_array_fold_0_step_program ++
                      []) _
                    (FixedArrayResult.writeLength
                      (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                      (heapTop + 48) 1)
                    (before.toState.toLocals []) env
                  apply ScalarTransition.guardedBackEdgeProgram_spec
                    (initial := before.toState)
                    (afterBody := after.toState)
                    (afterCondition := after.toState)
                    (result := false) (values := [])
                  · rw [AnnotationMatches.function_0_array_fold_0_body_eval]
                    rfl
                  · rw [AnnotationMatches.function_0_array_fold_0_condition_eval]
                    rfl
                  · intro hFalse
                    cases hFalse
                  · intro _
                    refine ⟨advanced.toState, ?_, ?_⟩
                    · rw [
                        AnnotationMatches.function_0_array_fold_0_step_continuing_eval]
                      rfl
                    · change productLoopInv
                          (FixedArrayResult.writeLength
                            (FixedArrayAllocator.allocStore initial heapTop 16 1
                              allocs)
                            (heapTop + 48) 1)
                          inputPtr (heapTop + 48) input
                          (FixedArrayResult.writeLength
                            (FixedArrayAllocator.allocStore initial heapTop 16 1
                              allocs)
                            (heapTop + 48) 1)
                          (advanced.toState.toLocals []) ∧
                        productLoopMeasure input
                            (FixedArrayResult.writeLength
                              (FixedArrayAllocator.allocStore initial heapTop 16
                                1 allocs)
                              (heapTop + 48) 1)
                            (advanced.toState.toLocals []) <
                          productLoopMeasure input
                            (FixedArrayResult.writeLength
                              (FixedArrayAllocator.allocStore initial heapTop 16
                                1 allocs)
                              (heapTop + 48) 1)
                            (productLoopFrame inputPtr (heapTop + 48)
                              input.size index accumulated item scratch
                              conditionScratch staged releaseReady)
                      have hAdvancedFrame : advanced.toState.toLocals [] =
                          productLoopFrame inputPtr (heapTop + 48) input.size
                            (index + 1) updated input[index] updated 0 updated 1 := by
                        dsimp [advanced]
                        unfold productLoopFrame
                        rw [← hIndexSucc]
                        rfl
                      constructor
                      · unfold productLoopInv
                        refine ⟨index + 1, input[index], updated, 0, updated, 1,
                          by omega, rfl, ?_⟩
                        rw [ArrayFold.foldPrefix_succ input productStep 1 index
                          hIndexLt]
                        exact hAdvancedFrame
                      · rw [hAdvancedFrame]
                        have hIndexSuccNat :
                            (UInt64.ofNat (index + 1)).toNat = index + 1 :=
                          UInt64.toNat_ofNat_of_lt' (by
                            have hUInt64Size : UInt64.size =
                                18446744073709551616 := rfl
                            omega)
                        change input.size -
                            (UInt64.ofNat (index + 1)).toNat <
                          input.size - (UInt64.ofNat index).toNat
                        rw [hIndexSuccNat, hIndexNat]
                        omega
  · intro hSize
    have hAllocFit : heapTop.toNat + 48 + (8 : UInt64).toNat ≤
        initial.mem.pages * 65536 := by
      simpa [LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec.heapReserveBytes,
        hSize] using hHeapFitMemory
    have hFacts := Allocation.bumpFacts heapTop 8 initial.mem.pages
      hAllocFit hPages
    have hRootAddress : (heapTop + 48).toUInt32.toNat =
        heapTop.toNat + 48 := by
      simpa using hFacts.wordAddress_toNat 0 (by decide)
    have hExpected :
        LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec.expected input =
          #[] := by
      rw [LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec.expected,
        if_neg hSize]
    have hResultFit32 : (heapTop + 48).toNat + 8 ≤ 4294967296 := by
      rw [hFacts.rootToNat]
      simpa [hExpected] using hOutputFit32
    have hResultFitMemory :
        (heapTop + 48).toNat + 8 ≤ initial.mem.pages * 65536 := by
      rw [hFacts.rootToNat]
      simpa [hExpected] using hOutputFitMemory
    change Wasm.wp _
      (FixedArrayCapacity.constantProgram 0 1 11 ++ _) _ _ _ _
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero, FixedArrayLengthDispatch.branchFrame]
    · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero, Wasm.Locals.validIndex,
        FixedArrayLengthDispatch.branchFrame]
    · change Wasm.wp _
        (FixedArrayAllocatorWindow.region 2 1 ++ _) _ _ _ _
      apply FixedArrayAllocatorWindow.region_spec_withTail 2 4
        (heapTop := heapTop) (capacity := 8) (stride := 1)
        (allocs := allocs)
      · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero, FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame]
      · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero, FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame]
      · rfl
      · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero, FixedArrayCapacity.capacityFrame,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity,
          FixedArrayLengthDispatch.branchFrame]
        decide
      · decide
      · exact hAllocFit
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
        · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.ValueType.zero, Wasm.Locals.get,
            FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayCapacity.normalizedCapacity,
            FixedArrayCapacity.unnormalizedCapacity,
            FixedArrayLengthDispatch.branchFrame]
        · rw [hRootAddress, FixedArrayAllocator.allocStore_pages]
          omega
        · apply FixedArrayResult.finishProgram_spec
            (root := heapTop + 48) (rootLocal := 7)
            (destinationLocal := 5) (returnLocal := 6)
          · rfl
          · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams,
              Wasm.ValueType.zero, Wasm.Locals.get,
              FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayCapacity.normalizedCapacity,
              FixedArrayCapacity.unnormalizedCapacity,
              FixedArrayLengthDispatch.branchFrame]
          · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams,
              Wasm.ValueType.zero, FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame]
          · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams,
              Wasm.ValueType.zero, Wasm.Locals.validIndex,
              FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame]
          · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams,
              Wasm.ValueType.zero, FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame]
          · norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams,
              Wasm.ValueType.zero, Wasm.Locals.validIndex,
              FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame]
          · simp only [Wasm.wp_nil, FixedArrayEqNode.branchPost]
            rw [Wasm.wp_localGet_cons]
            have hReturn :
                (FixedArrayResult.finishFrame
                    (FixedArrayAllocatorWindow.allocFrame 2
                      (FixedArrayCapacity.capacityFrame
                        (FixedArrayLengthDispatch.branchFrame 7
                          (LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.toLocals
                            (List.take
                              LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.numParams
                              [.i64 inputPtr]).reverse)
                          inputPtr)
                        11
                        (FixedArrayCapacity.normalizedCapacity 0 1))
                      heapTop 8)
                    5 6 (heapTop + 48)).get 6 =
                  some (.i64 (heapTop + 48)) := by
              norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
                Wasm.Function.toLocals, Wasm.Function.numParams,
                Wasm.ValueType.zero, Wasm.Locals.get,
                FixedArrayResult.finishFrame,
                FixedArrayAllocatorWindow.allocFrame,
                FixedArrayCapacity.capacityFrame,
                FixedArrayCapacity.normalizedCapacity,
                FixedArrayCapacity.unnormalizedCapacity,
                FixedArrayLengthDispatch.branchFrame]
            have hReturn' :
                ({ FixedArrayResult.finishFrame
                    (FixedArrayAllocatorWindow.allocFrame 2
                      (FixedArrayCapacity.capacityFrame
                        (FixedArrayLengthDispatch.branchFrame 7
                          (LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.toLocals
                            (List.take
                              LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.numParams
                              [.i64 inputPtr]).reverse)
                          inputPtr)
                        11
                        (FixedArrayCapacity.normalizedCapacity 0 1))
                      heapTop 8)
                    5 6 (heapTop + 48) with values := [] } : Wasm.Locals).get
                    6 = some (.i64 (heapTop + 48)) := by
              simpa only [Wasm.Locals.get] using hReturn
            rw [hReturn']
            simp only [Wasm.wp_nil]
            refine ⟨heapTop + 48, rfl, ?_⟩
            change UInt64Array.At _ _ _
            rw [hExpected]
            apply FixedArrayResult.emptyStore_at
            · exact hResultFit32
            · simpa [FixedArrayAllocator.allocStore_pages] using
                hResultFitMemory

end LeanExeGen.GeneratedRa8e90ffc5781d113.Behavior
