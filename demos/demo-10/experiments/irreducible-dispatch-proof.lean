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
import Project.ProofKit.FixedArrayResult
import Project.ProofKit.FixedArrayTraversalInput
import Project.ProofKit.Frame
import Project.ProofKit.ScalarTransition

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRa8e90ffc5781d113.Behavior

open Wasm Project.ProofKit

attribute [local irreducible] LeanExeGen.GeneratedRa8e90ffc5781d113.func0

def foldLoopState (inputPtr root size accumulator index item temporary
    done staged release : UInt64) : ScalarTransition.U64State :=
  LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state
    inputPtr accumulator item temporary 0 0 0 root 0 0 0 inputPtr size index
    size size done staged release 0 0

def foldLoopInvariant (foldStore : Store Unit) (input : Array UInt64)
    (inputPtr root : UInt64) : Store Unit → Locals → Prop :=
  fun st frame =>
    ∃ index item temporary done staged release,
      index ≤ input.size ∧
      st = foldStore ∧
      frame =
        (foldLoopState inputPtr root (UInt64.ofNat input.size)
          (ArrayFold.foldPrefix input
            (fun product element : UInt64 => product * element) 1 index)
          (UInt64.ofNat index) item temporary done staged release).toState.toLocals []

def foldLoopMeasure (input : Array UInt64) (_st : Store Unit)
    (frame : Locals) : Nat :=
  input.size - match frame.get 13 with
    | some (.i64 index) => index.toNat
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
  apply Wasm.TerminatesWith.of_wp_entry_for (f := LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def) rfl
  change Wasm.wp _ LeanExeGen.GeneratedRa8e90ffc5781d113.func0 _ _ _ _
  rw [LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_length_dispatch_0_function_eq]
  wp_fixed_array_length_le_dispatch_from hArray at 7, 8
  case hParams => rfl
  case hValues => rfl
  case hInputLocalPositive => omega
  case hInputLocal =>
    norm_num [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
      Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.Function.numLocals, List.take, List.replicate,
      Wasm.ValueType.zero]
  case hMaximumSize => norm_num [UInt64.size]
  case hValid =>
    intro hSize
    change wp _ (FixedArrayCapacity.constantProgram 1 1 11 ++ _) _ _ _ _
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [FixedArrayLengthDispatch.branchFrame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.Function.numLocals, List.take, List.replicate,
        Wasm.ValueType.zero]
    · norm_num [Wasm.Locals.validIndex,
        FixedArrayLengthDispatch.branchFrame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.Function.numLocals, List.take, List.replicate,
        Wasm.ValueType.zero]
    · have hFit : heapTop.toNat + 48 + 16 ≤ initial.mem.pages * 65536 := by
        simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
      change wp _ (FixedArrayAllocatorWindow.region 2 1 ++ _) _ _ _ _
      apply FixedArrayAllocatorWindow.region_spec_withTail
        (offset := 2) (tail := 4) (heapTop := heapTop) (capacity := 16)
        (stride := 1) (allocs := allocs)
      case hParams =>
        norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.Function.numLocals, List.take, List.replicate,
          Wasm.ValueType.zero]
      case hLocals =>
        norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.Function.numLocals, List.take, List.replicate,
          Wasm.ValueType.zero]
      case hValues => rfl
      case hCapacityLocal =>
        norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity,
          FixedArrayLengthDispatch.branchFrame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.Function.numLocals, List.take, List.replicate,
          Wasm.ValueType.zero] <;> native_decide
      case hCapacity => native_decide
      case hFitMemory => exact hFit
      case hPages => exact hPages
      case hMemory32 => rfl
      case hHeapTop => exact hHeapTop
      case hFreeList => exact hFreeList
      case hAllocs => exact hAllocs
      case hNext =>
        have hBump := Allocation.bumpFacts heapTop 16 initial.mem.pages hFit hPages
        have hRootNat : (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
          simpa using hBump.wordAddress_toNat 0 (by native_decide)
        have hInputAllocated :=
          FixedArrayPairResult.input_preserved_by_alloc initial heapTop 16 1
            allocs inputPtr input hArray hInputBelow hFit hPages
        have hInputFold : UInt64Array.At
            (FixedArrayResult.writeLength
              (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
              (heapTop + 48) 1)
            inputPtr input := by
          unfold FixedArrayResult.writeLength
          apply hInputAllocated.write64After
          rw [hRootNat]
          omega
        change wp _ (FixedArrayResult.lengthStoreProgram 7 1 ++ _) _ _ _ _
        apply FixedArrayResult.lengthStore_spec (root := heapTop + 48)
        · rfl
        · norm_num [Wasm.Locals.get,
            FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayCapacity.normalizedCapacity,
            FixedArrayCapacity.unnormalizedCapacity,
            FixedArrayLengthDispatch.branchFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.Function.numLocals, List.take, List.replicate,
            Wasm.ValueType.zero] <;> norm_num
        · rw [FixedArrayAllocator.allocStore_pages, hRootNat]
          omega
        · change wp _
            (FixedArrayFold.forwardSetupProgram 11 12 13 16 14 1 18 15 1 ++ _)
            _ _ _ _
          apply FixedArrayFold.forwardSetupProgram_spec
            (inputPtr := inputPtr) (input := input)
          · norm_num [FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame,
              LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams,
              Wasm.Function.numLocals, List.take, List.replicate,
              Wasm.ValueType.zero]
          · rfl
          · intro slot hSlot
            norm_num [FixedArrayFold.setupLocals,
              FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame,
              LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams,
              Wasm.Function.numLocals, List.take, List.replicate,
              Wasm.ValueType.zero] at hSlot ⊢
            omega
          · native_decide
          · exact hInputFold
          · apply Wasm.wp_block_cons
            apply Wasm.wp_loop_cons
              (Inv := foldLoopInvariant
                (FixedArrayResult.writeLength
                  (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                  (heapTop + 48) 1)
                input inputPtr (heapTop + 48))
              (μ := foldLoopMeasure input)
            · unfold foldLoopInvariant
              refine ⟨0, 0, 0, inputPtr, 0, 0, by omega, rfl, ?_⟩
              norm_num [foldLoopState, ArrayFold.foldPrefix,
                LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                ScalarTransition.U64State.toState,
                FixedArrayFold.forwardSetupFrame,
                FixedArrayAllocatorWindow.allocFrame,
                FixedArrayCapacity.capacityFrame,
                FixedArrayCapacity.normalizedCapacity,
                FixedArrayCapacity.unnormalizedCapacity,
                FixedArrayLengthDispatch.branchFrame,
                LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
                Wasm.Function.toLocals, Wasm.Function.numParams,
                Wasm.Function.numLocals, List.take, List.replicate,
                Wasm.ValueType.zero] <;> native_decide
            · intro st frame hInv
              rcases hInv with
                ⟨index, item, temporary, done, staged, release,
                  hIndexLe, rfl, rfl⟩
              let accumulator := ArrayFold.foldPrefix input
                (fun product element : UInt64 => product * element) 1 index
              by_cases hIndex : index < input.size
              · have hIndexEncoded :
                    UInt64.ofNat index < UInt64.ofNat input.size := by
                  rw [UInt64.lt_iff_toNat_lt,
                    UInt64.toNat_ofNat_of_lt' (by
                      have hInputSize := hInputFold.size_lt
                      omega),
                    UInt64.toNat_ofNat_of_lt' hInputFold.size_lt]
                  exact hIndex
                change wp _
                  (FixedArrayTraversalInput.continuingProgram 11 13 15 2 ++ _)
                  _ _ _ _
                apply FixedArrayTraversalInput.continuingProgram_spec
                  (inputPtr := inputPtr) (indexValue := UInt64.ofNat index)
                  (stopValue := UInt64.ofNat input.size) (input := input)
                  (hValues := rfl) (hArrayLocal := rfl)
                  (hIndexLocal := rfl) (hStopLocal := rfl)
                  (hIndexValue := rfl) (hContinue := hIndexEncoded)
                  (index := index) (hItem := by
                    norm_num [Wasm.Locals.validIndex, foldLoopState,
                      LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                      ScalarTransition.U64State.toState])
                  (hInput := hInputFold) (hIndex := hIndex)
                · change wp _
                    (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_step_program ++ _)
                    _ _
                    ((foldLoopState inputPtr (heapTop + 48)
                      (UInt64.ofNat input.size) accumulator
                      (UInt64.ofNat index) input[index] temporary done staged
                      release).toState.toLocals []) _
                  let nextAccumulator := accumulator * input[index]
                  apply ScalarTransition.guardedBackEdgeProgram_spec
                    (scratch := 11)
                    (body := LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_body)
                    (condition := LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_condition)
                    (continuing := LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_step_continuing)
                    (initial := (foldLoopState inputPtr (heapTop + 48)
                      (UInt64.ofNat input.size) accumulator
                      (UInt64.ofNat index) input[index] temporary done staged
                      release).toState)
                    (afterBody := (foldLoopState inputPtr (heapTop + 48)
                      (UInt64.ofNat input.size) nextAccumulator
                      (UInt64.ofNat index) input[index] nextAccumulator 0
                      nextAccumulator 1).toState)
                    (afterCondition := (foldLoopState inputPtr (heapTop + 48)
                      (UInt64.ofNat input.size) nextAccumulator
                      (UInt64.ofNat index) input[index] nextAccumulator 0
                      nextAccumulator 1).toState)
                    (result := false) (values := [])
                  · simpa [foldLoopState, nextAccumulator,
                      LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_bodyTransition,
                      ScalarTransition.U64Op.apply] using
                      (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_body_eval
                        inputPtr accumulator input[index] temporary 0 0 0
                        (heapTop + 48) 0 0 0 inputPtr
                        (UInt64.ofNat input.size) (UInt64.ofNat index)
                        (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                        done staged release 0 0)
                  · simpa [foldLoopState,
                      LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_conditionTransition]
                      using
                      (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_condition_eval
                        inputPtr nextAccumulator input[index] nextAccumulator
                        0 0 0 (heapTop + 48) 0 0 0 inputPtr
                        (UInt64.ofNat input.size) (UInt64.ofNat index)
                        (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                        0 nextAccumulator 1 0 0)
                  · simp
                  · intro _
                    refine ⟨(foldLoopState inputPtr (heapTop + 48)
                      (UInt64.ofNat input.size) nextAccumulator
                      (UInt64.ofNat index + 1) input[index] nextAccumulator 0
                      nextAccumulator 1).toState, ?_, ?_⟩
                    · simpa [foldLoopState,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_step_continuingTransition,
                        ScalarTransition.U64Op.apply] using
                        (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_step_continuing_eval
                          inputPtr nextAccumulator input[index] nextAccumulator
                          0 0 0 (heapTop + 48) 0 0 0 inputPtr
                          (UInt64.ofNat input.size) (UInt64.ofNat index)
                          (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                          0 nextAccumulator 1 0 0)
                    · have hIndex64 : index < UInt64.size := by
                        have hInputSize := hInputFold.size_lt
                        omega
                      have hIndexSucc64 : index + 1 < UInt64.size := by
                        have hInputSize := hInputFold.size_lt
                        omega
                      have hIndexSucc :
                          UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by
                        apply UInt64.toNat.inj
                        rw [UInt64.toNat_add,
                          UInt64.toNat_ofNat_of_lt' hIndex64]
                        norm_num
                      constructor
                      · unfold foldLoopInvariant
                        refine ⟨index + 1, input[index], nextAccumulator, 0,
                          nextAccumulator, 1, by omega, rfl, ?_⟩
                        rw [ArrayFold.foldPrefix_succ input
                          (fun product element : UInt64 => product * element)
                          1 index hIndex]
                        dsimp [nextAccumulator, accumulator]
                        rw [hIndexSucc]
                      · change
                          input.size - (UInt64.ofNat index + 1).toNat <
                            input.size - (UInt64.ofNat index).toNat
                        rw [hIndexSucc,
                          UInt64.toNat_ofNat_of_lt' hIndex64,
                          UInt64.toNat_ofNat_of_lt' hIndexSucc64]
                        omega
              · have hIndexEq : index = input.size := by omega
                subst index
                change wp _
                  (FixedArrayTraversalInput.continuingProgram 11 13 15 2 ++ _)
                  _ _ _ _
                apply FixedArrayTraversalInput.continuingProgram_exit_spec
                · rfl
                · rfl
                · rfl
                · let product := input.foldl
                    (fun product element : UInt64 => product * element) 1
                  have hRootFit32 :
                      (heapTop + 48).toNat + 16 ≤ 4294967296 := by
                    rw [hBump.rootToNat]
                    have h := hBump.fit32
                    norm_num at h ⊢
                    exact h
                  have hRootFitMemory :
                      (heapTop + 48).toNat + 16 ≤
                        initial.mem.pages * 65536 := by
                    rw [hBump.rootToNat]
                    exact hFit
                  have hOutput : UInt64Array.At
                      (FixedArrayResult.singletonStore
                        (FixedArrayAllocator.allocStore initial heapTop 16 1
                          allocs)
                        (heapTop + 48) product)
                      (heapTop + 48) #[product] :=
                    FixedArrayResult.singletonStore_at _ _ _ hRootFit32
                      hRootFitMemory
                  have hPayloadNat :
                      (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat =
                        heapTop.toNat + 56 := by
                    simpa [FixedArrayResult.payloadAddress] using
                      hBump.wordAddress_toNat 1 (by native_decide)
                  change wp _ (FixedArrayFold.resultProgram 1 10 ++ _) _ _ _ _
                  apply FixedArrayFold.resultProgram_spec (value := product)
                  · rfl
                  · norm_num [Wasm.Locals.get, foldLoopState,
                      LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                      ScalarTransition.U64State.toState, accumulator, product,
                      ArrayFold.foldPrefix_size]
                  · norm_num [foldLoopState,
                      LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                      ScalarTransition.U64State.toState]
                  · norm_num [Wasm.Locals.validIndex, foldLoopState,
                      LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                      ScalarTransition.U64State.toState]
                  · change wp _
                      (FixedArrayResult.payloadStoreProgram 7 10 0 ++ _)
                      _ _ _ _
                    apply FixedArrayResult.payloadStore_spec
                      (root := heapTop + 48) (value := product)
                    · norm_num [Wasm.Locals.get, FixedArrayFold.resultFrame,
                        foldLoopState,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                        ScalarTransition.U64State.toState]
                    · norm_num [Wasm.Locals.get, FixedArrayFold.resultFrame,
                        foldLoopState,
                        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                        ScalarTransition.U64State.toState]
                    · rw [FixedArrayResult.writeLength_pages,
                        FixedArrayAllocator.allocStore_pages, hPayloadNat]
                      omega
                    · change wp _
                        (FixedArrayResult.finishProgram 7 4 6 ++ []) _ _ _ _
                      apply FixedArrayResult.finishProgram_spec
                        (root := heapTop + 48)
                      · rfl
                      · norm_num [Wasm.Locals.get,
                          FixedArrayFold.resultFrame, foldLoopState,
                          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                          ScalarTransition.U64State.toState]
                      · norm_num [FixedArrayFold.resultFrame, foldLoopState,
                          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                          ScalarTransition.U64State.toState]
                      · norm_num [Wasm.Locals.validIndex,
                          FixedArrayFold.resultFrame, foldLoopState,
                          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                          ScalarTransition.U64State.toState]
                      · norm_num [FixedArrayFold.resultFrame, foldLoopState,
                          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                          ScalarTransition.U64State.toState]
                      · norm_num [Wasm.Locals.validIndex,
                          FixedArrayFold.resultFrame, foldLoopState,
                          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                          ScalarTransition.U64State.toState]
                      · simp only [LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_length_dispatch_0_suffix_program]
                        rw [wp_nil]
                        simpa [FixedArrayEqNode.branchPost, wp_simp,
                          FixedArrayResult.finishFrame,
                          FixedArrayFold.resultFrame, Wasm.Locals.get,
                          foldLoopState,
                          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
                          ScalarTransition.U64State.toState,
                          LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
                          Wasm.Function.toLocals, Wasm.Function.numParams,
                          Wasm.Function.numLocals, List.take, List.drop,
                          List.replicate, Wasm.ValueType.zero,
                          accumulator, product, ArrayFold.foldPrefix_size,
                          FixedArrayResult.singletonStore,
                          FormalSpec.expected, hSize,
                          FormalSpec.UInt64ArrayAt, UInt64Array.At] using
                          hOutput
  case hInvalid =>
    intro hSize
    change wp _ (FixedArrayCapacity.constantProgram 0 1 11 ++ _) _ _ _ _
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [FixedArrayLengthDispatch.branchFrame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.Function.numLocals, List.take, List.replicate,
        Wasm.ValueType.zero]
    · norm_num [Wasm.Locals.validIndex,
        FixedArrayLengthDispatch.branchFrame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.Function.numLocals, List.take, List.replicate,
        Wasm.ValueType.zero]
    · have hFit : heapTop.toNat + 48 + 8 ≤ initial.mem.pages * 65536 := by
        simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
      change wp _ (FixedArrayAllocatorWindow.region 2 1 ++ _) _ _ _ _
      apply FixedArrayAllocatorWindow.region_spec_withTail
        (offset := 2) (tail := 4) (heapTop := heapTop) (capacity := 8)
        (stride := 1) (allocs := allocs)
      case hParams =>
        norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.Function.numLocals, List.take, List.replicate,
          Wasm.ValueType.zero]
      case hLocals =>
        norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayLengthDispatch.branchFrame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.Function.numLocals, List.take, List.replicate,
          Wasm.ValueType.zero]
      case hValues => rfl
      case hCapacityLocal =>
        norm_num [FixedArrayCapacity.capacityFrame,
          FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity,
          FixedArrayLengthDispatch.branchFrame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.Function.numLocals, List.take, List.replicate,
          Wasm.ValueType.zero] <;> native_decide
      case hCapacity => native_decide
      case hFitMemory => exact hFit
      case hPages => exact hPages
      case hMemory32 => rfl
      case hHeapTop => exact hHeapTop
      case hFreeList => exact hFreeList
      case hAllocs => exact hAllocs
      case hNext =>
        have hBump := Allocation.bumpFacts heapTop 8 initial.mem.pages hFit hPages
        have hRootNat : (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
          simpa using hBump.wordAddress_toNat 0 (by native_decide)
        have hRootFit32 : (heapTop + 48).toNat + 8 ≤ 4294967296 := by
          rw [hBump.rootToNat]
          have h := hBump.fit32
          norm_num at h ⊢
          exact h
        have hRootFitMemory :
            (heapTop + 48).toNat + 8 ≤ initial.mem.pages * 65536 := by
          rw [hBump.rootToNat]
          exact hFit
        have hOutput : UInt64Array.At
            (FixedArrayResult.writeLength
              (FixedArrayAllocator.allocStore initial heapTop 8 1 allocs)
              (heapTop + 48) 0)
            (heapTop + 48) #[] :=
          FixedArrayResult.emptyStore_at _ _ hRootFit32 hRootFitMemory
        change wp _ (FixedArrayResult.lengthStoreProgram 7 0 ++ _) _ _ _ _
        apply FixedArrayResult.lengthStore_spec (root := heapTop + 48)
        · rfl
        · norm_num [Wasm.Locals.get,
            FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame,
            FixedArrayCapacity.normalizedCapacity,
            FixedArrayCapacity.unnormalizedCapacity,
            FixedArrayLengthDispatch.branchFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.Function.numLocals, List.take, List.replicate,
            Wasm.ValueType.zero] <;> norm_num
        · rw [FixedArrayAllocator.allocStore_pages, hRootNat]
          exact hFit
        · change wp _ (FixedArrayResult.finishProgram 7 5 6 ++ []) _ _ _ _
          apply FixedArrayResult.finishProgram_spec (root := heapTop + 48)
          · rfl
          · norm_num [Wasm.Locals.get,
              FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayCapacity.normalizedCapacity,
              FixedArrayCapacity.unnormalizedCapacity,
              FixedArrayLengthDispatch.branchFrame,
              LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams,
              Wasm.Function.numLocals, List.take, List.replicate,
              Wasm.ValueType.zero] <;> norm_num
          · norm_num [FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame,
              LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams,
              Wasm.Function.numLocals, List.take, List.replicate,
              Wasm.ValueType.zero]
          · norm_num [Wasm.Locals.validIndex,
              FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame,
              LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams,
              Wasm.Function.numLocals, List.take, List.replicate,
              Wasm.ValueType.zero]
          · norm_num [FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame,
              LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams,
              Wasm.Function.numLocals, List.take, List.replicate,
              Wasm.ValueType.zero]
          · norm_num [Wasm.Locals.validIndex,
              FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayLengthDispatch.branchFrame,
              LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams,
              Wasm.Function.numLocals, List.take, List.replicate,
              Wasm.ValueType.zero]
          · simp only [LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_length_dispatch_0_suffix_program]
            rw [wp_nil]
            simpa [FixedArrayEqNode.branchPost, wp_simp,
              FixedArrayResult.finishFrame, Wasm.Locals.get,
              FixedArrayAllocatorWindow.allocFrame,
              FixedArrayCapacity.capacityFrame,
              FixedArrayCapacity.normalizedCapacity,
              FixedArrayCapacity.unnormalizedCapacity,
              FixedArrayLengthDispatch.branchFrame,
              LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams,
              Wasm.Function.numLocals, List.take, List.drop,
              List.replicate, Wasm.ValueType.zero,
              FormalSpec.expected, hSize,
              FormalSpec.UInt64ArrayAt, UInt64Array.At] using hOutput

end LeanExeGen.GeneratedRa8e90ffc5781d113.Behavior
