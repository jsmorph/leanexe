import LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec
import LeanExeGen.GeneratedR23fa7efc3fb0298b.Program
import LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches
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

namespace LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior

open Wasm Project.ProofKit

def sumPrefix (input : Array UInt64) (index : Nat) : UInt64 :=
  ArrayFold.foldPrefix input (fun sum element => sum + element) 0 index

def sumFoldFrame (inputPtr root : UInt64) (input : Array UInt64)
    (index : Nat) (item done releaseReady : UInt64) : Wasm.Locals :=
  AnnotationMatches.function_0_array_fold_0_continuing_frame
    inputPtr
    (sumPrefix input index)
    item
    (sumPrefix input index)
    0 0 0 root 0 0 0
    inputPtr
    (UInt64.ofNat input.size)
    (UInt64.ofNat index)
    (UInt64.ofNat input.size)
    (UInt64.ofNat input.size)
    done
    (sumPrefix input index)
    releaseReady
    0 0

def SumInvariant (loopStore : Wasm.Store Unit) (inputPtr root : UInt64)
    (input : Array UInt64) (st : Wasm.Store Unit) (frame : Wasm.Locals) :
    Prop :=
  ∃ index item done releaseReady,
    index ≤ input.size ∧
    st = loopStore ∧
    frame = sumFoldFrame inputPtr root input index item done releaseReady

def sumFrameIndex (frame : Wasm.Locals) : Nat :=
  match frame.get 13 with
  | some (.i64 index) => index.toNat
  | _ => 0

def sumMeasure (input : Array UInt64) (frame : Wasm.Locals) : Nat :=
  input.size - sumFrameIndex frame

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
  · norm_num
  · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.ValueType.zero]
  · norm_num
  case hInvalid =>
    intro hSize
    change Wasm.wp module
      (FixedArrayCapacity.constantProgram 0 1 11 ++
        (FixedArrayAllocatorWindow.region 2 1 ++
          (FixedArrayResult.lengthStoreProgram 7 0 ++
            FixedArrayResult.finishProgram 7 5 6)))
      _ initial _ env
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · norm_num [Wasm.Locals.validIndex,
        FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · have hCapacity :
          FixedArrayCapacity.normalizedCapacity 0 1 = 8 := by
        native_decide
      have hFit :
          heapTop.toNat + 48 +
              (FixedArrayCapacity.normalizedCapacity 0 1).toNat ≤
            initial.mem.pages * 65536 := by
        simpa [hCapacity, FormalSpec.heapReserveBytes, hSize] using
          hHeapFitMemory
      have hFacts := Allocation.bumpFacts heapTop
        (FixedArrayCapacity.normalizedCapacity 0 1)
        initial.mem.pages hFit hPages
      apply FixedArrayAllocatorWindow.region_spec_withTail
        (offset := 2) (tail := 4) (heapTop := heapTop)
        (capacity := FixedArrayCapacity.normalizedCapacity 0 1)
        (stride := 1) (allocs := allocs)
      · simp only [FixedArrayCapacity.capacityFrame_params,
          FixedArrayLengthDispatch.branchFrame_params]
        norm_num [func0Def, Wasm.Function.toLocals,
          Wasm.Function.numParams, Wasm.ValueType.zero]
      · simp only [FixedArrayCapacity.capacityFrame_locals_length,
          FixedArrayLengthDispatch.branchFrame_locals_length]
        norm_num [func0Def, Wasm.Function.toLocals,
          Wasm.Function.numParams, Wasm.ValueType.zero]
      · simp only [FixedArrayCapacity.capacityFrame_values]
      · apply FixedArrayCapacity.capacityFrame_internal_get_capacity
        · simp only [FixedArrayLengthDispatch.branchFrame_params]
          norm_num [func0Def, Wasm.Function.toLocals,
            Wasm.Function.numParams, Wasm.ValueType.zero]
        · simp only [Wasm.Locals.validIndex,
            FixedArrayLengthDispatch.branchFrame_params,
            FixedArrayLengthDispatch.branchFrame_locals_length]
          norm_num [func0Def, Wasm.Function.toLocals,
            Wasm.Function.numParams, Wasm.ValueType.zero]
      · rw [hCapacity]
        decide
      · exact hFit
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · apply FixedArrayResult.lengthStore_spec
        · simp only [FixedArrayAllocatorWindow.allocFrame_values,
            FixedArrayCapacity.capacityFrame_values]
        · apply FixedArrayAllocatorWindow.allocFrame_get_root
            (offset := 2) (tail := 4)
          · simp only [FixedArrayCapacity.capacityFrame_params,
              FixedArrayLengthDispatch.branchFrame_params]
            norm_num [func0Def, Wasm.Function.toLocals,
              Wasm.Function.numParams, Wasm.ValueType.zero]
          · simp only [FixedArrayCapacity.capacityFrame_locals_length,
              FixedArrayLengthDispatch.branchFrame_locals_length]
            norm_num [func0Def, Wasm.Function.toLocals,
              Wasm.Function.numParams, Wasm.ValueType.zero]
        · rw [FixedArrayAllocator.allocStore_pages]
          have hRootAddress := hFacts.wordAddress_toNat 0 (by
            rw [hCapacity]
            decide)
          have hRootAddress' :
              (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
            simpa using hRootAddress
          rw [hRootAddress']
          rw [hCapacity] at hFit
          omega
        · have hOutput : UInt64Array.At
              (FixedArrayResult.writeLength
                (FixedArrayAllocator.allocStore initial heapTop
                  (FixedArrayCapacity.normalizedCapacity 0 1) 1 allocs)
                (heapTop + 48) 0)
              (heapTop + 48) #[] := by
            apply FixedArrayResult.emptyStore_at
            · rw [hFacts.rootToNat]
              omega
            · rw [FixedArrayAllocator.allocStore_pages, hFacts.rootToNat]
              omega
          apply FixedArrayResult.finishProgram_spec
          · simp only [FixedArrayAllocatorWindow.allocFrame_values,
              FixedArrayCapacity.capacityFrame_values]
          · apply FixedArrayAllocatorWindow.allocFrame_get_root
              (offset := 2) (tail := 4)
            · simp only [FixedArrayCapacity.capacityFrame_params,
                FixedArrayLengthDispatch.branchFrame_params]
              norm_num [func0Def, Wasm.Function.toLocals,
                Wasm.Function.numParams, Wasm.ValueType.zero]
            · simp only [FixedArrayCapacity.capacityFrame_locals_length,
                FixedArrayLengthDispatch.branchFrame_locals_length]
              norm_num [func0Def, Wasm.Function.toLocals,
                Wasm.Function.numParams, Wasm.ValueType.zero]
          · simp only [FixedArrayAllocatorWindow.allocFrame_params,
              FixedArrayCapacity.capacityFrame_params,
              FixedArrayLengthDispatch.branchFrame_params]
            norm_num [func0Def, Wasm.Function.toLocals,
              Wasm.Function.numParams, Wasm.ValueType.zero]
          · simp only [Wasm.Locals.validIndex,
              FixedArrayAllocatorWindow.allocFrame_params,
              FixedArrayAllocatorWindow.allocFrame_locals_length,
              FixedArrayCapacity.capacityFrame_params,
              FixedArrayCapacity.capacityFrame_locals_length,
              FixedArrayLengthDispatch.branchFrame_params,
              FixedArrayLengthDispatch.branchFrame_locals_length]
            norm_num [func0Def, Wasm.Function.toLocals,
              Wasm.Function.numParams, Wasm.ValueType.zero]
          · simp only [FixedArrayAllocatorWindow.allocFrame_params,
              FixedArrayCapacity.capacityFrame_params,
              FixedArrayLengthDispatch.branchFrame_params]
            norm_num [func0Def, Wasm.Function.toLocals,
              Wasm.Function.numParams, Wasm.ValueType.zero]
          · simp only [Wasm.Locals.validIndex,
              FixedArrayAllocatorWindow.allocFrame_params,
              FixedArrayAllocatorWindow.allocFrame_locals_length,
              FixedArrayCapacity.capacityFrame_params,
              FixedArrayCapacity.capacityFrame_locals_length,
              FixedArrayLengthDispatch.branchFrame_params,
              FixedArrayLengthDispatch.branchFrame_locals_length]
            norm_num [func0Def, Wasm.Function.toLocals,
              Wasm.Function.numParams, Wasm.ValueType.zero]
          · rw [Wasm.wp_nil]
            simp only [FixedArrayEqNode.branchPost]
            have hReturn := FixedArrayResult.finishFrame_return_get
              (FixedArrayAllocatorWindow.allocFrame 2
                (FixedArrayCapacity.capacityFrame
                  (FixedArrayLengthDispatch.branchFrame 7
                    (func0Def.toLocals
                      (List.take func0Def.numParams [.i64 inputPtr]).reverse)
                    inputPtr)
                  11 (FixedArrayCapacity.normalizedCapacity 0 1))
                heapTop (FixedArrayCapacity.normalizedCapacity 0 1))
              5 6 (heapTop + 48) (by
                simp only [FixedArrayAllocatorWindow.allocFrame_params,
                  FixedArrayCapacity.capacityFrame_params,
                  FixedArrayLengthDispatch.branchFrame_params]
                norm_num [func0Def, Wasm.Function.toLocals,
                  Wasm.Function.numParams, Wasm.ValueType.zero]) (by
                simp only [Wasm.Locals.validIndex,
                  FixedArrayAllocatorWindow.allocFrame_params,
                  FixedArrayAllocatorWindow.allocFrame_locals_length,
                  FixedArrayCapacity.capacityFrame_params,
                  FixedArrayCapacity.capacityFrame_locals_length,
                  FixedArrayLengthDispatch.branchFrame_params,
                  FixedArrayLengthDispatch.branchFrame_locals_length]
                norm_num [func0Def, Wasm.Function.toLocals,
                  Wasm.Function.numParams, Wasm.ValueType.zero])
            simp only [wp_localGet_cons,
              Project.ProofKit.Frame.withValues_get, hReturn, Wasm.wp_nil]
            refine ⟨heapTop + 48, ?_, ?_⟩
            · norm_num [func0Def, Wasm.Function.numParams]
            · change FormalSpec.UInt64ArrayAt _ _ #[] at hOutput
              simpa [FormalSpec.expected, hSize] using hOutput
  case hValid =>
    intro hSize
    change Wasm.wp module
      (FixedArrayCapacity.constantProgram 1 1 11 ++
        (FixedArrayAllocatorWindow.region 2 1 ++
          (FixedArrayResult.lengthStoreProgram 7 1 ++
            (AnnotationMatches.function_0_array_fold_0_setup_program ++
              ([.block 0 0 [.loop 0 0
                (AnnotationMatches.function_0_array_fold_0_continuing_program ++
                  AnnotationMatches.function_0_array_fold_0_step_program)]] ++
                AnnotationMatches.function_0_array_fold_0_singleton_result_program)))))
      _ initial _ env
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · norm_num [Wasm.Locals.validIndex,
        FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · have hCapacity :
          FixedArrayCapacity.normalizedCapacity 1 1 = 16 := by
        native_decide
      have hCapacityNat :
          (FixedArrayCapacity.normalizedCapacity 1 1).toNat = 16 := by
        rw [hCapacity]
        rfl
      have hFit :
          heapTop.toNat + 48 +
              (FixedArrayCapacity.normalizedCapacity 1 1).toNat ≤
            initial.mem.pages * 65536 := by
        simpa [hCapacity, FormalSpec.heapReserveBytes, hSize] using
          hHeapFitMemory
      have hFacts := Allocation.bumpFacts heapTop
        (FixedArrayCapacity.normalizedCapacity 1 1)
        initial.mem.pages hFit hPages
      have hRootAddress := hFacts.wordAddress_toNat 0 (by
        rw [hCapacity]
        decide)
      have hRootAddress' :
          (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
        simpa using hRootAddress
      have hInputAlloc := FixedArrayPairResult.input_preserved_by_alloc
        initial heapTop (FixedArrayCapacity.normalizedCapacity 1 1) 1
        allocs inputPtr input hArray hInputBelow hFit hPages
      have hInputLoop : UInt64Array.At
          (FixedArrayResult.writeLength
            (FixedArrayAllocator.allocStore initial heapTop
              (FixedArrayCapacity.normalizedCapacity 1 1) 1 allocs)
            (heapTop + 48) 1)
          inputPtr input := by
        apply hInputAlloc.write64After
        rw [hRootAddress']
        omega
      apply FixedArrayAllocatorWindow.region_spec_withTail
        (offset := 2) (tail := 4) (heapTop := heapTop)
        (capacity := FixedArrayCapacity.normalizedCapacity 1 1)
        (stride := 1) (allocs := allocs)
      · simp only [FixedArrayCapacity.capacityFrame_params,
          FixedArrayLengthDispatch.branchFrame_params]
        norm_num [func0Def, Wasm.Function.toLocals,
          Wasm.Function.numParams, Wasm.ValueType.zero]
      · simp only [FixedArrayCapacity.capacityFrame_locals_length,
          FixedArrayLengthDispatch.branchFrame_locals_length]
        norm_num [func0Def, Wasm.Function.toLocals,
          Wasm.Function.numParams, Wasm.ValueType.zero]
      · simp only [FixedArrayCapacity.capacityFrame_values]
      · apply FixedArrayCapacity.capacityFrame_internal_get_capacity
        · simp only [FixedArrayLengthDispatch.branchFrame_params]
          norm_num [func0Def, Wasm.Function.toLocals,
            Wasm.Function.numParams, Wasm.ValueType.zero]
        · simp only [Wasm.Locals.validIndex,
            FixedArrayLengthDispatch.branchFrame_params,
            FixedArrayLengthDispatch.branchFrame_locals_length]
          norm_num [func0Def, Wasm.Function.toLocals,
            Wasm.Function.numParams, Wasm.ValueType.zero]
      · rw [hCapacity]
        decide
      · exact hFit
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · apply FixedArrayResult.lengthStore_spec
        · simp only [FixedArrayAllocatorWindow.allocFrame_values,
            FixedArrayCapacity.capacityFrame_values]
        · apply FixedArrayAllocatorWindow.allocFrame_get_root
            (offset := 2) (tail := 4)
          · simp only [FixedArrayCapacity.capacityFrame_params,
              FixedArrayLengthDispatch.branchFrame_params]
            norm_num [func0Def, Wasm.Function.toLocals,
              Wasm.Function.numParams, Wasm.ValueType.zero]
          · simp only [FixedArrayCapacity.capacityFrame_locals_length,
              FixedArrayLengthDispatch.branchFrame_locals_length]
            norm_num [func0Def, Wasm.Function.toLocals,
              Wasm.Function.numParams, Wasm.ValueType.zero]
        · rw [FixedArrayAllocator.allocStore_pages, hRootAddress']
          rw [hCapacity] at hFit
          omega
        · apply FixedArrayFold.forwardSetupProgram_spec
            (inputPtr := inputPtr) (input := input)
          · simp only [FixedArrayAllocatorWindow.allocFrame_params,
              FixedArrayCapacity.capacityFrame_params,
              FixedArrayLengthDispatch.branchFrame_params]
            norm_num [func0Def, Wasm.Function.toLocals,
              Wasm.Function.numParams, Wasm.ValueType.zero]
          · simp only [FixedArrayAllocatorWindow.allocFrame_values,
              FixedArrayCapacity.capacityFrame_values]
          · intro slot hSlot
            simp only [FixedArrayAllocatorWindow.allocFrame_locals_length,
              FixedArrayCapacity.capacityFrame_locals_length,
              FixedArrayLengthDispatch.branchFrame_locals_length]
            norm_num [func0Def, Wasm.Function.toLocals,
              Wasm.Function.numParams, Wasm.ValueType.zero]
            simp [FixedArrayFold.setupLocals] at hSlot
            omega
          · native_decide
          · exact hInputLoop
          · wp_block_loop
              invariant (SumInvariant
                (FixedArrayResult.writeLength
                  (FixedArrayAllocator.allocStore initial heapTop
                    (FixedArrayCapacity.normalizedCapacity 1 1) 1 allocs)
                  (heapTop + 48) 1)
                inputPtr (heapTop + 48) input)
              decreasing (fun _ frame => sumMeasure input frame)
            · refine ⟨0, 0, inputPtr, 0, by omega, rfl, ?_⟩
              apply Project.ProofKit.Frame.ext
              · simp only [FixedArrayFold.forwardSetupFrame_params,
                  FixedArrayAllocatorWindow.allocFrame_params,
                  FixedArrayCapacity.capacityFrame_params,
                  FixedArrayLengthDispatch.branchFrame_params,
                  sumFoldFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
                norm_num [func0Def, Wasm.Function.toLocals,
                  Wasm.Function.numParams, Wasm.ValueType.zero]
              · simp [FixedArrayFold.forwardSetupFrame,
                  FixedArrayAllocatorWindow.allocFrame,
                  FixedArrayCapacity.capacityFrame,
                  FixedArrayLengthDispatch.branchFrame,
                  sumFoldFrame, sumPrefix, ArrayFold.foldPrefix,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame,
                  AnnotationMatches.function_0_array_fold_0_state,
                  ScalarTransition.U64State.toState,
                  ScalarTransition.State.toLocals,
                  func0Def, Wasm.Function.toLocals,
                  Wasm.Function.numParams, Wasm.ValueType.zero,
                  hCapacity]
              · rfl
            · rintro st frame
                ⟨index, item, done, releaseReady,
                  hIndex, rfl, rfl⟩
              by_cases hAtEnd : index = input.size
              · subst index
                apply FixedArrayTraversalInput.continuingProgram_exit_spec
                  (arrayLocal := 11) (indexLocal := 13)
                  (stopLocal := 15) (itemLocal := 2)
                  (index := UInt64.ofNat input.size)
                · simp only [sumFoldFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_values]
                · simp only [sumFoldFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13]
                · simp only [sumFoldFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_get_15]
                · change Wasm.wp module
                    AnnotationMatches.function_0_array_fold_0_singleton_result_program
                    _
                    (FixedArrayResult.writeLength
                      (FixedArrayAllocator.allocStore initial heapTop
                        (FixedArrayCapacity.normalizedCapacity 1 1) 1 allocs)
                      (heapTop + 48) 1)
                    (sumFoldFrame inputPtr (heapTop + 48) input input.size
                      item done releaseReady)
                    env
                  apply AnnotationMatches.function_0_array_fold_0_singleton_result_spec
                  · have hPayloadAddress := hFacts.wordAddress_toNat 1 (by
                      rw [hCapacity]
                      decide)
                    have hPayloadAddress' :
                        (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat =
                          heapTop.toNat + 56 := by
                      simpa [FixedArrayResult.payloadAddress] using
                        hPayloadAddress
                    have hPayloadFit :
                        heapTop.toNat + 64 ≤ initial.mem.pages * 65536 := by
                      convert hFit using 1 <;> simp [hCapacityNat]
                    rw [FixedArrayResult.writeLength_pages,
                      FixedArrayAllocator.allocStore_pages,
                      hPayloadAddress']
                    exact hPayloadFit
                  · have hReturn := FixedArrayResult.finishFrame_return_get
                      (FixedArrayFold.resultFrame
                        (sumFoldFrame inputPtr (heapTop + 48) input input.size
                          item done releaseReady)
                        10 (sumPrefix input input.size))
                      4 6 (heapTop + 48) (by
                        simp only [FixedArrayFold.resultFrame_params,
                          sumFoldFrame,
                          AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
                        norm_num) (by
                        simp only [Wasm.Locals.validIndex,
                          FixedArrayFold.resultFrame_params,
                          FixedArrayFold.resultFrame_locals_length,
                          sumFoldFrame,
                          AnnotationMatches.function_0_array_fold_0_continuing_frame_params,
                          AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
                        norm_num)
                    have hOutput : UInt64Array.At
                        (FixedArrayResult.singletonStore
                          (FixedArrayAllocator.allocStore initial heapTop
                            (FixedArrayCapacity.normalizedCapacity 1 1) 1 allocs)
                          (heapTop + 48) (sumPrefix input input.size))
                        (heapTop + 48) #[sumPrefix input input.size] := by
                      have hSingletonFit32 :
                          (heapTop + 48).toNat + 16 ≤ 4294967296 := by
                        rw [hFacts.rootToNat]
                        convert hFacts.fit32 using 1 <;> simp [hCapacityNat]
                      have hSingletonFitMemory :
                          (heapTop + 48).toNat + 16 ≤
                            (FixedArrayAllocator.allocStore initial heapTop
                              (FixedArrayCapacity.normalizedCapacity 1 1) 1 allocs).mem.pages *
                              65536 := by
                        rw [FixedArrayAllocator.allocStore_pages,
                          hFacts.rootToNat]
                        convert hFit using 1 <;> simp [hCapacityNat]
                      exact FixedArrayResult.singletonStore_at
                        (st := FixedArrayAllocator.allocStore initial heapTop
                          (FixedArrayCapacity.normalizedCapacity 1 1) 1 allocs)
                        (root := heapTop + 48)
                        (value := sumPrefix input input.size)
                        hSingletonFit32 hSingletonFitMemory
                    simp only [FixedArrayEqNode.branchPost,
                      wp_localGet_cons,
                      Project.ProofKit.Frame.withValues_get,
                      hReturn, Wasm.wp_nil]
                    refine ⟨heapTop + 48, ?_, ?_⟩
                    · norm_num [func0Def, Wasm.Function.numParams]
                    · change FormalSpec.UInt64ArrayAt _ _
                        #[sumPrefix input input.size] at hOutput
                      simpa [FormalSpec.expected, hSize, sumPrefix,
                        ArrayFold.foldPrefix_size,
                        FixedArrayResult.singletonStore] using hOutput
              · have hIndexLt : index < input.size := by omega

                let current := sumPrefix input index
                let element : UInt64 := input[index]
                let initialFold :=
                  AnnotationMatches.function_0_array_fold_0_state
                    inputPtr current element current 0 0 0 (heapTop + 48)
                    0 0 0 inputPtr
                    (UInt64.ofNat input.size) (UInt64.ofNat index)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    done current releaseReady 0 0
                let afterBody :=
                  AnnotationMatches.function_0_array_fold_0_state
                    inputPtr (current + element) element
                    (current + element) 0 0 0 (heapTop + 48)
                    0 0 0 inputPtr
                    (UInt64.ofNat input.size) (UInt64.ofNat index)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    0 (current + element) 1 0 0
                let afterContinue :=
                  AnnotationMatches.function_0_array_fold_0_state
                    inputPtr (current + element) element
                    (current + element) 0 0 0 (heapTop + 48)
                    0 0 0 inputPtr
                    (UInt64.ofNat input.size) (UInt64.ofNat (index + 1))
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    0 (current + element) 1 0 0
                have hIndex64 : index < UInt64.size := by
                  exact lt_trans hIndexLt hInputLoop.size_lt
                have hContinueGuard :
                    UInt64.ofNat index < UInt64.ofNat input.size := by
                  rw [UInt64.lt_iff_toNat_lt,
                    UInt64.toNat_ofNat_of_lt' hIndex64,
                    UInt64.toNat_ofNat_of_lt' hInputLoop.size_lt]
                  exact hIndexLt
                apply FixedArrayFoldBody.continuingGuardedProgram_spec
                  (arrayLocal := 11) (indexLocal := 13)
                  (stopLocal := 15) (itemLocal := 2) (scratch := 11)
                  (body := AnnotationMatches.function_0_array_fold_0_body)
                  (condition := AnnotationMatches.function_0_array_fold_0_condition)
                  (continuing := AnnotationMatches.function_0_array_fold_0_step_continuing)
                  (module_ := module) (env := env)
                  (st := FixedArrayResult.writeLength
                    (FixedArrayAllocator.allocStore initial heapTop
                      (FixedArrayCapacity.normalizedCapacity 1 1) 1 allocs)
                    (heapTop + 48) 1)
                  (frame := sumFoldFrame inputPtr (heapTop + 48) input index
                    item done releaseReady)
                  (inputPtr := inputPtr) (indexValue := UInt64.ofNat index)
                  (stopValue := UInt64.ofNat input.size)
                  (input := input) (index := index)
                  (stepProgram := AnnotationMatches.function_0_array_fold_0_step_program)
                  (initial := initialFold.toState)
                  (afterBody := afterBody.toState)
                  (afterCondition := afterBody.toState) (result := false)
                  (hValues := by
                    simp only [sumFoldFrame,
                      AnnotationMatches.function_0_array_fold_0_continuing_frame_values])
                  (hArrayLocal := by
                    simp only [sumFoldFrame,
                      AnnotationMatches.function_0_array_fold_0_continuing_frame_get_11])
                  (hIndexLocal := by
                    simp only [sumFoldFrame,
                      AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13])
                  (hStopLocal := by
                    simp only [sumFoldFrame,
                      AnnotationMatches.function_0_array_fold_0_continuing_frame_get_15])
                  (hIndexValue := rfl) (hContinueGuard := hContinueGuard)
                  (hItem := AnnotationMatches.function_0_array_fold_0_continuing_item_valid
                    inputPtr (sumPrefix input index) item (sumPrefix input index)
                    0 0 0 (heapTop + 48) 0 0 0 inputPtr
                    (UInt64.ofNat input.size) (UInt64.ofNat index)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    done (sumPrefix input index) releaseReady 0 0)
                  (hInput := hInputLoop) (hIndex := hIndexLt)
                  (hLoaded := by
                    simpa only [sumFoldFrame, initialFold, current,
                      AnnotationMatches.function_0_array_fold_0_continuing_frame]
                      using AnnotationMatches.function_0_array_fold_0_continuing_loaded_frame_eq
                        inputPtr (sumPrefix input index) item
                        (sumPrefix input index) 0 0 0 (heapTop + 48)
                        0 0 0 inputPtr
                        (UInt64.ofNat input.size) (UInt64.ofNat index)
                        (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                        done (sumPrefix input index) releaseReady 0 0 element)
                  (hStepProgram := rfl)
                  (hBody := by
                    simpa [initialFold, afterBody, current,
                      AnnotationMatches.function_0_array_fold_0_bodyTransition,
                      ScalarTransition.U64Op.apply]
                      using AnnotationMatches.function_0_array_fold_0_body_eval
                        inputPtr current element current 0 0 0 (heapTop + 48)
                        0 0 0 inputPtr
                        (UInt64.ofNat input.size) (UInt64.ofNat index)
                        (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                        done current releaseReady 0 0)
                  (hCondition := by
                    simpa [afterBody,
                      AnnotationMatches.function_0_array_fold_0_conditionTransition]
                      using AnnotationMatches.function_0_array_fold_0_condition_eval
                        inputPtr (current + element) element
                        (current + element) 0 0 0 (heapTop + 48)
                        0 0 0 inputPtr
                        (UInt64.ofNat input.size) (UInt64.ofNat index)
                        (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                        0 (current + element) 1 0 0)
                · simp
                · intro _
                  refine ⟨afterContinue.toState, ?_, ?_⟩
                  · simpa [afterBody, afterContinue,
                      AnnotationMatches.function_0_array_fold_0_step_continuingTransition,
                      ScalarTransition.U64Op.apply, UInt64.ofNat_add]
                      using AnnotationMatches.function_0_array_fold_0_step_continuing_eval
                        inputPtr (current + element) element
                        (current + element) 0 0 0 (heapTop + 48)
                        0 0 0 inputPtr
                        (UInt64.ofNat input.size) (UInt64.ofNat index)
                        (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                        0 (current + element) 1 0 0
                  · have hPrefix :
                        sumPrefix input (index + 1) = current + element := by
                      simpa [sumPrefix, current, element] using
                        ArrayFold.foldPrefix_succ input
                          (fun sum element : UInt64 => sum + element) 0
                          index hIndexLt
                    have hAfterContinue :
                        afterContinue.toState.toLocals [] =
                          sumFoldFrame inputPtr (heapTop + 48) input
                            (index + 1) element 0 1 := by
                      simp [afterContinue, sumFoldFrame, current, element, hPrefix,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame,
                        AnnotationMatches.function_0_array_fold_0_state,
                        ScalarTransition.U64State.toState]
                    simp only [List.take_zero, List.drop_zero, List.nil_append,
                      sumFoldFrame,
                      AnnotationMatches.function_0_array_fold_0_continuing_frame_values]
                    change SumInvariant
                        (FixedArrayResult.writeLength
                          (FixedArrayAllocator.allocStore initial heapTop
                            (FixedArrayCapacity.normalizedCapacity 1 1) 1 allocs)
                          (heapTop + 48) 1)
                        inputPtr (heapTop + 48) input
                        (FixedArrayResult.writeLength
                          (FixedArrayAllocator.allocStore initial heapTop
                            (FixedArrayCapacity.normalizedCapacity 1 1) 1 allocs)
                          (heapTop + 48) 1)
                        (afterContinue.toState.toLocals []) ∧
                      sumMeasure input (afterContinue.toState.toLocals []) <
                        sumMeasure input
                          (sumFoldFrame inputPtr (heapTop + 48) input index
                            item done releaseReady)
                    constructor
                    · refine ⟨index + 1, element, 0, 1, by omega, rfl, ?_⟩
                      exact hAfterContinue
                    · rw [hAfterContinue]
                      unfold sumMeasure sumFrameIndex
                      simp only [sumFoldFrame,
                        AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13]
                      rw [UInt64.toNat_ofNat_of_lt' hIndex64]
                      have hIndexSucc64 : index + 1 < UInt64.size := by
                        have hInputSize := hInputLoop.size_lt
                        omega
                      rw [UInt64.toNat_ofNat_of_lt' hIndexSucc64]
                      omega

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior
