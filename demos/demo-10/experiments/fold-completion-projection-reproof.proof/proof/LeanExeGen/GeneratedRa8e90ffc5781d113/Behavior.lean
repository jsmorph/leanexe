import LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec
import LeanExeGen.GeneratedRa8e90ffc5781d113.Program
import LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.Allocation
import Project.ProofKit.Control
import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayCapacity
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

namespace LeanExeGen.GeneratedRa8e90ffc5781d113.Behavior

open Wasm Project.ProofKit

def productPrefix (input : Array UInt64) (index : Nat) : UInt64 :=
  ArrayFold.foldPrefix input (fun product element => product * element) 1 index

def productLoopFrame (inputPtr root : UInt64) (input : Array UInt64)
    (index : Nat) (item temporary done staged releaseReady : UInt64) :
    Wasm.Locals :=
  AnnotationMatches.function_0_array_fold_0_continuing_frame
    inputPtr (productPrefix input index) item temporary
    0 0 0 root 0 0 0 inputPtr (UInt64.ofNat input.size)
    (UInt64.ofNat index) (UInt64.ofNat input.size)
    (UInt64.ofNat input.size) done staged releaseReady 0 0

def ProductLoopInv (loopSt : Wasm.Store Unit) (inputPtr root : UInt64)
    (input : Array UInt64) : Wasm.Store Unit → Wasm.Locals → Prop :=
  fun st frame => ∃ index item temporary done staged releaseReady,
    st = loopSt ∧ index ≤ input.size ∧
      frame = productLoopFrame inputPtr root input index item temporary
        done staged releaseReady

def productLoopMeasure (input : Array UInt64) :
    Wasm.Store Unit → Wasm.Locals → Nat :=
  fun _ frame =>
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
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def) rfl
  wp_fixed_array_length_le_dispatch_from hArray at 7, 8
  · simp [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
      Wasm.Function.toLocals, Wasm.Function.numParams, Wasm.ValueType.zero]
  · simp [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
      Wasm.Function.toLocals, Wasm.Function.numParams, Wasm.ValueType.zero]
  · simp
  · simp [LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
      Wasm.Function.toLocals, Wasm.Function.numParams, Wasm.ValueType.zero]
  · norm_num [UInt64.size]
  case hInvalid =>
    intro hSize
    let entryFrame : Wasm.Locals :=
      LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.toLocals
        (List.take LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.numParams
          [.i64 inputPtr]).reverse
    let branchFrame : Wasm.Locals :=
      FixedArrayLengthDispatch.branchFrame 7 entryFrame inputPtr
    change wp module
      (FixedArrayCapacity.constantProgram 0 1 11 ++
        (FixedArrayAllocatorWindow.region 2 1 ++
          (FixedArrayResult.lengthStoreProgram 7 0 ++
            FixedArrayResult.finishProgram 7 5 6))) _ initial branchFrame env
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · simp [branchFrame, entryFrame,
        FixedArrayLengthDispatch.branchFrame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · simp [Wasm.Locals.validIndex, branchFrame, entryFrame,
        FixedArrayLengthDispatch.branchFrame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · let capacityFrame : Wasm.Locals :=
        FixedArrayCapacity.capacityFrame branchFrame 11 8
      change wp module
        (FixedArrayAllocatorWindow.region 2 1 ++
          (FixedArrayResult.lengthStoreProgram 7 0 ++
            FixedArrayResult.finishProgram 7 5 6)) _ initial capacityFrame env
      have hFitMemory :
          heapTop.toNat + 48 + (8 : UInt64).toNat ≤
            initial.mem.pages * 65536 := by
        simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
      have hFit32 :
          heapTop.toNat + 48 + (8 : UInt64).toNat ≤ 4294967296 := by
        simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFit32
      have hBranchParams : branchFrame.params.length = 1 := by
        simp only [branchFrame,
          FixedArrayLengthDispatch.branchFrame_params]
        rfl
      have hBranchLocals : branchFrame.locals.length = 20 := by
        simp only [branchFrame,
          FixedArrayLengthDispatch.branchFrame_locals_length]
        rfl
      have hCapacityParams : capacityFrame.params.length = 1 := by
        rw [FixedArrayCapacity.capacityFrame_params]
        exact hBranchParams
      have hCapacityLocals : capacityFrame.locals.length = 20 := by
        rw [FixedArrayCapacity.capacityFrame_locals_length]
        exact hBranchLocals
      have hCapacityValues : capacityFrame.values = [] := by
        rw [FixedArrayCapacity.capacityFrame_values]
      apply FixedArrayAllocatorWindow.region_spec_withTail 2 4
        (heapTop := heapTop) (capacity := 8) (stride := 1)
        (allocs := allocs)
      · exact hCapacityParams
      · simpa using hCapacityLocals
      · exact hCapacityValues
      · apply FixedArrayCapacity.capacityFrame_internal_get_capacity
        · omega
        · change 11 < branchFrame.params.length + branchFrame.locals.length
          omega
      · change 8 ≤ 8
        omega
      · exact hFitMemory
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · let allocSt : Wasm.Store Unit :=
          FixedArrayAllocator.allocStore initial heapTop 8 1 allocs
        let allocFrame : Wasm.Locals :=
          FixedArrayAllocatorWindow.allocFrame 2 capacityFrame heapTop 8
        let root : UInt64 := heapTop + 48
        change wp module
          (FixedArrayResult.lengthStoreProgram 7 0 ++
            FixedArrayResult.finishProgram 7 5 6) _ allocSt allocFrame env
        have hFacts := Allocation.bumpFacts heapTop 8 initial.mem.pages
          hFitMemory hPages
        have hRootAddressNat : root.toUInt32.toNat = heapTop.toNat + 48 := by
          simpa [root] using hFacts.wordAddress_toNat 0 (by decide)
        have hAllocValues : allocFrame.values = [] := by
          simp only [allocFrame,
            FixedArrayAllocatorWindow.allocFrame_values]
          exact hCapacityValues
        have hAllocParams : allocFrame.params.length = 1 := by
          simp only [allocFrame,
            FixedArrayAllocatorWindow.allocFrame_params]
          exact hCapacityParams
        have hAllocLocals : allocFrame.locals.length = 20 := by
          simp only [allocFrame,
            FixedArrayAllocatorWindow.allocFrame_locals_length]
          exact hCapacityLocals
        have hRoot : allocFrame.get 7 = some (.i64 root) := by
          exact FixedArrayAllocatorWindow.allocFrame_get_root 2 4
            capacityFrame heapTop 8 hCapacityParams
              (by simpa using hCapacityLocals)
        have hRootBound :
            root.toUInt32.toNat + 8 ≤ allocSt.mem.pages * 65536 := by
          rw [hRootAddressNat]
          simp only [allocSt, FixedArrayAllocator.allocStore_pages]
          omega
        apply FixedArrayResult.lengthStore_spec
          (root := root) (length := 0) (rootLocal := 7)
        · exact hAllocValues
        · exact hRoot
        · exact hRootBound
        · apply FixedArrayResult.finishProgram_spec
            (root := root) (rootLocal := 7) (destinationLocal := 5)
            (returnLocal := 6)
          · exact hAllocValues
          · exact hRoot
          · simpa [hAllocParams]
          · simpa [Wasm.Locals.validIndex, hAllocParams, hAllocLocals]
          · simpa [hAllocParams]
          · simpa [Wasm.Locals.validIndex, hAllocParams, hAllocLocals]
          · have hRootFit32 : root.toNat + 8 ≤ 4294967296 := by
              simp only [root, hFacts.rootToNat]
              omega
            have hRootFitMemory :
                root.toNat + 8 ≤ allocSt.mem.pages * 65536 := by
              simp only [root, hFacts.rootToNat, allocSt,
                FixedArrayAllocator.allocStore_pages]
              omega
            have hOutput := FixedArrayResult.emptyStore_at allocSt root
              hRootFit32 hRootFitMemory
            rw [Wasm.wp_nil]
            simp only [FixedArrayEqNode.branchPost]
            have hReturn := FixedArrayResult.finishFrame_return_get
              allocFrame 5 6 root (by simpa [hAllocParams])
                (by simpa [Wasm.Locals.validIndex, hAllocParams,
                  hAllocLocals])
            have hReturn' :
                ({ FixedArrayResult.finishFrame allocFrame 5 6 root with
                    values := [] } : Wasm.Locals).get 6 = some (.i64 root) := by
              simpa only [Wasm.Locals.get] using hReturn
            simp only [wp_localGet_cons, hReturn', Wasm.wp_nil]
            refine ⟨root, ?_, ?_⟩
            · rfl
            · simp only [FormalSpec.expected, hSize, if_false]
              change UInt64Array.At
                (FixedArrayResult.writeLength allocSt root 0) root #[]
              exact hOutput
  case hValid =>
    intro hSize
    let entryFrame : Wasm.Locals :=
      LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.toLocals
        (List.take LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.numParams
          [.i64 inputPtr]).reverse
    let branchFrame : Wasm.Locals :=
      FixedArrayLengthDispatch.branchFrame 7 entryFrame inputPtr
    change wp module
      (FixedArrayCapacity.constantProgram 1 1 11 ++
        (FixedArrayAllocatorWindow.region 2 1 ++
          (FixedArrayResult.lengthStoreProgram 7 1 ++
            (AnnotationMatches.function_0_array_fold_0_setup_program ++
              ([.block 0 0 [.loop 0 0
                (AnnotationMatches.function_0_array_fold_0_continuing_program ++
                  AnnotationMatches.function_0_array_fold_0_step_program)]] ++
                AnnotationMatches.function_0_array_fold_0_singleton_result_program)))))
      _ initial branchFrame env
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · simp [branchFrame, entryFrame,
        FixedArrayLengthDispatch.branchFrame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · simp [Wasm.Locals.validIndex, branchFrame, entryFrame,
        FixedArrayLengthDispatch.branchFrame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · let capacityFrame : Wasm.Locals :=
        FixedArrayCapacity.capacityFrame branchFrame 11 16
      change wp module
        (FixedArrayAllocatorWindow.region 2 1 ++
          (FixedArrayResult.lengthStoreProgram 7 1 ++
            (AnnotationMatches.function_0_array_fold_0_setup_program ++
              ([.block 0 0 [.loop 0 0
                (AnnotationMatches.function_0_array_fold_0_continuing_program ++
                  AnnotationMatches.function_0_array_fold_0_step_program)]] ++
                AnnotationMatches.function_0_array_fold_0_singleton_result_program))))
        _ initial capacityFrame env
      have hFitMemory :
          heapTop.toNat + 48 + (16 : UInt64).toNat ≤
            initial.mem.pages * 65536 := by
        simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
      have hFit32 :
          heapTop.toNat + 48 + (16 : UInt64).toNat ≤ 4294967296 := by
        simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFit32
      have hFitMemoryNat :
          heapTop.toNat + 48 + 16 ≤ initial.mem.pages * 65536 := by
        exact hFitMemory
      have hFit32Nat : heapTop.toNat + 48 + 16 ≤ 4294967296 := by
        exact hFit32
      have hBranchParamsValue : branchFrame.params = [.i64 inputPtr] := by
        rw [FixedArrayLengthDispatch.branchFrame_params]
        rfl
      have hBranchParams : branchFrame.params.length = 1 := by
        simp [hBranchParamsValue]
      have hBranchLocals : branchFrame.locals.length = 20 := by
        simp only [branchFrame,
          FixedArrayLengthDispatch.branchFrame_locals_length]
        rfl
      have hCapacityParamsValue :
          capacityFrame.params = [.i64 inputPtr] := by
        rw [FixedArrayCapacity.capacityFrame_params]
        exact hBranchParamsValue
      have hCapacityParams : capacityFrame.params.length = 1 := by
        simp [hCapacityParamsValue]
      have hCapacityLocals : capacityFrame.locals.length = 20 := by
        rw [FixedArrayCapacity.capacityFrame_locals_length]
        exact hBranchLocals
      have hCapacityValues : capacityFrame.values = [] := by
        rw [FixedArrayCapacity.capacityFrame_values]
      apply FixedArrayAllocatorWindow.region_spec_withTail 2 4
        (heapTop := heapTop) (capacity := 16) (stride := 1)
        (allocs := allocs)
      · exact hCapacityParams
      · simpa using hCapacityLocals
      · exact hCapacityValues
      · apply FixedArrayCapacity.capacityFrame_internal_get_capacity
        · omega
        · change 11 < branchFrame.params.length + branchFrame.locals.length
          omega
      · change 8 ≤ 16
        omega
      · exact hFitMemory
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · let allocSt : Wasm.Store Unit :=
          FixedArrayAllocator.allocStore initial heapTop 16 1 allocs
        let allocFrame : Wasm.Locals :=
          FixedArrayAllocatorWindow.allocFrame 2 capacityFrame heapTop 16
        let root : UInt64 := heapTop + 48
        change wp module
          (FixedArrayResult.lengthStoreProgram 7 1 ++
            (AnnotationMatches.function_0_array_fold_0_setup_program ++
              ([.block 0 0 [.loop 0 0
                (AnnotationMatches.function_0_array_fold_0_continuing_program ++
                  AnnotationMatches.function_0_array_fold_0_step_program)]] ++
                AnnotationMatches.function_0_array_fold_0_singleton_result_program)))
          _ allocSt allocFrame env
        have hFacts := Allocation.bumpFacts heapTop 16 initial.mem.pages
          hFitMemory hPages
        have hRootAddressNat : root.toUInt32.toNat = heapTop.toNat + 48 := by
          simpa [root] using hFacts.wordAddress_toNat 0 (by decide)
        have hAllocValues : allocFrame.values = [] := by
          simp only [allocFrame,
            FixedArrayAllocatorWindow.allocFrame_values]
          exact hCapacityValues
        have hAllocParamsValue : allocFrame.params = [.i64 inputPtr] := by
          simp only [allocFrame,
            FixedArrayAllocatorWindow.allocFrame_params]
          exact hCapacityParamsValue
        have hAllocParams : allocFrame.params.length = 1 := by
          simp [hAllocParamsValue]
        have hAllocLocals : allocFrame.locals.length = 20 := by
          simp only [allocFrame,
            FixedArrayAllocatorWindow.allocFrame_locals_length]
          exact hCapacityLocals
        have hRoot : allocFrame.get 7 = some (.i64 root) := by
          exact FixedArrayAllocatorWindow.allocFrame_get_root 2 4
            capacityFrame heapTop 16 hCapacityParams
              (by simpa using hCapacityLocals)
        have hRootBound :
            root.toUInt32.toNat + 8 ≤ allocSt.mem.pages * 65536 := by
          rw [hRootAddressNat]
          simp only [allocSt, FixedArrayAllocator.allocStore_pages]
          omega
        have hInputAlloc : UInt64Array.At allocSt inputPtr input := by
          exact FixedArrayPairResult.input_preserved_by_alloc initial heapTop
            16 1 allocs inputPtr input hArray hInputBelow hFitMemory hPages
        apply FixedArrayResult.lengthStore_spec
          (root := root) (length := 1) (rootLocal := 7)
        · exact hAllocValues
        · exact hRoot
        · exact hRootBound
        · let loopSt : Wasm.Store Unit :=
            FixedArrayResult.writeLength allocSt root 1
          have hInputLoop : UInt64Array.At loopSt inputPtr input := by
            dsimp [loopSt, FixedArrayResult.writeLength]
            apply hInputAlloc.write64After
            rw [hRootAddressNat]
            omega
          have hLoopPages : loopSt.mem.pages = initial.mem.pages := by
            simp [loopSt, allocSt, FixedArrayResult.writeLength_pages,
              FixedArrayAllocator.allocStore_pages]
          change wp module
            (AnnotationMatches.function_0_array_fold_0_setup_program ++
              ([.block 0 0 [.loop 0 0
                (AnnotationMatches.function_0_array_fold_0_continuing_program ++
                  AnnotationMatches.function_0_array_fold_0_step_program)]] ++
                AnnotationMatches.function_0_array_fold_0_singleton_result_program))
            _ loopSt allocFrame env
          apply FixedArrayFold.forwardSetupProgram_spec
            (inputPtr := inputPtr) (input := input)
          · exact hAllocParamsValue
          · exact hAllocValues
          · intro slot hSlot
            simp [FixedArrayFold.setupLocals] at hSlot
            omega
          · decide
          · exact hInputLoop
          · wp_block_loop
              invariant ProductLoopInv loopSt inputPtr root input
              decreasing productLoopMeasure input
            · refine ⟨0, 0, 0, inputPtr, 0, 0, rfl, by omega, ?_⟩
              simp (config := { maxSteps := 1000000 }) [
                FixedArrayFold.forwardSetupFrame, productLoopFrame,
                productPrefix, ArrayFold.foldPrefix,
                AnnotationMatches.function_0_array_fold_0_continuing_frame,
                AnnotationMatches.function_0_array_fold_0_state,
                ScalarTransition.U64State.toState,
                allocFrame, FixedArrayAllocatorWindow.allocFrame,
                capacityFrame, FixedArrayCapacity.capacityFrame,
                branchFrame, FixedArrayLengthDispatch.branchFrame,
                entryFrame, root,
                LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
                Wasm.Function.toLocals, Wasm.Function.numParams,
                Wasm.ValueType.zero]
            · intro st frame hInv
              rcases hInv with
                ⟨index, item, temporary, done, staged, releaseReady,
                  rfl, hIndex, rfl⟩
              have hFrameValues :
                  (productLoopFrame inputPtr root input index item temporary
                    done staged releaseReady).values = [] := by
                simp only [productLoopFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_values]
              have hFrameIndex :
                  (productLoopFrame inputPtr root input index item temporary
                    done staged releaseReady).get 13 =
                    some (.i64 (UInt64.ofNat index)) := by
                simp only [productLoopFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13]
              have hFrameStop :
                  (productLoopFrame inputPtr root input index item temporary
                    done staged releaseReady).get 15 =
                    some (.i64 (UInt64.ofNat input.size)) := by
                simp only [productLoopFrame,
                  AnnotationMatches.function_0_array_fold_0_continuing_frame_get_15]
              by_cases hDone : index = input.size
              · subst index
                apply FixedArrayTraversalInput.continuingProgram_exit_spec
                  (arrayLocal := 11) (indexLocal := 13) (stopLocal := 15)
                  (itemLocal := 2) (index := UInt64.ofNat input.size)
                  (hValues := hFrameValues) (hIndex := hFrameIndex)
                  (hStop := hFrameStop)
                have hPayloadAddressNat :
                    (FixedArrayResult.payloadAddress root 0).toUInt32.toNat =
                      heapTop.toNat + 48 + 8 := by
                  simpa [root, FixedArrayResult.payloadAddress] using
                    hFacts.wordAddress_toNat 1 (by decide)
                have hPayloadBound :
                    (FixedArrayResult.payloadAddress root 0).toUInt32.toNat + 8 ≤
                      loopSt.mem.pages * 65536 := by
                  rw [hPayloadAddressNat, hLoopPages]
                  omega
                change wp module
                  AnnotationMatches.function_0_array_fold_0_singleton_result_program
                  _ loopSt
                  (productLoopFrame inputPtr root input input.size item temporary
                    done staged releaseReady) env
                apply AnnotationMatches.function_0_array_fold_0_singleton_result_spec
                  (hPayloadBound := hPayloadBound)
                simp only [FixedArrayEqNode.branchPost]
                let completedFrame :=
                  productLoopFrame inputPtr root input input.size item temporary
                    done staged releaseReady
                let placedFrame := FixedArrayFold.resultFrame completedFrame 10
                  (productPrefix input input.size)
                have hCompletedParams : completedFrame.params.length = 1 := by
                  simp only [completedFrame, productLoopFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_params]
                  rfl
                have hCompletedLocals : completedFrame.locals.length = 20 := by
                  simp only [completedFrame, productLoopFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_locals_length]
                have hPlacedParams : placedFrame.params.length = 1 := by
                  simp only [placedFrame,
                    FixedArrayFold.resultFrame_params]
                  exact hCompletedParams
                have hPlacedLocals : placedFrame.locals.length = 20 := by
                  simp only [placedFrame,
                    FixedArrayFold.resultFrame_locals_length]
                  exact hCompletedLocals
                have hReturn := FixedArrayResult.finishFrame_return_get
                  placedFrame 4 6 root (by omega)
                    (by simpa [Wasm.Locals.validIndex, hPlacedParams,
                      hPlacedLocals])
                have hReturn' :
                    ({ FixedArrayResult.finishFrame placedFrame 4 6 root with
                        values := [] } : Wasm.Locals).get 6 =
                      some (.i64 root) := by
                  simpa only [Wasm.Locals.get] using hReturn
                change wp module [.localGet 6] _
                  (FixedArrayResult.writePayload loopSt root 0
                    (productPrefix input input.size))
                  { FixedArrayResult.finishFrame placedFrame 4 6 root with
                    values := [] } env
                simp only [wp_localGet_cons, hReturn', Wasm.wp_nil]
                have hRootFit32 : root.toNat + 16 ≤ 4294967296 := by
                  simp only [root, hFacts.rootToNat]
                  exact hFit32Nat
                have hRootFitMemory :
                    root.toNat + 16 ≤ allocSt.mem.pages * 65536 := by
                  simp only [root, hFacts.rootToNat, allocSt,
                    FixedArrayAllocator.allocStore_pages]
                  exact hFitMemoryNat
                have hOutput : UInt64Array.At
                    (FixedArrayResult.writePayload loopSt root 0
                      (productPrefix input input.size)) root
                    #[productPrefix input input.size] := by
                  simpa [loopSt, FixedArrayResult.singletonStore] using
                    FixedArrayResult.singletonStore_at allocSt root
                      (productPrefix input input.size) hRootFit32 hRootFitMemory
                refine ⟨root, rfl, ?_⟩
                simp only [FormalSpec.expected, hSize, if_true]
                change UInt64Array.At
                  (FixedArrayResult.writePayload loopSt root 0
                    (productPrefix input input.size)) root
                  #[input.foldl (fun product element => product * element) 1]
                rw [← ArrayFold.foldPrefix_size input
                  (fun product element => product * element) 1]
                exact hOutput
              · have hIndexLt : index < input.size := by omega
                have hFrameArray :
                    (productLoopFrame inputPtr root input index item temporary
                      done staged releaseReady).get 11 = some (.i64 inputPtr) := by
                  simp only [productLoopFrame,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame_get_11]
                have hItemValid :
                    (productLoopFrame inputPtr root input index item temporary
                      done staged releaseReady).validIndex 2 := by
                  exact
                    AnnotationMatches.function_0_array_fold_0_continuing_item_valid
                      inputPtr (productPrefix input index) item temporary
                      0 0 0 root 0 0 0 inputPtr (UInt64.ofNat input.size)
                      (UInt64.ofNat index) (UInt64.ofNat input.size)
                      (UInt64.ofNat input.size) done staged releaseReady 0 0
                have hIndexNat : (UInt64.ofNat index).toNat = index :=
                  UInt64.toNat_ofNat_of_lt' (by
                    have hSizeLt := hInputLoop.size_lt
                    omega)
                have hSizeNat : (UInt64.ofNat input.size).toNat = input.size :=
                  UInt64.toNat_ofNat_of_lt' hInputLoop.size_lt
                have hContinueEncoded :
                    UInt64.ofNat index < UInt64.ofNat input.size := by
                  rw [UInt64.lt_iff_toNat_lt, hIndexNat, hSizeNat]
                  exact hIndexLt
                let accumulator : UInt64 := productPrefix input index
                let element : UInt64 := input[index]'hIndexLt
                let loadedU : ScalarTransition.U64State :=
                  AnnotationMatches.function_0_array_fold_0_state
                    inputPtr accumulator element temporary 0 0 0 root 0 0 0 inputPtr
                    (UInt64.ofNat input.size) (UInt64.ofNat index)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                    done staged releaseReady 0 0
                let afterU : ScalarTransition.U64State :=
                  AnnotationMatches.function_0_array_fold_0_state
                    inputPtr (accumulator * element) element (accumulator * element)
                    0 0 0 root 0 0 0 inputPtr (UInt64.ofNat input.size)
                    (UInt64.ofNat index) (UInt64.ofNat input.size)
                    (UInt64.ofNat input.size) 0 (accumulator * element) 1 0 0
                let nextU : ScalarTransition.U64State :=
                  AnnotationMatches.function_0_array_fold_0_state
                    inputPtr (accumulator * element) element (accumulator * element)
                    0 0 0 root 0 0 0 inputPtr (UInt64.ofNat input.size)
                    (UInt64.ofNat index + 1) (UInt64.ofNat input.size)
                    (UInt64.ofNat input.size) 0 (accumulator * element) 1 0 0
                refine FixedArrayFoldBody.continuingGuardedProgram_spec
                  (arrayLocal := 11) (indexLocal := 13) (stopLocal := 15)
                  (itemLocal := 2) (scratch := 11)
                  (body := AnnotationMatches.function_0_array_fold_0_body)
                  (condition :=
                    AnnotationMatches.function_0_array_fold_0_condition)
                  (continuing :=
                    AnnotationMatches.function_0_array_fold_0_step_continuing)
                  (module_ := module) (env := env) (st := loopSt)
                  (frame := productLoopFrame inputPtr root input index item
                    temporary done staged releaseReady)
                  (inputPtr := inputPtr) (indexValue := UInt64.ofNat index)
                  (stopValue := UInt64.ofNat input.size)
                  (input := input) (index := index)
                  (stepProgram :=
                    AnnotationMatches.function_0_array_fold_0_step_program)
                  (initial := loadedU.toState) (afterBody := afterU.toState)
                  (afterCondition := afterU.toState) (result := false)
                  (hValues := hFrameValues) (hArrayLocal := hFrameArray)
                  (hIndexLocal := hFrameIndex) (hStopLocal := hFrameStop)
                  (hIndexValue := rfl) (hContinueGuard := hContinueEncoded)
                  (hItem := hItemValid) (hInput := hInputLoop)
                  (hIndex := hIndexLt) (hLoaded := ?_)
                  (hStepProgram := rfl) (hBody := ?_) (hCondition := ?_)
                  (hExit := ?_) (hContinue := ?_)
                · simpa only [productLoopFrame, loadedU, accumulator, element,
                    AnnotationMatches.function_0_array_fold_0_continuing_frame]
                    using
                    (AnnotationMatches.function_0_array_fold_0_continuing_loaded_frame_eq
                      inputPtr (productPrefix input index) item temporary
                      0 0 0 root 0 0 0 inputPtr (UInt64.ofNat input.size)
                      (UInt64.ofNat index) (UInt64.ofNat input.size)
                      (UInt64.ofNat input.size) done staged releaseReady 0 0
                      element)
                · simpa [loadedU, afterU,
                    AnnotationMatches.function_0_array_fold_0_bodyTransition,
                    ScalarTransition.U64Op.apply] using
                    (AnnotationMatches.function_0_array_fold_0_body_eval
                      inputPtr accumulator element temporary 0 0 0 root 0 0 0
                      inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                      done staged releaseReady 0 0)
                · simpa [afterU,
                    AnnotationMatches.function_0_array_fold_0_conditionTransition]
                    using
                    (AnnotationMatches.function_0_array_fold_0_condition_eval
                      inputPtr (accumulator * element) element (accumulator * element)
                      0 0 0 root 0 0 0 inputPtr (UInt64.ofNat input.size)
                      (UInt64.ofNat index) (UInt64.ofNat input.size)
                      (UInt64.ofNat input.size) 0 (accumulator * element) 1 0 0)
                · simp
                · intro _
                  refine ⟨nextU.toState, ?_, ?_⟩
                  · simpa [afterU, nextU,
                      AnnotationMatches.function_0_array_fold_0_step_continuingTransition,
                      ScalarTransition.U64Op.apply] using
                      (AnnotationMatches.function_0_array_fold_0_step_continuing_eval
                        inputPtr (accumulator * element) element (accumulator * element)
                        0 0 0 root 0 0 0 inputPtr (UInt64.ofNat input.size)
                        (UInt64.ofNat index) (UInt64.ofNat input.size)
                        (UInt64.ofNat input.size) 0 (accumulator * element) 1 0 0)
                  · change
                      ProductLoopInv loopSt inputPtr root input loopSt
                          (nextU.toState.toLocals []) ∧
                        productLoopMeasure input loopSt
                            (nextU.toState.toLocals []) <
                          productLoopMeasure input loopSt
                            (productLoopFrame inputPtr root input index item
                              temporary done staged releaseReady)
                    have hPrefixSucc :
                        productPrefix input (index + 1) = accumulator * element := by
                      simpa [productPrefix, accumulator, element] using
                        ArrayFold.foldPrefix_succ input
                          (fun product element => product * element) 1 index
                          hIndexLt
                    have hIndexSucc :
                        UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by
                      change UInt64.ofNat index + UInt64.ofNat 1 =
                        UInt64.ofNat (index + 1)
                      rw [← UInt64.ofNat_add]
                    have hNextFrame :
                        nextU.toState.toLocals [] =
                          productLoopFrame inputPtr root input (index + 1)
                            element (accumulator * element) 0
                              (accumulator * element) 1 := by
                      change
                        AnnotationMatches.function_0_array_fold_0_continuing_frame
                            inputPtr (accumulator * element) element
                            (accumulator * element) 0 0 0 root 0 0 0 inputPtr
                            (UInt64.ofNat input.size) (UInt64.ofNat index + 1)
                            (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                            0 (accumulator * element) 1 0 0 =
                          AnnotationMatches.function_0_array_fold_0_continuing_frame
                            inputPtr (productPrefix input (index + 1)) element
                            (accumulator * element) 0 0 0 root 0 0 0 inputPtr
                            (UInt64.ofNat input.size) (UInt64.ofNat (index + 1))
                            (UInt64.ofNat input.size) (UInt64.ofNat input.size)
                            0 (accumulator * element) 1 0 0
                      rw [hPrefixSucc, hIndexSucc]
                    constructor
                    · refine ⟨index + 1, element, accumulator * element, 0,
                        accumulator * element, 1, rfl, by omega, hNextFrame⟩
                    · have hOldMeasure :
                          productLoopMeasure input loopSt
                              (productLoopFrame inputPtr root input index item
                                temporary done staged releaseReady) =
                            input.size - index := by
                        simp only [productLoopMeasure, hFrameIndex, hIndexNat]
                      have hNextIndexNat :
                          (UInt64.ofNat (index + 1)).toNat = index + 1 :=
                        UInt64.toNat_ofNat_of_lt' (by
                          have hSizeLt := hInputLoop.size_lt
                          omega)
                      have hNextFrameIndex :
                          (productLoopFrame inputPtr root input (index + 1)
                            element (accumulator * element) 0
                              (accumulator * element) 1).get 13 =
                              some (.i64 (UInt64.ofNat (index + 1))) := by
                        simp only [productLoopFrame,
                          AnnotationMatches.function_0_array_fold_0_continuing_frame_get_13]
                      rw [hNextFrame, hOldMeasure]
                      simp only [productLoopMeasure, hNextFrameIndex,
                        hNextIndexNat]
                      omega

end LeanExeGen.GeneratedRa8e90ffc5781d113.Behavior
