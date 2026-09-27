import LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec
import LeanExeGen.GeneratedRa8e90ffc5781d113.Program
import LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.Control
import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayCapacity
import Project.ProofKit.FixedArrayFold
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

def artifactPost (input : Array UInt64) (inputPtr : UInt64) :
    Wasm.Assertion Unit :=
  fun continuation => match continuation with
    | .Fallthrough final frame =>
        ∃ outputPtr,
          frame.values.take
              LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.results.length ++
              [.i64 inputPtr].drop
                LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.numParams =
            [.i64 outputPtr] ∧
          FormalSpec.UInt64ArrayAt final outputPtr (FormalSpec.expected input)
    | .Return final values =>
        ∃ outputPtr,
          values.take
              LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.results.length ++
              [.i64 inputPtr].drop
                LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.numParams =
            [.i64 outputPtr] ∧
          FormalSpec.UInt64ArrayAt final outputPtr (FormalSpec.expected input)
    | _ => False

def foldFrame (input : Array UInt64) (inputPtr root : UInt64) (index : Nat)
    (item temporary done staged releaseReady : UInt64) : Wasm.Locals :=
  LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame
    inputPtr
    (Project.ProofKit.ArrayFold.foldPrefix input
      (fun product element => product * element) 1 index)
    item temporary 0 0 0 root 0 0 0 inputPtr (UInt64.ofNat input.size)
    (UInt64.ofNat index) (UInt64.ofNat input.size) (UInt64.ofNat input.size)
    done staged releaseReady 0 0

def foldInvariant (input : Array UInt64) (inputPtr root : UInt64)
    (loopStore : Wasm.Store Unit) : Wasm.AssertionF Unit :=
  fun current frame =>
    current = loopStore ∧
      ∃ index, index ≤ input.size ∧
        ∃ item temporary done staged releaseReady,
          frame = foldFrame input inputPtr root index item temporary done staged
            releaseReady

def foldMeasure (input : Array UInt64) (_ : Wasm.Store Unit)
    (frame : Wasm.Locals) : Nat :=
  match frame.locals[12]? with
  | some (Value.i64 index) => input.size - index.toNat
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
  let entryFrame : Wasm.Locals :=
    LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.toLocals [.i64 inputPtr]
  let branchFrame : Wasm.Locals :=
    Project.ProofKit.FixedArrayLengthDispatch.branchFrame 7 entryFrame inputPtr
  have hBranchParams : branchFrame.params = [.i64 inputPtr] := by
    simp [branchFrame, entryFrame,
      Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
      LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
      Wasm.Function.toLocals, Wasm.ValueType.zero]
  have hBranchLocals : branchFrame.locals.length = 20 := by
    simp [branchFrame, entryFrame,
      Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
      LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
      Wasm.Function.toLocals, Wasm.ValueType.zero]
  have hBranchValues : branchFrame.values = [] := by
    rfl
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def) rfl
  apply Wasm.wp.conseq (Q := artifactPost input inputPtr)
  · intro continuation hPost
    cases continuation <;> simpa [artifactPost] using hPost
  change Wasm.wp _
    (Project.ProofKit.FixedArrayLengthDispatch.leProgram 7 8 _ _ ++ [.localGet 6])
    (artifactPost input inputPtr) initial entryFrame env
  apply Project.ProofKit.FixedArrayLengthDispatch.leProgram_spec
    (frame := entryFrame) (hInput := hArray)
  · simp [entryFrame, LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
      Wasm.Function.toLocals, Wasm.ValueType.zero]
  · simp [entryFrame, LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
      Wasm.Function.toLocals, Wasm.ValueType.zero]
  · norm_num
  · norm_num [entryFrame, LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
      Wasm.Function.toLocals, Wasm.ValueType.zero]
  · norm_num [UInt64.size]
  case hValid =>
    intro hSmall
    have hFitMemory : heapTop.toNat + 48 + 16 ≤
        initial.mem.pages * 65536 := by
      simpa [FormalSpec.expected, hSmall] using hOutputFitMemory
    have hFacts := Project.ProofKit.Allocation.bumpFacts
      heapTop 16 initial.mem.pages hFitMemory hPages
    change Wasm.wp _
      (Project.ProofKit.FixedArrayCapacity.constantProgram 1 1 11 ++ _)
      _ initial branchFrame env
    apply Project.ProofKit.FixedArrayCapacity.constantProgram_spec
    · exact hBranchValues
    · simp [hBranchParams]
    · simp [Wasm.Locals.validIndex, hBranchParams, hBranchLocals]
    change Wasm.wp _
      (Project.ProofKit.FixedArrayAllocatorWindow.region 2 1 ++ _)
      _ initial _ env
    apply Project.ProofKit.FixedArrayAllocatorWindow.region_spec_withTail
      (offset := 2) (tail := 4) (heapTop := heapTop) (capacity := 16)
      (stride := 1) (allocs := allocs)
    · simp [Project.ProofKit.FixedArrayCapacity.capacityFrame, hBranchParams]
    · simp [Project.ProofKit.FixedArrayCapacity.capacityFrame, hBranchLocals]
    · rfl
    · norm_num [Project.ProofKit.FixedArrayCapacity.capacityFrame,
        Project.ProofKit.FixedArrayCapacity.normalizedCapacity,
        Project.ProofKit.FixedArrayCapacity.unnormalizedCapacity,
        hBranchParams, hBranchLocals, List.getElem?_set] <;> native_decide
    · native_decide
    · exact hFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    let validCapacityFrame : Wasm.Locals :=
      Project.ProofKit.FixedArrayCapacity.capacityFrame branchFrame 11
        (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 1 1)
    let validStore : Wasm.Store Unit :=
      Project.ProofKit.FixedArrayAllocator.allocStore
        initial heapTop 16 1 allocs
    let validFrame : Wasm.Locals :=
      Project.ProofKit.FixedArrayAllocatorWindow.allocFrame
        2 validCapacityFrame heapTop 16
    let loopStore : Wasm.Store Unit :=
      Project.ProofKit.FixedArrayResult.writeLength
        validStore (heapTop + 48) 1
    have hRootAddress :
        (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
      simpa using hFacts.wordAddress_toNat 0 (by native_decide)
    have hInputAlloc :=
      Project.ProofKit.FixedArrayPairResult.input_preserved_by_alloc
        initial heapTop 16 1 allocs inputPtr input hArray hInputBelow
        hFitMemory hPages
    have hInputLoop : UInt64Array.At loopStore inputPtr input := by
      have hAfter : inputPtr.toNat + 8 * (input.size + 1) ≤
          (heapTop + 48).toUInt32.toNat := by
        rw [hRootAddress]
        omega
      simpa [loopStore, validStore,
        Project.ProofKit.FixedArrayResult.writeLength] using
          hInputAlloc.write64After hAfter
    change Wasm.wp _
      (Project.ProofKit.FixedArrayResult.lengthStoreProgram 7 1 ++ _)
      _ validStore validFrame env
    apply Project.ProofKit.FixedArrayResult.lengthStore_spec
      (root := heapTop + 48)
    · rfl
    · norm_num [validFrame, validCapacityFrame, Wasm.Locals.get,
        Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
        Project.ProofKit.FixedArrayCapacity.capacityFrame,
        Project.ProofKit.FixedArrayCapacity.normalizedCapacity,
        Project.ProofKit.FixedArrayCapacity.unnormalizedCapacity,
        hBranchParams, hBranchLocals, List.getElem?_set]
    · rw [hRootAddress]
      simp only [validStore,
        Project.ProofKit.FixedArrayAllocator.allocStore_pages]
      omega
    change Wasm.wp _
      (Project.ProofKit.FixedArrayFold.forwardSetupProgram
        11 12 13 16 14 1 18 15 1 ++ _)
      _ loopStore validFrame env
    apply Project.ProofKit.FixedArrayFold.forwardSetupProgram_spec
      (inputPtr := inputPtr) (input := input)
    · simp [validFrame, validCapacityFrame,
        Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
        Project.ProofKit.FixedArrayCapacity.capacityFrame, hBranchParams]
    · rfl
    · intro slot hSlot
      simp [Project.ProofKit.FixedArrayFold.setupLocals] at hSlot
      rcases hSlot with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [validFrame, validCapacityFrame,
          Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
          Project.ProofKit.FixedArrayCapacity.capacityFrame,
          hBranchParams, hBranchLocals]
    · native_decide
    · exact hInputLoop
    change Wasm.wp _
      ([.block 0 0 [.loop 0 0
          (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_program ++
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_step_program)]] ++
        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_result_program ++
        Project.ProofKit.FixedArrayResult.payloadStoreProgram 7 10 0 ++
        Project.ProofKit.FixedArrayResult.finishProgram 7 4 6)
      _ loopStore _ env
    apply Wasm.wp_block_cons
    apply Wasm.wp_loop_cons
      (Inv := foldInvariant input inputPtr (heapTop + 48) loopStore)
      (μ := foldMeasure input)
    · refine ⟨rfl, 0, by omega, 0, 0, inputPtr, 0, 0, ?_⟩
      simp [foldFrame,
        Project.ProofKit.FixedArrayFold.forwardSetupFrame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
        Project.ProofKit.ScalarTransition.U64State.toState,
        Project.ProofKit.ScalarTransition.State.toLocals,
        Project.ProofKit.ArrayFold.foldPrefix,
        validFrame, validCapacityFrame,
        Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
        Project.ProofKit.FixedArrayCapacity.capacityFrame,
        Project.ProofKit.FixedArrayCapacity.normalizedCapacity,
        Project.ProofKit.FixedArrayCapacity.unnormalizedCapacity,
        branchFrame, entryFrame,
        Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
        LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
        Wasm.Function.toLocals, Wasm.ValueType.zero]
    · rintro current frame
        ⟨rfl, index, hIndex, item, temporary, done, staged, releaseReady,
          rfl⟩
      have hIndexNat : (UInt64.ofNat index).toNat = index := by
        apply UInt64.toNat_ofNat_of_lt'
        have hSize := hArray.size_lt
        omega
      by_cases hDoneIndex : index = input.size
      · subst index
        apply Project.ProofKit.FixedArrayTraversalInput.continuingProgram_exit_spec
          (arrayLocal := 11) (indexLocal := 13) (stopLocal := 15)
          (itemLocal := 2) (index := UInt64.ofNat input.size)
        · rfl
        · simp [foldFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
            Project.ProofKit.ScalarTransition.U64State.toState,
            Project.ProofKit.ScalarTransition.State.toLocals,
            Wasm.Locals.get]
        · simp [foldFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
            Project.ProofKit.ScalarTransition.U64State.toState,
            Project.ProofKit.ScalarTransition.State.toLocals,
            Wasm.Locals.get]
        change Wasm.wp _
          (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_result_program ++
            Project.ProofKit.FixedArrayResult.payloadStoreProgram 7 10 0 ++
            Project.ProofKit.FixedArrayResult.finishProgram 7 4 6)
          (Project.ProofKit.FixedArrayEqNode.branchPost _ env [.localGet 6]
            (artifactPost input inputPtr)) loopStore
          (foldFrame input inputPtr (heapTop + 48) input.size item temporary
            done staged releaseReady) env
        apply Project.ProofKit.FixedArrayFold.resultProgram_spec
          (accumulatorLocal := 1) (resultLocal := 10)
          (value := Project.ProofKit.ArrayFold.foldPrefix input
            (fun product element => product * element) 1 input.size)
        · rfl
        · simp [foldFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
            Project.ProofKit.ScalarTransition.U64State.toState,
            Project.ProofKit.ScalarTransition.State.toLocals,
            Wasm.Locals.get]
        · simp [foldFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
            Project.ProofKit.ScalarTransition.U64State.toState,
            Project.ProofKit.ScalarTransition.State.toLocals]
        · simp [Wasm.Locals.validIndex, foldFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
            Project.ProofKit.ScalarTransition.U64State.toState,
            Project.ProofKit.ScalarTransition.State.toLocals]
        change Wasm.wp _
          (Project.ProofKit.FixedArrayResult.payloadStoreProgram 7 10 0 ++
            Project.ProofKit.FixedArrayResult.finishProgram 7 4 6)
          _ loopStore _ env
        apply Project.ProofKit.FixedArrayResult.payloadStore_spec
          (root := heapTop + 48)
          (value := Project.ProofKit.ArrayFold.foldPrefix input
            (fun product element => product * element) 1 input.size)
        · simp [Project.ProofKit.FixedArrayFold.resultFrame, foldFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
            Project.ProofKit.ScalarTransition.U64State.toState,
            Project.ProofKit.ScalarTransition.State.toLocals,
            Wasm.Locals.get, List.getElem?_set]
        · simp [Project.ProofKit.FixedArrayFold.resultFrame, foldFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
            Project.ProofKit.ScalarTransition.U64State.toState,
            Project.ProofKit.ScalarTransition.State.toLocals,
            Wasm.Locals.get, List.getElem?_set]
        · have hPayloadAddress :
              (Project.ProofKit.FixedArrayResult.payloadAddress
                (heapTop + 48) 0).toUInt32.toNat = heapTop.toNat + 56 := by
            simpa [Project.ProofKit.FixedArrayResult.payloadAddress] using
              hFacts.wordAddress_toNat 1 (by native_decide)
          rw [hPayloadAddress]
          simp only [loopStore, validStore,
            Project.ProofKit.FixedArrayResult.writeLength,
            Mem.write64_pages,
            Project.ProofKit.FixedArrayAllocator.allocStore_pages]
          omega
        have hRootFit32 : (heapTop + 48).toNat + 16 ≤ 4294967296 := by
          rw [hFacts.rootToNat]
          exact hFacts.fit32
        have hRootFitMemory : (heapTop + 48).toNat + 16 ≤
            validStore.mem.pages * 65536 := by
          rw [hFacts.rootToNat]
          simp only [validStore,
            Project.ProofKit.FixedArrayAllocator.allocStore_pages]
          exact hFitMemory
        have hOutput := Project.ProofKit.FixedArrayResult.singletonStore_at
          validStore (heapTop + 48)
          (Project.ProofKit.ArrayFold.foldPrefix input
            (fun product element => product * element) 1 input.size)
          hRootFit32 hRootFitMemory
        change Wasm.wp _
          (Project.ProofKit.FixedArrayResult.finishProgram 7 4 6 ++ [])
          _ _ _ env
        apply Project.ProofKit.FixedArrayResult.finishProgram_spec
          (root := heapTop + 48)
        · rfl
        · simp [Project.ProofKit.FixedArrayFold.resultFrame, foldFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
            Project.ProofKit.ScalarTransition.U64State.toState,
            Project.ProofKit.ScalarTransition.State.toLocals,
            Wasm.Locals.get, List.getElem?_set]
        · simp [Project.ProofKit.FixedArrayFold.resultFrame, foldFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
            Project.ProofKit.ScalarTransition.U64State.toState,
            Project.ProofKit.ScalarTransition.State.toLocals]
        · simp [Wasm.Locals.validIndex,
            Project.ProofKit.FixedArrayFold.resultFrame, foldFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
            Project.ProofKit.ScalarTransition.U64State.toState,
            Project.ProofKit.ScalarTransition.State.toLocals]
        · simp [Project.ProofKit.FixedArrayFold.resultFrame, foldFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
            Project.ProofKit.ScalarTransition.U64State.toState,
            Project.ProofKit.ScalarTransition.State.toLocals]
        · simp [Wasm.Locals.validIndex,
            Project.ProofKit.FixedArrayFold.resultFrame, foldFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
            Project.ProofKit.ScalarTransition.U64State.toState,
            Project.ProofKit.ScalarTransition.State.toLocals]
        have hOutputFormal : FormalSpec.UInt64ArrayAt
            (Project.ProofKit.FixedArrayResult.singletonStore validStore
              (heapTop + 48)
              (Project.ProofKit.ArrayFold.foldPrefix input
                (fun product element => product * element) 1 input.size))
            (heapTop + 48)
            #[Project.ProofKit.ArrayFold.foldPrefix input
              (fun product element => product * element) 1 input.size] := by
          change UInt64Array.At _ _ _
          exact hOutput
        have hNumParams : 1 ≤
            LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.numParams := by
          native_decide
        simpa [wp_nil, Project.ProofKit.FixedArrayEqNode.branchPost,
          artifactPost, Project.ProofKit.FixedArrayResult.finishFrame,
          Project.ProofKit.FixedArrayResult.singletonStore,
          Project.ProofKit.FixedArrayResult.writePayload,
          Project.ProofKit.FixedArrayResult.writeLength,
          Project.ProofKit.FixedArrayFold.resultFrame, foldFrame,
          loopStore, validStore, wp_simp,
          Wasm.Locals.get, List.getElem?_set,
          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
          LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
          Project.ProofKit.ScalarTransition.U64State.toState,
          Project.ProofKit.ScalarTransition.State.toLocals,
          LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
          FormalSpec.expected, hSmall,
          Project.ProofKit.ArrayFold.foldPrefix_size] using
            And.intro hNumParams hOutputFormal
      · have hIndexLt : index < input.size := by omega
        have hContinue : UInt64.ofNat index < UInt64.ofNat input.size := by
          rw [UInt64.lt_iff_toNat_lt, hIndexNat,
            UInt64.toNat_ofNat_of_lt' hArray.size_lt]
          exact hIndexLt
        let accumulated : UInt64 := Project.ProofKit.ArrayFold.foldPrefix input
          (fun product element => product * element) 1 index
        let element : UInt64 := input[index]
        let product : UInt64 := accumulated * element
        apply LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_spec
          (v0 := inputPtr) (v1 := accumulated) (v2 := item) (v3 := temporary)
          (v4 := 0) (v5 := 0) (v6 := 0) (v7 := heapTop + 48)
          (v8 := 0) (v9 := 0) (v10 := 0) (v11 := inputPtr)
          (v12 := UInt64.ofNat input.size) (v13 := UInt64.ofNat index)
          (v14 := UInt64.ofNat input.size) (v15 := UInt64.ofNat input.size)
          (v16 := done) (v17 := staged) (v18 := releaseReady)
          (v19 := 0) (v20 := 0) (input := input) (index := index)
          (hIndexValue := rfl) (hContinue := hContinue)
          (hInput := hInputLoop) (hIndex := hIndexLt)
        have hLoadedFrame :
            Project.ProofKit.FixedArrayTraversalInput.dynamicResultFrame
              (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame
                inputPtr accumulated item temporary 0 0 0 (heapTop + 48) 0 0 0
                inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                (UInt64.ofNat input.size) (UInt64.ofNat input.size) done staged
                releaseReady 0 0)
              2 element
              (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_item_valid
                inputPtr accumulated item temporary 0 0 0 (heapTop + 48) 0 0 0
                inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                (UInt64.ofNat input.size) (UInt64.ofNat input.size) done staged
                releaseReady 0 0) =
            (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state
              inputPtr accumulated element temporary 0 0 0 (heapTop + 48) 0 0 0
              inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
              (UInt64.ofNat input.size) (UInt64.ofNat input.size) done staged
              releaseReady 0 0).toState.toLocals [] := by
          simp [Project.ProofKit.FixedArrayTraversalInput.dynamicResultFrame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_frame,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_continuing_item_valid,
            Project.ProofKit.ScalarTransition.U64State.toState,
            Project.ProofKit.ScalarTransition.State.toLocals,
            Wasm.Locals.set, Wasm.Locals.validIndex]
        rw [hLoadedFrame]
        change Wasm.wp _
          (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_step_program ++ [])
          _ loopStore _ env
        apply Project.ProofKit.ScalarTransition.guardedBackEdgeProgram_spec
          (initial :=
            (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state
              inputPtr accumulated element temporary 0 0 0 (heapTop + 48) 0 0 0
              inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
              (UInt64.ofNat input.size) (UInt64.ofNat input.size) done staged
              releaseReady 0 0).toState)
          (afterBody :=
            (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state
              inputPtr product element product 0 0 0 (heapTop + 48) 0 0 0
              inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
              (UInt64.ofNat input.size) (UInt64.ofNat input.size) 0 product
              1 0 0).toState)
          (afterCondition :=
            (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state
              inputPtr product element product 0 0 0 (heapTop + 48) 0 0 0
              inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
              (UInt64.ofNat input.size) (UInt64.ofNat input.size) 0 product
              1 0 0).toState)
          (result := false) (values := [])
        · simpa [accumulated, element, product,
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_bodyTransition,
            Project.ProofKit.ScalarTransition.U64Op.apply] using
            (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_body_eval
              inputPtr accumulated element temporary 0 0 0 (heapTop + 48) 0 0 0
              inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
              (UInt64.ofNat input.size) (UInt64.ofNat input.size) done staged
              releaseReady 0 0)
        · simpa [
            LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_conditionTransition] using
            (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_condition_eval
              inputPtr product element product 0 0 0 (heapTop + 48) 0 0 0
              inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
              (UInt64.ofNat input.size) (UInt64.ofNat input.size) 0 product
              1 0 0)
        · simp
        · intro _
          refine ⟨
            (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state
              inputPtr product element product 0 0 0 (heapTop + 48) 0 0 0
              inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index + 1)
              (UInt64.ofNat input.size) (UInt64.ofNat input.size) 0 product
              1 0 0).toState, ?_, ?_⟩
          · simpa [
              LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_step_continuingTransition,
              Project.ProofKit.ScalarTransition.U64Op.apply] using
              (LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_step_continuing_eval
                inputPtr product element product 0 0 0 (heapTop + 48) 0 0 0
                inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index)
                (UInt64.ofNat input.size) (UInt64.ofNat input.size) 0 product
                1 0 0)
          · have hIndexSucc :
                UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by
              apply UInt64.toNat.inj
              rw [UInt64.toNat_add, hIndexNat,
                UInt64.toNat_ofNat_of_lt' (by
                  have hSize := hArray.size_lt
                  omega)]
              have hOne : (1 : UInt64).toNat = 1 := rfl
              rw [hOne, Nat.mod_eq_of_lt]
              have hSize := hArray.size_lt
              omega
            have hIndexSuccNat : (UInt64.ofNat (index + 1)).toNat =
                index + 1 := by
              apply UInt64.toNat_ofNat_of_lt'
              have hSize := hArray.size_lt
              omega
            change
              foldInvariant input inputPtr (heapTop + 48) loopStore loopStore
                  ((LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state
                    inputPtr product element product 0 0 0 (heapTop + 48) 0 0 0
                    inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index + 1)
                    (UInt64.ofNat input.size) (UInt64.ofNat input.size) 0
                    product 1 0 0).toState.toLocals []) ∧
                foldMeasure input loopStore
                    ((LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches.function_0_array_fold_0_state
                      inputPtr product element product 0 0 0 (heapTop + 48) 0 0 0
                      inputPtr (UInt64.ofNat input.size) (UInt64.ofNat index + 1)
                      (UInt64.ofNat input.size) (UInt64.ofNat input.size) 0
                      product 1 0 0).toState.toLocals []) <
                  foldMeasure input loopStore
                    (foldFrame input inputPtr (heapTop + 48) index item temporary
                      done staged releaseReady)
            constructor
            · refine ⟨rfl, index + 1, by omega, element, product, 0,
                product, 1, ?_⟩
              have hFoldSucc :
                  Project.ProofKit.ArrayFold.foldPrefix input
                      (fun product element => product * element) 1
                      (index + 1) = product := by
                rw [Project.ProofKit.ArrayFold.foldPrefix_succ input
                  (fun product element => product * element) 1 index hIndexLt]
              unfold foldFrame
              rw [hFoldSucc, ← hIndexSucc]
              rfl
            · change input.size - (UInt64.ofNat index + 1).toNat <
                input.size - (UInt64.ofNat index).toNat
              rw [hIndexSucc, hIndexSuccNat, hIndexNat]
              omega
  case hInvalid =>
    intro hLarge
    have hFitMemory : heapTop.toNat + 48 + 8 ≤
        initial.mem.pages * 65536 := by
      simpa [FormalSpec.expected, hLarge] using hOutputFitMemory
    have hFacts := Project.ProofKit.Allocation.bumpFacts
      heapTop 8 initial.mem.pages hFitMemory hPages
    change Wasm.wp _
      (Project.ProofKit.FixedArrayCapacity.constantProgram 0 1 11 ++ _)
      _ initial branchFrame env
    apply Project.ProofKit.FixedArrayCapacity.constantProgram_spec
    · exact hBranchValues
    · simp [hBranchParams]
    · simp [Wasm.Locals.validIndex, hBranchParams, hBranchLocals]
    change Wasm.wp _
      (Project.ProofKit.FixedArrayAllocatorWindow.region 2 1 ++ _)
      _ initial _ env
    apply Project.ProofKit.FixedArrayAllocatorWindow.region_spec_withTail
      (offset := 2) (tail := 4) (heapTop := heapTop) (capacity := 8)
      (stride := 1) (allocs := allocs)
    · simp [Project.ProofKit.FixedArrayCapacity.capacityFrame, hBranchParams]
    · simp [Project.ProofKit.FixedArrayCapacity.capacityFrame, hBranchLocals]
    · rfl
    · norm_num [Project.ProofKit.FixedArrayCapacity.capacityFrame,
        Project.ProofKit.FixedArrayCapacity.normalizedCapacity,
        Project.ProofKit.FixedArrayCapacity.unnormalizedCapacity,
        hBranchParams, hBranchLocals, List.getElem?_set] <;> native_decide
    · native_decide
    · exact hFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    change Wasm.wp _
      (Project.ProofKit.FixedArrayResult.lengthStoreProgram 7 0 ++
        Project.ProofKit.FixedArrayResult.finishProgram 7 5 6)
      _ _ _ env
    apply Project.ProofKit.FixedArrayResult.lengthStore_spec
      (root := heapTop + 48)
    · rfl
    · norm_num [Wasm.Locals.get,
        Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
        Project.ProofKit.FixedArrayCapacity.capacityFrame,
        Project.ProofKit.FixedArrayCapacity.normalizedCapacity,
        Project.ProofKit.FixedArrayCapacity.unnormalizedCapacity,
        hBranchParams, hBranchLocals, List.getElem?_set]
    · have hRootAddress :
          (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
        simpa using hFacts.wordAddress_toNat 0 (by native_decide)
      rw [hRootAddress,
        Project.ProofKit.FixedArrayAllocator.allocStore_pages]
      omega
    have hRootFit32 : (heapTop + 48).toNat + 8 ≤ 4294967296 := by
      rw [hFacts.rootToNat]
      exact hFacts.fit32
    have hRootFitMemory :
        (heapTop + 48).toNat + 8 ≤
          (Project.ProofKit.FixedArrayAllocator.allocStore
            initial heapTop 8 1 allocs).mem.pages * 65536 := by
      rw [hFacts.rootToNat,
        Project.ProofKit.FixedArrayAllocator.allocStore_pages]
      exact hFitMemory
    have hOutput := Project.ProofKit.FixedArrayResult.emptyStore_at
      (Project.ProofKit.FixedArrayAllocator.allocStore
        initial heapTop 8 1 allocs) (heapTop + 48)
      hRootFit32 hRootFitMemory
    change Wasm.wp _
      (Project.ProofKit.FixedArrayResult.finishProgram 7 5 6 ++ [])
      _ _ _ env
    apply Project.ProofKit.FixedArrayResult.finishProgram_spec
      (root := heapTop + 48)
    · rfl
    · norm_num [Wasm.Locals.get,
        Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
        Project.ProofKit.FixedArrayCapacity.capacityFrame,
        Project.ProofKit.FixedArrayCapacity.normalizedCapacity,
        Project.ProofKit.FixedArrayCapacity.unnormalizedCapacity,
        hBranchParams, hBranchLocals, List.getElem?_set]
    · norm_num [Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
        Project.ProofKit.FixedArrayCapacity.capacityFrame,
        hBranchParams]
    · norm_num [Wasm.Locals.validIndex,
        Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
        Project.ProofKit.FixedArrayCapacity.capacityFrame,
        hBranchParams, hBranchLocals]
    · norm_num [Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
        Project.ProofKit.FixedArrayCapacity.capacityFrame,
        hBranchParams]
    · norm_num [Wasm.Locals.validIndex,
        Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
        Project.ProofKit.FixedArrayCapacity.capacityFrame,
        hBranchParams, hBranchLocals]
    have hNumParams : 1 ≤
        LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def.numParams := by
      native_decide
    have hOutputFormal : FormalSpec.UInt64ArrayAt
        (Project.ProofKit.FixedArrayResult.writeLength
          (Project.ProofKit.FixedArrayAllocator.allocStore
            initial heapTop 8 1 allocs) (heapTop + 48) 0)
        (heapTop + 48) #[] := by
      change UInt64Array.At _ _ _
      exact hOutput
    simpa [wp_nil, Project.ProofKit.FixedArrayEqNode.branchPost,
      artifactPost,
      Project.ProofKit.FixedArrayResult.finishFrame, wp_simp,
      Wasm.Locals.get, Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
      Project.ProofKit.FixedArrayCapacity.capacityFrame,
      Project.ProofKit.FixedArrayCapacity.normalizedCapacity,
      Project.ProofKit.FixedArrayCapacity.unnormalizedCapacity,
      hBranchParams, hBranchLocals, List.getElem?_set,
      LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def,
      FormalSpec.expected, hLarge] using And.intro hNumParams hOutputFormal

end LeanExeGen.GeneratedRa8e90ffc5781d113.Behavior
