import LeanExeGen.GeneratedRb9ad29e25c8033e5.FormalSpec
import LeanExeGen.GeneratedRb9ad29e25c8033e5.Program
import LeanExeGen.GeneratedRb9ad29e25c8033e5.AnnotationMatches
import Project.ProofKit.Annotation
import Project.ProofKit.Array
import Project.ProofKit.EncodedIndexDecoder
import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayCapacity
import Project.ProofKit.FixedArrayCopy
import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArrayFindIdxEq
import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArrayPairResult
import Project.ProofKit.FixedArrayResult

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRb9ad29e25c8033e5.Behavior

open Wasm Project.ProofKit

private theorem bounded_suffix_scalar (size index : Nat)
    (hSize : size ≤ 8) (hIndex : index < size) :
    UInt64.ofNat size - 1 - UInt64.ofNat index =
      UInt64.ofNat (size - 1 - index) := by
  interval_cases size <;>
    interval_cases index <;>
      native_decide

private theorem bounded_length_scalar (size : Nat)
    (hSize : size ≤ 8) (hPositive : 0 < size) :
    UInt64.ofNat size - 1 = UInt64.ofNat (size - 1) := by
  interval_cases size <;>
    native_decide

private theorem input_before_bump_root (inputPtr heapTop : UInt64) (size : Nat)
    (hInputBelow : inputPtr.toNat + 8 * (size + 1) ≤ heapTop.toNat)
    (hRoot : (heapTop + 48).toNat = heapTop.toNat + 48) :
    inputPtr.toNat + 8 * (size + 1) ≤ (heapTop + 48).toNat := by
  rw [hRoot]
  omega

private theorem bounded_target_fit (heapTop capacity : UInt64)
    (size bound : Nat) (hPositive : 0 < size)
    (hRoot : (heapTop + 48).toNat = heapTop.toNat + 48)
    (hCapacity : capacity.toNat = 8 * size)
    (hFit : heapTop.toNat + 48 + capacity.toNat ≤ bound) :
    (heapTop + 48).toNat + 8 * ((size - 1) + 1) ≤ bound := by
  rw [hCapacity] at hFit
  rw [hRoot]
  omega

theorem artifact_behavior :
    LeanExeGen.GeneratedRb9ad29e25c8033e5.FormalSpec.ArtifactSpec LeanExeGen.GeneratedRb9ad29e25c8033e5.«module» := by
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
    (f := LeanExeGen.GeneratedRb9ad29e25c8033e5.func0Def) rfl
  simp only [LeanExeGen.GeneratedRb9ad29e25c8033e5.func0Def,
    Wasm.Function.toLocals, Wasm.Function.numParams,
    Wasm.ValueType.zero, List.length, List.take, List.drop,
    List.map, List.reverse]
  change wp _ LeanExeGen.GeneratedRb9ad29e25c8033e5.func0 _ initial
    ({ params := [.i64 inputPtr],
       locals := List.replicate 23 (.i64 0), values := [] } : Wasm.Locals) env
  rw [LeanExeGen.GeneratedRb9ad29e25c8033e5.AnnotationMatches.function_0_length_dispatch_0_function_eq]
  wp_fixed_array_length_le_dispatch_from hArray at 8, 8
  · rfl
  · rfl
  · decide
  · change 8 < 24
    decide
  · decide
  · intro hSize
    change wp _
      (Project.ProofKit.FixedArrayFindIdxEq.program 8 0 ++ _) _ _ _ _
    apply Project.ProofKit.FixedArrayFindIdxEq.program_spec
      (tail := 12) (hInput := hArray)
    · decide
    · rfl
    · norm_num
        [Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
          LeanExeGen.GeneratedRb9ad29e25c8033e5.func0Def,
          Wasm.Function.toLocals]
    · rfl
    · intro hFind item
      have hFind' : input.findIdx? (fun element => element == (0 : UInt64)) =
          none := by
        simpa [Project.ProofKit.FixedArrayFindIdxEq.predicate] using hFind
      have hExpected : FormalSpec.expected input = input := by
        simp [FormalSpec.expected, hSize, hFind']
      rw [hExpected]
      simp (config := { maxSteps := 10000000 }) (discharger := omega)
        [wp_simp, Project.ProofKit.FixedArrayEqNode.branchPost,
          LeanExeGen.GeneratedRb9ad29e25c8033e5.AnnotationMatches.function_0_length_dispatch_0_suffix_program,
          Project.ProofKit.FixedArrayFindIdxEq.noneFrame,
          Project.ProofKit.FixedArrayFindIdxEq.loopFrame,
          Project.ProofKit.FixedArrayFindIdxEq.setupFrame,
          Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
          Wasm.Locals.get, Wasm.Locals.set?, List.getElem?_cons_zero,
          List.getElem?_cons_succ]
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      simp (config := { maxSteps := 10000000 }) (discharger := omega)
        [wp_simp, Project.ProofKit.FixedArrayEqNode.branchPost,
          LeanExeGen.GeneratedRb9ad29e25c8033e5.AnnotationMatches.function_0_length_dispatch_0_suffix_program,
          Project.ProofKit.FixedArrayFindIdxEq.noneFrame,
          Project.ProofKit.FixedArrayFindIdxEq.loopFrame,
          Project.ProofKit.FixedArrayFindIdxEq.setupFrame,
          Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
          Wasm.Locals.get, Wasm.Locals.set?, List.getElem?_cons_zero,
          List.getElem?_cons_succ, hArray]
      change UInt64Array.At initial inputPtr input
      exact hArray
    · intro index hIndex hFind
      have hEncodedBound : index + 1 < UInt64.size := by
        have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
        omega
      have hEncodedNe :=
        Project.ProofKit.FixedArrayFindIdxEq.encodedIndex_ne_zero hEncodedBound
      have hIndexToNat : (UInt64.ofNat index).toNat = index :=
        UInt64.toNat_ofNat_of_lt' (lt_trans hIndex hArray.size_lt)
      have hInputSizeToNat : (UInt64.ofNat input.size).toNat = input.size :=
        UInt64.toNat_ofNat_of_lt' hArray.size_lt
      have hIndexEncoded : UInt64.ofNat index < UInt64.ofNat input.size := by
        rw [UInt64.lt_iff_toNat_lt, hIndexToNat, hInputSizeToNat]
        exact hIndex
      have hLengthBound' : inputPtr.toUInt32.toNat + 8 ≤
          initial.mem.pages * 65536 := by
        simpa [Project.ProofKit.Memory.toUInt32_toNat] using hLengthBound
      simp (config := { maxSteps := 10000000 }) (discharger := omega)
        [wp_simp, Project.ProofKit.FixedArrayFindIdxEq.someFrame,
          Project.ProofKit.FixedArrayFindIdxEq.loopFrame,
          Project.ProofKit.FixedArrayFindIdxEq.setupFrame,
          Project.ProofKit.FixedArrayLengthDispatch.branchFrame,
          Wasm.Locals.get, Wasm.Locals.set?, List.getElem?_cons_zero,
          List.getElem?_cons_succ, hEncodedNe]
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      rw [wp_localGet_cons]
      simp only [Wasm.Locals.get, List.length, Nat.reduceAdd, Nat.reduceLT, if_true,
        List.getElem?_cons_zero]
      rw [wp_localSet_cons]
      simp only [Wasm.Locals.set?, List.length, Nat.reduceAdd, Nat.reduceLT,
        Nat.reduceSub, if_true, if_false, List.set]
      change wp _
        (Project.ProofKit.EncodedIndexDecoder.program 2 8 4 ++ _) _ _ _ _
      apply Project.ProofKit.EncodedIndexDecoder.program_spec
        (encoded := Project.ProofKit.FixedArrayFindIdxEq.encodedIndex index)
      · rfl
      · simp
      · simp [Wasm.Locals.validIndex]
      · simp
      · simp [Wasm.Locals.validIndex]
      · rw [wp_localGet_cons]
        rw [Project.ProofKit.EncodedIndexDecoder.resultFrame_decoded _ 8 4 _
          (by simp) (by simp [Wasm.Locals.validIndex])]
        rw [if_neg hEncodedNe,
          Project.ProofKit.FixedArrayFindIdxEq.encodedIndex_sub_one]
        simp only
        rw [wp_localGet_cons]
        simp only [Project.ProofKit.EncodedIndexDecoder.resultFrame, hEncodedNe,
          Wasm.Locals.get, List.length, List.length_set, Nat.reduceAdd,
          Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, if_true, if_false,
          List.getElem?_set,
          List.getElem?_cons_zero, List.getElem?_cons_succ]
        wp_alloc_to_store_lists []
        simp only [wp_load64_cons]
        have hTwo32 : 2 ^ 32 = 4294967296 := by norm_num
        rw [hTwo32, hInputAddress]
        simp only [UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero]
        rw [if_neg (Nat.not_lt.mpr hLengthBound'), hLengthRead]
        rw [wp_ltUI64_cons]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp [hIndexEncoded])]
        wp_alloc_to_store_lists []
        simp only [wp_load64_cons]
        rw [hTwo32, hInputAddress]
        simp only [UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero]
        rw [if_neg (Nat.not_lt.mpr hLengthBound'), hLengthRead]
        wp_alloc_to_store_lists []
        rw [wp_ltUI64_cons]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp [hIndexEncoded])]
        wp_alloc_window_lists [hIndexToNat, hInputSizeToNat]
        let capacity : UInt64 :=
          (8 + (UInt64.ofNat input.size - 1) * 8 + 7) / 8 * 8
        have hPositive : 0 < input.size := by omega
        have hFindFormal :
            input.findIdx? (fun element => element == (0 : UInt64)) =
              some index := by
          change input.findIdx?
            (Project.ProofKit.FixedArrayFindIdxEq.predicate 0) = some index
          exact hFind
        have hCapacityNotSmall : ¬capacity < 8 := by
          dsimp [capacity]
          interval_cases hInputSize : input.size <;>
            native_decide
        have hCapacityNat : capacity.toNat = 8 * input.size := by
          dsimp [capacity]
          interval_cases hInputSize : input.size <;>
            native_decide
        have hCapacityLower : 8 ≤ capacity.toNat := by
          rw [hCapacityNat]
          omega
        have hCapacityFit : heapTop.toNat + 48 + capacity.toNat ≤
            initial.mem.pages * 65536 := by
          rw [hCapacityNat]
          simpa [FormalSpec.heapReserveBytes, hSize, hFindFormal,
            Nat.add_assoc] using hHeapFitMemory
        apply wp_iff_cons
        · rfl
        rw [if_neg hCapacityNotSmall]
        rw [if_neg (by simp)]
        rw [wp_nil]
        apply Project.ProofKit.FixedArrayAllocatorWindow.region_spec_withTail
          (offset := 9) (tail := 0) (heapTop := heapTop)
          (capacity := capacity) (stride := 1) (allocs := allocs)
          (rest :=
            Project.ProofKit.FixedArrayResult.lengthStoreLocalProgram 14 13 ++
              (Project.ProofKit.FixedArrayCopy.program 1 8 14 11 12 15 ++
                [Wasm.Instruction.localGet 14]))
        · simp
        · simp
        · rfl
        · rfl
        · exact hCapacityLower
        · exact hCapacityFit
        · exact hPages
        · rfl
        · exact hHeapTop
        · exact hFreeList
        · exact hAllocs
        · apply Project.ProofKit.FixedArrayResult.lengthStoreLocal_spec
            (module_ := module) (env := env) (root := heapTop + 48)
            (length := UInt64.ofNat input.size - 1)
            (rootLocal := 14) (lengthLocal := 13)
            (rest := Project.ProofKit.FixedArrayCopy.program
              1 8 14 11 12 15 ++ [Wasm.Instruction.localGet 14])
          · apply Project.ProofKit.FixedArrayAllocatorWindow.allocFrame_get_root
              (offset := 9) (tail := 0)
            · simp
            · simp
          · simp (config := { maxSteps := 10000000 })
              [Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
                Wasm.Locals.get, List.getElem?_set]
          · rw [Project.ProofKit.FixedArrayAllocator.allocStore_pages,
              show (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 by
                simpa using
                  (Project.ProofKit.Allocation.bumpFacts heapTop capacity
                    initial.mem.pages hCapacityFit hPages).wordAddress_toNat
                      0 (by omega)]
            omega
          · apply Project.ProofKit.FixedArrayCopy.eraseIdxProgram_spec
              (sourceLocal := 8) (targetLocal := 14) (prefixLocal := 11)
              (suffixLocal := 12) (counterLocal := 15)
              (sourcePtr := inputPtr) (targetPtr := heapTop + 48)
              (input := input) (erase := index)
              (hErase := hIndex)
              (hCounter := by
                simp [Wasm.Locals.validIndex,
                  Project.ProofKit.FixedArrayAllocatorWindow.allocFrame])
              (rest := [Wasm.Instruction.localGet 14])
            · decide
            · decide
            · decide
            · decide
            · simp [Project.ProofKit.FixedArrayAllocatorWindow.allocFrame]
            · simp (config := { maxSteps := 10000000 })
                [Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
                  Wasm.Locals.get]
            · simp (config := { maxSteps := 10000000 })
                [Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
                  Wasm.Locals.get]
            · simp (config := { maxSteps := 10000000 })
                [Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
                  Wasm.Locals.get]
            · simp (config := { maxSteps := 10000000 })
                [Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
                  Wasm.Locals.get,
                  bounded_suffix_scalar input.size index hSize hIndex]
            · exact bounded_target_fit heapTop capacity input.size 4294967296
                hPositive
                (Project.ProofKit.Allocation.bumpFacts heapTop capacity
                  initial.mem.pages hCapacityFit hPages).rootToNat
                hCapacityNat (by
                  rw [hCapacityNat]
                  simpa [FormalSpec.heapReserveBytes, hSize, hFindFormal,
                    Nat.add_assoc] using hHeapFit32)
            · rw [Project.ProofKit.FixedArrayResult.writeLength_pages,
                Project.ProofKit.FixedArrayAllocator.allocStore_pages]
              exact bounded_target_fit heapTop capacity input.size
                (initial.mem.pages * 65536) hPositive
                (Project.ProofKit.Allocation.bumpFacts heapTop capacity
                  initial.mem.pages hCapacityFit hPages).rootToNat
                hCapacityNat hCapacityFit
            · unfold Project.ProofKit.FixedArrayResult.writeLength
              rw [bounded_length_scalar input.size hSize hPositive]
              apply Wasm.Mem.read64_write64_same
            · exact input_before_bump_root inputPtr heapTop input.size
                hInputBelow
                (Project.ProofKit.Allocation.bumpFacts heapTop capacity
                  initial.mem.pages hCapacityFit hPages).rootToNat
            · intro final hResult
              simp only [wp_localGet_cons]
              rw [Project.ProofKit.FixedArrayCopy.counterFrame_get_ne
                (hNe := by decide)]
              simp (config := { maxSteps := 10000000 }) (discharger := omega)
                [wp_simp,
                  Project.ProofKit.FixedArrayCopy.counterFrame,
                  Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
                  Wasm.Locals.get, Wasm.Locals.set?]
              simp only [Project.ProofKit.FixedArrayEqNode.branchPost]
              simp (config := { maxSteps := 10000000 }) (discharger := omega)
                [wp_simp,
                  LeanExeGen.GeneratedRb9ad29e25c8033e5.AnnotationMatches.function_0_length_dispatch_0_suffix_program,
                  Project.ProofKit.FixedArrayCopy.counterFrame,
                  Project.ProofKit.FixedArrayAllocatorWindow.allocFrame,
                  Wasm.Locals.get, Wasm.Locals.set?, FormalSpec.expected,
                  hSize, hFindFormal]
              simp only [List.getElem?_cons_zero]
              exact ⟨heapTop + 48, rfl, hResult⟩
            · exact
                (Project.ProofKit.FixedArrayPairResult.input_preserved_by_alloc
                  initial heapTop capacity 1 allocs inputPtr input hArray
                  hInputBelow hCapacityFit hPages).write64After
                    (address := (heapTop + 48).toUInt32)
                    (value := UInt64.ofNat input.size - 1) (by
                      rw [show (heapTop + 48).toUInt32.toNat =
                          heapTop.toNat + 48 by
                        simpa using
                          (Project.ProofKit.Allocation.bumpFacts heapTop capacity
                            initial.mem.pages hCapacityFit hPages).wordAddress_toNat
                              0 (by omega)]
                      omega)
  · intro hSize
    have hExpected : FormalSpec.expected input = #[] := by
      simp [FormalSpec.expected, hSize]
    have hCapacity :
        Project.ProofKit.FixedArrayCapacity.normalizedCapacity 0 1 = 8 := by
      native_decide
    have hCapacityFit : heapTop.toNat + 48 +
        (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 0 1).toNat ≤
          initial.mem.pages * 65536 := by
      rw [hCapacity]
      simpa [FormalSpec.heapReserveBytes, hSize, Nat.add_assoc] using
        hHeapFitMemory
    change wp _
      (Project.ProofKit.FixedArrayCapacity.constantProgram 0 1 12 ++
        (Project.ProofKit.FixedArrayAllocatorWindow.region 3 1 ++ _))
      _ _ _ _
    apply
      Project.ProofKit.FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail
        (length := 0) (stride := 1) (offset := 3) (tail := 6)
        (heapTop := heapTop) (allocs := allocs)
    · rfl
    · simp [Project.ProofKit.FixedArrayLengthDispatch.branchFrame]
    · rfl
    · exact hCapacityFit
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · have hBumpFacts := Project.ProofKit.Allocation.bumpFacts heapTop
          (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 0 1)
          initial.mem.pages hCapacityFit hPages
      have hRootAddressNat : (heapTop + 48).toUInt32.toNat =
          heapTop.toNat + 48 := by
        simpa using hBumpFacts.wordAddress_toNat 0 (by
          rw [hCapacity]
          decide)
      have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
          (Project.ProofKit.FixedArrayAllocator.allocStore initial heapTop
            (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 0 1)
            1 allocs).mem.pages * 65536 := by
        rw [Project.ProofKit.FixedArrayAllocator.allocStore_pages,
          hRootAddressNat]
        rw [hCapacity] at hCapacityFit
        omega
      have hRootFit32 : (heapTop + 48).toNat + 8 ≤ 4294967296 := by
        rw [hBumpFacts.rootToNat]
        simpa [FormalSpec.heapReserveBytes, hSize, Nat.add_assoc] using
          hHeapFit32
      have hRootFitMemory : (heapTop + 48).toNat + 8 ≤
          (Project.ProofKit.FixedArrayAllocator.allocStore initial heapTop
            (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 0 1)
            1 allocs).mem.pages * 65536 := by
        rw [Project.ProofKit.FixedArrayAllocator.allocStore_pages,
          hBumpFacts.rootToNat]
        simpa [FormalSpec.heapReserveBytes, hSize, Nat.add_assoc] using
          hHeapFitMemory
      have hRoot :
          (Project.ProofKit.FixedArrayAllocatorWindow.allocFrame 3
            (Project.ProofKit.FixedArrayCapacity.capacityFrame
              (Project.ProofKit.FixedArrayLengthDispatch.branchFrame 8
                { params := [.i64 inputPtr],
                  locals := List.replicate 23 (.i64 0) }
                inputPtr)
              12
              (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 0 1))
            heapTop
            (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 0 1)).get
              8 = some (.i64 (heapTop + 48)) := by
        exact Project.ProofKit.FixedArrayAllocatorWindow.allocFrame_get_root
          3 6 _ heapTop _ (by rfl) (by
            rw [
              Project.ProofKit.FixedArrayCapacity.capacityFrame_locals_length,
              Project.ProofKit.FixedArrayLengthDispatch.branchFrame_locals_length]
            simp)
      have hFrameParams :
          (Project.ProofKit.FixedArrayAllocatorWindow.allocFrame 3
            (Project.ProofKit.FixedArrayCapacity.capacityFrame
              (Project.ProofKit.FixedArrayLengthDispatch.branchFrame 8
                { params := [.i64 inputPtr],
                  locals := List.replicate 23 (.i64 0) }
                inputPtr)
              12
              (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 0 1))
            heapTop
            (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 0 1)).params.length =
              1 := by
        rfl
      have hFrameLocals :
          (Project.ProofKit.FixedArrayAllocatorWindow.allocFrame 3
            (Project.ProofKit.FixedArrayCapacity.capacityFrame
              (Project.ProofKit.FixedArrayLengthDispatch.branchFrame 8
                { params := [.i64 inputPtr],
                  locals := List.replicate 23 (.i64 0) }
                inputPtr)
              12
              (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 0 1))
            heapTop
            (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 0 1)).locals.length =
              23 := by
        rw [
          Project.ProofKit.FixedArrayAllocatorWindow.allocFrame_locals_length,
          Project.ProofKit.FixedArrayCapacity.capacityFrame_locals_length,
          Project.ProofKit.FixedArrayLengthDispatch.branchFrame_locals_length]
        simp
      change wp _
        (Project.ProofKit.FixedArrayResult.lengthStoreProgram 8 0 ++ _)
        _ _ _ _
      apply Project.ProofKit.FixedArrayResult.lengthStore_spec
        (root := heapTop + 48) (length := 0) (rootLocal := 8)
      · rfl
      · exact hRoot
      · exact hRootBound
      · change wp _
          (Project.ProofKit.FixedArrayResult.finishProgram 8 6 7 ++ _)
          _ _ _ _
        apply Project.ProofKit.FixedArrayResult.finishProgram_spec
          (root := heapTop + 48) (rootLocal := 8)
          (destinationLocal := 6) (returnLocal := 7)
        · rfl
        · exact hRoot
        · rw [hFrameParams]
          decide
        · simp only [Wasm.Locals.validIndex, hFrameParams, hFrameLocals]
          decide
        · rw [hFrameParams]
          decide
        · simp only [Wasm.Locals.validIndex, hFrameParams, hFrameLocals]
          decide
        · have hEmpty := Project.ProofKit.FixedArrayResult.emptyStore_at
              (Project.ProofKit.FixedArrayAllocator.allocStore initial heapTop
                (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 0 1)
                1 allocs)
              (heapTop + 48) hRootFit32 hRootFitMemory
          rw [wp_nil]
          simp only [Project.ProofKit.FixedArrayEqNode.branchPost]
          simp only [
            LeanExeGen.GeneratedRb9ad29e25c8033e5.AnnotationMatches.function_0_length_dispatch_0_suffix_program]
          rw [wp_localGet_cons]
          have hReturnGet :
              ({ Project.ProofKit.FixedArrayResult.finishFrame
                  (Project.ProofKit.FixedArrayAllocatorWindow.allocFrame 3
                    (Project.ProofKit.FixedArrayCapacity.capacityFrame
                      (Project.ProofKit.FixedArrayLengthDispatch.branchFrame 8
                        { params := [.i64 inputPtr],
                          locals := List.replicate 23 (.i64 0) }
                        inputPtr)
                      12
                      (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 0 1))
                    heapTop
                    (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 0 1))
                  6 7 (heapTop + 48) with values := [] } : Wasm.Locals).get 7 =
                some (.i64 (heapTop + 48)) := by
            simpa only [Wasm.Locals.get] using
              (Project.ProofKit.FixedArrayResult.finishFrame_return_get
                (Project.ProofKit.FixedArrayAllocatorWindow.allocFrame 3
                  (Project.ProofKit.FixedArrayCapacity.capacityFrame
                    (Project.ProofKit.FixedArrayLengthDispatch.branchFrame 8
                      { params := [.i64 inputPtr],
                        locals := List.replicate 23 (.i64 0) }
                      inputPtr)
                    12
                    (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 0 1))
                  heapTop
                  (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 0 1))
                6 7 (heapTop + 48) (by rw [hFrameParams]; decide)
                (by
                  simp only [Wasm.Locals.validIndex, hFrameParams,
                    hFrameLocals]
                  decide))
          rw [hReturnGet]
          simp only
          rw [wp_nil]
          have hEmptyFormal : FormalSpec.UInt64ArrayAt
              (Project.ProofKit.FixedArrayResult.writeLength
                (Project.ProofKit.FixedArrayAllocator.allocStore initial heapTop
                  (Project.ProofKit.FixedArrayCapacity.normalizedCapacity 0 1)
                  1 allocs)
                (heapTop + 48) 0)
              (heapTop + 48) #[] := by
            rcases hEmpty with ⟨hFit32, hFitMemory, hLength, hElements⟩
            exact ⟨hFit32, hFitMemory, hLength, hElements⟩
          refine ⟨heapTop + 48, by simp, ?_⟩
          simpa only [hExpected] using hEmptyFormal

end LeanExeGen.GeneratedRb9ad29e25c8033e5.Behavior
