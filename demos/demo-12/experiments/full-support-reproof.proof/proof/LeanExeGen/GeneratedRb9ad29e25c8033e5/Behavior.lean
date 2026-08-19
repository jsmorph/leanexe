import LeanExeGen.GeneratedRb9ad29e25c8033e5.FormalSpec
import LeanExeGen.GeneratedRb9ad29e25c8033e5.Program
import LeanExeGen.GeneratedRb9ad29e25c8033e5.AnnotationMatches
import Project.ProofKit.Annotation
import Project.ProofKit.Allocation
import Project.ProofKit.Array
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

theorem lengthStoreLocal_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (root length : UInt64)
    (rootLocal lengthLocal : Nat)
    (hRoot : frame.get rootLocal = some (.i64 root))
    (hLength : frame.get lengthLocal = some (.i64 length))
    (hBound : root.toUInt32.toNat + 8 ≤ st.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q
      (FixedArrayResult.writeLength st root length) frame env) :
    wp module_
      ([.localGet rootLocal, .wrapI64, .localGet lengthLocal, .store64 0] ++
        rest) Q st frame env := by
  have hLengthAfter (values : List Value) :
      ({ frame with values := values } : Locals).get lengthLocal =
        some (.i64 length) := by
    simpa only [Wasm.Locals.get] using hLength
  simp only [List.cons_append, List.nil_append]
  simp only [wp_localGet_cons, hRoot, wp_wrapI64_cons, hLengthAfter,
    wp_store64_cons]
  have hTwo32 : 2 ^ 32 = 4294967296 := by norm_num
  rw [hTwo32, ← Memory.toUInt32_eq_ofNat]
  simp only [UInt32.toNat_zero, add_zero]
  rw [if_neg (Nat.not_lt.mpr hBound)]
  cases frame
  simp_all [FixedArrayResult.writeLength]

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
  change Wasm.wp _ LeanExeGen.GeneratedRb9ad29e25c8033e5.func0 _ _ _ _
  rw [LeanExeGen.GeneratedRb9ad29e25c8033e5.AnnotationMatches.function_0_length_dispatch_0_function_eq]
  wp_fixed_array_length_le_dispatch_from hArray at 8, 8
  all_goals try rfl
  all_goals try decide
  · simp [LeanExeGen.GeneratedRb9ad29e25c8033e5.func0Def,
      Wasm.Function.toLocals, Wasm.Function.numParams, Wasm.ValueType.zero]
  · intro hSize
    change wp LeanExeGen.GeneratedRb9ad29e25c8033e5.«module»
      (FixedArrayFindIdxEq.program 8 0 ++ _) _ initial _ env
    apply FixedArrayFindIdxEq.program_spec
      (scratch := 8) (tail := 12) (key := 0)
      (inputPtr := inputPtr) (input := input) (hInput := hArray)
    · decide
    · rfl
    · simp only [FixedArrayLengthDispatch.branchFrame_locals_length]
      simp [LeanExeGen.GeneratedRb9ad29e25c8033e5.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams, Wasm.ValueType.zero]
    · exact FixedArrayLengthDispatch.branchFrame_values _ _ _
    · intro hFind item
      have hFind' :
          input.findIdx? (fun element => element == (0 : UInt64)) = none := by
        simpa [FixedArrayFindIdxEq.predicate] using hFind
      have hExpected : FormalSpec.expected input = input := by
        simp [FormalSpec.expected, hSize, hFind']
      simp (config := { maxSteps := 10000000 }) (discharger := omega)
        [wp_simp, FixedArrayFindIdxEq.noneFrame,
          FixedArrayFindIdxEq.loopFrame, FixedArrayFindIdxEq.setupFrame,
          FixedArrayLengthDispatch.branchFrame, Wasm.Locals.get,
          Wasm.Locals.set?, List.getElem?_cons_zero,
          LeanExeGen.GeneratedRb9ad29e25c8033e5.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero, FixedArrayEqNode.branchPost,
          LeanExeGen.GeneratedRb9ad29e25c8033e5.AnnotationMatches.function_0_length_dispatch_0_suffix_program,
          hExpected, hArray]
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      simp (config := { maxSteps := 10000000 }) (discharger := omega)
        [wp_simp, Wasm.Locals.get, Wasm.Locals.set?,
          List.getElem?_cons_zero, FixedArrayEqNode.branchPost,
          LeanExeGen.GeneratedRb9ad29e25c8033e5.AnnotationMatches.function_0_length_dispatch_0_suffix_program,
          LeanExeGen.GeneratedRb9ad29e25c8033e5.func0Def,
          hExpected, hArray]
      change UInt64Array.At initial inputPtr input
      exact hArray
    · intro index hIndex hFind
      have hFindSpec :
          input.findIdx? (fun element => element == (0 : UInt64)) =
            some index := by
        have hFindSpec := hFind
        change input.findIdx? (fun element => element == (0 : UInt64)) =
          some index at hFindSpec
        exact hFindSpec
      have hExpected : FormalSpec.expected input = input.eraseIdx! index := by
        simp [FormalSpec.expected, hSize, hFindSpec]
      let searchFrame := FixedArrayFindIdxEq.someFrame 8
        (FixedArrayLengthDispatch.branchFrame 8
          (LeanExeGen.GeneratedRb9ad29e25c8033e5.func0Def.toLocals
            (List.take
              LeanExeGen.GeneratedRb9ad29e25c8033e5.func0Def.numParams
              [.i64 inputPtr]).reverse)
          inputPtr)
        inputPtr input index
      change wp LeanExeGen.GeneratedRb9ad29e25c8033e5.«module» _ _ initial
        searchFrame env
      have hSearchParams : searchFrame.params = [.i64 inputPtr] := by
        simp only [searchFrame, FixedArrayFindIdxEq.someFrame_params,
          FixedArrayLengthDispatch.branchFrame_params]
        rfl
      have hSearchLocals : searchFrame.locals.length = 23 := by
        simp only [searchFrame, FixedArrayFindIdxEq.someFrame_locals_length,
          FixedArrayLengthDispatch.branchFrame_locals_length]
        simp [LeanExeGen.GeneratedRb9ad29e25c8033e5.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      have hSearchValues : searchFrame.values =
          [.i64 (FixedArrayFindIdxEq.encodedIndex index)] := by
        exact FixedArrayFindIdxEq.someFrame_values _ _ _ _ _
      have hIndexSucc : index + 1 < UInt64.size := by
        have hInputSize := hArray.size_lt
        omega
      have hEncodedNe : FixedArrayFindIdxEq.encodedIndex index ≠ 0 :=
        FixedArrayFindIdxEq.encodedIndex_ne_zero hIndexSucc
      have hEncodedNotLt :
          ¬FixedArrayFindIdxEq.encodedIndex index < (1 : UInt64) := by
        rw [FixedArrayFindIdxEq.encodedIndex_eq_ofNat_succ hIndexSucc,
          UInt64.lt_iff_toNat_lt,
          UInt64.toNat_ofNat_of_lt' hIndexSucc]
        have hOne : (1 : UInt64).toNat = 1 := rfl
        rw [hOne]
        omega
      have hIndexLt64 : index < UInt64.size := by
        omega
      have hIndexEncodedLt :
          UInt64.ofNat index < UInt64.ofNat input.size := by
        rw [UInt64.lt_iff_toNat_lt,
          UInt64.toNat_ofNat_of_lt' hIndexLt64,
          UInt64.toNat_ofNat_of_lt' hArray.size_lt]
        exact hIndex
      simp (config := { maxSteps := 10000000 }) (discharger := omega)
        [wp_simp, Wasm.Locals.get, Wasm.Locals.set?,
          List.length_set, List.getElem?_set, hSearchParams,
          hSearchLocals, hSearchValues, hEncodedNe]
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      simp (config := { maxSteps := 10000000 }) (discharger := omega)
        [wp_simp, Wasm.Locals.get, Wasm.Locals.set?,
          List.length_set, List.getElem?_set, List.getElem?_cons_zero,
          hSearchParams,
          hSearchLocals, hEncodedNe]
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      simp (config := { maxSteps := 10000000 }) (discharger := omega)
        [wp_simp, Wasm.Locals.get, Wasm.Locals.set?,
          List.length_set, List.getElem?_set, hSearchLocals,
          hEncodedNotLt]
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      simp (config := { maxSteps := 10000000 }) (discharger := omega)
        [wp_simp, Wasm.Locals.get, Wasm.Locals.set?,
          List.length_set, List.getElem?_set,
          FixedArrayFindIdxEq.encodedIndex_sub_one, hSearchLocals,
          hLengthBound, hInputAddress, hLengthRead, hIndexEncodedLt]
      rw [if_neg (Nat.not_lt.mpr hLengthBound)]
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simpa using hIndexEncodedLt)]
      simp (config := { maxSteps := 10000000 }) (discharger := omega)
        [wp_simp, Wasm.Locals.get, Wasm.Locals.set?,
          List.length_set, List.getElem?_set, hSearchLocals,
          hIndexEncodedLt]
      rw [if_neg (Nat.not_lt.mpr hLengthBound)]
      rw [hInputAddress, hLengthRead]
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simpa using hIndexEncodedLt)]
      simp (config := { maxSteps := 10000000 }) (discharger := omega)
        [wp_simp, Wasm.Locals.get, Wasm.Locals.set?,
          List.length_set, List.getElem?_set, hSearchLocals]
      have hInputPos : 0 < input.size := by omega
      have hOneToNat : (1 : UInt64).toNat = 1 := rfl
      have hSevenToNat : (7 : UInt64).toNat = 7 := rfl
      have hEightToNat : (8 : UInt64).toNat = 8 := rfl
      have hResultLengthNat :
          (UInt64.ofNat input.size - 1).toNat = input.size - 1 := by
        calc
          (UInt64.ofNat input.size - 1).toNat =
              (UInt64.ofNat input.size).toNat - (1 : UInt64).toNat :=
            Memory.toNat_sub_of_le _ _ (by
              rw [UInt64.toNat_ofNat_of_lt' hArray.size_lt]
              rw [hOneToNat]
              omega)
          _ = input.size - 1 := by
            rw [UInt64.toNat_ofNat_of_lt' hArray.size_lt, hOneToNat]
      have hCapacityNat :
          ((8 + (UInt64.ofNat input.size - 1) * 8 + 7) / 8 * 8).toNat =
            8 * input.size := by
        interval_cases hInputSize : input.size <;>
          norm_num [hInputSize, hResultLengthNat, hSevenToNat, hEightToNat]
      have hCapacityNotSmall :
          ¬(8 + (UInt64.ofNat input.size - 1) * 8 + 7) / 8 * 8 <
            (8 : UInt64) := by
        rw [UInt64.lt_iff_toNat_lt, hCapacityNat]
        change ¬8 * input.size < 8
        omega
      let capacity : UInt64 :=
        (8 + (UInt64.ofNat input.size - 1) * 8 + 7) / 8 * 8
      let preAllocFrame : Locals :=
        { params := [.i64 inputPtr]
          locals :=
            (((((((((((searchFrame.locals.set 1
              (.i64 (FixedArrayFindIdxEq.encodedIndex index))).set 2
              (.i64 inputPtr)).set 7
              (.i64 (FixedArrayFindIdxEq.encodedIndex index))).set 8
              (.i64 1)).set 3 (.i64 (UInt64.ofNat index))).set 7
              (.i64 inputPtr)).set 8 (.i64 (UInt64.ofNat index))).set 9
              (.i64 (UInt64.ofNat input.size))).set 12
              (.i64 (UInt64.ofNat input.size - 1))).set 10
              (.i64 (UInt64.ofNat index))).set 11
              (.i64 (UInt64.ofNat input.size - 1 - UInt64.ofNat index))).set
              17 (.i64 capacity)
          values := [] }
      have hPreParams : preAllocFrame.params.length = 1 := by rfl
      have hPreLocals : preAllocFrame.locals.length = 23 := by
        simp [preAllocFrame, hSearchLocals]
      have hPreValues : preAllocFrame.values = [] := rfl
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp [hCapacityNotSmall])]
      rw [wp_nil]
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      change wp LeanExeGen.GeneratedRb9ad29e25c8033e5.«module»
        (FixedArrayAllocatorWindow.region 9 1 ++ _) _ initial preAllocFrame env
      apply FixedArrayAllocatorWindow.region_spec_withTail
        (offset := 9) (tail := 0) (frame := preAllocFrame)
        (heapTop := heapTop) (capacity := capacity)
        (stride := 1) (allocs := allocs)
      · exact hPreParams
      · simpa using hPreLocals
      · exact hPreValues
      · simp [preAllocFrame, capacity, hSearchLocals]
      · change 8 ≤ capacity.toNat
        rw [show capacity.toNat = 8 * input.size by
          simpa [capacity] using hCapacityNat]
        omega
      · change heapTop.toNat + 48 + capacity.toNat ≤
          initial.mem.pages * 65536
        rw [show capacity.toNat = 8 * input.size by
          simpa [capacity] using hCapacityNat]
        simpa [FormalSpec.heapReserveBytes, hSize, hFindSpec,
          Nat.add_assoc] using hHeapFitMemory
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · let allocSt := FixedArrayAllocator.allocStore initial heapTop
          capacity 1 allocs
        let allocFrame := FixedArrayAllocatorWindow.allocFrame 9
          preAllocFrame heapTop capacity
        change wp LeanExeGen.GeneratedRb9ad29e25c8033e5.«module» _ _
          allocSt allocFrame env
        have hCapacityToNat : capacity.toNat = 8 * input.size := by
          simpa [capacity] using hCapacityNat
        have hFitCapacity : heapTop.toNat + 48 + capacity.toNat ≤
            initial.mem.pages * 65536 := by
          rw [hCapacityToNat]
          simpa [FormalSpec.heapReserveBytes, hSize, hFindSpec,
            Nat.add_assoc] using hHeapFitMemory
        have hFacts := Allocation.bumpFacts heapTop capacity
          initial.mem.pages hFitCapacity hPages
        have hAllocParams : allocFrame.params.length = 1 := by
          simpa only [allocFrame,
            FixedArrayAllocatorWindow.allocFrame_params] using hPreParams
        have hAllocLocals : allocFrame.locals.length = 23 := by
          simpa only [allocFrame,
            FixedArrayAllocatorWindow.allocFrame_locals_length] using
              hPreLocals
        have hAllocValues : allocFrame.values = [] := by
          simpa only [allocFrame,
            FixedArrayAllocatorWindow.allocFrame_values] using hPreValues
        have hRoot : allocFrame.get 14 =
            some (.i64 (heapTop + 48)) := by
          unfold allocFrame
          apply FixedArrayAllocatorWindow.allocFrame_get_root
            (offset := 9) (tail := 0)
          · exact hPreParams
          · simpa using hPreLocals
        have hRootAddress :
            (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
          simpa using hFacts.wordAddress_toNat 0 (by
            rw [hCapacityToNat]
            omega)
        have hResultLengthU :
            UInt64.ofNat input.size - 1 =
              UInt64.ofNat (input.size - 1) := by
          have hResultSizeLt : input.size - 1 < UInt64.size := by
            rw [show UInt64.size = 18446744073709551616 by rfl]
            omega
          apply UInt64.toNat.inj
          rw [hResultLengthNat,
            UInt64.toNat_ofNat_of_lt' hResultSizeLt]
        have hResultLengthLocal : allocFrame.get 13 =
            some (.i64 (UInt64.ofNat (input.size - 1))) := by
          simp [allocFrame, FixedArrayAllocatorWindow.allocFrame,
            preAllocFrame, Wasm.Locals.get, hSearchLocals,
            hResultLengthU]
        change wp LeanExeGen.GeneratedRb9ad29e25c8033e5.«module»
          ([.localGet 14, .wrapI64, .localGet 13, .store64 0] ++
            (FixedArrayCopy.program 1 8 14 11 12 15 ++ [.localGet 14]))
          _ allocSt allocFrame env
        apply lengthStoreLocal_spec
          (root := heapTop + 48)
          (length := UInt64.ofNat (input.size - 1))
          (rootLocal := 14) (lengthLocal := 13)
        · exact hRoot
        · exact hResultLengthLocal
        · rw [hRootAddress, FixedArrayAllocator.allocStore_pages]
          rw [hCapacityToNat] at hFitCapacity
          omega
        · change wp LeanExeGen.GeneratedRb9ad29e25c8033e5.«module»
            (FixedArrayCopy.program 1 8 14 11 12 15 ++ [.localGet 14])
            _ _ allocFrame env
          let copySt := FixedArrayResult.writeLength allocSt
            (heapTop + 48) (UInt64.ofNat (input.size - 1))
          change wp LeanExeGen.GeneratedRb9ad29e25c8033e5.«module»
            (FixedArrayCopy.program 1 8 14 11 12 15 ++ [.localGet 14])
            _ copySt allocFrame env
          have hInputAlloc := FixedArrayPairResult.input_preserved_by_alloc
            initial heapTop capacity 1 allocs inputPtr input hArray
              hInputBelow hFitCapacity hPages
          have hSourceCopy : UInt64Array.At copySt inputPtr input := by
            unfold copySt FixedArrayResult.writeLength
            apply UInt64Array.At.write64After
              (address := (heapTop + 48).toUInt32)
              (value := UInt64.ofNat (input.size - 1))
            · rw [hRootAddress]
              omega
            · exact hInputAlloc
          have hSourceLocal : allocFrame.get 8 =
              some (.i64 inputPtr) := by
            simp [allocFrame, FixedArrayAllocatorWindow.allocFrame,
              preAllocFrame, Wasm.Locals.get, hSearchLocals]
          have hPrefixLocal : allocFrame.get 11 =
              some (.i64 (UInt64.ofNat index)) := by
            simp [allocFrame, FixedArrayAllocatorWindow.allocFrame,
              preAllocFrame, Wasm.Locals.get, hSearchLocals]
          have hResultSizeLt : input.size - 1 < UInt64.size := by
            rw [show UInt64.size = 18446744073709551616 by rfl]
            omega
          have hIndexLeResult :
              UInt64.ofNat index ≤ UInt64.ofNat (input.size - 1) := by
            rw [UInt64.le_iff_toNat_le,
              UInt64.toNat_ofNat_of_lt' hIndexLt64,
              UInt64.toNat_ofNat_of_lt' hResultSizeLt]
            omega
          have hSuffixSizeLt : input.size - 1 - index < UInt64.size := by
            omega
          have hSuffixLengthU :
              UInt64.ofNat input.size - 1 - UInt64.ofNat index =
                UInt64.ofNat (input.size - 1 - index) := by
            rw [hResultLengthU]
            apply UInt64.toNat.inj
            rw [Memory.toNat_sub_of_le _ _ hIndexLeResult,
              UInt64.toNat_ofNat_of_lt' hResultSizeLt,
              UInt64.toNat_ofNat_of_lt' hIndexLt64,
              UInt64.toNat_ofNat_of_lt' hSuffixSizeLt]
          have hSuffixLocal : allocFrame.get 12 =
              some (.i64 (UInt64.ofNat (input.size - 1 - index))) := by
            simp [allocFrame, FixedArrayAllocatorWindow.allocFrame,
              preAllocFrame, Wasm.Locals.get, hSearchLocals,
              hSuffixLengthU]
          have hCounter : allocFrame.validIndex 15 := by
            simp only [Wasm.Locals.validIndex, hAllocParams, hAllocLocals]
            omega
          have hResultWords : (input.size - 1) + 1 = input.size := by
            omega
          have hTargetFit32 :
              (heapTop + 48).toNat +
                  8 * ((input.size - 1) + 1) ≤ 4294967296 := by
            rw [hFacts.rootToNat, hResultWords]
            simpa [FormalSpec.heapReserveBytes, hSize, hFindSpec,
              Nat.add_assoc] using hHeapFit32
          have hTargetFitMemory :
              (heapTop + 48).toNat +
                  8 * ((input.size - 1) + 1) ≤
                copySt.mem.pages * 65536 := by
            rw [hFacts.rootToNat, hResultWords]
            rw [show copySt.mem.pages = initial.mem.pages by
              simp [copySt, FixedArrayResult.writeLength, allocSt,
                FixedArrayAllocator.allocStore_pages]]
            simpa [FormalSpec.heapReserveBytes, hSize, hFindSpec,
              Nat.add_assoc] using hHeapFitMemory
          have hTargetLength :
              copySt.mem.read64 (heapTop + 48).toUInt32 =
                UInt64.ofNat (input.size - 1) := by
            simp [copySt, FixedArrayResult.writeLength]
          have hBefore :
              inputPtr.toNat + 8 * (input.size + 1) ≤
                (heapTop + 48).toNat := by
            rw [hFacts.rootToNat]
            omega
          apply FixedArrayCopy.eraseIdxProgram_spec
            (sourceLocal := 8) (targetLocal := 14)
            (prefixLocal := 11) (suffixLocal := 12)
            (counterLocal := 15) (initial := copySt)
            (frame := allocFrame) (sourcePtr := inputPtr)
            (targetPtr := heapTop + 48) (input := input)
            (erase := index) (hCounter := hCounter)
          · exact hIndex
          · exact hSourceCopy
          · decide
          · decide
          · decide
          · decide
          · exact hAllocValues
          · exact hSourceLocal
          · exact hRoot
          · exact hPrefixLocal
          · exact hSuffixLocal
          · exact hTargetFit32
          · exact hTargetFitMemory
          · exact hTargetLength
          · exact hBefore
          · intro final hResult
            let doneFrame := FixedArrayCopy.counterFrame allocFrame 15
              (input.size - 1 - index) hCounter
            have hDoneParams : doneFrame.params.length = 1 := by
              simpa only [doneFrame,
                FixedArrayCopy.counterFrame_params_length] using hAllocParams
            have hDoneLocals : doneFrame.locals.length = 23 := by
              simpa only [doneFrame,
                FixedArrayCopy.counterFrame_locals_length] using hAllocLocals
            have hDoneValues : doneFrame.values = [] := by
              exact FixedArrayCopy.counterFrame_values allocFrame 15
                (input.size - 1 - index) hCounter
            have hRootAfter : doneFrame.get 14 =
                  some (.i64 (heapTop + 48)) :=
              (FixedArrayCopy.counterFrame_get_ne allocFrame 15
                (input.size - 1 - index) 14 hCounter (by decide)).trans hRoot
            change wp LeanExeGen.GeneratedRb9ad29e25c8033e5.«module»
              [.localGet 14] _ final doneFrame env
            rw [wp_localGet_cons, hRootAfter]
            change wp LeanExeGen.GeneratedRb9ad29e25c8033e5.«module» [] _
              final { doneFrame with values := [.i64 (heapTop + 48)] } env
            rw [wp_nil]
            simp (config := { maxSteps := 10000000 })
              (discharger := omega)
              [hDoneParams, hDoneLocals, Wasm.Locals.get,
                Wasm.Locals.set?, List.getElem?_set,
                FixedArrayEqNode.branchPost,
                LeanExeGen.GeneratedRb9ad29e25c8033e5.AnnotationMatches.function_0_length_dispatch_0_suffix_program,
                LeanExeGen.GeneratedRb9ad29e25c8033e5.func0Def,
                hExpected]
            change UInt64Array.At final (heapTop + 48)
              (input.eraseIdx! index)
            exact hResult
  · intro hSize
    change wp LeanExeGen.GeneratedRb9ad29e25c8033e5.«module»
      (FixedArrayCapacity.constantProgram 0 1 12 ++
        (FixedArrayAllocatorWindow.region 3 1 ++ _)) _ initial _ env
    apply FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail
      (length := 0) (stride := 1) (offset := 3) (tail := 6)
      (heapTop := heapTop) (allocs := allocs)
    · rfl
    · simp only [FixedArrayLengthDispatch.branchFrame_locals_length]
      simp [LeanExeGen.GeneratedRb9ad29e25c8033e5.func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams, Wasm.ValueType.zero]
    · exact FixedArrayLengthDispatch.branchFrame_values _ _ _
    · simpa [FixedArrayCapacity.normalizedCapacity,
        FixedArrayCapacity.unnormalizedCapacity,
        FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · have hFit : heapTop.toNat + 48 +
          (FixedArrayCapacity.normalizedCapacity 0 1).toNat ≤
            initial.mem.pages * 65536 := by
        simpa [FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity,
          FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
      have hFacts := Allocation.bumpFacts heapTop
        (FixedArrayCapacity.normalizedCapacity 0 1) initial.mem.pages
        hFit hPages
      let baseFrame := FixedArrayCapacity.capacityFrame
        (FixedArrayLengthDispatch.branchFrame 8
          (LeanExeGen.GeneratedRb9ad29e25c8033e5.func0Def.toLocals
            (List.take
              LeanExeGen.GeneratedRb9ad29e25c8033e5.func0Def.numParams
              [.i64 inputPtr]).reverse)
          inputPtr)
        12 (FixedArrayCapacity.normalizedCapacity 0 1)
      let resultFrame := FixedArrayAllocatorWindow.allocFrame 3 baseFrame
        heapTop (FixedArrayCapacity.normalizedCapacity 0 1)
      change wp LeanExeGen.GeneratedRb9ad29e25c8033e5.«module» _ _
        (FixedArrayAllocator.allocStore initial heapTop
          (FixedArrayCapacity.normalizedCapacity 0 1) 1 allocs)
        resultFrame env
      have hBaseParams : baseFrame.params.length = 1 := by
        rfl
      have hBaseLocals : baseFrame.locals.length = 23 := by
        simp only [baseFrame, FixedArrayCapacity.capacityFrame_locals_length,
          FixedArrayLengthDispatch.branchFrame_locals_length]
        simp [LeanExeGen.GeneratedRb9ad29e25c8033e5.func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      have hFrameParams : resultFrame.params.length = 1 := by
        simpa only [resultFrame,
          FixedArrayAllocatorWindow.allocFrame_params] using hBaseParams
      have hFrameLocals : resultFrame.locals.length = 23 := by
        simpa only [resultFrame,
          FixedArrayAllocatorWindow.allocFrame_locals_length] using hBaseLocals
      have hFrameValues : resultFrame.values = [] := by
        simp only [resultFrame, FixedArrayAllocatorWindow.allocFrame_values,
          baseFrame, FixedArrayCapacity.capacityFrame_values]
      have hRoot : resultFrame.get 8 =
          some (.i64 (heapTop + 48)) := by
        unfold resultFrame
        apply FixedArrayAllocatorWindow.allocFrame_get_root
          (offset := 3) (tail := 6)
        · exact hBaseParams
        · simpa using hBaseLocals
      have hRootAddress :
          (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
        simpa using hFacts.wordAddress_toNat 0
          (FixedArrayCapacity.normalizedCapacity_toNat_ge_eight 0 1)
      change wp LeanExeGen.GeneratedRb9ad29e25c8033e5.«module»
        (FixedArrayResult.lengthStoreProgram 8 0 ++ _) _ _ _ env
      apply FixedArrayResult.lengthStore_spec
      · exact hFrameValues
      · exact hRoot
      · rw [hRootAddress, FixedArrayAllocator.allocStore_pages]
        omega
      · change wp LeanExeGen.GeneratedRb9ad29e25c8033e5.«module»
          (FixedArrayResult.finishProgram 8 6 7 ++ _) _ _ _ env
        apply FixedArrayResult.finishProgram_spec
        · exact hFrameValues
        · exact hRoot
        · rw [hFrameParams]
          omega
        · simp only [Wasm.Locals.validIndex, hFrameParams, hFrameLocals]
          omega
        · rw [hFrameParams]
          omega
        · simp only [Wasm.Locals.validIndex, hFrameParams, hFrameLocals]
          omega
        · have hReturnValid : resultFrame.validIndex 7 := by
            simp only [Wasm.Locals.validIndex, hFrameParams, hFrameLocals]
            omega
          have hReturnLower : resultFrame.params.length ≤ 7 := by
            rw [hFrameParams]
            omega
          have hReturn := FixedArrayResult.finishFrame_return_get
            resultFrame 6 7 (heapTop + 48) hReturnLower hReturnValid
          have hReturnCleared :
              ({ FixedArrayResult.finishFrame resultFrame 6 7 (heapTop + 48)
                with values := [] } : Locals).get 7 =
                some (.i64 (heapTop + 48)) := by
            simpa only [Wasm.Locals.get] using hReturn
          simp only [wp_simp,
            FixedArrayEqNode.branchPost,
            LeanExeGen.GeneratedRb9ad29e25c8033e5.AnnotationMatches.function_0_length_dispatch_0_suffix_program,
            hReturnCleared]
          refine ⟨heapTop + 48, rfl, ?_⟩
          change UInt64Array.At _ (heapTop + 48) (FormalSpec.expected input)
          rw [FormalSpec.expected, if_neg hSize]
          apply FixedArrayResult.emptyStore_at
          · rw [hFacts.rootToNat]
            omega
          · rw [hFacts.rootToNat, FixedArrayAllocator.allocStore_pages]
            omega

end LeanExeGen.GeneratedRb9ad29e25c8033e5.Behavior
