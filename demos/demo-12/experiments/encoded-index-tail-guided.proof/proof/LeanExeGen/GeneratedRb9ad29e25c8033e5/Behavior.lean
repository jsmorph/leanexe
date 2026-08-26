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

private theorem allocFrame_shape
    (offset : Nat) (frame : Locals) (heapTop capacity : UInt64) :
    (FixedArrayAllocatorWindow.allocFrame offset frame heapTop capacity).params.length =
        frame.params.length ∧
      (FixedArrayAllocatorWindow.allocFrame offset frame heapTop capacity).locals.length =
        frame.locals.length ∧
      (FixedArrayAllocatorWindow.allocFrame offset frame heapTop capacity).values =
        frame.values := by
  exact ⟨congrArg List.length
      (FixedArrayAllocatorWindow.allocFrame_params offset frame heapTop capacity),
    FixedArrayAllocatorWindow.allocFrame_locals_length offset frame heapTop capacity,
    FixedArrayAllocatorWindow.allocFrame_values offset frame heapTop capacity⟩

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
  apply Wasm.TerminatesWith.of_wp_entry_for (f := func0Def) rfl
  wp_fixed_array_length_le_dispatch_from hArray at 8, 8
  · rfl
  · rfl
  · decide
  · simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  · decide
  · intro hSize
    change wp module (FixedArrayFindIdxEq.program 8 0 ++ _) _ initial _ env
    apply FixedArrayFindIdxEq.program_spec
      (scratch := 8) (tail := 12) (key := 0)
      (inputPtr := inputPtr) (input := input) (hInput := hArray)
    · decide
    · rw [FixedArrayLengthDispatch.branchFrame_params]
      rfl
    · rw [FixedArrayLengthDispatch.branchFrame_locals_length]
      simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
    · rw [FixedArrayLengthDispatch.branchFrame_values]
    · intro hFind item
      have hFind' :
          input.findIdx? (fun element => element == (0 : UInt64)) = none := by
        simpa [FixedArrayFindIdxEq.predicate] using hFind
      simp (config := { maxSteps := 10000000 }) (discharger := omega)
        [wp_simp, FixedArrayFindIdxEq.noneFrame,
          FixedArrayFindIdxEq.loopFrame, FixedArrayFindIdxEq.setupFrame,
          FixedArrayLengthDispatch.branchFrame,
          Wasm.Locals.get, Wasm.Locals.set?,
          List.getElem?_cons_zero,
          func0Def, Function.toLocals, Function.numParams, ValueType.zero,
          FormalSpec.expected, hSize, hFind']
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      simp (config := { maxSteps := 10000000 }) (discharger := omega)
        [FixedArrayEqNode.branchPost, wp_simp, Wasm.Locals.get,
          Wasm.Locals.set?, List.getElem?_cons_zero]
      exact hArray
    · intro index hIndex hFind
      have hInputSizeBound := hArray.size_lt
      have hIndexSuccBound : index + 1 < UInt64.size := by omega
      have hEncodedNe : FixedArrayFindIdxEq.encodedIndex index ≠ 0 :=
        FixedArrayFindIdxEq.encodedIndex_ne_zero hIndexSuccBound
      let entryFrame :=
        func0Def.toLocals
          (List.take func0Def.numParams [.i64 inputPtr]).reverse
      let boundedFrame :=
        FixedArrayLengthDispatch.branchFrame 8 entryFrame inputPtr
      let searchFrame :=
        FixedArrayFindIdxEq.someFrame 8 boundedFrame inputPtr input index
      let encodedFrame : Locals :=
        { searchFrame with
          locals := searchFrame.locals.set 1
            (.i64 (FixedArrayFindIdxEq.encodedIndex index))
          values := [] }
      let decoderInput : Locals :=
        { encodedFrame with
          locals := encodedFrame.locals.set 2 (.i64 inputPtr)
          values := [] }
      have hSearchParams : searchFrame.params = [.i64 inputPtr] := by
        simp [searchFrame, boundedFrame, entryFrame, func0Def,
          FixedArrayFindIdxEq.someFrame_params,
          FixedArrayLengthDispatch.branchFrame_params,
          Function.toLocals, Function.numParams, ValueType.zero]
      have hSearchLocals : searchFrame.locals.length = 23 := by
        simp [searchFrame, boundedFrame, entryFrame, func0Def,
          FixedArrayFindIdxEq.someFrame_locals_length,
          FixedArrayLengthDispatch.branchFrame_locals_length,
          Function.toLocals, Function.numParams, ValueType.zero]
      simp (config := { maxSteps := 10000000 }) (discharger := omega)
        [wp_simp, FixedArrayFindIdxEq.someFrame_values,
          FixedArrayFindIdxEq.someFrame_params,
          FixedArrayFindIdxEq.someFrame_locals_length,
          FixedArrayLengthDispatch.branchFrame_params,
          FixedArrayLengthDispatch.branchFrame_locals_length,
          Wasm.Locals.get, Wasm.Locals.set?, List.getElem?_set,
          func0Def, Function.toLocals, Function.numParams, ValueType.zero,
          hEncodedNe]
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      simp only [wp_localGet_cons, Wasm.Locals.get, List.length_cons,
        Nat.reduceLT, List.getElem?_cons_zero]
      simp only [wp_localSet_cons]
      simp (config := { maxSteps := 10000000 }) (discharger := omega)
        only [Wasm.Locals.set?, FixedArrayFindIdxEq.someFrame_params,
          FixedArrayFindIdxEq.someFrame_locals_length,
          FixedArrayLengthDispatch.branchFrame_params,
          FixedArrayLengthDispatch.branchFrame_locals_length,
          List.length_cons, Nat.reduceLT, Nat.reduceSub, List.length_set,
          func0Def, Function.toLocals, Function.numParams, ValueType.zero]
      change wp module
        (((Annotation.resolve func0
          [{ instructionIndex := 7, field := .thenBranch },
           { instructionIndex := 20, field := .elseBranch }]).getD []).drop 2)
        _ initial decoderInput env
      rw [AnnotationMatches.function_0_encoded_index_0_tail_eq]
      apply EncodedIndexDecoder.program_spec
        (encodedLocal := 2) (scratch := 8) (decodedLocal := 4)
        (encoded := FixedArrayFindIdxEq.encodedIndex index)
      · simp (config := { maxSteps := 10000000 }) (discharger := omega)
          [decoderInput, encodedFrame, Wasm.Locals.get, List.getElem?_set,
            hSearchParams, hSearchLocals]
      · simp [decoderInput, encodedFrame, hSearchParams]
      · simp [Wasm.Locals.validIndex, decoderInput, encodedFrame,
          hSearchParams, hSearchLocals]
      · simp [decoderInput, encodedFrame, hSearchParams]
      · simp [Wasm.Locals.validIndex, decoderInput, encodedFrame,
          hSearchParams, hSearchLocals]
      · let decodedFrame :=
          EncodedIndexDecoder.resultFrame decoderInput 8 4
            (FixedArrayFindIdxEq.encodedIndex index)
        change wp module _ _ initial decodedFrame env
        have hDecoded :
            decodedFrame.get 4 = some (.i64 (UInt64.ofNat index)) := by
          simpa [decodedFrame, hEncodedNe] using
            (EncodedIndexDecoder.resultFrame_decoded decoderInput 8 4
              (FixedArrayFindIdxEq.encodedIndex index)
              (by simp [decoderInput, encodedFrame, hSearchParams])
              (by simp [Wasm.Locals.validIndex, decoderInput, encodedFrame,
                hSearchParams, hSearchLocals]))
        have hDecoderSource :
            decodedFrame.get 3 = some (.i64 inputPtr) := by
          have hDecoderParams : decoderInput.params.length = 1 := by
            simp [decoderInput, encodedFrame, hSearchParams]
          have hDecoderLocals : decoderInput.locals.length = 23 := by
            simp [decoderInput, encodedFrame, hSearchLocals]
          have hDecoderSourceLocal :
              decoderInput.locals[2]? = some (.i64 inputPtr) := by
            simp [decoderInput, encodedFrame, hSearchLocals]
          have hDecoderSourceGet :
              decoderInput.locals[2] = .i64 inputPtr := by
            have h := hDecoderSourceLocal
            rw [List.getElem?_eq_getElem (by omega)] at h
            exact Option.some.inj h
          simp (discharger := omega)
            [decodedFrame, EncodedIndexDecoder.resultFrame, hEncodedNe,
              Wasm.Locals.get, hDecoderParams, hDecoderLocals,
              hDecoderSourceGet]
        have hDecoderSourceWithValues (values : List Value) :
            ({ decodedFrame with values := values } : Locals).get 3 =
              some (.i64 inputPtr) := by
          simpa only [Wasm.Locals.get] using hDecoderSource
        have hDecodedParams : decodedFrame.params.length = 1 := by
          simp [decodedFrame, decoderInput, encodedFrame, hSearchParams]
        have hDecodedLocals : decodedFrame.locals.length = 23 := by
          simp [decodedFrame, decoderInput, encodedFrame, hSearchLocals]
        have hDecodedValues : decodedFrame.values = [] := by
          simp [decodedFrame, decoderInput, encodedFrame]
        change wp module
          ([.localGet 4, .localGet 3, .localSet 8] ++ _)
          _ initial decodedFrame env
        simp only [List.cons_append, List.nil_append, wp_localGet_cons,
          hDecoded, hDecoderSourceWithValues, wp_localSet_cons]
        simp (config := { maxSteps := 10000000 }) (discharger := omega)
          only [Wasm.Locals.set?, Wasm.Locals.get, hDecodedParams,
            hDecodedLocals, List.length_cons, Nat.reduceLT, Nat.reduceSub,
            List.length_set, List.getElem?_set]
        wp_run
        simp (config := { maxSteps := 10000000 }) (discharger := omega)
          [Wasm.Locals.set?, Wasm.Locals.get, hDecodedParams,
            hDecodedLocals, hLengthBound, hInputAddress, hLengthRead,
            UInt64.lt_iff_toNat_lt, hInputSizeBound]
        rw [if_neg (by omega)]
        rw [Nat.mod_eq_of_lt (by omega : index < UInt64.size),
          Nat.mod_eq_of_lt hInputSizeBound, if_pos hIndex]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        simp only [hDecodedValues]
        let outerFrame : Locals :=
          { decodedFrame with
            locals := decodedFrame.locals.set 7 (.i64 inputPtr)
            values := [] }
        change wp module _ _ initial outerFrame env
        have hDecodedSourceLocal :
            decodedFrame.locals[2]? = some (.i64 inputPtr) := by
          simpa [Wasm.Locals.get, hDecodedParams, hDecodedLocals] using
            hDecoderSource
        have hDecodedIndexLocal :
            decodedFrame.locals[3]? = some (.i64 (UInt64.ofNat index)) := by
          simpa [Wasm.Locals.get, hDecodedParams, hDecodedLocals] using hDecoded
        have hDecodedSourceGet :
            decodedFrame.locals[2] = .i64 inputPtr := by
          have h := hDecodedSourceLocal
          rw [List.getElem?_eq_getElem (by omega)] at h
          exact Option.some.inj h
        have hDecodedIndexGet :
            decodedFrame.locals[3] = .i64 (UInt64.ofNat index) := by
          have h := hDecodedIndexLocal
          rw [List.getElem?_eq_getElem (by omega)] at h
          exact Option.some.inj h
        have hOuterSource :
            outerFrame.get 3 = some (.i64 inputPtr) := by
          simp (discharger := omega)
            [outerFrame, Wasm.Locals.get, hDecodedParams, hDecodedLocals,
              hDecodedSourceGet, List.getElem?_set]
        have hOuterIndex :
            outerFrame.get 4 = some (.i64 (UInt64.ofNat index)) := by
          simp (discharger := omega)
            [outerFrame, Wasm.Locals.get, hDecodedParams, hDecodedLocals,
              hDecodedIndexGet, List.getElem?_set]
        simp (config := { maxSteps := 10000000 }) (discharger := omega)
          [wp_simp, outerFrame, Wasm.Locals.get, Wasm.Locals.set?,
            hDecodedParams, hDecodedLocals, hDecodedSourceGet,
            hDecodedIndexGet, hOuterSource, hOuterIndex, hLengthBound,
            hInputAddress, hLengthRead, UInt64.lt_iff_toNat_lt,
            hInputSizeBound]
        rw [if_neg (by omega)]
        simp (config := { maxSteps := 10000000 }) (discharger := omega)
          only [List.getElem?_set, List.length_set, hDecodedLocals,
            Nat.reduceLT]
        simp only [if_true]
        rw [UInt64.toNat_ofNat_of_lt' (by omega : index < UInt64.size),
          UInt64.toNat_ofNat_of_lt' hInputSizeBound, if_pos hIndex]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        let scalarFrame : Locals :=
          { decodedFrame with
            locals := ((decodedFrame.locals.set 7 (.i64 inputPtr)).set 8
              (.i64 (UInt64.ofNat index))).set 9
              (.i64 (UInt64.ofNat input.size))
            values := [] }
        let capacity : UInt64 :=
          (8 + (UInt64.ofNat input.size - 1) * 8 + 7) / 8 * 8
        have hResultLengthNat :
            (UInt64.ofNat input.size - 1).toNat = input.size - 1 := by
          calc
            (UInt64.ofNat input.size - 1).toNat =
                (UInt64.ofNat input.size).toNat - (1 : UInt64).toNat :=
              Memory.toNat_sub_of_le _ _ (by
                rw [UInt64.toNat_ofNat_of_lt' hInputSizeBound]
                have hOne : (1 : UInt64).toNat = 1 := rfl
                rw [hOne]
                omega)
            _ = input.size - 1 := by
              rw [UInt64.toNat_ofNat_of_lt' hInputSizeBound]
              rfl
        have hCapacityNat : capacity.toNat = 8 * input.size := by
          have hEight : (8 : UInt64).toNat = 8 := rfl
          have hSeven : (7 : UInt64).toNat = 7 := rfl
          simp only [capacity, UInt64.toNat_mul, UInt64.toNat_div,
            UInt64.toNat_add, hResultLengthNat, hEight, hSeven]
          norm_num
          omega
        have hCapacity : 8 ≤ capacity.toNat := by omega
        have hCapacityNotSmall : ¬ capacity < 8 := by
          rw [UInt64.lt_iff_toNat_lt]
          exact Nat.not_lt.mpr (by simpa using hCapacity)
        change wp module _ _ initial scalarFrame env
        simp (config := { maxSteps := 10000000 }) (discharger := omega)
          [wp_simp, scalarFrame, Wasm.Locals.get, Wasm.Locals.set?,
            hDecodedParams, hDecodedLocals, hDecodedSourceGet,
            hDecodedIndexGet, List.getElem?_set]
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simpa [capacity] using hCapacityNotSmall)]
        rw [wp_nil]
        let allocationFrame : Locals :=
          { scalarFrame with
            locals := (((scalarFrame.locals.set 12
              (.i64 (UInt64.ofNat input.size - 1))).set 10
              (.i64 (UInt64.ofNat index))).set 11
              (.i64 ((UInt64.ofNat input.size - 1) -
                UInt64.ofNat index))).set 17 (.i64 capacity)
            values := [] }
        change wp module
          (FixedArrayAllocatorWindow.region 9 1 ++ _)
          _ initial allocationFrame env
        have hFind' :
            input.findIdx? (fun element => element == (0 : UInt64)) =
              some index := by
          change input.findIdx? (FixedArrayFindIdxEq.predicate 0) = some index
          exact hFind
        have hFitCapacity :
            heapTop.toNat + 48 + capacity.toNat ≤
              initial.mem.pages * 65536 := by
          rw [hCapacityNat]
          simpa [FormalSpec.heapReserveBytes, hSize, hFind', Nat.add_assoc]
            using hHeapFitMemory
        apply FixedArrayAllocatorWindow.region_spec
          (offset := 9) (module_ := module) (env := env) (st := initial)
          (frame := allocationFrame) (heapTop := heapTop)
          (capacity := capacity) (stride := 1) (allocs := allocs)
        · simp [allocationFrame, scalarFrame, hDecodedParams]
        · simp [allocationFrame, scalarFrame, hDecodedLocals]
        · simp [allocationFrame]
        · apply List.getElem?_set_self
          simp [allocationFrame, scalarFrame, hDecodedLocals]
        · exact hCapacity
        · exact hFitCapacity
        · exact hPages
        · decide
        · exact hHeapTop
        · exact hFreeList
        · exact hAllocs
        · let allocatedStore :=
            FixedArrayAllocator.allocStore initial heapTop capacity 1 allocs
          let allocatedFrame :=
            FixedArrayAllocatorWindow.allocFrame 9 allocationFrame
              heapTop capacity
          change wp module _ _ allocatedStore allocatedFrame env
          have hAllocationParams : allocationFrame.params.length = 1 := by
            simp [allocationFrame, scalarFrame, hDecodedParams]
          have hAllocationLocals : allocationFrame.locals.length = 23 := by
            simp [allocationFrame, scalarFrame, hDecodedLocals]
          have hAllocationValues : allocationFrame.values = [] := by
            simp [allocationFrame]
          have hAllocatedShape :=
            allocFrame_shape 9 allocationFrame heapTop capacity
          have hAllocatedParams : allocatedFrame.params.length = 1 := by
            change (FixedArrayAllocatorWindow.allocFrame 9 allocationFrame
              heapTop capacity).params.length = 1
            exact hAllocatedShape.1.trans hAllocationParams
          have hAllocatedLocals : allocatedFrame.locals.length = 23 := by
            change (FixedArrayAllocatorWindow.allocFrame 9 allocationFrame
              heapTop capacity).locals.length = 23
            exact hAllocatedShape.2.1.trans hAllocationLocals
          have hAllocatedValues : allocatedFrame.values = [] := by
            change (FixedArrayAllocatorWindow.allocFrame 9 allocationFrame
              heapTop capacity).values = []
            exact hAllocatedShape.2.2.trans hAllocationValues
          have hAllocatedRoot :
              allocatedFrame.get 14 = some (.i64 (heapTop + 48)) := by
            change (FixedArrayAllocatorWindow.allocFrame 9 allocationFrame
              heapTop capacity).get 14 = some (.i64 (heapTop + 48))
            apply FixedArrayAllocatorWindow.allocFrame_get_root
              9 0 allocationFrame heapTop capacity hAllocationParams
            simpa only [Nat.reduceAdd, Nat.add_zero] using hAllocationLocals
          have hAllocatedLength :
              allocatedFrame.get 13 =
                some (.i64 (UInt64.ofNat input.size - 1)) := by
            simp (config := { maxSteps := 10000000 }) (discharger := omega)
              [allocatedFrame, FixedArrayAllocatorWindow.allocFrame,
                allocationFrame, scalarFrame, Wasm.Locals.get,
                hDecodedParams, hDecodedLocals, List.getElem?_set]
          have hFacts := Allocation.bumpFacts heapTop capacity
            initial.mem.pages hFitCapacity hPages
          have hRootAddressNat :
              (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
            simpa using hFacts.wordAddress_toNat 0 (by omega)
          have hRootBound :
              (heapTop + 48).toUInt32.toNat + 8 ≤
                allocatedStore.mem.pages * 65536 := by
            rw [hRootAddressNat]
            simp only [allocatedStore, FixedArrayAllocator.allocStore_pages]
            omega
          change wp module
            (FixedArrayResult.lengthStoreLocalProgram 14 13 ++ _)
            _ allocatedStore allocatedFrame env
          apply FixedArrayResult.lengthStoreLocal_spec
            (root := heapTop + 48)
            (length := UInt64.ofNat input.size - 1)
            (rootLocal := 14) (lengthLocal := 13)
          · exact hAllocatedRoot
          · exact hAllocatedLength
          · exact hRootBound
          · let resultStore := FixedArrayResult.writeLength allocatedStore
              (heapTop + 48) (UInt64.ofNat input.size - 1)
            change wp module _ _ resultStore allocatedFrame env
            have hResultLength :
                UInt64.ofNat input.size - 1 =
                  UInt64.ofNat (input.size - 1) := by
              apply UInt64.toNat.inj
              rw [hResultLengthNat,
                UInt64.toNat_ofNat_of_lt' (by omega :
                  input.size - 1 < UInt64.size)]
            have hSuffixNat :
                ((UInt64.ofNat input.size - 1) -
                    UInt64.ofNat index).toNat =
                  input.size - 1 - index := by
              calc
                ((UInt64.ofNat input.size - 1) -
                    UInt64.ofNat index).toNat =
                    (UInt64.ofNat input.size - 1).toNat -
                      (UInt64.ofNat index).toNat :=
                  Memory.toNat_sub_of_le _ _ (by
                    rw [hResultLengthNat,
                      UInt64.toNat_ofNat_of_lt' (by omega :
                        index < UInt64.size)]
                    omega)
                _ = input.size - 1 - index := by
                  rw [hResultLengthNat,
                    UInt64.toNat_ofNat_of_lt' (by omega :
                      index < UInt64.size)]
            have hSuffixWord :
                (UInt64.ofNat input.size - 1) - UInt64.ofNat index =
                  UInt64.ofNat (input.size - 1 - index) := by
              apply UInt64.toNat.inj
              rw [hSuffixNat,
                UInt64.toNat_ofNat_of_lt' (by omega :
                  input.size - 1 - index < UInt64.size)]
            have hAllocatedSource :
                allocatedFrame.get 8 = some (.i64 inputPtr) := by
              simp (config := { maxSteps := 10000000 })
                (discharger := omega)
                [allocatedFrame, FixedArrayAllocatorWindow.allocFrame,
                  allocationFrame, scalarFrame, Wasm.Locals.get,
                  hDecodedParams, hDecodedLocals, List.getElem?_set]
            have hAllocatedPrefix :
                allocatedFrame.get 11 =
                  some (.i64 (UInt64.ofNat index)) := by
              simp (config := { maxSteps := 10000000 })
                (discharger := omega)
                [allocatedFrame, FixedArrayAllocatorWindow.allocFrame,
                  allocationFrame, scalarFrame, Wasm.Locals.get,
                  hDecodedParams, hDecodedLocals, List.getElem?_set]
            have hAllocatedSuffix :
                allocatedFrame.get 12 =
                  some (.i64 (UInt64.ofNat (input.size - 1 - index))) := by
              simp (config := { maxSteps := 10000000 })
                (discharger := omega)
                [allocatedFrame, FixedArrayAllocatorWindow.allocFrame,
                  allocationFrame, scalarFrame, Wasm.Locals.get,
                  hDecodedParams, hDecodedLocals, List.getElem?_set,
                  hSuffixWord]
            have hCounter : allocatedFrame.validIndex 15 := by
              simp [Wasm.Locals.validIndex, hAllocatedParams,
                hAllocatedLocals]
            have hInputAllocated : UInt64Array.At allocatedStore inputPtr input :=
              FixedArrayPairResult.input_preserved_by_alloc
                initial heapTop capacity 1 allocs inputPtr input hArray
                hInputBelow hFitCapacity hPages
            have hInputResult : UInt64Array.At resultStore inputPtr input := by
              change UInt64Array.At
                { allocatedStore with
                  mem := allocatedStore.mem.write64
                    (heapTop + 48).toUInt32
                    (UInt64.ofNat input.size - 1) }
                inputPtr input
              exact UInt64Array.At.write64After
                (by rw [hRootAddressNat]; omega) hInputAllocated
            have hTargetFit32 :
                (heapTop + 48).toNat +
                    8 * ((input.size - 1) + 1) ≤ 4294967296 := by
              rw [hFacts.rootToNat]
              have hFit32 := hFacts.fit32
              rw [hCapacityNat] at hFit32
              omega
            have hTargetFitMemory :
                (heapTop + 48).toNat +
                    8 * ((input.size - 1) + 1) ≤
                  resultStore.mem.pages * 65536 := by
              rw [hFacts.rootToNat]
              simp only [resultStore, FixedArrayResult.writeLength,
                Mem.write64_pages, allocatedStore,
                FixedArrayAllocator.allocStore_pages]
              rw [hCapacityNat] at hFitCapacity
              omega
            have hTargetLength :
                resultStore.mem.read64 (heapTop + 48).toUInt32 =
                  UInt64.ofNat (input.size - 1) := by
              simp [resultStore, FixedArrayResult.writeLength,
                Mem.read64_write64_same, hResultLength]
            have hBefore :
                inputPtr.toNat + 8 * (input.size + 1) ≤
                  (heapTop + 48).toNat := by
              rw [hFacts.rootToNat]
              omega
            change wp module
              (FixedArrayCopy.program 1 8 14 11 12 15 ++ _)
              _ resultStore allocatedFrame env
            apply FixedArrayCopy.eraseIdxProgram_spec
              (sourceLocal := 8) (targetLocal := 14)
              (prefixLocal := 11) (suffixLocal := 12)
              (counterLocal := 15) (sourcePtr := inputPtr)
              (targetPtr := heapTop + 48) (input := input) (erase := index)
              (hCounter := hCounter)
            · exact hIndex
            · exact hInputResult
            · decide
            · decide
            · decide
            · decide
            · exact hAllocatedValues
            · exact hAllocatedSource
            · exact hAllocatedRoot
            · exact hAllocatedPrefix
            · exact hAllocatedSuffix
            · exact hTargetFit32
            · exact hTargetFitMemory
            · exact hTargetLength
            · exact hBefore
            · intro final hResult
              have hCounterRoot :
                  (FixedArrayCopy.counterFrame allocatedFrame 15
                    (input.size - 1 - index) hCounter).get 14 =
                    some (.i64 (heapTop + 48)) := by
                exact (FixedArrayCopy.counterFrame_get_ne allocatedFrame 15
                  (input.size - 1 - index) 14 hCounter (by decide)).trans
                  hAllocatedRoot
              have hCounterParams :
                  (FixedArrayCopy.counterFrame allocatedFrame 15
                    (input.size - 1 - index) hCounter).params.length = 1 := by
                rw [FixedArrayCopy.counterFrame_params_length]
                exact hAllocatedParams
              have hCounterLocals :
                  (FixedArrayCopy.counterFrame allocatedFrame 15
                    (input.size - 1 - index) hCounter).locals.length = 23 := by
                rw [FixedArrayCopy.counterFrame_locals_length]
                exact hAllocatedLocals
              have hExpected :
                  FormalSpec.expected input = input.eraseIdx! index := by
                simp [FormalSpec.expected, hSize, hFind']
              simp only [wp_localGet_cons, hCounterRoot]
              simp (config := { maxSteps := 10000000 })
                (discharger := omega)
                [wp_simp, FixedArrayEqNode.branchPost,
                  FixedArrayCopy.counterFrame_values,
                  FixedArrayCopy.counterFrame_params_length,
                  FixedArrayCopy.counterFrame_locals_length,
                  hCounterParams, hCounterLocals,
                  Wasm.Locals.get, Wasm.Locals.set?, hExpected,
                  List.getElem?_set]
              exact hResult
  · intro hInvalid
    let entryFrame :=
      func0Def.toLocals
        (List.take func0Def.numParams [.i64 inputPtr]).reverse
    let invalidFrame :=
      FixedArrayLengthDispatch.branchFrame 8 entryFrame inputPtr
    change wp module
      (FixedArrayCapacity.constantProgram 0 1 12 ++
        FixedArrayAllocatorWindow.region 3 1 ++ _)
      _ initial invalidFrame env
    have hInvalidParams : invalidFrame.params.length = 1 := by
      simp [invalidFrame, entryFrame,
        FixedArrayLengthDispatch.branchFrame_params,
        func0Def, Function.toLocals, Function.numParams, ValueType.zero]
    have hInvalidLocals : invalidFrame.locals.length = 23 := by
      simp [invalidFrame, entryFrame,
        FixedArrayLengthDispatch.branchFrame_locals_length,
        func0Def, Function.toLocals, Function.numParams, ValueType.zero]
    have hInvalidValues : invalidFrame.values = [] := by
      simp [invalidFrame, FixedArrayLengthDispatch.branchFrame_values]
    have hInvalidFit :
        heapTop.toNat + 48 +
            (FixedArrayCapacity.normalizedCapacity 0 1).toNat ≤
          initial.mem.pages * 65536 := by
      simpa [FixedArrayCapacity.normalizedCapacity,
        FixedArrayCapacity.unnormalizedCapacity,
        FormalSpec.heapReserveBytes, hInvalid] using hHeapFitMemory
    apply FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail
      (length := 0) (stride := 1) (offset := 3) (tail := 6)
      (module_ := module) (env := env) (st := initial)
      (frame := invalidFrame) (heapTop := heapTop) (allocs := allocs)
    · exact hInvalidParams
    · simpa only [Nat.reduceAdd, Nat.add_zero] using hInvalidLocals
    · exact hInvalidValues
    · exact hInvalidFit
    · exact hPages
    · decide
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · let capacity := FixedArrayCapacity.normalizedCapacity 0 1
      let capacityFrame :=
        FixedArrayCapacity.capacityFrame invalidFrame 12 capacity
      let allocatedStore :=
        FixedArrayAllocator.allocStore initial heapTop capacity 1 allocs
      let allocatedFrame :=
        FixedArrayAllocatorWindow.allocFrame 3 capacityFrame heapTop capacity
      change wp module _ _ allocatedStore allocatedFrame env
      have hCapacityEq : capacity = 8 := by
        rfl
      have hCapacityFrameParams : capacityFrame.params.length = 1 := by
        change (FixedArrayCapacity.capacityFrame invalidFrame 12
          capacity).params.length = 1
        rw [FixedArrayCapacity.capacityFrame_params]
        exact hInvalidParams
      have hCapacityFrameLocals : capacityFrame.locals.length = 23 := by
        change (FixedArrayCapacity.capacityFrame invalidFrame 12
          capacity).locals.length = 23
        rw [FixedArrayCapacity.capacityFrame_locals_length]
        exact hInvalidLocals
      have hCapacityFrameValues : capacityFrame.values = [] := by
        change (FixedArrayCapacity.capacityFrame invalidFrame 12
          capacity).values = []
        exact FixedArrayCapacity.capacityFrame_values invalidFrame 12 capacity
      have hAllocatedShape :=
        allocFrame_shape 3 capacityFrame heapTop capacity
      have hAllocatedParams : allocatedFrame.params.length = 1 := by
        change (FixedArrayAllocatorWindow.allocFrame 3 capacityFrame
          heapTop capacity).params.length = 1
        exact hAllocatedShape.1.trans hCapacityFrameParams
      have hAllocatedLocals : allocatedFrame.locals.length = 23 := by
        change (FixedArrayAllocatorWindow.allocFrame 3 capacityFrame
          heapTop capacity).locals.length = 23
        exact hAllocatedShape.2.1.trans hCapacityFrameLocals
      have hAllocatedValues : allocatedFrame.values = [] := by
        change (FixedArrayAllocatorWindow.allocFrame 3 capacityFrame
          heapTop capacity).values = []
        exact hAllocatedShape.2.2.trans hCapacityFrameValues
      have hAllocatedRoot :
          allocatedFrame.get 8 = some (.i64 (heapTop + 48)) := by
        change (FixedArrayAllocatorWindow.allocFrame 3 capacityFrame
          heapTop capacity).get 8 = some (.i64 (heapTop + 48))
        apply FixedArrayAllocatorWindow.allocFrame_get_root
          3 6 capacityFrame heapTop capacity hCapacityFrameParams
        simpa only [Nat.reduceAdd] using hCapacityFrameLocals
      have hFitMemory :
          heapTop.toNat + 48 + capacity.toNat ≤
            initial.mem.pages * 65536 := by
        simpa [capacity] using hInvalidFit
      have hFacts := Allocation.bumpFacts heapTop capacity
        initial.mem.pages hFitMemory hPages
      have hRootAddressNat :
          (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
        simpa using hFacts.wordAddress_toNat 0 (by
          rw [hCapacityEq]
          decide)
      have hRootFit32 :
          (heapTop + 48).toNat + 8 ≤ 4294967296 := by
        rw [hFacts.rootToNat]
        have hFit32 := hFacts.fit32
        rw [hCapacityEq] at hFit32
        omega
      have hRootFitMemory :
          (heapTop + 48).toNat + 8 ≤
            allocatedStore.mem.pages * 65536 := by
        rw [hFacts.rootToNat]
        simp only [allocatedStore, FixedArrayAllocator.allocStore_pages]
        rw [hCapacityEq] at hFitMemory
        omega
      have hRootBound :
          (heapTop + 48).toUInt32.toNat + 8 ≤
            allocatedStore.mem.pages * 65536 := by
        rw [hRootAddressNat]
        simpa only [hFacts.rootToNat] using hRootFitMemory
      change wp module
        (FixedArrayResult.lengthStoreProgram 8 0 ++ _)
        _ allocatedStore allocatedFrame env
      apply FixedArrayResult.lengthStore_spec
        (root := heapTop + 48) (length := 0) (rootLocal := 8)
      · exact hAllocatedValues
      · exact hAllocatedRoot
      · exact hRootBound
      · let resultStore :=
          FixedArrayResult.writeLength allocatedStore (heapTop + 48) 0
        change wp module _ _ resultStore allocatedFrame env
        have hEmpty : UInt64Array.At resultStore (heapTop + 48) #[] := by
          exact FixedArrayResult.emptyStore_at allocatedStore (heapTop + 48)
            hRootFit32 hRootFitMemory
        change wp module
          (FixedArrayResult.finishProgram 8 6 7 ++ [])
          _ resultStore allocatedFrame env
        apply FixedArrayResult.finishProgram_spec
          (root := heapTop + 48) (rootLocal := 8)
          (destinationLocal := 6) (returnLocal := 7)
        · exact hAllocatedValues
        · exact hAllocatedRoot
        · omega
        · simp [Wasm.Locals.validIndex, hAllocatedParams,
            hAllocatedLocals]
        · omega
        · simp [Wasm.Locals.validIndex, hAllocatedParams,
            hAllocatedLocals]
        · rw [wp_nil]
          have hReturnRoot :
              (FixedArrayResult.finishFrame allocatedFrame 6 7
                (heapTop + 48)).get 7 = some (.i64 (heapTop + 48)) := by
            apply FixedArrayResult.finishFrame_return_get
            · omega
            · simp [Wasm.Locals.validIndex, hAllocatedParams,
                hAllocatedLocals]
          have hExpected : FormalSpec.expected input = #[] := by
            simp [FormalSpec.expected, hInvalid]
          simp only [FixedArrayEqNode.branchPost]
          have hReturnRootValues :
              ({ FixedArrayResult.finishFrame allocatedFrame 6 7
                (heapTop + 48) with values := [] } : Locals).get 7 =
                some (.i64 (heapTop + 48)) := by
            simpa only [Wasm.Locals.get] using hReturnRoot
          simp only [wp_localGet_cons, hReturnRootValues]
          rw [wp_nil]
          refine ⟨heapTop + 48, ?_, ?_⟩
          · simp [func0Def, Function.numParams]
          · rw [hExpected]
            exact hEmpty

end LeanExeGen.GeneratedRb9ad29e25c8033e5.Behavior
