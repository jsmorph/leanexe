import LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec
import LeanExeGen.GeneratedR23fa7efc3fb0298b.Program
import LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArrayLengthDispatch

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior

open Wasm Project.ProofKit

private def capacityPrefix (length : UInt64) : Wasm.Program :=
  [
  .constI64 8,
  .constI64 length,
  .constI64 1,
  .mulI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .constI64 7,
  .addI64,
  .constI64 8,
  .divUI64,
  .constI64 8,
  .mulI64,
  .localSet 11,
  .localGet 11,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [.constI64 8, .localSet 11] []
  ]

private def foldBody : Wasm.Program :=
  [
  .localGet 13,
  .localGet 15,
  .geUI64,
  .br_if 1,
  .localGet 11,
  .localGet 13,
  .constI64 1,
  .mulI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .load64 0,
  .localSet 2,
  .localGet 1,
  .localGet 2,
  .addI64,
  .localSet 3,
  .localGet 3,
  .localSet 17,
  .constI64 0,
  .localSet 16,
  .localGet 17,
  .localSet 1,
  .constI64 1,
  .localSet 18,
  .localGet 16,
  .constI64 0,
  .neI64,
  .br_if 1,
  .localGet 13,
  .constI64 1,
  .addI64,
  .localSet 13,
  .br 0
  ]

private def validSuffix : Wasm.Program :=
  [
  .localGet 7,
  .wrapI64,
  .constI64 1,
  .store64 0,
  .localGet 0,
  .localSet 11,
  .localGet 11,
  .wrapI64,
  .load64 0,
  .localSet 12,
  .constI64 0,
  .localSet 13,
  .localGet 0,
  .localSet 16,
  .localGet 16,
  .wrapI64,
  .load64 0,
  .localSet 14,
  .constI64 0,
  .localSet 1,
  .constI64 0,
  .localSet 18,
  .localGet 14,
  .localGet 12,
  .ltUI64,
  .iff 0 1 [.localGet 14] [.localGet 12],
  .localSet 15,
  .block 0 0 [.loop 0 0 foldBody],
  .localGet 1,
  .localSet 10,
  .localGet 7,
  .constI64 0,
  .constI64 1,
  .mulI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 10,
  .store64 0,
  .localGet 7,
  .localSet 4,
  .localGet 4,
  .localSet 6
  ]

private def invalidSuffix : Wasm.Program :=
  [
  .localGet 7,
  .wrapI64,
  .constI64 0,
  .store64 0,
  .localGet 7,
  .localSet 5,
  .localGet 5,
  .localSet 6
  ]

private def validProgram : Wasm.Program :=
  capacityPrefix 1 ++
    FixedArrayAllocatorWindow.region 2 1 ++ validSuffix

private def invalidProgram : Wasm.Program :=
  capacityPrefix 0 ++
    FixedArrayAllocatorWindow.region 2 1 ++ invalidSuffix

private def sumPrefix (input : Array UInt64) (index : Nat) : UInt64 :=
  (input.extract 0 index).foldl (fun sum element => sum + element) 0

private theorem sumPrefix_succ (input : Array UInt64) (index : Nat)
    (hIndex : index < input.size) :
    sumPrefix input (index + 1) = sumPrefix input index + input[index]! := by
  unfold sumPrefix
  rw [Array.extract_succ_right (by omega) hIndex]
  rw [Array.foldl_push]
  simp [hIndex]

private theorem sumPrefix_all (input : Array UInt64) :
    sumPrefix input input.size =
      input.foldl (fun sum element => sum + element) 0 := by
  simp [sumPrefix, Array.extract_eq_self_of_le]

private def foldFrame (inputPtr heapTop : UInt64) (input : Array UInt64)
    (sum element scratch flag : UInt64) (index : Nat) : Locals :=
  { params := [.i64 inputPtr]
    locals := [
      .i64 sum, .i64 element, .i64 sum, .i64 0, .i64 0,
      .i64 0, .i64 (heapTop + 48), .i64 0, .i64 0, .i64 0,
      .i64 inputPtr, .i64 (UInt64.ofNat input.size),
      .i64 (UInt64.ofNat index), .i64 (UInt64.ofNat input.size),
      .i64 (UInt64.ofNat input.size), .i64 scratch, .i64 sum,
      .i64 flag, .i64 0, .i64 0]
    values := [] }

private def foldInv (resultStore : Store Unit) (inputPtr heapTop : UInt64)
    (input : Array UInt64) : AssertionF Unit :=
  fun st frame =>
    ∃ index sum element scratch flag,
      index ≤ input.size ∧
      sum = sumPrefix input index ∧
      st = resultStore ∧
      frame = foldFrame inputPtr heapTop input sum element scratch flag index

private def foldMeasure (input : Array UInt64) (_ : Store Unit)
    (frame : Locals) : Nat :=
  match frame.locals[12]? with
  | some (Value.i64 index) => input.size - index.toNat
  | _ => 0

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
  change wp _ (FixedArrayLengthDispatch.leProgram 7 8 _ _ ++ _) _ _ _ _
  apply FixedArrayLengthDispatch.leProgram_spec
    (inputPtr := inputPtr) (input := input)
  · rfl
  · rfl
  · decide
  · norm_num [func0Def, Wasm.Function.toLocals]
  · decide
  · exact hArray
  · intro hSize
    have hExpected : FormalSpec.expected input =
        #[sumPrefix input input.size] := by
      simp [FormalSpec.expected, hSize, sumPrefix_all]
    have hFitValid : heapTop.toNat + 48 + 16 ≤
        initial.mem.pages * 65536 := by
      simpa [hExpected] using hOutputFitMemory
    change wp module validProgram _ initial
      { params := [.i64 inputPtr]
        locals := [
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 inputPtr, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
        values := [] } env
    unfold validProgram capacityPrefix
    simp only [List.cons_append, List.nil_append]
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_neg (by decide)]
    rw [wp_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    change wp module
      (FixedArrayAllocatorWindow.region 2 1 ++ validSuffix) _ initial
      { params := [.i64 inputPtr]
        locals := [
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 inputPtr, .i64 0, .i64 0, .i64 0,
          .i64 16, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
        values := [] } env
    apply FixedArrayAllocatorWindow.region_spec_withTail 2 4 module env
      initial _ heapTop 16 1 allocs
    · rfl
    · rfl
    · rfl
    · rfl
    · decide
    · exact hFitValid
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · have hBump := Allocation.bumpFacts heapTop 16 initial.mem.pages
        hFitValid hPages
      have hRootAddress :
          UInt32.ofNat ((heapTop.toNat + 48) % 4294967296) =
            (heapTop + 48).toUInt32 := by
        simpa using hBump.wordAddress 0 (by decide)
      have hPayloadAddress :
          UInt32.ofNat ((heapTop.toNat + 48 + 8) % 4294967296) =
            (heapTop + 48 + 8).toUInt32 := by
        have hRoot64 : heapTop.toNat + 48 < 18446744073709551616 := by
          omega
        simpa [Nat.mod_eq_of_lt hRoot64, Nat.add_assoc] using
          hBump.wordAddress 1 (by decide)
      have hPayloadBound :
          (heapTop.toNat + 48 + 8) % 4294967296 + 8 ≤
            (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs).mem.pages *
              65536 := by
        rw [Nat.mod_eq_of_lt (by omega),
          FixedArrayAllocator.allocStore_pages]
        omega
      have hInputAlloc := FixedArrayPairResult.input_preserved_by_alloc
        initial heapTop 16 1 allocs inputPtr input hArray hInputBelow
        hFitValid hPages
      have hInputResult : UInt64Array.At
          (FixedArrayResult.writeLength
            (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
            (heapTop + 48) 1) inputPtr input := by
        unfold FixedArrayResult.writeLength
        apply hInputAlloc.write64After
        rw [show (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 by
          simpa using hBump.wordAddress_toNat 0 (by decide)]
        omega
      have hInputLoadBound : inputPtr.toNat % 4294967296 + 8 ≤
          (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs).mem.pages *
            65536 := by
        rw [FixedArrayAllocator.allocStore_pages]
        exact hLengthBound
      have hInputResultLength :
          ((FixedArrayAllocator.allocStore initial heapTop 16 1 allocs).mem.write64
            (heapTop + 48).toUInt32 1).read64 inputPtr.toUInt32 =
            UInt64.ofNat input.size := by
        simpa [FixedArrayResult.writeLength] using hInputResult.lengthRead
      unfold validSuffix
      wp_run
      simp [FixedArrayAllocatorWindow.allocFrame]
      rw [if_neg (by
        rw [Nat.mod_eq_of_lt]
        · rw [FixedArrayAllocator.allocStore_pages]
          omega
        · omega)]
      rw [hRootAddress]
      rw [if_neg (Nat.not_lt.mpr hInputLoadBound)]
      rw [if_neg (Nat.not_lt.mpr hInputLoadBound)]
      rw [hInputResult.pointerAddress_eq, hInputResultLength]
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      apply wp_block_cons
      apply wp_loop_cons
        (Inv := foldInv
          (FixedArrayResult.writeLength
            (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
            (heapTop + 48) 1)
          inputPtr heapTop input)
        (μ := foldMeasure input)
      · unfold foldInv
        refine ⟨0, 0, 0, inputPtr, 0, by omega, ?_, rfl, rfl⟩
        simp [sumPrefix]
      · rintro st frame
          ⟨index, sum, element, scratch, flag, hIndex, hSum, hStore, rfl⟩
        subst st
        have hIndexNat : (UInt64.ofNat index).toNat = index := by
          apply UInt64.toNat_ofNat_of_lt'
          have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
          omega
        simp only [foldBody, foldFrame]
        wp_run
        simp
        by_cases hDone : index = input.size
        · subst index
          have hGuard :
              (if UInt64.ofNat input.size ≤ UInt64.ofNat input.size
                then (1 : UInt32) else 0) = 1 := by
            simp
          rw [hGuard]
          simp only [FixedArrayEqNode.branchPost]
          wp_run
          change (if
            (FixedArrayResult.writeLength
                (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                (heapTop + 48) 1).mem.pages * 65536 <
              (heapTop.toNat + 48 + 8) % 4294967296 + 8
            then False else _)
          rw [if_neg (Nat.not_lt.mpr (by
            simpa [FixedArrayResult.writeLength,
              Mem.write64_pages] using hPayloadBound))]
          rw [hPayloadAddress]
          refine ⟨heapTop + 48, rfl, ?_⟩
          rw [hExpected, ← hSum]
          change UInt64Array.At _ (heapTop + 48) #[sum]
          simpa [FixedArrayResult.singletonStore,
            FixedArrayResult.writePayload, FixedArrayResult.writeLength,
            FixedArrayResult.payloadAddress] using
            (FixedArrayResult.singletonStore_at
              (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
              (heapTop + 48) sum
              (by rw [hBump.rootToNat]; exact hBump.fit32)
              (by
                rw [hBump.rootToNat,
                  FixedArrayAllocator.allocStore_pages]
                omega))
        · have hIndexLt : index < input.size := by omega
          have hNotGe :
              ¬UInt64.ofNat input.size ≤ UInt64.ofNat index := by
            rw [UInt64.le_iff_toNat_le,
              UInt64.toNat_ofNat_of_lt' hInputResult.size_lt, hIndexNat]
            omega
          rw [if_neg hNotGe]
          obtain ⟨hLoadBound, hLoadRead⟩ :=
            hInputResult.generatedElement index hIndexLt
          have hLoadRead' :
              (FixedArrayResult.writeLength
                (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                (heapTop + 48) 1).mem.read64
                (UInt32.ofNat
                  ((inputPtr.toNat + (index + 1) * 8) % 4294967296)) =
                input[index]! := by
            simpa [Nat.mul_comm, hIndexLt] using hLoadRead
          have hIndexSucc :
              UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by
            apply UInt64.toNat.inj
            rw [UInt64.toNat_add, hIndexNat]
            have hOne : (1 : UInt64).toNat = 1 := rfl
            rw [hOne, UInt64.toNat_ofNat_of_lt' (by
              have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
              omega)]
            have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
            rw [Nat.mod_eq_of_lt]
            omega
          rw [if_neg (Nat.not_lt.mpr (by
            simpa [FixedArrayResult.writeLength, Mem.write64_pages] using
              hLoadBound))]
          rw [hLoadRead', hIndexSucc]
          refine ⟨?_, ?_⟩
          · unfold foldInv
            refine ⟨index + 1, sum + input[index]!, input[index]!, 0, 1,
              by omega, ?_, rfl, rfl⟩
            rw [sumPrefix_succ input index hIndexLt, hSum]
          · simp [foldMeasure, hIndexNat]
            omega
  · intro hSize
    have hExpected : FormalSpec.expected input = #[] := by
      simp [FormalSpec.expected, hSize]
    have hFitEmpty : heapTop.toNat + 48 + 8 ≤
        initial.mem.pages * 65536 := by
      simpa [hExpected] using hOutputFitMemory
    change wp module invalidProgram _ initial
      { params := [.i64 inputPtr]
        locals := [
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 inputPtr, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
        values := [] } env
    unfold invalidProgram capacityPrefix
    simp only [List.cons_append, List.nil_append]
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_neg (by decide)]
    rw [wp_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    change wp module
      (FixedArrayAllocatorWindow.region 2 1 ++ invalidSuffix) _ initial
      { params := [.i64 inputPtr]
        locals := [
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 inputPtr, .i64 0, .i64 0, .i64 0,
          .i64 8, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
        values := [] } env
    apply FixedArrayAllocatorWindow.region_spec_withTail 2 4 module env
      initial _ heapTop 8 1 allocs
    · rfl
    · rfl
    · rfl
    · rfl
    · decide
    · exact hFitEmpty
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · have hBump := Allocation.bumpFacts heapTop 8 initial.mem.pages
        hFitEmpty hPages
      have hRootAddress :
          UInt32.ofNat ((heapTop.toNat + 48) % 4294967296) =
            (heapTop + 48).toUInt32 := by
        simpa using hBump.wordAddress 0 (by decide)
      unfold invalidSuffix
      wp_run
      simp [FixedArrayAllocatorWindow.allocFrame]
      rw [if_neg (by
        rw [Nat.mod_eq_of_lt]
        · rw [FixedArrayAllocator.allocStore_pages]
          omega
        · omega)]
      rw [hRootAddress]
      simp only [FixedArrayEqNode.branchPost]
      wp_run
      refine ⟨heapTop + 48, rfl, ?_⟩
      rw [hExpected]
      change UInt64Array.At
        { (FixedArrayAllocator.allocStore initial heapTop 8 1 allocs) with
          mem := (FixedArrayAllocator.allocStore
            initial heapTop 8 1 allocs).mem.write64
            (heapTop + 48).toUInt32 0 }
        (heapTop + 48) #[]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hBump.rootToNat]
        simpa using hBump.fit32
      · rw [hBump.rootToNat, Mem.write64_pages,
          FixedArrayAllocator.allocStore_pages]
        omega
      · exact Mem.read64_write64_same ..
      · intro i hi
        simp at hi

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior
