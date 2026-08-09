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

def allocationInputFrame (inputPtr capacity : UInt64) : Locals :=
  { params := [.i64 inputPtr]
    locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 inputPtr, .i64 0, .i64 0, .i64 0, .i64 capacity, .i64 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
    values := [] }

def allocatedInputFrame (inputPtr heapTop capacity : UInt64) : Locals :=
  { params := [.i64 inputPtr]
    locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 (heapTop + 48), .i64 0, .i64 0, .i64 0, .i64 capacity,
      .i64 0, .i64 0, .i64 (heapTop + 48 + capacity),
      .i64 ((heapTop + 48 + capacity - 1) / 65536 + 1),
      .i64 (heapTop + 48), .i64 0, .i64 0, .i64 0, .i64 0]
    values := [] }

def resultLengthStore (initial : Store Unit) (heapTop capacity stride allocs value : UInt64) :
    Store Unit :=
  { FixedArrayAllocator.allocStore initial heapTop capacity stride allocs with
    mem := (FixedArrayAllocator.allocStore initial heapTop capacity stride allocs).mem.write64
      (heapTop + 48).toUInt32 value }

def sumLoopFrame (inputPtr root : UInt64) (size index : Nat) (sum element next
    scratch temp marker : UInt64) : Locals :=
  { params := [.i64 inputPtr]
    locals := [.i64 sum, .i64 element, .i64 next, .i64 0, .i64 0, .i64 0,
      .i64 root, .i64 0, .i64 0, .i64 0, .i64 inputPtr,
      .i64 (UInt64.ofNat size), .i64 (UInt64.ofNat index),
      .i64 (UInt64.ofNat size), .i64 (UInt64.ofNat size), .i64 scratch,
      .i64 temp, .i64 marker, .i64 0, .i64 0]
    values := [] }

def sumLoopMeasure (input : Array UInt64) (frame : Locals) : Nat :=
  input.size - match frame.locals[12]? with
    | some (Value.i64 index) => index.toNat
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
  apply TerminatesWith.of_wp_entry_for (f := func0Def) rfl
  wp_fixed_array_length_le_dispatch 7, 8
  · rfl
  · rfl
  · decide
  · simp [func0Def, Function.toLocals]
  · decide
  · exact hArray
  · intro hSize
    wp_alloc_window [func0Def, FixedArrayLengthDispatch.branchFrame,
      List.getElem?_cons_zero]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    rw [wp_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    change wp module (FixedArrayAllocatorWindow.region 2 1 ++ _) _ initial
      (allocationInputFrame inputPtr 16) env
    apply FixedArrayAllocatorWindow.region_spec_withTail 2 4
      (heapTop := heapTop) (capacity := 16) (stride := 1) (allocs := allocs)
    · rfl
    · rfl
    · rfl
    · rfl
    · decide
    · simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · have hFitMemory : heapTop.toNat + 48 + (16 : UInt64).toNat ≤
          initial.mem.pages * 65536 := by
        simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
      have hFacts := Allocation.bumpFacts heapTop 16 initial.mem.pages
        hFitMemory hPages
      have hRootToNat : (heapTop + 48).toUInt32.toNat =
          heapTop.toNat + 48 := by
        simpa using hFacts.wordAddress_toNat 0 (by decide)
      have hRootAddress :
          UInt32.ofNat ((heapTop.toNat + 48) % 4294967296) =
            (heapTop + 48).toUInt32 := by
        rw [← hFacts.rootToNat]
        exact (Memory.toUInt32_eq_ofNat (heapTop + 48)).symm
      have hRootAddressAdd : heapTop.toUInt32 + 48 =
          (heapTop + 48).toUInt32 := by
        apply UInt32.toNat.inj
        rw [hRootToNat]
        simp only [UInt32.toNat_add, UInt32.toNat_ofNat,
          Memory.toUInt32_toNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hRootStoreAddress :
          UInt32.ofNat ((heapTop + 48).toNat % 2 ^ 32) =
            (heapTop + 48).toUInt32 := by
        rw [show 2 ^ 32 = 4294967296 by norm_num]
        exact (Memory.toUInt32_eq_ofNat (heapTop + 48)).symm
      have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
          (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs).mem.pages *
            65536 := by
        rw [FixedArrayAllocator.allocStore_pages, hRootToNat]
        omega
      have hRootGeneratedBound :
          (heapTop.toNat + 48) % 4294967296 + 8 ≤
            initial.mem.pages * 65536 := by
        simpa [Memory.toUInt32_toNat, hFacts.rootToNat,
          FixedArrayAllocator.allocStore_pages] using hRootBound
      have hInputAlloc := FixedArrayPairResult.input_preserved_by_alloc
        initial heapTop 16 1 allocs inputPtr input hArray hInputBelow
          hFitMemory hPages
      have hInputStored : UInt64Array.At
          { FixedArrayAllocator.allocStore initial heapTop 16 1 allocs with
            mem := (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs).mem.write64
              (heapTop + 48).toUInt32 1 }
          inputPtr input := by
        apply hInputAlloc.write64After
        rw [hRootToNat]
        omega
      have hAllocParams :
          (FixedArrayAllocatorWindow.allocFrame 2
            (allocationInputFrame inputPtr 16) heapTop 16).params.length = 1 := rfl
      have hAllocLocals :
          (FixedArrayAllocatorWindow.allocFrame 2
            (allocationInputFrame inputPtr 16) heapTop 16).locals.length = 20 := by
        simp [FixedArrayAllocatorWindow.allocFrame, allocationInputFrame]
      have hAllocValues :
          (FixedArrayAllocatorWindow.allocFrame 2
            (allocationInputFrame inputPtr 16) heapTop 16).values = [] := rfl
      have hAllocRoot :
          (FixedArrayAllocatorWindow.allocFrame 2
            (allocationInputFrame inputPtr 16) heapTop 16).locals[6]? =
              some (.i64 (heapTop + 48)) := by
        simp [FixedArrayAllocatorWindow.allocFrame, allocationInputFrame]
      have hAllocatedFrame :
          FixedArrayAllocatorWindow.allocFrame 2
              (allocationInputFrame inputPtr 16) heapTop 16 =
            allocatedInputFrame inputPtr heapTop 16 := by
        simp [FixedArrayAllocatorWindow.allocFrame, allocationInputFrame,
          allocatedInputFrame]
      wp_alloc_to_store [hAllocParams, hAllocLocals, hAllocValues, hAllocRoot,
        List.getElem?_cons_zero]
      rw [wp_store64_cons]
      simp only [UInt32.toNat_zero, Nat.add_zero]
      rw [hRootStoreAddress, if_neg (Nat.not_lt.mpr hRootBound)]
      rw [hAllocatedFrame]
      rw [UInt32.add_zero]
      change wp module _ _ (resultLengthStore initial heapTop 16 1 allocs 1)
        (allocatedInputFrame inputPtr heapTop 16) env
      change UInt64Array.At (resultLengthStore initial heapTop 16 1 allocs 1)
        inputPtr input at hInputStored
      wp_alloc_to_store [allocatedInputFrame, List.length,
        List.getElem?_cons_zero]
      rw [wp_load64_cons]
      simp only [show 2 ^ 32 = 4294967296 by norm_num,
        UInt32.toNat_zero, Nat.add_zero]
      rw [hInputStored.pointerAddress_eq]
      rw [if_neg (Nat.not_lt.mpr hInputStored.lengthBound)]
      rw [UInt32.add_zero, hInputStored.lengthRead]
      wp_alloc_to_store [List.length, List.getElem?_cons_zero,
        List.getElem?_cons_succ]
      rw [wp_load64_cons]
      simp only [show 2 ^ 32 = 4294967296 by norm_num,
        UInt32.toNat_zero, Nat.add_zero]
      rw [hInputStored.pointerAddress_eq]
      rw [if_neg (Nat.not_lt.mpr hInputStored.lengthBound)]
      rw [UInt32.add_zero, hInputStored.lengthRead]
      wp_alloc_to_store [List.length, List.getElem?_cons_zero,
        List.getElem?_cons_succ]
      rw [wp_ltUI64_cons]
      simp only [lt_self_iff_false, if_false]
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_alloc_to_store [List.length, List.getElem?_cons_zero,
        List.getElem?_cons_succ]
      rw [wp_nil]
      simp only [List.take, List.drop_zero, List.append_nil]
      wp_alloc_to_store [List.length, List.getElem?_cons_zero,
        List.getElem?_cons_succ]
      apply wp_block_cons
      apply wp_loop_cons
        (Inv := fun st frame =>
          st = resultLengthStore initial heapTop 16 1 allocs 1 ∧
          ∃ index : Nat, index ≤ input.size ∧
          ∃ element next scratch temp marker : UInt64,
            frame = sumLoopFrame inputPtr (heapTop + 48) input.size index
              (ArrayFold.foldPrefix input (fun sum element => sum + element) 0 index)
              element next scratch temp marker)
        (μ := fun _ frame => sumLoopMeasure input frame)
      · refine ⟨rfl, 0, by omega, 0, 0, inputPtr, 0, 0, ?_⟩
        simp [sumLoopFrame, ArrayFold.foldPrefix]
      · rintro st frame
        rintro ⟨rfl, index, hIndex, element, next, scratch, temp, marker, rfl⟩
        wp_alloc_to_store [sumLoopFrame, List.length,
          List.getElem?_cons_zero, List.getElem?_cons_succ]
        rw [wp_geUI64_cons]
        simp only
        by_cases hDone : index = input.size
        · subst index
          have hEncodedLe : UInt64.ofNat input.size ≤
              UInt64.ofNat input.size := by
            rw [UInt64.le_iff_toNat_le]
          rw [if_pos hEncodedLe]
          rw [wp_br_if_cons]
          simp [show (1 : UInt32) ≠ 0 by
            exact Ne.symm UInt32.zero_ne_one]
          have hCapacityFit32 : heapTop.toNat + 48 + 16 ≤
              4294967296 := by
            simpa using hFacts.fit32
          have hCapacityFitMemory : heapTop.toNat + 48 + 16 ≤
              initial.mem.pages * 65536 := by
            simpa using hFitMemory
          have hPayloadBound :
              (heapTop.toNat + 48 + 8) % 4294967296 + 8 ≤
                (resultLengthStore initial heapTop 16 1 allocs 1).mem.pages *
                  65536 := by
            rw [Nat.mod_eq_of_lt (by omega)]
            simp only [resultLengthStore, Mem.write64_pages,
              FixedArrayAllocator.allocStore_pages]
            omega
          rw [if_neg (Nat.not_lt.mpr hPayloadBound)]
          simp only [FixedArrayEqNode.branchPost]
          wp_run
          simp only [List.length, List.getElem?_cons_zero,
            List.getElem?_cons_succ]
          refine ⟨heapTop + 48, rfl, ?_⟩
          rw [FormalSpec.expected, if_pos hSize,
            ArrayFold.foldPrefix_size]
          unfold FormalSpec.UInt64ArrayAt
          change UInt64Array.At _ (heapTop + 48)
            #[input.foldl (fun sum element => sum + element) 0]
          have hPayloadToNat : (heapTop + 48 + 8).toUInt32.toNat =
              heapTop.toNat + 48 + 8 := by
            simpa using hFacts.wordAddress_toNat 1 (by decide)
          have hPayloadAddress :
              UInt32.ofNat ((heapTop.toNat + 48 + 8) % 4294967296) =
                (heapTop + 48 + 8).toUInt32 := by
            simpa [Nat.mod_eq_of_lt (show
              heapTop.toNat + 48 < 18446744073709551616 by omega)] using
                hFacts.wordAddress 1 (by decide)
          rw [hPayloadAddress]
          apply UInt64Array.singleton
          · rw [hFacts.rootToNat]
            omega
          · rw [hFacts.rootToNat]
            simp only [Mem.write64_pages, resultLengthStore,
              FixedArrayAllocator.allocStore_pages]
            omega
          · rw [Memory.read64_write64_disjoint _ _ _ _ (Or.inl (by
                rw [hRootToNat, hPayloadToNat]))]
            simpa [resultLengthStore] using
              (Mem.read64_write64_same
                (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs).mem
                (heapTop + 48).toUInt32 1)
          · exact Mem.read64_write64_same _ _ _
        · have hIndexLt : index < input.size := by omega
          have hIndex64 : index < UInt64.size := by
            have hSize64 := hInputStored.size_lt
            omega
          have hSize64 := hInputStored.size_lt
          have hEncodedLt : UInt64.ofNat index < UInt64.ofNat input.size := by
            rw [UInt64.lt_iff_toNat_lt,
              UInt64.toNat_ofNat_of_lt' hIndex64,
              UInt64.toNat_ofNat_of_lt' hSize64]
            exact hIndexLt
          have hNotGe : ¬UInt64.ofNat index ≥ UInt64.ofNat input.size := by
            change ¬UInt64.ofNat input.size ≤ UInt64.ofNat index
            rw [UInt64.le_iff_toNat_le,
              UInt64.toNat_ofNat_of_lt' hSize64,
              UInt64.toNat_ofNat_of_lt' hIndex64]
            exact Nat.not_le_of_lt hIndexLt
          rw [if_neg hNotGe]
          rw [wp_br_if_cons]
          simp only
          have hIndexToNat : (UInt64.ofNat index).toNat = index :=
            UInt64.toNat_ofNat_of_lt' hIndex64
          wp_alloc_to_store [sumLoopFrame, List.length,
            List.getElem?_cons_zero, List.getElem?_cons_succ, hIndexToNat]
          rw [wp_mulI64_cons]
          simp only [UInt64.mul_one]
          wp_alloc_to_store [List.length, List.getElem?_cons_zero,
            List.getElem?_cons_succ, hIndexToNat]
          rw [wp_mulI64_cons]
          simp only
          wp_alloc_to_store [List.length, List.getElem?_cons_zero,
            List.getElem?_cons_succ, hIndexToNat]
          have hOffset : (UInt64.ofNat index + 1) * 8 =
              UInt64.ofNat (8 * (index + 1)) := by
            change (UInt64.ofNat index + UInt64.ofNat 1) * UInt64.ofNat 8 = _
            rw [← UInt64.ofNat_add, ← UInt64.ofNat_mul, Nat.mul_comm]
          have hComputedAddress :
              UInt32.ofNat
                  ((inputPtr + (UInt64.ofNat index + 1) * 8).toNat %
                    4294967296) =
                (inputPtr + UInt64.ofNat (8 * (index + 1))).toUInt32 := by
            rw [hOffset]
            exact (Memory.toUInt32_eq_ofNat _).symm
          rw [wp_load64_cons]
          simp only [show 2 ^ 32 = 4294967296 by norm_num,
            UInt32.toNat_zero, Nat.add_zero]
          rw [hComputedAddress]
          rw [if_neg (Nat.not_lt.mpr
            (hInputStored.elementBound index hIndexLt))]
          rw [UInt32.add_zero, hInputStored.elementRead index hIndexLt]
          wp_alloc_to_store [List.length, List.getElem?_cons_zero,
            List.getElem?_cons_succ, hIndexToNat]
          rw [wp_neI64_cons]
          simp only
          rw [if_neg (by simp)]
          rw [wp_br_if_cons]
          simp only
          wp_alloc_to_store [List.length, List.getElem?_cons_zero,
            List.getElem?_cons_succ, hIndexToNat]
          rw [wp_br_cons]
          simp only [List.take_zero, List.drop_zero, List.nil_append]
          have hIndexSucc : UInt64.ofNat index + 1 =
              UInt64.ofNat (index + 1) := by
            change UInt64.ofNat index + UInt64.ofNat 1 = _
            rw [← UInt64.ofNat_add]
          have hIndexSucc64 : index + 1 < UInt64.size := by omega
          have hIndexSuccToNat : (UInt64.ofNat (index + 1)).toNat =
              index + 1 := UInt64.toNat_ofNat_of_lt' hIndexSucc64
          refine ⟨⟨True.intro, index + 1, by omega,
            input[index],
            ArrayFold.foldPrefix input (fun sum element => sum + element) 0
                index + input[index],
            0,
            ArrayFold.foldPrefix input (fun sum element => sum + element) 0
                index + input[index],
            1, ?_⟩, ?_⟩
          · rw [ArrayFold.foldPrefix_succ input
              (fun sum element => sum + element) 0 index hIndexLt]
            rw [hIndexSucc]
            simp only [List.set_cons_zero, List.set_cons_succ]
          · change input.size - (UInt64.ofNat index + 1).toNat <
              input.size - (UInt64.ofNat index).toNat
            rw [hIndexSucc, hIndexSuccToNat, hIndexToNat]
            omega
  · intro hSize
    wp_alloc_window [func0Def, FixedArrayLengthDispatch.branchFrame,
      List.getElem?_cons_zero]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    rw [wp_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    change wp module (FixedArrayAllocatorWindow.region 2 1 ++ _) _ initial
      (allocationInputFrame inputPtr 8) env
    apply FixedArrayAllocatorWindow.region_spec_withTail 2 4
      (heapTop := heapTop) (capacity := 8) (stride := 1) (allocs := allocs)
    · rfl
    · rfl
    · rfl
    · rfl
    · decide
    · simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · have hFitMemory : heapTop.toNat + 48 + (8 : UInt64).toNat ≤
          initial.mem.pages * 65536 := by
        simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
      have hFacts := Allocation.bumpFacts heapTop 8 initial.mem.pages
        hFitMemory hPages
      have hRootToNat : (heapTop + 48).toUInt32.toNat =
          heapTop.toNat + 48 := by
        simpa using hFacts.wordAddress_toNat 0 (by decide)
      have hRootAddress :
          UInt32.ofNat ((heapTop.toNat + 48) % 4294967296) =
            (heapTop + 48).toUInt32 := by
        rw [← hFacts.rootToNat]
        exact (Memory.toUInt32_eq_ofNat (heapTop + 48)).symm
      have hRootAddressAdd : heapTop.toUInt32 + 48 =
          (heapTop + 48).toUInt32 := by
        apply UInt32.toNat.inj
        rw [hRootToNat]
        simp only [UInt32.toNat_add, UInt32.toNat_ofNat,
          Memory.toUInt32_toNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hRootStoreAddress :
          UInt32.ofNat ((heapTop + 48).toNat % 2 ^ 32) =
            (heapTop + 48).toUInt32 := by
        rw [show 2 ^ 32 = 4294967296 by norm_num]
        exact (Memory.toUInt32_eq_ofNat (heapTop + 48)).symm
      have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
          (FixedArrayAllocator.allocStore initial heapTop 8 1 allocs).mem.pages *
            65536 := by
        rw [FixedArrayAllocator.allocStore_pages, hRootToNat]
        omega
      have hRootGeneratedBound :
          (heapTop.toNat + 48) % 4294967296 + 8 ≤
            initial.mem.pages * 65536 := by
        simpa [Memory.toUInt32_toNat, hFacts.rootToNat,
          FixedArrayAllocator.allocStore_pages] using hRootBound
      have hAllocParams :
          (FixedArrayAllocatorWindow.allocFrame 2
            (allocationInputFrame inputPtr 8) heapTop 8).params.length = 1 := rfl
      have hAllocLocals :
          (FixedArrayAllocatorWindow.allocFrame 2
            (allocationInputFrame inputPtr 8) heapTop 8).locals.length = 20 := by
        simp [FixedArrayAllocatorWindow.allocFrame, allocationInputFrame]
      have hAllocValues :
          (FixedArrayAllocatorWindow.allocFrame 2
            (allocationInputFrame inputPtr 8) heapTop 8).values = [] := rfl
      have hAllocRoot :
          (FixedArrayAllocatorWindow.allocFrame 2
            (allocationInputFrame inputPtr 8) heapTop 8).locals[6]? =
              some (.i64 (heapTop + 48)) := by
        simp [FixedArrayAllocatorWindow.allocFrame, allocationInputFrame]
      have hAllocatedFrame :
          FixedArrayAllocatorWindow.allocFrame 2
              (allocationInputFrame inputPtr 8) heapTop 8 =
            allocatedInputFrame inputPtr heapTop 8 := by
        simp [FixedArrayAllocatorWindow.allocFrame, allocationInputFrame,
          allocatedInputFrame]
      wp_alloc_to_store [hAllocParams, hAllocLocals, hAllocValues, hAllocRoot,
        List.getElem?_cons_zero]
      rw [wp_store64_cons]
      simp only [UInt32.toNat_zero, Nat.add_zero]
      rw [hRootStoreAddress, if_neg (Nat.not_lt.mpr hRootBound)]
      rw [hAllocatedFrame]
      rw [UInt32.add_zero]
      change wp module _ _ (resultLengthStore initial heapTop 8 1 allocs 0)
        (allocatedInputFrame inputPtr heapTop 8) env
      wp_alloc_to_store [allocatedInputFrame, List.length,
        List.getElem?_cons_zero]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ]
      rw [wp_nil]
      simp only [FixedArrayEqNode.branchPost]
      wp_run
      simp only [Nat.zero_add, Nat.reduceLT, List.length_set, List.length,
        List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ]
      refine ⟨heapTop + 48, rfl, ?_⟩
      rw [FormalSpec.expected, if_neg hSize]
      unfold FormalSpec.UInt64ArrayAt
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [hFacts.rootToNat] using hFacts.fit32
      · rw [hFacts.rootToNat]
        simpa [resultLengthStore, FixedArrayAllocator.allocStore_pages] using
          hFitMemory
      · simpa [resultLengthStore] using
          (Mem.read64_write64_same
            (FixedArrayAllocator.allocStore initial heapTop 8 1 allocs).mem
            (heapTop + 48).toUInt32 0)
      · intro i hi
        simp at hi

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior
