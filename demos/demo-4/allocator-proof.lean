import LeanExeGen.GeneratedRc77513211b55010d.FormalSpec
import LeanExeGen.GeneratedRc77513211b55010d.Program
import Project.ProofKit.Array
import Project.ProofKit.FixedArrayAllocatorWindow

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRc77513211b55010d.Behavior

open Wasm Project.ProofKit

private def mapSuffix : Wasm.Program :=
  [
  .localGet 7,
  .wrapI64,
  .localGet 6,
  .store64 0,
  .constI64 0,
  .localSet 8,
  .block 0 0 [
    .loop 0 0 [
      .localGet 8,
      .localGet 6,
      .geUI64,
      .br_if 1,
      .localGet 5,
      .localGet 8,
      .constI64 1,
      .mulI64,
      .constI64 1,
      .addI64,
      .constI64 8,
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 0,
      .localSet 1,
      .localGet 7,
      .localGet 8,
      .constI64 1,
      .mulI64,
      .constI64 1,
      .addI64,
      .constI64 8,
      .mulI64,
      .addI64,
      .wrapI64,
      .localGet 1,
      .constI64 1,
      .addI64,
      .store64 0,
      .localGet 8,
      .constI64 1,
      .addI64,
      .localSet 8,
      .br 0
    ]
  ],
  .localGet 7,
  .localSet 2,
  .localGet 2,
  .localSet 4
  ]

private def emptySuffix : Wasm.Program :=
  [
  .localGet 5,
  .wrapI64,
  .constI64 0,
  .store64 0,
  .localGet 5,
  .localSet 3,
  .localGet 3,
  .localSet 4
  ]

private def mapFrame (inputPtr heapTop capacity : UInt64)
    (input : Array UInt64) (last : UInt64) (index : Nat) : Wasm.Locals :=
  { params := [.i64 inputPtr],
    locals := [.i64 last, .i64 0, .i64 0, .i64 0,
      .i64 inputPtr, .i64 (UInt64.ofNat input.size), .i64 (heapTop + 48),
      .i64 (UInt64.ofNat index), .i64 0, .i64 0, .i64 capacity,
      .i64 0, .i64 0, .i64 (heapTop + 48 + capacity),
      .i64 ((heapTop + 48 + capacity - 1) / 65536 + 1),
      .i64 (heapTop + 48)],
    values := [] }

private def mapInv (initial : Wasm.Store Unit)
    (inputPtr heapTop capacity : UInt64) (input : Array UInt64) :
    Wasm.AssertionF Unit :=
  fun st frame =>
    ∃ index last, index ≤ input.size ∧
      frame = mapFrame inputPtr heapTop capacity input last index ∧
      st.mem.pages = initial.mem.pages ∧
      UInt64Array.At st inputPtr input ∧
      st.mem.read64 (heapTop + 48).toUInt32 = UInt64.ofNat input.size ∧
      ∀ i, i < index →
        st.mem.read64
          (heapTop + 48 + UInt64.ofNat (8 * (i + 1))).toUInt32 =
          input[i]! + 1

private def mapMeasure (input : Array UInt64) (_ : Wasm.Store Unit)
    (frame : Wasm.Locals) : Nat :=
  match frame.locals with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: .i64 index :: _ =>
      input.size - index.toNat
  | _ => 0

private theorem input_preserved_by_alloc
    (st : Wasm.Store Unit) (heapTop capacity stride allocs inputPtr : UInt64)
    (input : Array UInt64)
    (hInput : UInt64Array.At st inputPtr input)
    (hInputBelow : inputPtr.toNat + 8 * (input.size + 1) ≤ heapTop.toNat)
    (hFitMemory : heapTop.toNat + 48 + capacity.toNat ≤
      st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536) :
    UInt64Array.At
      (Project.ProofKit.FixedArrayAllocator.allocStore
        st heapTop capacity stride allocs)
      inputPtr input := by
  apply hInput.frameBefore hInputBelow
  · exact Project.ProofKit.FixedArrayAllocator.allocStore_pages ..
  · intro address hAddress
    simp only [Project.ProofKit.FixedArrayAllocator.allocStore,
      Project.ProofKit.FixedArrayAllocator.headerMem]
    repeat' rw [Project.ProofKit.Memory.write64_bytes_before _ _ _ (by
      simp
      omega)]

theorem artifact_behavior :
    LeanExeGen.GeneratedRc77513211b55010d.FormalSpec.ArtifactSpec LeanExeGen.GeneratedRc77513211b55010d.«module» := by
  refine ⟨0, rfl, ?_⟩
  intro env initial inputPtr input hInput
  rcases hInput with
    ⟨hArray, heapTop, allocs, retains, releases, frees, hGlobals,
      hInputBelow, hFit32, hFitMemory, hPages⟩
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
  by_cases hSize : input.size ≤ 8
  · rw [FormalSpec.expected, if_pos hSize]
    let capacity : UInt64 :=
      (8 + UInt64.ofNat input.size * 8 + 7) / 8 * 8
    have hCapacityNat : capacity.toNat = 8 * (input.size + 1) := by
      have hEight : (8 : UInt64).toNat = 8 := rfl
      have hSeven : (7 : UInt64).toNat = 7 := rfl
      simp only [capacity, UInt64.toNat_mul, UInt64.toNat_div,
        UInt64.toNat_add,
        UInt64.toNat_ofNat_of_lt' hArray.size_lt, hEight, hSeven]
      norm_num
      omega
    have hCapacity : 8 ≤ capacity.toNat := by omega
    have hCapacityU : (8 : UInt64) ≤ capacity := by
      rw [UInt64.le_iff_toNat_le]
      exact hCapacity
    have hFitCapacity :
        heapTop.toNat + 48 + capacity.toNat ≤ initial.mem.pages * 65536 := by
      rw [hCapacityNat]
      simpa [FormalSpec.expected, hSize] using hFitMemory
    have hEncodedSize : UInt64.ofNat input.size ≤ 8 := by
      rw [UInt64.le_iff_toNat_le,
        UInt64.toNat_ofNat_of_lt' hArray.size_lt]
      exact hSize
    apply TerminatesWith.of_wp_entry_for
      (f := LeanExeGen.GeneratedRc77513211b55010d.func0Def) rfl
    change wp LeanExeGen.GeneratedRc77513211b55010d.«module»
      LeanExeGen.GeneratedRc77513211b55010d.func0 _ initial
      { params := [.i64 inputPtr],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold LeanExeGen.GeneratedRc77513211b55010d.func0
    wp_run
    simp [hInputAddress, hLengthBound, hLengthRead, hEncodedSize]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    wp_run
    simp [hInputAddress, hLengthBound, hLengthRead]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simpa [capacity] using hCapacityU)]
    rw [wp_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    change wp LeanExeGen.GeneratedRc77513211b55010d.«module»
      (Project.ProofKit.FixedArrayAllocatorWindow.region 2 1 ++ mapSuffix)
      _ initial
      { params := [.i64 inputPtr],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0,
          .i64 inputPtr, .i64 (UInt64.ofNat input.size),
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 capacity,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    apply Project.ProofKit.FixedArrayAllocatorWindow.region_spec_withTail
      2 0 LeanExeGen.GeneratedRc77513211b55010d.«module» env initial _
      heapTop capacity 1 allocs
    · rfl
    · rfl
    · rfl
    · simp
    · exact hCapacity
    · exact hFitCapacity
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · have hBump := Project.ProofKit.Allocation.bumpFacts
        heapTop capacity initial.mem.pages hFitCapacity hPages
      have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
          (Project.ProofKit.FixedArrayAllocator.allocStore
            initial heapTop capacity 1 allocs).mem.pages * 65536 := by
        rw [show (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 by
          simpa using hBump.wordAddress_toNat 0 hCapacity]
        rw [Project.ProofKit.FixedArrayAllocator.allocStore_pages]
        omega
      have hRootAddress :
          UInt32.ofNat ((heapTop.toNat + 48) % 4294967296) =
            (heapTop + 48).toUInt32 := by
        simpa using hBump.wordAddress 0 hCapacity
      unfold mapSuffix
      wp_run
      simp [Project.ProofKit.FixedArrayAllocatorWindow.allocFrame]
      refine ⟨?_, ?_⟩
      · rw [Nat.mod_eq_of_lt]
        · rw [Project.ProofKit.FixedArrayAllocator.allocStore_pages]
          omega
        · omega
      · apply wp_block_cons
        apply wp_loop_cons
          (Inv := mapInv initial inputPtr heapTop capacity input)
          (μ := mapMeasure input)
        · rw [hRootAddress]
          unfold mapInv mapFrame
          refine ⟨0, 0, Nat.zero_le _, rfl, ?_, ?_, ?_, ?_⟩
          · simp [Project.ProofKit.FixedArrayAllocator.allocStore_pages,
              Wasm.Mem.write64_pages]
          · have hInputAlloc := input_preserved_by_alloc initial heapTop
                capacity 1 allocs inputPtr input hArray hInputBelow
                hFitCapacity hPages
            apply hInputAlloc.write64After
            rw [show (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 by
              simpa using hBump.wordAddress_toNat 0 hCapacity]
            omega
          · exact Wasm.Mem.read64_write64_same ..
          · intro i hi
            omega
        · rintro st frame
            ⟨index, last, hIndex, rfl, hCurrentPages, hCurrentInput,
              hCurrentLength, hPrefix⟩
          have hIndexNat : (UInt64.ofNat index).toNat = index := by
            apply UInt64.toNat_ofNat_of_lt'
            have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
            omega
          simp only [mapFrame]
          wp_run
          simp
          by_cases hDone : index = input.size
          · subst index
            have hGuard :
                (if UInt64.ofNat input.size ≤ UInt64.ofNat input.size
                  then (1 : UInt32) else 0) = 1 := by
              simp
            rw [hGuard]
            refine ⟨heapTop + 48, ?_, ?_⟩
            · simp [LeanExeGen.GeneratedRc77513211b55010d.func0Def]
            · change UInt64Array.At st (heapTop + 48)
                (input.map fun element => element + 1)
              refine ⟨?_, ?_, ?_, ?_⟩
              · rw [hBump.rootToNat, Array.size_map, ← hCapacityNat]
                exact hBump.fit32
              · rw [hBump.rootToNat, Array.size_map, hCurrentPages]
                rw [hCapacityNat] at hFitCapacity
                omega
              · simpa using hCurrentLength
              · intro i hi
                have hiInput : i < input.size := by simpa using hi
                simpa [hiInput] using hPrefix i hiInput
          · have hIndexLt : index < input.size := by omega
            have hNotGe : ¬UInt64.ofNat input.size ≤ UInt64.ofNat index := by
              rw [UInt64.le_iff_toNat_le,
                UInt64.toNat_ofNat_of_lt' hCurrentInput.size_lt, hIndexNat]
              omega
            rw [if_neg hNotGe]
            obtain ⟨hLoadBound, hLoadRead⟩ :=
              hCurrentInput.generatedElement index hIndexLt
            have hWordFit : 8 * (index + 1 + 1) ≤ capacity.toNat := by
              rw [hCapacityNat]
              omega
            have hOutputAddress :
                UInt32.ofNat
                    ((heapTop.toNat + 48 + (index + 1) * 8) % 4294967296) =
                  (heapTop + 48 + UInt64.ofNat (8 * (index + 1))).toUInt32 := by
              have hRoot64 : heapTop.toNat + 48 < 18446744073709551616 := by
                have hFit := hBump.fit32
                omega
              simpa [Nat.mod_eq_of_lt hRoot64, Nat.mul_comm, Nat.add_assoc]
                using hBump.wordAddress (index + 1) hWordFit
            have hLoadRead' :
                st.mem.read64
                    (UInt32.ofNat
                      ((inputPtr.toNat + (index + 1) * 8) % 4294967296)) =
                  input[index]! := by
              simpa [Nat.mul_comm, hIndexLt] using hLoadRead
            have hIndexSucc :
                UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by
              apply UInt64.toNat.inj
              rw [UInt64.toNat_add, hIndexNat]
              have hOne : (1 : UInt64).toNat = 1 := rfl
              rw [hOne,
                UInt64.toNat_ofNat_of_lt' (by
                  have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
                  omega)]
              have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
              rw [Nat.mod_eq_of_lt]
              omega
            refine ⟨hLoadBound, ?_, ?_, ?_⟩
            · rw [Nat.mod_eq_of_lt]
              · rw [hCurrentPages]
                omega
              · have hFit := hBump.fit32
                rw [hCapacityNat] at hFit
                omega
            · rw [hOutputAddress, hLoadRead', hIndexSucc]
              unfold mapInv
              refine ⟨index + 1, input[index]!, by omega, ?_, ?_, ?_, ?_, ?_⟩
              · rfl
              · simpa [Wasm.Mem.write64_pages] using hCurrentPages
              · apply hCurrentInput.write64After
                rw [hBump.wordAddress_toNat (index + 1) hWordFit]
                omega
              · calc
                  (st.mem.write64
                      (heapTop + 48 + UInt64.ofNat (8 * (index + 1))).toUInt32
                      (input[index]! + 1)).read64 (heapTop + 48).toUInt32 =
                      st.mem.read64 (heapTop + 48).toUInt32 := by
                        apply Project.ProofKit.Memory.read64_write64_disjoint
                        left
                        rw [show (heapTop + 48).toUInt32.toNat =
                            heapTop.toNat + 48 by
                              simpa using hBump.wordAddress_toNat 0 hCapacity,
                          hBump.wordAddress_toNat (index + 1) hWordFit]
                        omega
                  _ = UInt64.ofNat input.size := hCurrentLength
              · intro i hi
                by_cases hEq : i = index
                · subst i
                  exact Wasm.Mem.read64_write64_same ..
                · have hiIndex : i < index := by omega
                  have hWordFitI : 8 * (i + 1 + 1) ≤ capacity.toNat := by
                    rw [hCapacityNat]
                    omega
                  calc
                    (st.mem.write64
                        (heapTop + 48 + UInt64.ofNat (8 * (index + 1))).toUInt32
                        (input[index]! + 1)).read64
                        (heapTop + 48 + UInt64.ofNat (8 * (i + 1))).toUInt32 =
                        st.mem.read64
                          (heapTop + 48 + UInt64.ofNat (8 * (i + 1))).toUInt32 := by
                            apply Project.ProofKit.Memory.read64_write64_disjoint
                            left
                            rw [hBump.wordAddress_toNat (i + 1) hWordFitI,
                              hBump.wordAddress_toNat (index + 1) hWordFit]
                            omega
                    _ = input[i]! + 1 := hPrefix i hiIndex
            · simp [mapMeasure, hIndexNat]
              omega
  · rw [FormalSpec.expected, if_neg hSize]
    have hEncodedNotLe : ¬UInt64.ofNat input.size ≤ 8 := by
      have hEight : (8 : UInt64).toNat = 8 := rfl
      rw [UInt64.le_iff_toNat_le,
        UInt64.toNat_ofNat_of_lt' hArray.size_lt, hEight]
      omega
    have hFitEmpty : heapTop.toNat + 48 + 8 ≤
        initial.mem.pages * 65536 := by
      simpa [FormalSpec.expected, hSize] using hFitMemory
    apply TerminatesWith.of_wp_entry_for
      (f := LeanExeGen.GeneratedRc77513211b55010d.func0Def) rfl
    change wp LeanExeGen.GeneratedRc77513211b55010d.«module»
      LeanExeGen.GeneratedRc77513211b55010d.func0 _ initial
      { params := [.i64 inputPtr],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold LeanExeGen.GeneratedRc77513211b55010d.func0
    wp_run
    simp [hInputAddress, hLengthBound, hLengthRead, hEncodedNotLe]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by decide)]
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_neg (by decide)]
    rw [wp_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    change wp LeanExeGen.GeneratedRc77513211b55010d.«module»
      (Project.ProofKit.FixedArrayAllocatorWindow.region 0 1 ++ emptySuffix)
      _ initial
      { params := [.i64 inputPtr],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0,
          .i64 inputPtr, .i64 0, .i64 0, .i64 0,
          .i64 8, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    apply Project.ProofKit.FixedArrayAllocatorWindow.region_spec_withTail
      0 2 LeanExeGen.GeneratedRc77513211b55010d.«module» env initial _
      heapTop 8 1 allocs
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
    · have hBumpEmpty := Project.ProofKit.Allocation.bumpFacts
        heapTop 8 initial.mem.pages hFitEmpty hPages
      have hRootAddress :
          UInt32.ofNat ((heapTop.toNat + 48) % 4294967296) =
            (heapTop + 48).toUInt32 := by
        simpa using hBumpEmpty.wordAddress 0 (by decide)
      unfold emptySuffix
      wp_run
      simp [Project.ProofKit.FixedArrayAllocatorWindow.allocFrame]
      refine ⟨?_, ?_⟩
      · rw [Nat.mod_eq_of_lt]
        · rw [Project.ProofKit.FixedArrayAllocator.allocStore_pages]
          omega
        · omega
      · rw [hRootAddress]
        refine ⟨heapTop + 48, ?_, ?_⟩
        · simp [LeanExeGen.GeneratedRc77513211b55010d.func0Def]
        · change UInt64Array.At
            { (Project.ProofKit.FixedArrayAllocator.allocStore
                initial heapTop 8 1 allocs) with
              mem := (Project.ProofKit.FixedArrayAllocator.allocStore
                initial heapTop 8 1 allocs).mem.write64
                (heapTop + 48).toUInt32 0 }
            (heapTop + 48) #[]
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hBumpEmpty.rootToNat]
            simpa using hBumpEmpty.fit32
          · rw [hBumpEmpty.rootToNat, Wasm.Mem.write64_pages,
              Project.ProofKit.FixedArrayAllocator.allocStore_pages]
            omega
          · exact Wasm.Mem.read64_write64_same ..
          · intro i hi
            simp at hi

end LeanExeGen.GeneratedRc77513211b55010d.Behavior
