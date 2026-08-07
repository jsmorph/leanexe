import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArrayPairResult

namespace Project.ProofKit.FixedArrayMapAdd

open Wasm

def expected (maximumSize : Nat) (addend : UInt64)
    (input : Array UInt64) : Array UInt64 :=
  if input.size ≤ maximumSize then
    input.map fun element => element + addend
  else
    #[]

def entryFrame (inputPtr : UInt64) : Locals :=
  { params := [.i64 inputPtr]
    locals := List.replicate 16 (.i64 0)
    values := [] }

def mapPrefix : Wasm.Program :=
  [
  .localGet 0,
  .localSet 5,
  .localGet 5,
  .wrapI64,
  .load64 0,
  .localSet 6,
  .constI64 8,
  .localGet 6,
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
  .iff 0 0 [
    .constI64 8,
    .localSet 11
  ] []
  ]

def mapSuffix (addend : UInt64) : Wasm.Program :=
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
      .constI64 addend,
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

def mapProgram (addend : UInt64) : Wasm.Program :=
  mapPrefix ++ FixedArrayAllocatorWindow.region 2 1 ++ mapSuffix addend

def emptyPrefix : Wasm.Program :=
  [
  .constI64 8,
  .constI64 0,
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
  .localSet 9,
  .localGet 9,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [
    .constI64 8,
    .localSet 9
  ] []
  ]

def emptySuffix : Wasm.Program :=
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

def emptyProgram : Wasm.Program :=
  emptyPrefix ++ FixedArrayAllocatorWindow.region 0 1 ++ emptySuffix

def wrapperProgram (maximumSize : Nat) (addend : UInt64) : Wasm.Program :=
  FixedArrayLengthDispatch.leProgram 5 maximumSize
    (mapProgram addend) emptyProgram ++ [.localGet 4]

private def mapFrame (inputPtr heapTop capacity : UInt64)
    (input : Array UInt64) (last : UInt64) (index : Nat) : Locals :=
  { params := [.i64 inputPtr]
    locals := [.i64 last, .i64 0, .i64 0, .i64 0,
      .i64 inputPtr, .i64 (UInt64.ofNat input.size), .i64 (heapTop + 48),
      .i64 (UInt64.ofNat index), .i64 0, .i64 0, .i64 capacity,
      .i64 0, .i64 0, .i64 (heapTop + 48 + capacity),
      .i64 ((heapTop + 48 + capacity - 1) / 65536 + 1),
      .i64 (heapTop + 48)]
    values := [] }

private def mapInv (initial : Store Unit)
    (inputPtr heapTop capacity addend : UInt64) (input : Array UInt64) :
    AssertionF Unit :=
  fun st frame =>
    ∃ index last, index ≤ input.size ∧
      frame = mapFrame inputPtr heapTop capacity input last index ∧
      st.mem.pages = initial.mem.pages ∧
      UInt64Array.At st inputPtr input ∧
      st.mem.read64 (heapTop + 48).toUInt32 = UInt64.ofNat input.size ∧
      ∀ i, i < index →
        st.mem.read64
          (heapTop + 48 + UInt64.ofNat (8 * (i + 1))).toUInt32 =
          input[i]! + addend

private def mapMeasure (input : Array UInt64) (_ : Store Unit)
    (frame : Locals) : Nat :=
  match frame.locals with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: .i64 index :: _ =>
      input.size - index.toNat
  | _ => 0

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1048576 in
set_option Elab.async false in
theorem wrapperProgram_spec
    (maximumSize : Nat) (addend : UInt64)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (inputPtr : UInt64) (input : Array UInt64)
    (heapTop allocs : UInt64)
    (hMaximumSize : maximumSize < UInt64.size)
    (hInput : UInt64Array.At initial inputPtr input)
    (hInputBelow : inputPtr.toNat + 8 * (input.size + 1) ≤ heapTop.toNat)
    (hFit32 : heapTop.toNat + 48 +
      8 * ((expected maximumSize addend input).size + 1) ≤ 4294967296)
    (hFitMemory : heapTop.toNat + 48 +
      8 * ((expected maximumSize addend input).size + 1) ≤
        initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hMemory32 : module_.memIs64 = false)
    (hHeapTop : initial.globals.globals[0]? = some (.i64 heapTop))
    (hFreeList : initial.globals.globals[1]? = some (.i64 0))
    (hAllocs : initial.globals.globals[2]? = some (.i64 allocs)) :
    wp module_ (wrapperProgram maximumSize addend)
      (FixedArrayPairResult.publicPost (expected maximumSize addend input))
      initial (entryFrame inputPtr) env := by
  unfold wrapperProgram
  apply FixedArrayLengthDispatch.leProgram_spec 5 maximumSize _ _ _
    module_ env initial (entryFrame inputPtr) inputPtr input
  · rfl
  · rfl
  · decide
  · simp [entryFrame]
  · exact hMaximumSize
  · exact hInput
  · intro hSize
    have hExpected : expected maximumSize addend input =
        input.map fun element => element + addend := by
      simp [expected, hSize]
    let capacity : UInt64 :=
      (8 + UInt64.ofNat input.size * 8 + 7) / 8 * 8
    have hCapacityNat : capacity.toNat = 8 * (input.size + 1) := by
      have hEight : (8 : UInt64).toNat = 8 := rfl
      have hSeven : (7 : UInt64).toNat = 7 := rfl
      simp only [capacity, UInt64.toNat_mul, UInt64.toNat_div,
        UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hInput.size_lt,
        hEight, hSeven]
      norm_num
      omega
    have hCapacity : 8 ≤ capacity.toNat := by omega
    have hCapacityU : (8 : UInt64) ≤ capacity := by
      rw [UInt64.le_iff_toNat_le]
      exact hCapacity
    have hFitCapacity :
        heapTop.toNat + 48 + capacity.toNat ≤
          initial.mem.pages * 65536 := by
      rw [hCapacityNat]
      simpa [hExpected] using hFitMemory
    change wp module_ (mapProgram addend) _ initial
      { params := [.i64 inputPtr]
        locals := [.i64 0, .i64 0, .i64 0, .i64 0,
          .i64 inputPtr, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0]
        values := [] } env
    unfold mapProgram mapPrefix
    simp only [List.cons_append, List.nil_append]
    wp_run
    simp [hInput.pointerAddress_eq, hInput.lengthRead]
    rw [if_neg (Nat.not_lt.mpr hInput.generatedLengthBound)]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simpa [capacity] using hCapacityU)]
    rw [wp_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    change wp module_
      (FixedArrayAllocatorWindow.region 2 1 ++ mapSuffix addend)
      _ initial
      { params := [.i64 inputPtr]
        locals := [.i64 0, .i64 0, .i64 0, .i64 0,
          .i64 inputPtr, .i64 (UInt64.ofNat input.size),
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 capacity,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
        values := [] } env
    apply FixedArrayAllocatorWindow.region_spec_withTail 2 0 module_ env
      initial _ heapTop capacity 1 allocs
    · rfl
    · rfl
    · rfl
    · simp
    · exact hCapacity
    · exact hFitCapacity
    · exact hPages
    · exact hMemory32
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · have hBump := Allocation.bumpFacts heapTop capacity initial.mem.pages
        hFitCapacity hPages
      have hRootAddress :
          UInt32.ofNat ((heapTop.toNat + 48) % 4294967296) =
            (heapTop + 48).toUInt32 := by
        simpa using hBump.wordAddress 0 hCapacity
      unfold mapSuffix
      wp_run
      simp [FixedArrayAllocatorWindow.allocFrame]
      rw [if_neg (by
        rw [Nat.mod_eq_of_lt]
        · rw [FixedArrayAllocator.allocStore_pages]
          omega
        · omega)]
      refine ?_
      · apply wp_block_cons
        apply wp_loop_cons
          (Inv := mapInv initial inputPtr heapTop capacity addend input)
          (μ := mapMeasure input)
        · rw [hRootAddress]
          unfold mapInv mapFrame
          refine ⟨0, 0, Nat.zero_le _, rfl, ?_, ?_, ?_, ?_⟩
          · simp [FixedArrayAllocator.allocStore_pages, Mem.write64_pages]
          · have hInputAlloc := FixedArrayPairResult.input_preserved_by_alloc
              initial heapTop capacity 1 allocs inputPtr input hInput
              hInputBelow hFitCapacity hPages
            apply hInputAlloc.write64After
            rw [show (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 by
              simpa using hBump.wordAddress_toNat 0 hCapacity]
            omega
          · exact Mem.read64_write64_same ..
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
            simp only [FixedArrayEqNode.branchPost]
            wp_run
            refine ⟨heapTop + 48, ?_, ?_⟩
            · rfl
            · rw [hExpected]
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
            rw [if_neg (Nat.not_lt.mpr hLoadBound)]
            rw [if_neg (Nat.not_lt.mpr (by
              rw [Nat.mod_eq_of_lt]
              · rw [hCurrentPages]
                omega
              · have hFit := hBump.fit32
                rw [hCapacityNat] at hFit
                omega))]
            rw [hOutputAddress, hLoadRead', hIndexSucc]
            refine ⟨?_, ?_⟩
            · unfold mapInv
              refine ⟨index + 1, input[index]!, by omega, ?_, ?_, ?_, ?_, ?_⟩
              · rfl
              · simpa [Mem.write64_pages] using hCurrentPages
              · apply hCurrentInput.write64After
                rw [hBump.wordAddress_toNat (index + 1) hWordFit]
                omega
              · calc
                  (st.mem.write64
                      (heapTop + 48 + UInt64.ofNat (8 * (index + 1))).toUInt32
                      (input[index]! + addend)).read64 (heapTop + 48).toUInt32 =
                      st.mem.read64 (heapTop + 48).toUInt32 := by
                        apply Memory.read64_write64_disjoint
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
                  exact Mem.read64_write64_same ..
                · have hiIndex : i < index := by omega
                  have hWordFitI : 8 * (i + 1 + 1) ≤ capacity.toNat := by
                    rw [hCapacityNat]
                    omega
                  calc
                    (st.mem.write64
                        (heapTop + 48 + UInt64.ofNat (8 * (index + 1))).toUInt32
                        (input[index]! + addend)).read64
                        (heapTop + 48 + UInt64.ofNat (8 * (i + 1))).toUInt32 =
                        st.mem.read64
                          (heapTop + 48 + UInt64.ofNat (8 * (i + 1))).toUInt32 := by
                            apply Memory.read64_write64_disjoint
                            left
                            rw [hBump.wordAddress_toNat (i + 1) hWordFitI,
                              hBump.wordAddress_toNat (index + 1) hWordFit]
                            omega
                    _ = input[i]! + addend := hPrefix i hiIndex
            · simp [mapMeasure, hIndexNat]
              omega
  · intro hSize
    have hExpected : expected maximumSize addend input = #[] := by
      simp [expected, hSize]
    have hFitEmpty : heapTop.toNat + 48 + 8 ≤
        initial.mem.pages * 65536 := by
      simpa [hExpected] using hFitMemory
    change wp module_ emptyProgram _ initial
      { params := [.i64 inputPtr]
        locals := [.i64 0, .i64 0, .i64 0, .i64 0,
          .i64 inputPtr, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0]
        values := [] } env
    unfold emptyProgram emptyPrefix
    simp only [List.cons_append, List.nil_append]
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_neg (by decide)]
    rw [wp_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    change wp module_
      (FixedArrayAllocatorWindow.region 0 1 ++ emptySuffix)
      _ initial
      { params := [.i64 inputPtr]
        locals := [.i64 0, .i64 0, .i64 0, .i64 0,
          .i64 inputPtr, .i64 0, .i64 0, .i64 0,
          .i64 8, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0]
        values := [] } env
    apply FixedArrayAllocatorWindow.region_spec_withTail 0 2 module_ env
      initial _ heapTop 8 1 allocs
    · rfl
    · rfl
    · rfl
    · rfl
    · decide
    · exact hFitEmpty
    · exact hPages
    · exact hMemory32
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · have hBump := Allocation.bumpFacts heapTop 8 initial.mem.pages
        hFitEmpty hPages
      have hRootAddress :
          UInt32.ofNat ((heapTop.toNat + 48) % 4294967296) =
            (heapTop + 48).toUInt32 := by
        simpa using hBump.wordAddress 0 (by decide)
      unfold emptySuffix
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
      refine ⟨heapTop + 48, ?_, ?_⟩
      · rfl
      · rw [hExpected]
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

end Project.ProofKit.FixedArrayMapAdd
