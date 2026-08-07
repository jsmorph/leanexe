import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArrayPairResult

set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace Project.ProofKit.FixedArrayFilterLt

open Wasm Project.ProofKit.FixedArrayAllocatorWindow

def expected (maximumSize : Nat) (threshold : UInt64)
    (input : Array UInt64) : Array UInt64 :=
  if input.size ≤ maximumSize then
    input.filter fun element => element < threshold
  else
    #[]

def heapReserveBytes (maximumSize : Nat) (input : Array UInt64) : Nat :=
  if input.size ≤ maximumSize then
    48 + 8 * (input.size + 1)
  else
    56

private def keptPrefix (threshold : UInt64)
    (input : Array UInt64) (index : Nat) : Array UInt64 :=
  (input.extract 0 index).filter fun element => element < threshold

private theorem keptPrefix_succ_pos (threshold : UInt64)
    (input : Array UInt64) (index : Nat)
    (hIndex : index < input.size) (hKeep : input[index]! < threshold) :
    keptPrefix threshold input (index + 1) =
      (keptPrefix threshold input index).push input[index]! := by
  unfold keptPrefix
  rw [Array.extract_succ_right (by omega) hIndex]
  simp only [show input[index]! = input[index] by simp [hIndex]]
  apply Array.filter_push_of_pos
  · simpa [hIndex] using hKeep
  · simp
    omega

private theorem keptPrefix_succ_neg (threshold : UInt64)
    (input : Array UInt64) (index : Nat)
    (hIndex : index < input.size) (hKeep : ¬input[index]! < threshold) :
    keptPrefix threshold input (index + 1) = keptPrefix threshold input index := by
  unfold keptPrefix
  rw [Array.extract_succ_right (by omega) hIndex]
  apply Array.filter_push_of_neg
  · simpa [hIndex] using hKeep
  · simp
    omega

private theorem keptPrefix_size_le (threshold : UInt64)
    (input : Array UInt64) (index : Nat)
    (hIndex : index ≤ input.size) :
    (keptPrefix threshold input index).size ≤ index := by
  unfold keptPrefix
  calc
    ((input.extract 0 index).filter fun element =>
      element < threshold).size ≤ (input.extract 0 index).size :=
        Array.size_filter_le
    _ = index := by simp [hIndex]

private theorem keptPrefix_all (threshold : UInt64) (input : Array UInt64) :
    keptPrefix threshold input input.size =
      input.filter fun element => element < threshold := by
  simp [keptPrefix, Array.extract_eq_self_of_le]

def entryFrame (inputPtr : UInt64) : Locals :=
  { params := [.i64 inputPtr]
    locals := List.replicate 21 (.i64 0)
    values := [] }

private def validPrefix : Wasm.Program :=
  [
  .localGet 0,
  .localSet 5,
  .localGet 5,
  .wrapI64,
  .load64 0,
  .localSet 6,
  .constI64 0,
  .localSet 7,
  .localGet 0,
  .localSet 15,
  .localGet 15,
  .wrapI64,
  .load64 0,
  .localSet 8,
  .localGet 6,
  .constI64 1,
  .mulI64,
  .localSet 12,
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
  .localSet 15,
  .localGet 15,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [
    .constI64 8,
    .localSet 15
  ] []
  ]

private def filterSuffix (threshold : UInt64) : Wasm.Program :=
  [
  .constI64 0,
  .localSet 11,
  .localGet 8,
  .localGet 6,
  .ltUI64,
  .iff 0 1 [
    .localGet 8
  ] [
    .localGet 6
  ],
  .localSet 9,
  .block 0 0 [
    .loop 0 0 [
      .localGet 7,
      .localGet 9,
      .geUI64,
      .br_if 1,
      .localGet 5,
      .localGet 7,
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
      .localGet 1,
      .constI64 threshold,
      .ltUI64,
      .iff 0 1 [
        .constI64 1
      ] [
        .constI64 0
      ],
      .constI64 0,
      .neI64,
      .iff 0 0 [
        .localGet 10,
        .localGet 11,
        .constI64 1,
        .mulI64,
        .constI64 1,
        .addI64,
        .constI64 8,
        .mulI64,
        .addI64,
        .wrapI64,
        .localGet 1,
        .store64 0,
        .localGet 11,
        .constI64 1,
        .addI64,
        .localSet 11
      ] [],
      .localGet 7,
      .constI64 1,
      .addI64,
      .localSet 7,
      .br 0
    ]
  ],
  .localGet 10,
  .wrapI64,
  .localGet 11,
  .store64 0,
  .localGet 10,
  .localSet 2,
  .localGet 2,
  .localSet 4
  ]

private def validAllocatorRegion : Wasm.Program :=
  [
  .constI64 0,
  .localSet 20,
  .constI64 0,
  .localSet 16,
  .globalGet 1,
  .localSet 17
  ] ++ FixedArrayAllocatorWindow.search 6 1 ++
    FixedArrayAllocatorWindow.bump 6 1 ++
  [
  .globalGet 2,
  .constI64 1,
  .addI64,
  .globalSet 2,
  .localGet 20,
  .localSet 10
  ]

private def validAllocatorFrame (base : Locals)
    (heapTop capacity : UInt64) : Locals :=
  { base with
    locals := ((((((base.locals.set 19 (.i64 0)).set 15 (.i64 0)).set
      16 (.i64 0)).set 17 (.i64 (heapTop + 48 + capacity))).set 18
        (.i64 ((heapTop + 48 + capacity - 1) / 65536 + 1))).set
      19 (.i64 (heapTop + 48))).set 9 (.i64 (heapTop + 48)) }

private def validProgram (threshold : UInt64) : Wasm.Program :=
  validPrefix ++ validAllocatorRegion ++ filterSuffix threshold

private def emptyPrefix : Wasm.Program :=
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

private def emptyProgram : Wasm.Program :=
  emptyPrefix ++ FixedArrayAllocatorWindow.region 0 1 ++ emptySuffix

def wrapperProgram (maximumSize : Nat) (threshold : UInt64) : Wasm.Program :=
  FixedArrayLengthDispatch.leProgram 5 maximumSize
    (validProgram threshold) emptyProgram ++
    [.localGet 4]

private def validFrame (inputPtr heapTop capacity : UInt64)
    (threshold : UInt64) (input : Array UInt64)
    (last : UInt64) (index : Nat) : Locals :=
  { params := [.i64 inputPtr]
    locals := [.i64 last, .i64 0, .i64 0, .i64 0,
      .i64 inputPtr, .i64 (UInt64.ofNat input.size),
      .i64 (UInt64.ofNat index), .i64 (UInt64.ofNat input.size),
      .i64 (UInt64.ofNat input.size), .i64 (heapTop + 48),
      .i64 (UInt64.ofNat (keptPrefix threshold input index).size),
      .i64 (UInt64.ofNat input.size), .i64 0, .i64 0, .i64 capacity,
      .i64 0, .i64 0, .i64 (heapTop + 48 + capacity),
      .i64 ((heapTop + 48 + capacity - 1) / 65536 + 1),
      .i64 (heapTop + 48), .i64 0]
    values := [] }

private def validInv (initial : Store Unit)
    (inputPtr heapTop capacity threshold : UInt64) (input : Array UInt64) :
    AssertionF Unit :=
  fun st frame =>
    ∃ index last, index ≤ input.size ∧
      frame = validFrame inputPtr heapTop capacity threshold input last index ∧
      st.mem.pages = initial.mem.pages ∧
      UInt64Array.At st inputPtr input ∧
      ∀ (i : Nat) (hi : i < (keptPrefix threshold input index).size),
        st.mem.read64
          (heapTop + 48 + UInt64.ofNat (8 * (i + 1))).toUInt32 =
          (keptPrefix threshold input index)[i]

private def validMeasure (input : Array UInt64) (_ : Store Unit)
    (frame : Locals) : Nat :=
  match frame.locals with
  | _ :: _ :: _ :: _ :: _ :: _ :: .i64 index :: _ =>
      input.size - index.toNat
  | _ => 0

private theorem validAllocatorRegion_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (heapTop capacity allocs : UInt64)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 21)
    (hValues : frame.values = [])
    (hCapacityLocal : frame.locals[14]? = some (.i64 capacity))
    (hCapacity : 8 ≤ capacity.toNat)
    (hFitMemory : heapTop.toNat + 48 + capacity.toNat ≤
      st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hMemory32 : module_.memIs64 = false)
    (hHeapTop : st.globals.globals[0]? = some (.i64 heapTop))
    (hFreeList : st.globals.globals[1]? = some (.i64 0))
    (hAllocs : st.globals.globals[2]? = some (.i64 allocs))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q
      (FixedArrayAllocator.allocStore st heapTop capacity 1 allocs)
      (validAllocatorFrame frame heapTop capacity) env) :
    wp module_ (validAllocatorRegion ++ rest) Q st frame env := by
  have hNot5 : ¬6 + 5 < 1 := by omega
  have hNot9 : ¬6 + 9 < 1 := by omega
  have hNot10 : ¬6 + 10 < 1 := by omega
  have hNot11 : ¬6 + 11 < 1 := by omega
  have hNot12 : ¬6 + 12 < 1 := by omega
  have hNot13 : ¬6 + 13 < 1 := by omega
  have hNot14 : ¬6 + 14 < 1 := by omega
  have hNotDestination : ¬10 < 1 := by omega
  have hValid5 : 6 + 5 < 1 + 21 := by omega
  have hValid9 : 6 + 9 < 1 + 21 := by omega
  have hValid10 : 6 + 10 < 1 + 21 := by omega
  have hValid11 : 6 + 11 < 1 + 21 := by omega
  have hValid12 : 6 + 12 < 1 + 21 := by omega
  have hValid13 : 6 + 13 < 1 + 21 := by omega
  have hValid14 : 6 + 14 < 1 + 21 := by omega
  have hValidDestination : 10 < 1 + 21 := by omega
  have hLocal4 : 6 + 4 < 21 := by omega
  have hLocal8 : 6 + 8 < 21 := by omega
  have hLocal9 : 6 + 9 < 21 := by omega
  have hLocal10 : 6 + 10 < 21 := by omega
  have hLocal11 : 6 + 11 < 21 := by omega
  have hLocal12 : 6 + 12 < 21 := by omega
  have hLocal13 : 6 + 13 < 21 := by omega
  have hLocalDestination : 9 < 21 := by omega
  have hCapacityGet : frame.locals[14] = .i64 capacity := by
    have h := hCapacityLocal
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  simp only [validAllocatorRegion, FixedArrayAllocatorWindow.search,
    FixedArrayAllocatorWindow.bump, List.cons_append, List.nil_append]
  wp_alloc_window [hParams, hLocals, hValues, hCapacityGet,
    hNot5, hNot9, hNot10, hNot11, hNot12, hNot13, hNot14,
    hNotDestination, hValid5, hValid9, hValid10, hValid11, hValid12,
    hValid13, hValid14, hValidDestination, hLocal4, hLocal8, hLocal9,
    hLocal10, hLocal11, hLocal12, hLocal13, hLocalDestination]
  simp only [hFreeList]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st' s => st' = st ∧
      s = FixedArrayAllocatorWindow.searchFrame 6 frame)
    (μ := fun _ _ => 0)
  · refine ⟨rfl, ?_⟩
    simp (discharger := omega)
      [FixedArrayAllocatorWindow.searchFrame, hValues]
  · rintro st1 s1 ⟨hSt, hFrame⟩
    subst st1
    subst s1
    simp only [FixedArrayAllocatorWindow.searchBody,
      FixedArrayAllocatorWindow.searchFrame]
    wp_alloc_window [hParams, hLocals, hValues, hCapacityGet,
      hNot5, hNot9, hNot10, hNot11, hNot12, hNot13, hNot14,
      hNotDestination, hValid5, hValid9, hValid10, hValid11, hValid12,
      hValid13, hValid14, hValidDestination, hLocal4, hLocal8, hLocal9,
      hLocal10, hLocal11, hLocal12, hLocal13, hLocalDestination]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_alloc_window [hParams, hLocals, hValues, hCapacityGet,
      hNot5, hNot9, hNot10, hNot11, hNot12, hNot13, hNot14,
      hNotDestination, hValid5, hValid9, hValid10, hValid11, hValid12,
      hValid13, hValid14, hValidDestination, hLocal4, hLocal8, hLocal9,
      hLocal10, hLocal11, hLocal12, hLocal13, hLocalDestination]
    simp only [hHeapTop]
    have hFacts := Allocation.bumpFacts heapTop capacity
      st.mem.pages hFitMemory hPages
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simpa using hFacts.noOverflow)]
    wp_alloc_window [hParams, hLocals, hValues, hCapacityGet,
      hNot5, hNot9, hNot10, hNot11, hNot12, hNot13, hNot14,
      hNotDestination, hValid5, hValid9, hValid10, hValid11, hValid12,
      hValid13, hValid14, hValidDestination, hLocal4, hLocal8, hLocal9,
      hLocal10, hLocal11, hLocal12, hLocal13, hLocalDestination]
    rw [hMemory32]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simpa using hFacts.noGrow)]
    rw [wp_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    have hHeader0ToNat : (heapTop + 48 - 48).toNat = heapTop.toNat := by
      rw [UInt64.toNat_sub, UInt64.toNat_add]
      have h48 : (48 : UInt64).toNat = 48 := rfl
      rw [h48]
      have hSize : UInt64.size = 18446744073709551616 := rfl
      omega
    have hTwo32 : 2 ^ 32 = 4294967296 := by norm_num
    have hBaseBound : heapTop.toNat % 4294967296 + 8 ≤
        st.mem.pages * 65536 := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hBase8Bound : (heapTop + 48 - 40).toNat % 4294967296 + 8 ≤
        st.mem.pages * 65536 := by
      rw [hFacts.header40ToNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hBase16Bound : (heapTop + 48 - 32).toNat % 4294967296 + 8 ≤
        st.mem.pages * 65536 := by
      rw [hFacts.header32ToNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hBase24Bound : (heapTop + 48 - 24).toNat % 4294967296 + 8 ≤
        st.mem.pages * 65536 := by
      rw [hFacts.header24ToNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hBase32Bound : (heapTop + 48 - 16).toNat % 4294967296 + 8 ≤
        st.mem.pages * 65536 := by
      rw [hFacts.header16ToNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hBase40Bound : (heapTop + 48 - 8).toNat % 4294967296 + 8 ≤
        st.mem.pages * 65536 := by
      rw [hFacts.header8ToNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hBaseBound32 :
        (UInt32.ofNat (heapTop.toNat % 4294967296)).toNat + 8 ≤
          st.mem.pages * 65536 := by
      simpa using hBaseBound
    have hBase8Bound32 :
        (UInt32.ofNat ((heapTop.toNat + 8) % 4294967296)).toNat + 8 ≤
          st.mem.pages * 65536 := by
      simpa [hFacts.header40ToNat] using hBase8Bound
    have hBase16Bound32 :
        (UInt32.ofNat ((heapTop.toNat + 16) % 4294967296)).toNat + 8 ≤
          st.mem.pages * 65536 := by
      simpa [hFacts.header32ToNat] using hBase16Bound
    have hBase24Bound32 :
        (UInt32.ofNat ((heapTop.toNat + 24) % 4294967296)).toNat + 8 ≤
          st.mem.pages * 65536 := by
      simpa [hFacts.header24ToNat] using hBase24Bound
    have hBase32Bound32 :
        (UInt32.ofNat ((heapTop.toNat + 32) % 4294967296)).toNat + 8 ≤
          st.mem.pages * 65536 := by
      simpa [hFacts.header16ToNat] using hBase32Bound
    have hBase40Bound32 :
        (UInt32.ofNat ((heapTop.toNat + 40) % 4294967296)).toNat + 8 ≤
          st.mem.pages * 65536 := by
      simpa [hFacts.header8ToNat] using hBase40Bound
    wp_alloc_to_store [hHeapTop, hParams, hLocals, hValues,
      hCapacityLocal, hCapacityGet,
      hNot5, hNot9, hNot10, hNot11, hNot12, hNot13, hNot14,
      hNotDestination, hValid5, hValid9, hValid10, hValid11, hValid12,
      hValid13, hValid14, hValidDestination, hLocal4, hLocal8, hLocal9,
      hLocal10, hLocal11, hLocal12, hLocal13, hLocalDestination,
      hHeader0ToNat]
    simp only [wp_store64_cons, hTwo32, UInt32.toNat_zero, Nat.add_zero]
    rw [if_neg (Nat.not_lt.mpr hBaseBound32)]
    wp_alloc_to_store [hParams, hLocals, hValues, hCapacityLocal,
      hCapacityGet, hNot5, hNot9, hNot10, hNot11, hNot12, hNot13,
      hNot14, hNotDestination, hValid5, hValid9, hValid10, hValid11,
      hValid12, hValid13, hValid14, hValidDestination, hLocal4, hLocal8,
      hLocal9, hLocal10, hLocal11, hLocal12, hLocal13,
      hLocalDestination, hFacts.header40ToNat]
    simp only [wp_store64_cons, hTwo32, UInt32.toNat_zero, Nat.add_zero,
      Mem.write64_pages]
    rw [if_neg (Nat.not_lt.mpr hBase8Bound32)]
    wp_alloc_to_store [hParams, hLocals, hValues, hCapacityLocal,
      hCapacityGet, hNot5, hNot9, hNot10, hNot11, hNot12, hNot13,
      hNot14, hNotDestination, hValid5, hValid9, hValid10, hValid11,
      hValid12, hValid13, hValid14, hValidDestination, hLocal4, hLocal8,
      hLocal9, hLocal10, hLocal11, hLocal12, hLocal13,
      hLocalDestination, hFacts.header32ToNat]
    simp only [wp_store64_cons, hTwo32, UInt32.toNat_zero, Nat.add_zero,
      Mem.write64_pages]
    rw [if_neg (Nat.not_lt.mpr hBase16Bound32)]
    wp_alloc_to_store [hParams, hLocals, hValues, hCapacityLocal,
      hCapacityGet, hNot5, hNot9, hNot10, hNot11, hNot12, hNot13,
      hNot14, hNotDestination, hValid5, hValid9, hValid10, hValid11,
      hValid12, hValid13, hValid14, hValidDestination, hLocal4, hLocal8,
      hLocal9, hLocal10, hLocal11, hLocal12, hLocal13,
      hLocalDestination, hFacts.header24ToNat]
    simp only [wp_store64_cons, hTwo32, UInt32.toNat_zero, Nat.add_zero,
      Mem.write64_pages]
    rw [if_neg (Nat.not_lt.mpr hBase24Bound32)]
    wp_alloc_to_store [hParams, hLocals, hValues, hCapacityLocal,
      hCapacityGet, hNot5, hNot9, hNot10, hNot11, hNot12, hNot13,
      hNot14, hNotDestination, hValid5, hValid9, hValid10, hValid11,
      hValid12, hValid13, hValid14, hValidDestination, hLocal4, hLocal8,
      hLocal9, hLocal10, hLocal11, hLocal12, hLocal13,
      hLocalDestination, hFacts.header16ToNat]
    simp only [wp_store64_cons, hTwo32, UInt32.toNat_zero, Nat.add_zero,
      Mem.write64_pages]
    rw [if_neg (Nat.not_lt.mpr hBase32Bound32)]
    wp_alloc_to_store [hParams, hLocals, hValues, hCapacityLocal,
      hCapacityGet, hNot5, hNot9, hNot10, hNot11, hNot12, hNot13,
      hNot14, hNotDestination, hValid5, hValid9, hValid10, hValid11,
      hValid12, hValid13, hValid14, hValidDestination, hLocal4, hLocal8,
      hLocal9, hLocal10, hLocal11, hLocal12, hLocal13,
      hLocalDestination, hFacts.header8ToNat]
    simp only [wp_store64_cons, hTwo32, UInt32.toNat_zero, Nat.add_zero,
      Mem.write64_pages]
    rw [if_neg (Nat.not_lt.mpr hBase40Bound32)]
    rw [wp_nil]
    wp_alloc_window [hAllocs, hParams, hLocals, hValues, hCapacityGet,
      hNot5, hNot9, hNot10, hNot11, hNot12, hNot13, hNot14,
      hNotDestination, hValid5, hValid9, hValid10, hValid11, hValid12,
      hValid13, hValid14, hValidDestination, hLocal4, hLocal8, hLocal9,
      hLocal10, hLocal11, hLocal12, hLocal13, hLocalDestination]
    simpa only [FixedArrayAllocator.allocStore, validAllocatorFrame,
      FixedArrayAllocator.headerMem, Memory.toUInt32_eq_ofNat,
      hFacts.rootToNat, hFacts.header40ToNat, hFacts.header32ToNat,
      hFacts.header24ToNat, hFacts.header16ToNat, hFacts.header8ToNat,
      hValues] using hNext

set_option Elab.async false in
theorem wrapperProgram_spec
    (maximumSize : Nat) (threshold : UInt64)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (inputPtr : UInt64) (input : Array UInt64)
    (heapTop allocs : UInt64)
    (hMaximumSize : maximumSize < UInt64.size)
    (hInput : UInt64Array.At initial inputPtr input)
    (hInputBelow : inputPtr.toNat + 8 * (input.size + 1) ≤ heapTop.toNat)
    (hHeapFitMemory : heapTop.toNat + heapReserveBytes maximumSize input ≤
      initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hMemory32 : module_.memIs64 = false)
    (hHeapTop : initial.globals.globals[0]? = some (.i64 heapTop))
    (hFreeList : initial.globals.globals[1]? = some (.i64 0))
    (hAllocs : initial.globals.globals[2]? = some (.i64 allocs)) :
    wp module_ (wrapperProgram maximumSize threshold)
      (FixedArrayPairResult.publicPost
        (expected maximumSize threshold input))
      initial (entryFrame inputPtr) env := by
  unfold wrapperProgram
  apply FixedArrayLengthDispatch.leProgram_spec 5 maximumSize _ _ _
    module_ env initial
    (entryFrame inputPtr) inputPtr input
  · rfl
  · rfl
  · decide
  · simp [entryFrame]
  · exact hMaximumSize
  · exact hInput
  · intro hSize
    have hExpected : expected maximumSize threshold input =
        input.filter fun element => element < threshold := by
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
      simpa [heapReserveBytes, hSize, Nat.add_assoc] using hHeapFitMemory
    change wp module_ (validProgram threshold) _
      initial
      { params := [.i64 inputPtr]
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 inputPtr,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0]
        values := [] } env
    unfold validProgram validPrefix
    simp only [List.cons_append, List.nil_append]
    wp_run
    simp [hInput.pointerAddress_eq, hInput.lengthRead]
    rw [if_neg (Nat.not_lt.mpr hInput.generatedLengthBound)]
    rw [if_neg (Nat.not_lt.mpr hInput.generatedLengthBound)]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simpa [capacity] using hCapacityU)]
    rw [wp_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    change wp module_
      (validAllocatorRegion ++ filterSuffix threshold) _ initial
      { params := [.i64 inputPtr]
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 inputPtr,
          .i64 (UInt64.ofNat input.size), .i64 0,
          .i64 (UInt64.ofNat input.size), .i64 0, .i64 0, .i64 0,
          .i64 (UInt64.ofNat input.size), .i64 0, .i64 0, .i64 capacity,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
        values := [] } env
    apply validAllocatorRegion_spec
      module_ env initial _
      heapTop capacity allocs
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
      unfold filterSuffix
      wp_run
      simp [validAllocatorFrame]
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      simp
      refine ?_
      · apply wp_block_cons
        apply wp_loop_cons
          (Inv := validInv initial inputPtr heapTop capacity threshold input)
          (μ := validMeasure input)
        · unfold validInv
          refine ⟨0, 0, Nat.zero_le _, ?_, ?_, ?_, ?_⟩
          · simp [validFrame, keptPrefix]
          · simp [FixedArrayAllocator.allocStore_pages]
          · exact FixedArrayPairResult.input_preserved_by_alloc
              initial heapTop capacity 1 allocs inputPtr input hInput
              hInputBelow hFitCapacity hPages
          · intro i hi
            simp [keptPrefix] at hi
        · rintro st frame
            ⟨index, last, hIndex, rfl, hCurrentPages, hCurrentInput,
              hPayload⟩
          have hIndexNat : (UInt64.ofNat index).toNat = index := by
            apply UInt64.toNat_ofNat_of_lt'
            have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
            omega
          simp only [validFrame]
          wp_run
          simp
          by_cases hDone : index = input.size
          · subst index
            have hGuard :
                (if UInt64.ofNat input.size ≤ UInt64.ofNat input.size
                  then (1 : UInt32) else 0) = 1 := by
              simp
            rw [hGuard]
            let hOutput := keptPrefix threshold input input.size
            have hOutputEq : hOutput =
                input.filter fun element => element < threshold := by
              simpa [hOutput] using keptPrefix_all threshold input
            have hOutputSize : hOutput.size ≤ input.size := by
              rw [hOutputEq]
              exact Array.size_filter_le
            have hOutputLengthBound :
                (heapTop.toNat + 48) % 4294967296 + 8 ≤
                  st.mem.pages * 65536 := by
              rw [Nat.mod_eq_of_lt, hCurrentPages]
              · omega
              · have hFit := hBump.fit32
                omega
            simp only [FixedArrayEqNode.branchPost]
            wp_run
            simp
            rw [if_neg (Nat.not_lt.mpr hOutputLengthBound)]
            rw [hRootAddress]
            refine ⟨heapTop + 48, ?_, ?_⟩
            · rfl
            · rw [hExpected, ← hOutputEq]
              refine ⟨?_, ?_, ?_, ?_⟩
              · rw [hBump.rootToNat]
                have hFit := hBump.fit32
                omega
              · rw [hBump.rootToNat, Mem.write64_pages, hCurrentPages]
                rw [hCapacityNat] at hFitCapacity
                omega
              · exact Mem.read64_write64_same ..
              · intro i hi
                calc
                  (st.mem.write64 (heapTop + 48).toUInt32
                      (UInt64.ofNat hOutput.size)).read64
                      (heapTop + 48 + UInt64.ofNat (8 * (i + 1))).toUInt32 =
                      st.mem.read64
                        (heapTop + 48 + UInt64.ofNat (8 * (i + 1))).toUInt32 := by
                        apply Memory.read64_write64_disjoint
                        right
                        rw [show (heapTop + 48).toUInt32.toNat =
                            heapTop.toNat + 48 by
                          simpa using hBump.wordAddress_toNat 0 hCapacity]
                        have hWordFit :
                            8 * (i + 1 + 1) ≤ capacity.toNat := by
                          rw [hCapacityNat]
                          omega
                        rw [hBump.wordAddress_toNat (i + 1) hWordFit]
                        omega
                  _ = hOutput[i] := hPayload i (by simpa [hOutput] using hi)
          · have hIndexLt : index < input.size := by omega
            have hNotGe : ¬UInt64.ofNat input.size ≤ UInt64.ofNat index := by
              rw [UInt64.le_iff_toNat_le,
                UInt64.toNat_ofNat_of_lt' hCurrentInput.size_lt, hIndexNat]
              omega
            rw [if_neg hNotGe]
            simp
            obtain ⟨hLoadBound, hLoadRead⟩ :=
              hCurrentInput.generatedElement index hIndexLt
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
            rw [hLoadRead']
            by_cases hKeep : input[index]! < threshold
            · have hPrefixSucc :=
                keptPrefix_succ_pos threshold input index hIndexLt hKeep
              have hPrefixSize :=
                keptPrefix_size_le threshold input index (by omega)
              have hCountSucc :
                  UInt64.ofNat (keptPrefix threshold input index).size + 1 =
                    UInt64.ofNat
                      ((keptPrefix threshold input index).push input[index]!).size := by
                rw [Array.size_push]
                apply UInt64.toNat.inj
                rw [UInt64.toNat_add,
                  UInt64.toNat_ofNat_of_lt' (by
                    have hUInt64Size : UInt64.size =
                        18446744073709551616 := rfl
                    omega)]
                have hOne : (1 : UInt64).toNat = 1 := rfl
                rw [hOne,
                  UInt64.toNat_ofNat_of_lt' (by
                    have hUInt64Size : UInt64.size =
                        18446744073709551616 := rfl
                    omega), Nat.mod_eq_of_lt]
                omega
              have hWordFit :
                  8 * ((keptPrefix threshold input index).size + 1 + 1) ≤
                    capacity.toNat := by
                rw [hCapacityNat]
                omega
              have hOutputAddress :
                  UInt32.ofNat
                      ((heapTop.toNat + 48 +
                        ((keptPrefix threshold input index).size + 1) * 8) %
                          4294967296) =
                    (heapTop + 48 + UInt64.ofNat
                      (8 * ((keptPrefix threshold input index).size + 1))).toUInt32 := by
                have hRoot64 : heapTop.toNat + 48 < 18446744073709551616 := by
                  have hFit := hBump.fit32
                  omega
                simpa [Nat.mod_eq_of_lt hRoot64, Nat.mul_comm, Nat.add_assoc]
                  using hBump.wordAddress
                    ((keptPrefix threshold input index).size + 1) hWordFit
              have hStoreBound :
                  (heapTop + 48 + UInt64.ofNat
                    (8 * ((keptPrefix threshold input index).size + 1))).toUInt32.toNat + 8 ≤
                      st.mem.pages * 65536 := by
                rw [hBump.wordAddress_toNat
                  ((keptPrefix threshold input index).size + 1) hWordFit,
                  hCurrentPages]
                omega
              have hGeneratedStoreBound :
                  (heapTop.toNat + 48 +
                    ((keptPrefix threshold input index).size + 1) * 8) %
                      4294967296 + 8 ≤ st.mem.pages * 65536 := by
                rw [Nat.mod_eq_of_lt, hCurrentPages]
                · omega
                · have hFit := hBump.fit32
                  omega
              simp [hKeep]
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp)]
              wp_run
              simp
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp)]
              wp_run
              simp
              rw [hOutputAddress]
              rw [if_neg (Nat.not_lt.mpr hGeneratedStoreBound)]
              refine ⟨?_, ?_⟩
              · unfold validInv
                refine ⟨index + 1, input[index]!, by omega, ?_, ?_, ?_, ?_⟩
                · simpa only [validFrame, hPrefixSucc, hIndexSucc, hCountSucc]
                · simpa [Mem.write64_pages] using hCurrentPages
                · apply hCurrentInput.write64After
                  rw [hBump.wordAddress_toNat
                    ((keptPrefix threshold input index).size + 1) hWordFit]
                  omega
                · intro i hiNext
                  have hi : i <
                      ((keptPrefix threshold input index).push input[index]!).size := by
                    simpa only [hPrefixSucc] using hiNext
                  have hRead :
                      (st.mem.write64
                          (heapTop + 48 + UInt64.ofNat
                            (8 * ((keptPrefix threshold input index).size + 1))).toUInt32
                          input[index]!).read64
                          (heapTop + 48 + UInt64.ofNat (8 * (i + 1))).toUInt32 =
                        ((keptPrefix threshold input index).push input[index]!)[i] := by
                    by_cases hEq : i = (keptPrefix threshold input index).size
                    · subst i
                      simpa [hIndexLt] using
                        (Mem.read64_write64_same st.mem
                          (heapTop + 48 + UInt64.ofNat
                            (8 * ((keptPrefix threshold input index).size + 1))).toUInt32
                          input[index]!)
                    · have hiOld : i < (keptPrefix threshold input index).size := by
                        rw [Array.size_push] at hi
                        omega
                      have hWordFitI :
                          8 * (i + 1 + 1) ≤ capacity.toNat := by
                        rw [hCapacityNat]
                        omega
                      calc
                        (st.mem.write64
                            (heapTop + 48 + UInt64.ofNat
                              (8 * ((keptPrefix threshold input index).size + 1))).toUInt32
                            input[index]!).read64
                            (heapTop + 48 + UInt64.ofNat (8 * (i + 1))).toUInt32 =
                            st.mem.read64
                              (heapTop + 48 + UInt64.ofNat (8 * (i + 1))).toUInt32 := by
                              apply Memory.read64_write64_disjoint
                              left
                              rw [hBump.wordAddress_toNat (i + 1) hWordFitI,
                                hBump.wordAddress_toNat
                                  ((keptPrefix threshold input index).size + 1) hWordFit]
                              omega
                        _ = (keptPrefix threshold input index)[i] := hPayload i hiOld
                        _ = ((keptPrefix threshold input index).push input[index]!)[i] := by
                          exact (Array.getElem_push_lt hiOld).symm
                  simpa only [hPrefixSucc] using hRead
              · simp [validMeasure, hIndexNat]
                omega
            · have hPrefixSucc :=
                keptPrefix_succ_neg threshold input index hIndexLt hKeep
              simp [hKeep]
              refine wp_iff_cons rfl ?_
              rw [if_neg (by simp)]
              wp_run
              simp
              refine wp_iff_cons rfl ?_
              rw [if_neg (by simp)]
              rw [wp_nil]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              wp_run
              refine ⟨?_, ?_⟩
              · unfold validInv
                refine ⟨index + 1, input[index]!, by omega, ?_,
                  hCurrentPages, hCurrentInput, ?_⟩
                · simp only [validFrame, hPrefixSucc, hIndexSucc]
                  simp [List.set]
                · simpa [hPrefixSucc] using hPayload
              · simp [validMeasure, hIndexNat]
                omega
  · intro hSize
    have hExpected : expected maximumSize threshold input = #[] := by
      simp [expected, hSize]
    have hFitEmpty : heapTop.toNat + 48 + 8 ≤
        initial.mem.pages * 65536 := by
      simpa [heapReserveBytes, hSize] using hHeapFitMemory
    change wp module_ emptyProgram _
      initial
      { params := [.i64 inputPtr]
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 inputPtr,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
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
      (FixedArrayAllocatorWindow.region 0 1 ++ emptySuffix) _ initial
      { params := [.i64 inputPtr]
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 inputPtr,
          .i64 0, .i64 0, .i64 0, .i64 8, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0]
        values := [] } env
    apply FixedArrayAllocatorWindow.region_spec_withTail 0 7
      module_ env initial _
      heapTop 8 1 allocs
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

end Project.ProofKit.FixedArrayFilterLt
