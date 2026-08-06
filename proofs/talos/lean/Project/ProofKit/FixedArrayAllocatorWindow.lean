import Project.ProofKit.FixedArrayAllocator

namespace Project.ProofKit.FixedArrayAllocatorWindow

open Wasm

theorem add_succ_sub_one (offset k : Nat) :
    offset + (k + 1) - 1 = offset + k := by
  omega

macro "wp_alloc_window" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 10000000 }) (discharger := omega) [wp_simp,
      Wasm.Locals.get, Wasm.Locals.set?, Wasm.Locals.validIndex,
      Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.Function.numLocals,
      List.take, List.drop, List.replicate, List.length, List.map,
      List.length_set, List.getElem?_set,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
      Wasm.ValueType.zero, List.headD, $ts,*])

macro "wp_alloc_to_store" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 10000000 }) (discharger := omega) only [
      wp_globalGet_cons, wp_globalSet_cons,
      wp_localGet_cons, wp_localSet_cons,
      wp_constI64_cons, wp_addI64_cons, wp_subI64_cons, wp_wrapI64_cons,
      Wasm.Locals.get, Wasm.Locals.set?, Wasm.Locals.validIndex,
      List.length_set, List.getElem?_set, Nat.reduceAdd, Nat.reduceLT,
      Nat.reduceLeDiff, Nat.reduceSub, add_succ_sub_one,
      Nat.add_left_cancel_iff, Nat.add_lt_add_iff_left, Nat.reduceEqDiff,
      if_true, if_false, $ts,*])

def searchBody (offset : Nat) (stride : UInt64) : Wasm.Program :=
  [
  .localGet (offset + 11),
  .constI64 0,
  .eqI64,
  .br_if 1,
  .localGet (offset + 14),
  .constI64 0,
  .neI64,
  .br_if 1,
  .localGet (offset + 11),
  .constI64 32,
  .subI64,
  .wrapI64,
  .load64 0,
  .localSet (offset + 12),
  .localGet (offset + 11),
  .constI64 8,
  .subI64,
  .wrapI64,
  .load64 0,
  .localSet (offset + 13),
  .localGet (offset + 12),
  .localGet (offset + 9),
  .geUI64,
  .iff 0 0 [
    .localGet (offset + 10),
    .constI64 0,
    .eqI64,
    .iff 0 0 [
      .localGet (offset + 13),
      .globalSet 1
    ] [
      .localGet (offset + 10),
      .constI64 8,
      .subI64,
      .wrapI64,
      .localGet (offset + 13),
      .store64 0
    ],
    .localGet (offset + 11),
    .constI64 48,
    .subI64,
    .wrapI64,
    .constI64 5501223100278326855,
    .store64 0,
    .localGet (offset + 11),
    .constI64 40,
    .subI64,
    .wrapI64,
    .constI64 1,
    .store64 0,
    .localGet (offset + 11),
    .constI64 32,
    .subI64,
    .wrapI64,
    .localGet (offset + 12),
    .store64 0,
    .localGet (offset + 11),
    .constI64 24,
    .subI64,
    .wrapI64,
    .constI64 2,
    .store64 0,
    .localGet (offset + 11),
    .constI64 16,
    .subI64,
    .wrapI64,
    .constI64 stride,
    .store64 0,
    .localGet (offset + 11),
    .constI64 8,
    .subI64,
    .wrapI64,
    .constI64 0,
    .store64 0,
    .localGet (offset + 11),
    .localSet (offset + 14)
  ] [
    .localGet (offset + 11),
    .localSet (offset + 10),
    .localGet (offset + 13),
    .localSet (offset + 11)
  ],
  .br 0
  ]

def search (offset : Nat) (stride : UInt64) : Wasm.Program :=
  [.block 0 0 [.loop 0 0 (searchBody offset stride)]]

def bump (offset : Nat) (stride : UInt64) : Wasm.Program :=
  [
  .localGet (offset + 14),
  .constI64 0,
  .eqI64,
  .iff 0 0 [
    .globalGet 0,
    .constI64 48,
    .addI64,
    .localGet (offset + 9),
    .addI64,
    .localSet (offset + 12),
    .localGet (offset + 12),
    .globalGet 0,
    .ltUI64,
    .iff 0 0 [.unreachable] [],
    .localGet (offset + 12),
    .constI64 1,
    .subI64,
    .constI64 65536,
    .divUI64,
    .constI64 1,
    .addI64,
    .localSet (offset + 13),
    .memorySize,
    .extendUI32,
    .localGet (offset + 13),
    .ltUI64,
    .iff 0 0 [
      .localGet (offset + 13),
      .memorySize,
      .extendUI32,
      .subI64,
      .wrapI64,
      .memoryGrow,
      .const 4294967295,
      .eq,
      .iff 0 0 [.unreachable] []
    ] [],
    .globalGet 0,
    .constI64 48,
    .addI64,
    .localSet (offset + 14),
    .localGet (offset + 12),
    .globalSet 0,
    .localGet (offset + 14),
    .constI64 48,
    .subI64,
    .wrapI64,
    .constI64 5501223100278326855,
    .store64 0,
    .localGet (offset + 14),
    .constI64 40,
    .subI64,
    .wrapI64,
    .constI64 1,
    .store64 0,
    .localGet (offset + 14),
    .constI64 32,
    .subI64,
    .wrapI64,
    .localGet (offset + 9),
    .store64 0,
    .localGet (offset + 14),
    .constI64 24,
    .subI64,
    .wrapI64,
    .constI64 2,
    .store64 0,
    .localGet (offset + 14),
    .constI64 16,
    .subI64,
    .wrapI64,
    .constI64 stride,
    .store64 0,
    .localGet (offset + 14),
    .constI64 8,
    .subI64,
    .wrapI64,
    .constI64 0,
    .store64 0
  ] []
  ]

def finish (offset : Nat) : Wasm.Program :=
  [
  .globalGet 2,
  .constI64 1,
  .addI64,
  .globalSet 2,
  .localGet (offset + 14),
  .localSet (offset + 5)
  ]

def region (offset : Nat) (stride : UInt64) : Wasm.Program :=
  [
  .constI64 0,
  .localSet (offset + 14),
  .constI64 0,
  .localSet (offset + 10),
  .globalGet 1,
  .localSet (offset + 11)
  ] ++ search offset stride ++ bump offset stride ++ finish offset

def searchFrame (offset : Nat) (base : Locals) : Locals :=
  { base with
    locals := ((base.locals.set (offset + 13) (.i64 0)).set
      (offset + 9) (.i64 0)).set (offset + 10) (.i64 0) }

def allocFrame (offset : Nat) (base : Locals)
    (heapTop capacity : UInt64) : Locals :=
  { base with
    locals := ((((((base.locals.set (offset + 13) (.i64 0)).set
      (offset + 9) (.i64 0)).set (offset + 10) (.i64 0)).set
      (offset + 11) (.i64 (heapTop + 48 + capacity))).set
      (offset + 12)
        (.i64 ((heapTop + 48 + capacity - 1) / 65536 + 1))).set
      (offset + 13) (.i64 (heapTop + 48))).set
      (offset + 4) (.i64 (heapTop + 48)) }

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem region_spec
    (offset : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit) (frame : Locals)
    (heapTop capacity stride allocs : UInt64)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = offset + 14)
    (hValues : frame.values = [])
    (hCapacityLocal : frame.locals[offset + 8]? = some (.i64 capacity))
    (hCapacity : 8 ≤ capacity.toNat)
    (hFitMemory : heapTop.toNat + 48 + capacity.toNat ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hMemory32 : module_.memIs64 = false)
    (hHeapTop : st.globals.globals[0]? = some (.i64 heapTop))
    (hFreeList : st.globals.globals[1]? = some (.i64 0))
    (hAllocs : st.globals.globals[2]? = some (.i64 allocs))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q
      (FixedArrayAllocator.allocStore st heapTop capacity stride allocs)
      (allocFrame offset frame heapTop capacity) env) :
    wp module_ (region offset stride ++ rest) Q st frame env := by
  have hNot5 : ¬offset + 5 < 1 := by omega
  have hNot9 : ¬offset + 9 < 1 := by omega
  have hNot10 : ¬offset + 10 < 1 := by omega
  have hNot11 : ¬offset + 11 < 1 := by omega
  have hNot12 : ¬offset + 12 < 1 := by omega
  have hNot13 : ¬offset + 13 < 1 := by omega
  have hNot14 : ¬offset + 14 < 1 := by omega
  have hValid5 : offset + 5 < 1 + (offset + 14) := by omega
  have hValid9 : offset + 9 < 1 + (offset + 14) := by omega
  have hValid10 : offset + 10 < 1 + (offset + 14) := by omega
  have hValid11 : offset + 11 < 1 + (offset + 14) := by omega
  have hValid12 : offset + 12 < 1 + (offset + 14) := by omega
  have hValid13 : offset + 13 < 1 + (offset + 14) := by omega
  have hValid14 : offset + 14 < 1 + (offset + 14) := by omega
  have hCapacityGet : frame.locals[offset + 8] = .i64 capacity := by
    have h := hCapacityLocal
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  simp only [region, search, bump, finish, List.cons_append, List.nil_append]
  wp_alloc_window [hParams, hLocals, hValues, hCapacityGet,
    hNot5, hNot9, hNot10, hNot11, hNot12, hNot13, hNot14,
    hValid5, hValid9, hValid10, hValid11, hValid12, hValid13, hValid14]
  simp only [hFreeList]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st' s => st' = st ∧ s = searchFrame offset frame)
    (μ := fun _ _ => 0)
  · refine ⟨rfl, ?_⟩
    simp (discharger := omega) [searchFrame, hValues]
  · rintro st1 s1 ⟨hSt, hFrame⟩
    subst st1
    subst s1
    simp only [searchBody, searchFrame]
    wp_alloc_window [hParams, hLocals, hValues, hCapacityGet,
      hNot5, hNot9, hNot10, hNot11, hNot12, hNot13, hNot14,
      hValid5, hValid9, hValid10, hValid11, hValid12, hValid13, hValid14]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_alloc_window [hParams, hLocals, hValues, hCapacityGet,
      hNot5, hNot9, hNot10, hNot11, hNot12, hNot13, hNot14,
      hValid5, hValid9, hValid10, hValid11, hValid12, hValid13, hValid14]
    simp only [hHeapTop]
    have hFacts := Allocation.bumpFacts heapTop capacity
      st.mem.pages hFitMemory hPages
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simpa using hFacts.noOverflow)]
    wp_alloc_window [hParams, hLocals, hValues, hCapacityGet,
      hNot5, hNot9, hNot10, hNot11, hNot12, hNot13, hNot14,
      hValid5, hValid9, hValid10, hValid11, hValid12, hValid13, hValid14]
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
      hValid5, hValid9, hValid10, hValid11, hValid12, hValid13, hValid14,
      hHeader0ToNat]
    simp only [wp_store64_cons, hTwo32, UInt32.toNat_zero, Nat.add_zero]
    rw [if_neg (Nat.not_lt.mpr hBaseBound32)]
    wp_alloc_to_store [hParams, hLocals, hValues, hCapacityLocal, hCapacityGet,
      hNot5, hNot9, hNot10, hNot11, hNot12, hNot13, hNot14,
      hValid5, hValid9, hValid10, hValid11, hValid12, hValid13, hValid14,
      hFacts.header40ToNat]
    simp only [wp_store64_cons, hTwo32, UInt32.toNat_zero, Nat.add_zero,
      Mem.write64_pages]
    rw [if_neg (Nat.not_lt.mpr hBase8Bound32)]
    wp_alloc_to_store [hParams, hLocals, hValues, hCapacityLocal, hCapacityGet,
      hNot5, hNot9, hNot10, hNot11, hNot12, hNot13, hNot14,
      hValid5, hValid9, hValid10, hValid11, hValid12, hValid13, hValid14,
      hFacts.header32ToNat]
    simp only [wp_store64_cons, hTwo32, UInt32.toNat_zero, Nat.add_zero,
      Mem.write64_pages]
    rw [if_neg (Nat.not_lt.mpr hBase16Bound32)]
    wp_alloc_to_store [hParams, hLocals, hValues, hCapacityLocal, hCapacityGet,
      hNot5, hNot9, hNot10, hNot11, hNot12, hNot13, hNot14,
      hValid5, hValid9, hValid10, hValid11, hValid12, hValid13, hValid14,
      hFacts.header24ToNat]
    simp only [wp_store64_cons, hTwo32, UInt32.toNat_zero, Nat.add_zero,
      Mem.write64_pages]
    rw [if_neg (Nat.not_lt.mpr hBase24Bound32)]
    wp_alloc_to_store [hParams, hLocals, hValues, hCapacityLocal, hCapacityGet,
      hNot5, hNot9, hNot10, hNot11, hNot12, hNot13, hNot14,
      hValid5, hValid9, hValid10, hValid11, hValid12, hValid13, hValid14,
      hFacts.header16ToNat]
    simp only [wp_store64_cons, hTwo32, UInt32.toNat_zero, Nat.add_zero,
      Mem.write64_pages]
    rw [if_neg (Nat.not_lt.mpr hBase32Bound32)]
    wp_alloc_to_store [hParams, hLocals, hValues, hCapacityLocal, hCapacityGet,
      hNot5, hNot9, hNot10, hNot11, hNot12, hNot13, hNot14,
      hValid5, hValid9, hValid10, hValid11, hValid12, hValid13, hValid14,
      hFacts.header8ToNat]
    simp only [wp_store64_cons, hTwo32, UInt32.toNat_zero, Nat.add_zero,
      Mem.write64_pages]
    rw [if_neg (Nat.not_lt.mpr hBase40Bound32)]
    rw [wp_nil]
    wp_alloc_window [hAllocs, hParams, hLocals, hValues, hCapacityGet,
      hNot5, hNot9, hNot10, hNot11, hNot12, hNot13, hNot14,
      hValid5, hValid9, hValid10, hValid11, hValid12, hValid13, hValid14]
    simpa only [FixedArrayAllocator.allocStore, allocFrame,
      FixedArrayAllocator.headerMem,
      Memory.toUInt32_eq_ofNat, hFacts.rootToNat,
      hFacts.header40ToNat, hFacts.header32ToNat, hFacts.header24ToNat,
      hFacts.header16ToNat, hFacts.header8ToNat, hValues] using hNext

end Project.ProofKit.FixedArrayAllocatorWindow
