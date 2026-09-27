import Project.ProofKit.FixedArrayAllocatorBase

namespace Project.ProofKit.FixedArrayAllocator
open Wasm

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1048576 in
set_option Elab.async false in
theorem region_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit) (frame : Locals)
    (heapTop capacity stride allocs : UInt64)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 14)
    (hValues : frame.values = [])
    (hCapacityLocal : frame.locals[8]? = some (.i64 capacity))
    (hCapacity : 8 ≤ capacity.toNat)
    (hFitMemory : heapTop.toNat + 48 + capacity.toNat ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hMemory32 : module_.memIs64 = false)
    (hHeapTop : st.globals.globals[0]? = some (.i64 heapTop))
    (hFreeList : st.globals.globals[1]? = some (.i64 0))
    (hAllocs : st.globals.globals[2]? = some (.i64 allocs))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (allocStore st heapTop capacity stride allocs)
      (allocFrame frame heapTop capacity) env) :
    wp module_ (region stride ++ rest) Q st frame env := by
  have hCapacityGet : frame.locals[8] = .i64 capacity := by
    have h := hCapacityLocal
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  simp only [region, search, bump, finish, List.cons_append, List.nil_append]
  wp_alloc_run [hParams, hLocals, hValues, hCapacityGet]
  simp only [hFreeList]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st' s => st' = st ∧ s = searchFrame frame)
    (μ := fun _ _ => 0)
  · refine ⟨rfl, ?_⟩
    simp [searchFrame, hValues]
  · rintro st1 s1 ⟨hSt, hFrame⟩
    subst st1
    subst s1
    simp only [searchBody, searchFrame]
    wp_alloc_run [hParams, hLocals, hValues, hCapacityGet]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_alloc_run [hParams, hLocals, hValues, hCapacityGet]
    simp only [hHeapTop]
    have hFacts := Project.ProofKit.Allocation.bumpFacts heapTop capacity
      st.mem.pages hFitMemory hPages
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simpa using hFacts.noOverflow)]
    wp_alloc_run [hParams, hLocals, hValues, hCapacityGet]
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
      hCapacityLocal, hCapacityGet, hHeader0ToNat]
    simp only [wp_store64_cons, hTwo32, UInt32.toNat_zero, Nat.add_zero]
    rw [if_neg (Nat.not_lt.mpr hBaseBound32)]
    wp_alloc_to_store [hParams, hLocals, hValues, hCapacityLocal,
      hCapacityGet, hFacts.header40ToNat]
    simp only [wp_store64_cons, hTwo32, UInt32.toNat_zero, Nat.add_zero,
      Mem.write64_pages]
    rw [if_neg (Nat.not_lt.mpr hBase8Bound32)]
    wp_alloc_to_store [hParams, hLocals, hValues, hCapacityLocal,
      hCapacityGet, hFacts.header32ToNat]
    simp only [wp_store64_cons, hTwo32, UInt32.toNat_zero, Nat.add_zero,
      Mem.write64_pages]
    rw [if_neg (Nat.not_lt.mpr hBase16Bound32)]
    wp_alloc_to_store [hParams, hLocals, hValues, hCapacityLocal,
      hCapacityGet, hFacts.header24ToNat]
    simp only [wp_store64_cons, hTwo32, UInt32.toNat_zero, Nat.add_zero,
      Mem.write64_pages]
    rw [if_neg (Nat.not_lt.mpr hBase24Bound32)]
    wp_alloc_to_store [hParams, hLocals, hValues, hCapacityLocal,
      hCapacityGet, hFacts.header16ToNat]
    simp only [wp_store64_cons, hTwo32, UInt32.toNat_zero, Nat.add_zero,
      Mem.write64_pages]
    rw [if_neg (Nat.not_lt.mpr hBase32Bound32)]
    wp_alloc_to_store [hParams, hLocals, hValues, hCapacityLocal,
      hCapacityGet, hFacts.header8ToNat]
    simp only [wp_store64_cons, hTwo32, UInt32.toNat_zero, Nat.add_zero,
      Mem.write64_pages]
    rw [if_neg (Nat.not_lt.mpr hBase40Bound32)]
    rw [wp_nil]
    wp_alloc_run [hAllocs, hParams, hLocals, hValues, hCapacityGet]
    simpa only [allocStore, allocFrame, headerMem,
      Project.ProofKit.Memory.toUInt32_eq_ofNat, hFacts.rootToNat,
      hFacts.header40ToNat, hFacts.header32ToNat, hFacts.header24ToNat,
      hFacts.header16ToNat, hFacts.header8ToNat, hValues] using hNext

end Project.ProofKit.FixedArrayAllocator
