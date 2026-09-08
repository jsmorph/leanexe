import Project.EulerGridStep.AllocationHeader

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def fieldSearchFrame (base : Locals) : Locals :=
  { base with locals := ((base.locals.set 19 (.i64 0)).set 15 (.i64 0)).set 16 (.i64 0) }

def fieldBumpFrame (base : Locals) (heapTop capacity : UInt64) : Locals :=
  { base with
    locals := ((((((base.locals.set 19 (.i64 0)).set 15 (.i64 0)).set 16 (.i64 0)).set
      17 (.i64 (heapTop + 48 + capacity))).set
      18 (.i64 ((heapTop + 48 + capacity - 1) / 65536 + 1))).set
      19 (.i64 (heapTop + 48))), values := [] }

def fieldAllocFrame (base : Locals) (heapTop capacity : UInt64) : Locals :=
  { fieldBumpFrame base heapTop capacity with
    locals := (fieldBumpFrame base heapTop capacity).locals.set 9 (.i64 (heapTop + 48)) }

def fieldBumpedStore (initial : Store Unit) (heapTop capacity : UInt64) : Store Unit :=
  { initial with globals := { globals := initial.globals.globals.set 0 (.i64 (heapTop + 48 + capacity)) } }

/-- Fresh allocation with empty free list and sufficient existing memory. -/
theorem field_allocation_bump_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit) (frame : Locals)
    (heapTop capacity allocs : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 20)
    (hValues : frame.values = [])
    (hCapacityLocal : frame.locals[14]? = some (.i64 capacity))
    (hCapacity : 8 ≤ capacity.toNat)
    (hFitMemory : heapTop.toNat + 48 + capacity.toNat ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536) (hMemory32 : module_.memIs64 = false)
    (hHeapTop : st.globals.globals[0]? = some (.i64 heapTop))
    (hFreeList : st.globals.globals[1]? = some (.i64 0))
    (hAllocs : st.globals.globals[2]? = some (.i64 allocs))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q
      (FixedArrayAllocator.allocStore st heapTop capacity 1 allocs)
      (fieldAllocFrame frame heapTop capacity) env) :
    wp module_ (fieldAllocationRegion ++ rest) Q st frame env := by
  have hCapacityGet : frame.locals[14] = .i64 capacity := by
    have h := hCapacityLocal
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  simp only [fieldAllocationRegion, search, List.cons_append, List.nil_append]
  rw [field_bump_header_shape]
  wp_alloc_window_lists [fieldBumpBody, fieldAcceptedBody, func27, hParams, hLocals, hValues, hCapacityGet]
  simp only [hFreeList]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st' s => st' = st ∧ s = fieldSearchFrame frame)
    (μ := fun _ _ => 0)
  · refine ⟨rfl, ?_⟩
    simp (discharger := omega) [fieldSearchFrame, hValues]
  · rintro st1 s1 ⟨hSt, hFrame⟩
    subst st1
    subst s1
    simp only [searchBody, fieldSearchFrame]
    wp_alloc_window_lists [fieldBumpBody, fieldAcceptedBody, func27, hParams, hLocals, hValues, hCapacityGet]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by simp)]
    wp_alloc_window_lists [fieldBumpBody, fieldAcceptedBody, func27, hParams, hLocals, hValues, hCapacityGet]
    simp only [hHeapTop]
    have hFacts := Allocation.bumpFacts heapTop capacity
      st.mem.pages hFitMemory hPages
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simpa using hFacts.noOverflow)]
    wp_alloc_window_lists [fieldBumpBody, fieldAcceptedBody, func27, hParams, hLocals, hValues, hCapacityGet]
    rw [hMemory32]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simpa using hFacts.noGrow)]
    rw [wp_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    wp_alloc_window_lists [hHeapTop, hParams, hLocals, hValues, hCapacityGet]
    change wp module_ (fieldHeaderStores ++ []) _ (fieldBumpedStore st heapTop capacity)
      (fieldBumpFrame frame heapTop capacity) env
    apply allocation_header_spec module_ env (fieldBumpedStore st heapTop capacity)
      (fieldBumpFrame frame heapTop capacity) (heapTop + 48) capacity
      (by simp [fieldBumpFrame, Wasm.Locals.get, hParams, hLocals])
      (by simp [fieldBumpFrame, Wasm.Locals.get, hParams, hLocals, hCapacityGet])
      rfl
      (by rw [hFacts.rootToNat]; omega)
      (by rw [hFacts.rootToNat]; have := hFacts.fit32; omega)
      (by change (heapTop + 48).toNat ≤ st.mem.pages * 65536; rw [hFacts.rootToNat]; omega)
      _ []
    rw [wp_nil]
    have hHeaderGlobals :
        (writeAllocationHeader (fieldBumpedStore st heapTop capacity) (heapTop + 48) capacity).globals =
          (fieldBumpedStore st heapTop capacity).globals := rfl
    wp_alloc_window_lists [hHeaderGlobals, fieldBumpedStore,
      fieldBumpFrame, hAllocs, hParams, hLocals, hValues, hCapacityGet]
    have hBumpedAllocs :
        (st.globals.globals.set 0 (.i64 (heapTop + 48 + capacity)))[2]? = some (.i64 allocs) := by
      simp [hAllocs]
    have hHeader0ToNat : (heapTop + 48 - 48).toNat = heapTop.toNat := by
      have h := Allocation.root_sub_toNat heapTop 48 (by have := hFacts.fit32; omega) (by decide)
      simpa using h
    simpa only [FixedArrayAllocator.allocStore, fieldAllocFrame, fieldBumpFrame,
      FixedArrayAllocator.headerMem, writeAllocationHeader, writeHeaderWord, fieldBumpedStore,
      Memory.toUInt32_eq_ofNat, hFacts.rootToNat, hHeader0ToNat,
      hFacts.header40ToNat, hFacts.header32ToNat, hFacts.header24ToNat,
      hFacts.header16ToNat, hFacts.header8ToNat, hValues, hBumpedAllocs] using hNext

#print axioms field_allocation_bump_spec
end Project.EulerGridStep.Execution
