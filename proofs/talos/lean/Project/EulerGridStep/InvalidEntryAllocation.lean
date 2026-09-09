import Project.EulerGridStep.InvalidEntryShape

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def invalidEntryFreshSearchFrame (base : Locals) : Locals :=
  { base with locals := ((base.locals.set 40 (.i64 0)).set 36 (.i64 0)).set 37 (.i64 0) }

def invalidEntryFreshBumpFrame (base : Locals) (heapTop capacity : UInt64) : Locals :=
  { base with
    locals := ((((((base.locals.set 40 (.i64 0)).set 36 (.i64 0)).set 37 (.i64 0)).set
      38 (.i64 (heapTop + 48 + capacity))).set
      39 (.i64 ((heapTop + 48 + capacity - 1) / 65536 + 1))).set
      40 (.i64 (heapTop + 48))), values := [] }

def invalidEntryFreshAllocFrame (base : Locals) (heapTop capacity : UInt64) : Locals :=
  { invalidEntryFreshBumpFrame base heapTop capacity with
    locals := (invalidEntryFreshBumpFrame base heapTop capacity).locals.set 31 (.i64 (heapTop + 48)) }

def invalidEntryFreshBumpedStore (initial : Store Unit) (heapTop capacity : UInt64) : Store Unit :=
  { initial with globals := { globals := initial.globals.globals.set 0 (.i64 (heapTop + 48 + capacity)) } }

/-- Fresh allocation with empty free list and sufficient existing memory. -/
theorem invalid_entry_allocation_bump_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit) (frame : Locals)
    (heapTop capacity allocs : UInt64)
    (hParams : frame.params.length = 2) (hLocals : frame.locals.length = 43)
    (hValues : frame.values = [])
    (hCapacityLocal : frame.locals[35]? = some (.i64 capacity))
    (hCapacity : 8 ≤ capacity.toNat)
    (hFitMemory : heapTop.toNat + 48 + capacity.toNat ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536) (hMemory32 : module_.memIs64 = false)
    (hHeapTop : st.globals.globals[0]? = some (.i64 heapTop))
    (hFreeList : st.globals.globals[1]? = some (.i64 0))
    (hAllocs : st.globals.globals[2]? = some (.i64 allocs))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q
      (FixedArrayAllocator.allocStore st heapTop capacity 1 allocs)
      (invalidEntryFreshAllocFrame frame heapTop capacity) env) :
    wp module_ (invalidEntryAllocationRegion ++ rest) Q st frame env := by
  have hCapacityGet : frame.locals[35] = .i64 capacity := by
    have h := hCapacityLocal
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  simp only [invalidEntryAllocationRegion, search, List.cons_append, List.nil_append]
  rw [invalid_entry_bump_header_shape]
  wp_alloc_window_lists [invalidEntryBumpBody, gridInvalidBody, func36, hParams, hLocals, hValues, hCapacityGet]
  simp only [hFreeList]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st' s => st' = st ∧ s = invalidEntryFreshSearchFrame frame)
    (μ := fun _ _ => 0)
  · refine ⟨rfl, ?_⟩
    simp (discharger := omega) [invalidEntryFreshSearchFrame, hValues]
  · rintro st1 s1 ⟨hSt, hFrame⟩
    subst st1
    subst s1
    simp only [searchBody, invalidEntryFreshSearchFrame]
    wp_alloc_window_lists [invalidEntryBumpBody, gridInvalidBody, func36, hParams, hLocals, hValues, hCapacityGet]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by simp)]
    wp_alloc_window_lists [invalidEntryBumpBody, gridInvalidBody, func36, hParams, hLocals, hValues, hCapacityGet]
    simp only [hHeapTop]
    have hFacts := Allocation.bumpFacts heapTop capacity
      st.mem.pages hFitMemory hPages
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simpa using hFacts.noOverflow)]
    wp_alloc_window_lists [invalidEntryBumpBody, gridInvalidBody, func36, hParams, hLocals, hValues, hCapacityGet]
    rw [hMemory32]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simpa using hFacts.noGrow)]
    rw [wp_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    wp_alloc_window_lists [hHeapTop, hParams, hLocals, hValues, hCapacityGet]
    change wp module_ (allocationHeaderProgram 42 37 ++ []) _ (invalidEntryFreshBumpedStore st heapTop capacity)
      (invalidEntryFreshBumpFrame frame heapTop capacity) env
    apply allocation_header_program_spec 42 37 module_ env (invalidEntryFreshBumpedStore st heapTop capacity)
      (invalidEntryFreshBumpFrame frame heapTop capacity) (heapTop + 48) capacity
      (by simp [invalidEntryFreshBumpFrame, Wasm.Locals.get, hParams, hLocals])
      (by simp [invalidEntryFreshBumpFrame, Wasm.Locals.get, hParams, hLocals, hCapacityGet])
      rfl
      (by rw [hFacts.rootToNat]; omega)
      (by rw [hFacts.rootToNat]; have := hFacts.fit32; omega)
      (by change (heapTop + 48).toNat ≤ st.mem.pages * 65536; rw [hFacts.rootToNat]; omega)
      _ []
    rw [wp_nil]
    have hHeaderGlobals :
        (writeAllocationHeader (invalidEntryFreshBumpedStore st heapTop capacity) (heapTop + 48) capacity).globals =
          (invalidEntryFreshBumpedStore st heapTop capacity).globals := rfl
    wp_alloc_window_lists [hHeaderGlobals, invalidEntryFreshBumpedStore,
      invalidEntryFreshBumpFrame, hAllocs, hParams, hLocals, hValues, hCapacityGet]
    have hBumpedAllocs :
        (st.globals.globals.set 0 (.i64 (heapTop + 48 + capacity)))[2]? = some (.i64 allocs) := by
      simp [hAllocs]
    have hHeader0ToNat : (heapTop + 48 - 48).toNat = heapTop.toNat := by
      have h := Allocation.root_sub_toNat heapTop 48 (by have := hFacts.fit32; omega) (by decide)
      simpa using h
    simpa only [FixedArrayAllocator.allocStore, invalidEntryFreshAllocFrame, invalidEntryFreshBumpFrame,
      FixedArrayAllocator.headerMem, writeAllocationHeader, writeHeaderWord, invalidEntryFreshBumpedStore,
      Memory.toUInt32_eq_ofNat, hFacts.rootToNat, hHeader0ToNat,
      hFacts.header40ToNat, hFacts.header32ToNat, hFacts.header24ToNat,
      hFacts.header16ToNat, hFacts.header8ToNat, hValues, hBumpedAllocs] using hNext

#print axioms invalid_entry_allocation_bump_spec
end Project.EulerGridStep.Execution
