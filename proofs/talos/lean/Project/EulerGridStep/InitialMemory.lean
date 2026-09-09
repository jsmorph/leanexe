import Project.EulerGridStep.InitializationFill
import Project.EulerGridStep.BufferState

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- The completed zero fill preserves the allocator's owned metadata. -/
theorem InitializedArray.preserves_header {initial final : Store Unit} {target : UInt64} {count : Nat}
    (h : InitializedArray initial final target count) (capacity : UInt64)
    (hHeader : OwnedHeader initial target capacity) : OwnedHeader final target capacity := by
  apply ownedHeader_of_byte_frame initial final target capacity hHeader
  intro address _ hHi
  exact h.outside address (Or.inl hHi)

/-- A separate input array survives the exact length store and zero loop. -/
theorem InitializedArray.preserves_array {initial final : Store Unit} {target : UInt64} {count : Nat}
    (h : InitializedArray initial final target count) (pointer : UInt64) (input : Array UInt64)
    (hInput : UInt64Array.At initial pointer input)
    (hSeparate : ObjectsSeparate target count pointer input.size) : UInt64Array.At final pointer input := by
  apply arrayAt_of_byte_frame initial final pointer input hInput (by rw [h.pages])
  intro address hLo hHi
  apply h.outside
  unfold ObjectsSeparate at hSeparate
  omega

/-- Allocation followed by zero fill establishes a live owned output and exact runtime counters. -/
theorem initial_buffer_state (initial final : Store Unit) (heap allocs releases frees : UInt64) (count : Nat)
    (hFit : heap.toNat + 48 + 8 * (count + 1) ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hFree : initial.globals.globals[1]? = some (.i64 0))
    (hAllocs : initial.globals.globals[2]? = some (.i64 allocs))
    (hReleases : initial.globals.globals[4]? = some (.i64 releases))
    (hFrees : initial.globals.globals[5]? = some (.i64 frees))
    (hFill : InitializedArray (FixedArrayAllocator.allocStore initial heap (fieldRequest count) 1 allocs)
      final (heap + 48) count) :
    BufferState final count [⟨heap + 48, Array.replicate count 0⟩] [] (allocs + 1) releases frees ∧
    final.globals.globals[0]? = some (.i64 (heap + 48 + fieldRequest count)) ∧
    final.mem.pages = initial.mem.pages := by
  have hFit32 : heap.toNat + 48 ≤ 4294967296 := by omega
  have hRoot := Allocation.root_toNat heap hFit32
  have hMem := fresh_alloc_memory initial heap (fieldRequest count) allocs hFit32
  have hHeader := ownedHeader_of_mem_eq _ _ (heap + 48) (fieldRequest count)
    (writeAllocationHeader_owned initial (heap + 48) (fieldRequest count)
      (by rw [hRoot]; omega) (by rw [hRoot]; omega)) hMem
  have hGlobals := congrArg Store.globals hFill.frame
  have hPagesEq : final.mem.pages = initial.mem.pages := by
    rw [hFill.pages]
    simp [FixedArrayAllocator.allocStore, FixedArrayAllocator.headerMem, Mem.write64_pages]
  have hGlobalLength := (List.getElem?_eq_some_iff.mp hFrees).choose
  refine ⟨⟨?_, trivial, ?_, ?_, ?_, ?_, by rw [hPagesEq]; exact hPages⟩, ?_, hPagesEq⟩
  · intro buffer hb
    have hb' : buffer = ⟨heap + 48, Array.replicate count 0⟩ := by simpa using hb
    subst buffer
    exact ⟨by simp, hFill.preserves_header _ hHeader, hFill.arrayAt⟩
  all_goals rw [hGlobals]
  all_goals simp (discharger := omega) [FixedArrayAllocator.allocStore, List.getElem?_set,
    hFree, hAllocs, hReleases, hFrees]
  all_goals first
    | omega
    | exact (List.getElem?_eq_some_iff.mp hFree).choose_spec
    | exact (List.getElem?_eq_some_iff.mp hReleases).choose_spec
    | exact (List.getElem?_eq_some_iff.mp hFrees).choose_spec

#print axioms InitializedArray.preserves_header
#print axioms InitializedArray.preserves_array
#print axioms initial_buffer_state
end Project.EulerGridStep.Execution
