import Project.EulerGridStep.BufferState

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Fresh allocation validity from one available object, independent of an arena slot count. -/
theorem fresh_valid_of_space (current : Store Unit) (heapTop source allocs : UInt64)
    (input : Array UInt64)
    (hSpace : heapTop.toNat + 48 + 8 * (input.size + 1) ≤ current.mem.pages * 65536)
    (hPages : current.mem.pages ≤ 65536)
    (hHeap : current.globals.globals[0]? = some (.i64 heapTop))
    (hFree : current.globals.globals[1]? = some (.i64 0))
    (hAllocs : current.globals.globals[2]? = some (.i64 allocs))
    (hSeparate : ObjectsSeparate (heapTop + 48) input.size source input.size) :
    (FieldAllocation.fresh heapTop allocs).Valid current source input := by
  have hSize : 8 * (input.size + 1) < UInt64.size := by
    change 8 * (input.size + 1) < 18446744073709551616
    omega
  have hCapacity : (fieldRequest input.size).toNat = 8 * (input.size + 1) :=
    UInt64.toNat_ofNat_of_lt' hSize
  have hFit : heapTop.toNat + 48 + (fieldRequest input.size).toNat ≤ current.mem.pages * 65536 := by
    simpa only [hCapacity] using hSpace
  have hFacts := Allocation.bumpFacts heapTop (fieldRequest input.size) current.mem.pages hFit hPages
  have hRoot : heapTop.toNat + 48 ≤ 4294967296 := by
    have := hFacts.fit32
    omega
  refine ⟨⟨hRoot, hHeap, hFree, hAllocs⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change 48 ≤ (heapTop + 48).toNat
    rw [hFacts.rootToNat]
    omega
  · change (heapTop + 48).toNat < 4294967296
    rw [hFacts.rootToNat]
    have := hFacts.fit32
    rw [hCapacity] at this
    omega
  · change 8 * (input.size + 1) ≤ (fieldRequest input.size).toNat
    rw [hCapacity]
  · change (heapTop + 48).toNat + (fieldRequest input.size).toNat ≤ 4294967296
    rw [hFacts.rootToNat]
    exact hFacts.fit32
  · change (heapTop + 48).toNat + (fieldRequest input.size).toNat ≤ current.mem.pages * 65536
    rw [hFacts.rootToNat]
    exact hFit
  · unfold ObjectsSeparate at hSeparate
    change source.toNat + 8 * (input.size + 1) ≤ (heapTop + 48).toNat - 48 ∨
      (heapTop + 48).toNat + 8 * (input.size + 1) ≤ source.toNat
    omega

#print axioms fresh_valid_of_space
end Project.EulerGridStep.Execution
