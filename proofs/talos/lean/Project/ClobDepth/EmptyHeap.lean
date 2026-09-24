import Project.ClobDepth.AllocationInit
import Project.ClobDepth.Entry

namespace Project.ClobDepth.EmptyHeap
open Wasm Project.Common Project.Clob Project.Runtime Project.ProofKit Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation Project.ClobDepth.HeapProof
  Project.EulerRiemann.Execution

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def capacityProg : Program := Entry.func6AllocProg.take 18

def finishProg : Program :=
  [.localGet 36, .localSet 26, .localGet 26, .wrapI64, .constI64 0,
    .store64 0, .localGet 26, .localSet 3, .localGet 3]

theorem decomposition : Entry.func6AllocProg =
    capacityProg ++ FixedArrayAllocate.program 31 2 ++ finishProg := by rfl

def finishFrame (base : Locals) (root : UInt64) : Locals :=
  { base with locals := (base.locals.set 23 (.i64 root)).set 0 (.i64 root)
              values := [.i64 root] }

theorem empty_result (initial : Store Unit) (heap : Heap) (hHeap : heap.At initial)
    (hFit32 : heap.top.toNat + 56 < 4294967296)
    (hFit : heap.top.toNat + 56 ≤ initial.mem.pages * 65536) :
    AllocatedResult initial heap 8 (initialized initial heap 8 0) [] := by
  have hBump (h : takeFirstFitFrom 0 8 heap.nodes = none) :
      heap.top.toNat + 48 + (8 : UInt64).toNat ≤ 4294967296 := by change _ + 48 + 8 ≤ _; omega
  have hStrict := allocated_strict_bound initial heap.top 8 heap.nodes hHeap.freeList
    (fun _ => by change _ + 48 + 8 < _; omega)
  dsimp only [allocatedNode] at hStrict
  have hBounds := allocated_bounds initial heap.top 8 heap.nodes hHeap.freeList hBump
  have hCap := allocated_capacity 8 heap.nodes
  have hLength := allocated_length initial heap 8 0 hHeap hBump (by omega)
  have hAddress : (allocatedRoot heap.top 8 heap.nodes).toNat + 8 < 4294967296 := by
    change 8 ≤ _ at hCap
    omega
  refine allocated_result initial (initialized initial heap 8 0) heap 8 [] hHeap (by decide)
    (fun _ => by change _ + 48 + 8 < _; omega)
    (fun _ => by change _ + 48 + 8 ≤ _; omega) rfl rfl ?_ ?_
  · refine ⟨hLength.1, ⟨?_, ?_⟩, ?_⟩
    · simpa only [initialized, toUInt32_eq_ofNat, List.length_nil] using hLength.2
    · change (allocatedRoot heap.top 8 heap.nodes).toNat % 4294967296 + 8 ≤ _
      rw [Nat.mod_eq_of_lt (by omega)]
      change _ ≤ (FixedArrayAllocate.allocated initial heap.top 8 2 heap.nodes).mem.pages * 65536
      rw [arrayAllocated_pages]
      change 8 ≤ _ at hCap
      omega
    · intro i hi; simp at hi
  · have h : MemEqOutsideFlatWords (heap.allocateArrayStore initial 8 2)
        (heap.allocateArrayStore initial 8 2) (allocatedRoot heap.top 8 heap.nodes) 0 := fun _ _ => rfl
    have hWritten := h.write64 (slot := 0) (value := 0) (by simpa using hAddress) (Nat.zero_le _)
    simpa only [initialized, toUInt32_eq_ofNat, Nat.zero_mul, Nat.add_zero, List.length_nil, show UInt64.ofNat 0 = 0 from rfl] using hWritten

theorem alloc_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Value) (hParams : params.length = 3)
    (hSaved : saved.length = 28) (hTail : tail.length = 10)
    (need previous current capacity next result : UInt64)
    (hHeap : heap.At store) (hFit32 : heap.top.toNat + 56 < 4294967296)
    (hFit : heap.top.toNat + 56 ≤ store.mem.pages * 65536)
    (hPages : store.mem.pages ≤ 65536) (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ previous current capacity next,
      wp «module» rest Q (initialized store heap 8 0)
        (finishFrame (FixedArraySearch.frame params saved tail 8 previous current capacity next
          (allocatedRoot heap.top 8 heap.nodes)) (allocatedRoot heap.top 8 heap.nodes)) env) :
    wp «module» (Entry.func6AllocProg ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env := by
  rw [decomposition]
  simp only [List.append_assoc]
  simp [capacityProg, Entry.func6AllocProg, wp_simp, FixedArraySearch.frame,
    Locals.get, Locals.set?, hParams, hSaved, hTail, List.take, List.drop]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  simp only [wp_nil, List.take_zero, List.drop_zero, List.nil_append]
  change wp «module» (FixedArrayAllocate.program 31 2 ++ _) _ store
    (FixedArraySearch.frame params saved tail 8 previous current capacity next result) env
  apply allocation_program env store heap params saved tail 31 (by omega)
    8 2 previous current capacity next result hHeap
    (fun _ => by change _ + 48 + 8 ≤ _ ∧ _ + 48 + 8 ≤ _; constructor <;> omega) hPages
  intro previous current capacity next
  have hResult := empty_result store heap hHeap hFit32 hFit
  have hRoot := hResult.owned.buffer.addressBound
  have hMemory := hResult.owned.buffer.memoryBound
  have hCapacity := hResult.owned.buffer.capacity
  dsimp only [allocatedNode, initialized] at hRoot hMemory hCapacity
  simp only [Mem.write64_pages] at hMemory
  simp only [fixedArrayBytes, List.length_nil] at hCapacity
  simp [finishProg, wp_simp, FixedArraySearch.frame,
    Locals.get, Locals.set?, hParams, hSaved, hTail, List.take, List.drop]
  rw [if_neg (by
    change ¬_ < (allocatedRoot heap.top 8 heap.nodes).toNat % 4294967296 + 8
    change (allocatedRoot heap.top 8 heap.nodes).toNat + _ < _ at hRoot
    change (allocatedRoot heap.top 8 heap.nodes).toNat + _ ≤ _ at hMemory
    change _ ≤ (allocatedCapacity 8 heap.nodes).toNat at hCapacity
    rw [Nat.mod_eq_of_lt (by omega)]; exact Nat.not_lt.mpr (by omega))]
  simpa [finishFrame, FixedArraySearch.frame, initialized, toUInt32_eq_ofNat, List.set_append, hSaved] using hNext previous current capacity next

#print axioms alloc_spec
#print axioms empty_result
end Project.ClobDepth.EmptyHeap
