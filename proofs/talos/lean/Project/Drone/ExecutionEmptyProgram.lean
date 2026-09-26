import Project.Drone.ExecutionPushAllocation
import Project.Drone.ExecutionEmptyWords
import Project.ProofKit.WordArrayHeader

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

def emptyProgram (base : Nat) : Wasm.Program :=
  FixedArrayCapacity.constantProgram 0 1 (base + 9) ++
  FixedArrayAllocate.program (base + 9) 1 ++
  [.localGet (base + 14), .localSet (base + 5)] ++
  FixedArrayResult.lengthStoreProgram (base + 5) 0 ++ [.localGet (base + 5)]

def emptyScratch (s : Scratch) (root previous current capacity next : UInt64) : Scratch :=
  { allocatedScratch { s with need := 8 } root previous current capacity next with counter := root }

theorem empty_program_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Wasm.Value) (s : Scratch) (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 8 heap.nodes = none →
      heap.top.toNat + 48 + 8 < 4294967296 ∧
      bumpPages heap.top 8 ≤ store.memoryCap Project.Drone.«module» 0)
    (hPages : store.mem.pages ≤ 65536) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next : UInt64,
      wp Project.Drone.«module» rest Q (emptyWordsStore heap store)
        { WordArrayPush.frame params saved tail
            (emptyScratch s (allocatedRoot heap.top 8 heap.nodes) previous current capacity next) with
          values := [.i64 (allocatedRoot heap.top 8 heap.nodes)] } env) :
    wp Project.Drone.«module» (emptyProgram (params.length + saved.length) ++ rest)
      Q store (WordArrayPush.frame params saved tail s) env := by
  simp only [emptyProgram, List.append_assoc]
  apply FixedArrayCapacity.constantProgram_spec 0 1 _ Project.Drone.«module» env store
    (WordArrayPush.frame params saved tail s) rfl (by simp [WordArrayPush.frame]; omega)
    (frame_valid params saved tail s 9 (by decide))
  rw [capacityFrame_eq]
  change wp _ _ _ _ (WordArrayPush.frame params saved tail { s with need := 8 }) _
  apply push_allocation_spec env store heap params saved tail { s with need := 8 } hHeap
    (fun h => ⟨(hBump h).1.le, (hBump h).2⟩) hPages
  intro previous current capacity next
  have hFit : takeFirstFitFrom 0 8 heap.nodes = none →
      heap.top.toNat + 48 + (8 : UInt64).toNat ≤ 4294967296 := fun h => (hBump h).1.le
  have hBounds := allocated_bounds store heap.top 8 heap.nodes hHeap.freeList hFit
  have hCapacity := allocated_capacity (8 : UInt64) heap.nodes
  have hRootNat : (allocatedRoot heap.top 8 heap.nodes).toUInt32.toNat =
      (allocatedRoot heap.top 8 heap.nodes).toNat := by
    rw [Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by have : (8 : UInt64).toNat = 8 := rfl; omega)]
  have hMemory : (allocatedRoot heap.top 8 heap.nodes).toUInt32.toNat + 8 ≤
      (heap.allocateArrayStore store 8 1).mem.pages * 65536 := by
    rw [hRootNat]
    change _ ≤ (FixedArrayAllocate.allocated store heap.top 8 1 heap.nodes).mem.pages * 65536
    rw [arrayAllocated_pages]
    have : (8 : UInt64).toNat = 8 := rfl
    omega
  wp_push_frame [List.cons_append, List.nil_append, allocatedScratch,
    FixedArrayResult.lengthStoreProgram, show 2^32 = 4294967296 by decide,
    ← Memory.toUInt32_eq_ofNat, UInt32.add_zero, UInt32.toNat_zero, Nat.not_lt.mpr hMemory]
  exact hNext previous current capacity next

theorem advance_empty_shape : (func19.drop 16).take 40 = emptyProgram 15 := rfl
theorem initial_empty_shape : func23.take 40 = emptyProgram 22 := rfl

#print axioms empty_program_spec
#print axioms advance_empty_shape
#print axioms initial_empty_shape
end Project.Drone.Execution
