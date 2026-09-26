import Project.Drone.ExecutionPushAllocation
import Project.Drone.ExecutionBorrowedWords
import Project.ProofKit.WordArrayPushCopy
import Project.ProofKit.WordArrayHeader
import Project.EulerRiemann.WordAllocationBounds

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

def pushNeed (size : Nat) : UInt64 :=
  FixedArrayCapacity.normalizedCapacity (UInt64.ofNat (size + 1)) 1

def pushScratch (s : Scratch) (size : Nat) : Scratch :=
  { prepared s size with need := pushNeed size }

def pushedScratch (s : Scratch) (size : Nat) (root previous current capacity next : UInt64) : Scratch :=
  { allocatedScratch (pushScratch s size) root previous current capacity next with
    target := root
    counter := UInt64.ofNat size }

theorem pushNeed_toNat (size : Nat) (hSize : size + 1 ≤ 4294967296) :
    (pushNeed size).toNat = 8 * (size + 2) := by
  rw [pushNeed, FixedArrayCapacity.wordCapacity_ofNat (size + 1) hSize,
    UInt64.toNat_ofNat_of_lt']
  change 8 * (size + 1 + 1) < 18446744073709551616
  omega

theorem word_push_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Wasm.Value) (s : Scratch) (source : FreeNode) (input : Array UInt64)
    (hSource : s.source = source.root) (hInput : BorrowedWords heap store source input)
    (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 (pushNeed input.size) heap.nodes = none →
      heap.top.toNat + 48 + (pushNeed input.size).toNat < 4294967296 ∧
      bumpPages heap.top (pushNeed input.size) ≤ store.memoryCap Project.Drone.«module» 0)
    (hPages : store.mem.pages ≤ 65536) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (previous current capacity next : UInt64),
      Memory.WritesRange (heap.allocateArrayStore store (pushNeed input.size) 1) final
        (allocatedRoot heap.top (pushNeed input.size) heap.nodes).toNat
        ((allocatedRoot heap.top (pushNeed input.size) heap.nodes).toNat + 8 * (input.size + 2)) →
      (heap.allocate (pushNeed input.size)).At final →
      BorrowedWords (heap.allocate (pushNeed input.size)) final source input →
      (heap.allocate (pushNeed input.size)).OwnsWords final
        (allocatedNode heap.top (pushNeed input.size) heap.nodes) (input.push s.value) →
      wp Project.Drone.«module» rest Q final
        { WordArrayPush.frame params saved tail
            (pushedScratch s input.size (allocatedRoot heap.top (pushNeed input.size) heap.nodes)
              previous current capacity next) with
          values := [.i64 (allocatedRoot heap.top (pushNeed input.size) heap.nodes)] } env) :
    wp Project.Drone.«module» (WordArrayPush.program (params.length + saved.length) ++ rest)
      Q store (WordArrayPush.frame params saved tail s) env := by
  let need := pushNeed input.size
  let root := allocatedRoot heap.top need heap.nodes
  let allocated := heap.allocateArrayStore store need 1
  let middle := FixedArrayResult.writeLength allocated root (UInt64.ofNat (input.size + 1))
  have hSize : input.size + 1 ≤ 4294967296 := by have := hInput.values.1; omega
  have hNeed : 8 * ((input.size + 1) + 1) ≤ need.toNat := by
    rw [pushNeed_toNat input.size hSize]
  have hFit : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun h => (hBump h).1.le
  have hBounds := heap.allocate_word_bounds store need 1 (input.size + 1) hHeap hNeed hFit
  change root.toNat + 8 * (input.size + 1 + 1) ≤ 4294967296 ∧
    root.toNat + 8 * (input.size + 1 + 1) ≤ allocated.mem.pages * 65536 at hBounds
  have hWrites : Memory.WritesRange allocated middle root.toNat
      (root.toNat + 8 * (input.size + 2)) :=
    (FixedArrayResult.writeLength_frame allocated root (UInt64.ofNat (input.size + 1))
      (by omega)).mono (by omega) (by omega)
  have hSep : source.root.toNat + 8 * (input.size + 1) ≤ root.toNat ∨
      root.toNat + 8 * (input.size + 2) ≤ source.root.toNat := by
    simpa only [Nat.add_assoc] using hInput.allocate_word_disjoint need (input.size + 1) hNeed hFit
  have hMiddle : UInt64Array.At middle s.source input := by
    rw [hSource]
    exact (hInput.arrayAllocated need 1 hHeap hFit).values.writesRange hWrites hSep
  simp only [WordArrayPush.program, List.append_assoc]
  apply prepare_spec Project.Drone.«module» env store params saved tail s input
    (by simpa only [hSource] using hInput.values)
  apply capacity_spec
  change wp _ (FixedArrayAllocate.program _ 1 ++ _) _ store
    (WordArrayPush.frame params saved tail (pushScratch s input.size)) env
  apply push_allocation_spec env store heap params saved tail (pushScratch s input.size) hHeap
    (fun h => ⟨(hBump h).1.le, (hBump h).2⟩) hPages
  intro previous current capacity next
  apply install_spec
  · change root.toUInt32.toNat + 8 ≤ allocated.mem.pages * 65536
    rw [Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by omega)]
    omega
  apply copy_spec Project.Drone.«module» env middle params saved tail
    { allocatedScratch (pushScratch s input.size) root previous current capacity next with target := root }
    input rfl rfl hMiddle (by change root.toNat + 8 * (input.size + 2) ≤ _; omega)
    (by simp only [middle, FixedArrayResult.writeLength_pages]; omega)
    (FixedArrayResult.writeLength_read ..)
    (by simpa only [allocatedScratch, pushScratch, prepared, hSource] using hSep)
  intro final hCopy _ hOutput
  have hTotal := hWrites.trans hCopy
  have hFinished := heap.finishWords store final need (input.push s.value) hHeap
    (by simpa only [Array.size_push] using hNeed) (fun h => (hBump h).1)
    (by simpa only [Array.size_push, Nat.add_assoc] using hTotal) hOutput
  exact hNext final previous current capacity next hTotal hFinished.1
    (hInput.arrayWritten need 1 (input.size + 1) hHeap hNeed hFit
      (by simpa only [Nat.add_assoc] using hTotal)) hFinished.2

#print axioms pushNeed_toNat
#print axioms word_push_spec
end Project.Drone.Execution
