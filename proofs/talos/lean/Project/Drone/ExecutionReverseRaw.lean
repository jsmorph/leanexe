import Project.Drone.ExecutionReverseProgram
import Project.Drone.ExecutionPush

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

def reverseNeed (size : Nat) : UInt64 := FixedArrayCapacity.normalizedCapacity (UInt64.ofNat size) 1

def reversedScratch (s : Scratch) (size : Nat) (root previous current capacity next : UInt64) : Scratch :=
  { allocatedScratch { s with need := reverseNeed size } root previous current capacity next with
    counter := root, value := UInt64.ofNat size }

theorem reverseNeed_toNat (size : Nat) (hSize : size ≤ 4294967296) :
    (reverseNeed size).toNat = 8 * (size + 1) := by
  rw [reverseNeed, FixedArrayCapacity.wordCapacity_ofNat size hSize, UInt64.toNat_ofNat_of_lt']
  change 8 * (size + 1) < 18446744073709551616
  omega

theorem word_reverse_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Value) (s : Scratch) (source : FreeNode) (input : Array UInt64)
    (hSource : s.nextLength = source.root) (hLength : s.target = UInt64.ofNat input.size)
    (hInput : BorrowedWords heap store source input) (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 (reverseNeed input.size) heap.nodes = none →
      heap.top.toNat + 48 + (reverseNeed input.size).toNat < 4294967296 ∧
      bumpPages heap.top (reverseNeed input.size) ≤ store.memoryCap Project.Drone.«module» 0)
    (hPages : store.mem.pages ≤ 65536) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (previous current capacity next : UInt64),
      Memory.WritesRange (heap.allocateArrayStore store (reverseNeed input.size) 1) final
        (allocatedRoot heap.top (reverseNeed input.size) heap.nodes).toNat
        ((allocatedRoot heap.top (reverseNeed input.size) heap.nodes).toNat + 8 * (input.size + 1)) →
      (heap.allocate (reverseNeed input.size)).At final →
      (heap.allocate (reverseNeed input.size)).OwnsWords final
        (allocatedNode heap.top (reverseNeed input.size) heap.nodes) input.reverse →
      wp Project.Drone.«module» rest Q final
        { frame params saved tail
            (reversedScratch s input.size (allocatedRoot heap.top (reverseNeed input.size) heap.nodes)
              previous current capacity next) with
          values := [.i64 (allocatedRoot heap.top (reverseNeed input.size) heap.nodes)] } env) :
    wp Project.Drone.«module» (reverseProgram (params.length + saved.length) ++ rest) Q store
      (frame params saved tail s) env := by
  let need := reverseNeed input.size
  let root := allocatedRoot heap.top need heap.nodes
  let allocated := heap.allocateArrayStore store need 1
  let middle := FixedArrayResult.writeLength allocated root (UInt64.ofNat input.size)
  have hSize : input.size ≤ 4294967296 := by have := hInput.values.1; omega
  have hNeed : 8 * (input.size + 1) ≤ need.toNat := by rw [reverseNeed_toNat input.size hSize]
  have hFit : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun h => (hBump h).1.le
  have hBounds := heap.allocate_word_bounds store need 1 input.size hHeap hNeed hFit
  change root.toNat + 8 * (input.size + 1) ≤ 4294967296 ∧
    root.toNat + 8 * (input.size + 1) ≤ allocated.mem.pages * 65536 at hBounds
  have hWrites : Memory.WritesRange allocated middle root.toNat (root.toNat + 8 * (input.size + 1)) :=
    (FixedArrayResult.writeLength_frame allocated root (UInt64.ofNat input.size) (by omega)).mono (by omega) (by omega)
  have hSep : source.root.toNat + 8 * (input.size + 1) ≤ root.toNat ∨
      root.toNat + 8 * (input.size + 1) ≤ source.root.toNat :=
    hInput.allocate_word_disjoint need input.size hNeed hFit
  have hMiddle : UInt64Array.At middle s.nextLength input := by
    rw [hSource]
    exact (hInput.arrayAllocated need 1 hHeap hFit).values.writesRange hWrites hSep
  simp only [reverseProgram, List.append_assoc]
  apply reverse_capacity_spec
  have hCapacity : FixedArrayCapacity.normalizedCapacity s.target 1 = need := by rw [hLength]; rfl
  rw [hCapacity]
  apply push_allocation_spec env store heap params saved tail { s with need := need } hHeap
    (fun h => ⟨(hBump h).1.le, (hBump h).2⟩) hPages
  intro previous current capacity next
  apply reverse_install_spec
  · change root.toUInt32.toNat + 8 ≤ allocated.mem.pages * 65536
    rw [Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hStore : FixedArrayResult.writeLength allocated root s.target = middle := by
    dsimp only [middle]
    rw [hLength]
  dsimp only [allocatedScratch]
  rw [hStore]
  rw [← List.append_assoc]
  apply reverse_copy_spec env middle params saved tail
    { allocatedScratch { s with need := need } root previous current capacity next with counter := root }
    input hLength hMiddle hBounds.1 (by simp only [middle, FixedArrayResult.writeLength_pages]; exact hBounds.2)
    (FixedArrayResult.writeLength_read ..) (by simpa only [allocatedScratch, hSource] using hSep)
  intro final hOutput hCopy
  have hTotal := hWrites.trans hCopy
  have hFinished := heap.finishWords store final need input.reverse hHeap
    (by simpa only [Array.size_reverse] using hNeed) (fun h => (hBump h).1)
    (by simpa only [Array.size_reverse] using hTotal) hOutput
  exact hNext final previous current capacity next hTotal hFinished.1 hFinished.2

#print axioms reverseNeed_toNat
#print axioms word_reverse_spec
end Project.Drone.Execution
