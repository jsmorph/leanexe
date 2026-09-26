import Project.Gpt2CachedStep.LinearRows.FrozenSpec
import Project.ProofKit.OwnedPacked

namespace Project.Gpt2CachedStep.Frozen.LinearRows.Spec
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution

theorem linearRows_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (weightOffset biasOffset inputWidth outputWidth rows : Nat)
    (hHeap : heap.At initial)
    (hweights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hinput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hinputSize : rows * inputWidth * 4 ≤ input.size)
    (hweightSize : (weightOffset + inputWidth * outputWidth) * 4 ≤ weights.size)
    (hbiasSize : (biasOffset + outputWidth) * 4 ≤ weights.size)
    (hwidth : inputWidth < UInt64.size) (houtWidth : outputWidth < UInt64.size)
    (hcount : 4 * (rows * outputWidth) ≤ 2^32)
    (hBump : takeFirstFitFrom 0
        (PackedCapacity.capacity (UInt64.ofNat (4 * (rows * outputWidth)))) heap.nodes = none →
      heap.top.toNat + 48 + PackedCapacity.capacityNat (4 * (rows * outputWidth)) < 2^32 ∧
      FixedArrayBump.requiredPages heap.top (PackedCapacity.capacity (UInt64.ofNat (4 * (rows * outputWidth)))) ≤
        initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hweightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hinputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size)) :
    let need := PackedCapacity.capacity (UInt64.ofNat (4 * (rows * outputWidth)))
    let node := allocatedNode heap.top need heap.nodes
    let result := LeanExe.Models.Gpt2.linearRows weights input weightOffset biasOffset inputWidth outputWidth rows
    TerminatesWith env «module» 21 initial
      [.i64 (UInt64.ofNat rows), .i64 (UInt64.ofNat outputWidth), .i64 (UInt64.ofNat inputWidth),
        .i64 (UInt64.ofNat biasOffset), .i64 (UInt64.ofNat weightOffset),
        .i64 (UInt64.ofNat input.size), .i64 inputPtr, .i64 inputOwner,
        .i64 (UInt64.ofNat weights.size), .i64 weightsPtr, .i64 weightsOwner]
      (fun final values =>
        values = [.i64 (UInt64.ofNat result.size), .i64 node.root, .i64 node.root] ∧
        (heap.allocate need).At final ∧
        (heap.allocate need).OwnsPacked final node result ∧
        heap.Frame initial (heap.allocate need) final ∧
        final.mem.pages ≤ 65536 ∧
        final.memoryCap «module» 0 = initial.memoryCap «module» 0) := by
  dsimp only
  let need := PackedCapacity.capacity (UInt64.ofNat (4 * (rows * outputWidth)))
  have hCapacity : need.toNat = PackedCapacity.capacityNat (4 * (rows * outputWidth)) :=
    PackedCapacity.capacity_toNat _ hcount
  have hNeed : 4 * (rows * outputWidth) ≤ need.toNat := by
    rw [hCapacity]
    exact PackedCapacity.capacityNat_ge _
  have hBound : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296 := by
    intro h
    rw [hCapacity]
    exact (hBump h).1
  have hSize : (LeanExe.Models.Gpt2.linearRows weights input weightOffset biasOffset
      inputWidth outputWidth rows).size = 4 * (rows * outputWidth) := by
    rw [Project.Gpt2LinearRows.linearRows_eq, PackedSource.generate_size]
  apply (linearRows_exact env initial weightsOwner inputOwner weightsPtr inputPtr weights input
    weightOffset biasOffset inputWidth outputWidth rows heap.top heap.allocations heap.nodes
    hweights hinput hinputSize hweightSize hbiasSize hwidth houtWidth hcount
    (by rw [hHeap.globals]; rfl) (by rw [hHeap.globals]; rfl) (by rw [hHeap.globals]; rfl)
    hHeap.freeList (fun h => ⟨(hBump h).1.le, (hBump h).2⟩) hPages
    hweightsProtected.below hinputProtected.below hweightsProtected.separated
    hinputProtected.separated hHeap.below).mono
  rintro final values ⟨hValues, hBytes, _, _, _, hWrites⟩
  have hWritten := heap.packedWritten_at initial final need _ hHeap hNeed
    (fun h => (hBound h).le) hWrites
  have hOwned := heap.ownsPacked_written initial final need
    (LeanExe.Models.Gpt2.linearRows weights input weightOffset biasOffset inputWidth outputWidth rows)
    hHeap (by rw [hSize]; exact hNeed) hBound (by rw [hSize]; exact hWrites) hBytes
  refine ⟨?_, hWritten, hOwned,
    heap.frame_packedWritten initial final need _ hHeap hNeed (fun h => (hBound h).le) hWrites,
    ?_, ?_⟩
  · rw [hSize]
    exact hValues
  · rw [hWrites.2.1]
    exact heap.allocatePackedStore_pages_le initial need hPages (fun h => (hBound h).le)
  · rw [hWrites.1]
    exact heap.allocatePackedStore_memoryCap initial need «module» 0

#print axioms linearRows_owned

end Project.Gpt2CachedStep.Frozen.LinearRows.Spec
