import Project.Gpt2QuantizedCached.Embedding.Body

namespace Project.Gpt2QuantizedCached.Embedding.Spec
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

theorem embedding_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (owner ptr : UInt64) (weights : ByteArray) (token : UInt32) (position : Nat)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hScaleSize : tokenScaleOffset + token.toNat * 4 + 4 ≤ weights.size)
    (hTokenSize : tokenWeightOffset + token.toNat * 768 + 768 ≤ weights.size)
    (hPositionSize : positionOffset + (position * 768 + 768) * 4 ≤ weights.size)
    (hToken : token.toNat < 50257) (hPosition : position < 128)
    (hWeightsProtected : heap.Protects ptr.toNat (ptr.toNat + weights.size))
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top need ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536) :
    let output := embedding weights token position
    let node := allocatedNode heap.top need heap.nodes
    TerminatesWith env «module» 30 initial
      [.i64 (UInt64.ofNat position), .i64 token.toUInt64,
        .i64 (UInt64.ofNat weights.size), .i64 ptr, .i64 owner]
      (fun final values =>
        values = [.i64 (UInt64.ofNat output.size), .i64 node.root, .i64 node.root] ∧
        (heap.allocate need).At final ∧
        (heap.allocate need).OwnsPacked final node output ∧
        heap.Frame initial (heap.allocate need) final ∧
        final.mem.pages ≤ 65536 ∧
        final.memoryCap «module» 0 = initial.memoryCap «module» 0) := by
  dsimp only
  rw [← UInt64.ofNat_uInt32ToNat token]
  refine TerminatesWith.of_wp_entry_for (f := func30Def) rfl ?_
  change wp «module» (func30 ++ []) _ initial
    { params := parameters owner ptr weights token position, locals := List.replicate 22 (.i64 0) } env
  apply body_spec env initial heap owner ptr weights token position _ hHeap hWeights
    hScaleSize hTokenSize hPositionSize hToken hPosition hWeightsProtected
    hBump hPages rfl (by simp) rfl (I64Values.replicate _ _)
  intro final result hValues hOutput
  simp only [wp_nil]
  have hPost := And.intro hOutput.heapAt
    (And.intro hOutput.owned (And.intro hOutput.frame (And.intro hOutput.pages (hOutput.memoryCap «module» 0))))
  have hRoot : allocatedRoot heap.top need heap.nodes =
      (allocatedNode heap.top need heap.nodes).root := rfl
  simpa [func30Def, Function.numParams, hValues, hRoot, -UInt64.ofNat_mul] using hPost

#print axioms embedding_exact

end Project.Gpt2QuantizedCached.Embedding.Spec
