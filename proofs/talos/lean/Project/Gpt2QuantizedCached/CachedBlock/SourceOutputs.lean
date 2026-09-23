import Project.Gpt2QuantizedCached.CachedBlock.Spec
import Project.Gpt2QuantizedCached.CachedBlock.Sizes
import Project.ProofKit.PackedStatus

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

theorem cachedBlock_status_zero_iff (weights input cache : ByteArray) (layer position : Nat) :
    (cachedBlock weights input cache layer position).status = 0 ↔
      (tensors weights input cache layer position).accepted = true := by
  rw [cachedBlock_tensors]
  generalize hValues : tensors weights input cache layer position = values
  cases hAccepted : values.accepted <;> simp [hAccepted]

theorem cachedBlock_failed (weights input cache : ByteArray) (layer position : Nat)
    (hInput : input.size = 3072) (hStatus : (cachedBlock weights input cache layer position).status ≠ 0) :
    (cachedBlock weights input cache layer position).hidden = .empty ∧
      (cachedBlock weights input cache layer position).cache = .empty := by
  rcases cachedBlock_sizes weights input cache layer position hInput with hSuccess | hFailure
  · exact False.elim (hStatus hSuccess.1)
  · exact hFailure.2

theorem Completion.sourcePacked (weights input cache : ByteArray) (layer position : Nat)
    {before heap : Heap} {initial final : Store Unit} {hidden cacheNode : FreeNode}
    (h : Completion before initial heap final (tensors weights input cache layer position).accepted
      hidden cacheNode (tensors weights input cache layer position).hidden
      (Project.Gpt2CachedStep.CachedBlock.cacheUpdate (tensors weights input cache layer position).qkv))
    (hInput : input.size = 3072) :
    heap.StatusPacked final (cachedBlock weights input cache layer position).status hidden
      (cachedBlock weights input cache layer position).hidden ∧
    heap.StatusPacked final (cachedBlock weights input cache layer position).status cacheNode
      (cachedBlock weights input cache layer position).cache := by
  constructor
  · exact ⟨fun hStatus => (Spec.Completion.sourceOutputs weights input cache layer position h hStatus).1,
      fun hStatus => (cachedBlock_failed weights input cache layer position hInput hStatus).1⟩
  · exact ⟨fun hStatus => (Spec.Completion.sourceOutputs weights input cache layer position h hStatus).2,
      fun hStatus => (cachedBlock_failed weights input cache layer position hInput hStatus).2⟩

#print axioms cachedBlock_status_zero_iff
#print axioms cachedBlock_failed
#print axioms Completion.sourcePacked
end Project.Gpt2QuantizedCached.CachedBlock
