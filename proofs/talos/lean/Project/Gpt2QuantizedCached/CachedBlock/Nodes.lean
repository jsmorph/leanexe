import Project.Gpt2QuantizedCached.CachedBlock.Resources
import Project.Gpt2QuantizedCached.GroupedProjection.Fresh
import Project.Gpt2CachedStep.LayerNorm.Fresh
import Project.Gpt2CachedStep.CachedAttention.Fresh
import Project.ProofKit.PackedOwners
import Project.ProofKit.PackedBindings

namespace Project.Gpt2QuantizedCached.CachedBlock
open Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open GroupedProjection.Projection

def normalizedNode (heap : Heap) : FreeNode := Gpt2CachedStep.LayerNorm.outputNode heap 1
def qkvNode (heap : Heap) : FreeNode := outputNode (normalizedHeap heap) 768 2304 1
def attentionNode (heap : Heap) (position : Nat) : FreeNode :=
  Gpt2CachedStep.CachedAttention.outputNode (qkvHeap heap) position
def projectionNode (heap : Heap) (position : Nat) : FreeNode :=
  outputNode (attentionHeap heap position) 768 768 1
def residualNode (heap : Heap) (position : Nat) : FreeNode :=
  allocatedNode (projectionHeap heap position).top residualNeed (projectionHeap heap position).nodes
def normalized2Node (heap : Heap) (position : Nat) : FreeNode :=
  Gpt2CachedStep.LayerNorm.outputNode (residualHeap heap position) 1
def expandedNode (heap : Heap) (position : Nat) : FreeNode :=
  outputNode (normalized2Heap heap position) 768 3072 1
def activatedNode (heap : Heap) (position : Nat) : FreeNode :=
  allocatedNode (expandedHeap heap position).top activatedNeed (expandedHeap heap position).nodes
def projected2Node (heap : Heap) (position : Nat) : FreeNode :=
  outputNode (activatedHeap heap position) 3072 768 1
def hiddenNode (heap : Heap) (position : Nat) : FreeNode :=
  allocatedNode (projected2Heap heap position).top residualNeed (projected2Heap heap position).nodes
def cacheNode (heap : Heap) (position : Nat) : FreeNode :=
  allocatedNode (hiddenHeap heap position).top cacheNeed (hiddenHeap heap position).nodes

theorem cacheNode_root (heap : Heap) (position : Nat) :
    (cacheNode heap position).root =
      allocatedRoot (hiddenHeap heap position).top cacheNeed (hiddenHeap heap position).nodes := by
  simp only [cacheNode, allocatedNode]

def temporaryItems (heap : Heap) (position : Nat) (values : Tensors) : List PackedReleaseMany.Item :=
  [⟨167, projected2Node heap position, values.projected2⟩,
   ⟨143, activatedNode heap position, values.activated⟩,
   ⟨134, expandedNode heap position, values.expanded⟩,
   ⟨110, normalized2Node heap position, values.normalized2⟩,
   ⟨95, residualNode heap position, values.residual⟩,
   ⟨83, projectionNode heap position, values.projected⟩,
   ⟨59, attentionNode heap position, values.mixed⟩,
   ⟨45, qkvNode heap, values.qkv⟩,
   ⟨21, normalizedNode heap, values.normalized⟩]

def finalHeap (heap : Heap) (position : Nat) : Heap :=
  (((((((((cacheHeap heap position).release (projected2Node heap position)).release
    (activatedNode heap position)).release (expandedNode heap position)).release
    (normalized2Node heap position)).release (residualNode heap position)).release
    (projectionNode heap position)).release (attentionNode heap position)).release
    (qkvNode heap)).release (normalizedNode heap)

theorem temporaryItems_finalHeap (heap : Heap) (position : Nat) (values : Tensors) :
    PackedReleaseMany.finalHeap (cacheHeap heap position) (temporaryItems heap position values) =
      finalHeap heap position := rfl

end Project.Gpt2QuantizedCached.CachedBlock
