import Project.Gpt2CachedStep.CachedBlock.FrozenAttention
import Project.Gpt2CachedStep.CachedBlock.FrozenNormalized2
import Project.Gpt2CachedStep.CachedBlock.FrozenActivated
import Project.Gpt2CachedStep.CachedBlock.FrozenProjected2
import Project.Gpt2CachedStep.CachedBlock.FrozenHidden
import Project.Gpt2CachedStep.CachedBlock.FrozenCache
import Project.Gpt2CachedStep.CachedBlock.FrozenCleanup
import Project.Gpt2CachedStep.CachedBlock.FrozenTensors
import Project.Gpt2CachedStep.LayerNorm.FrozenFresh
import Project.Gpt2CachedStep.CachedAttention.FrozenFresh
import Project.ProofKit.PackedOwners
import Project.ProofKit.PackedBindings

namespace Project.Gpt2CachedStep.Frozen.CachedBlock
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution LeanExe.Models.Gpt2
open LayerNorm (AllocationFits)

def normalizedHeap (heap : Heap) : Heap := LayerNorm.finalHeap heap 1
def qkvHeap (heap : Heap) : Heap := (normalizedHeap heap).allocate qkvNeed
def attentionHeap (heap : Heap) (position : Nat) : Heap := CachedAttention.finalHeap (qkvHeap heap) position
def projectionHeap (heap : Heap) (position : Nat) : Heap := (attentionHeap heap position).allocate projectionNeed
def residualHeap (heap : Heap) (position : Nat) : Heap := (projectionHeap heap position).allocate projectionNeed
def normalized2Heap (heap : Heap) (position : Nat) : Heap := LayerNorm.finalHeap (residualHeap heap position) 1
def expandedHeap (heap : Heap) (position : Nat) : Heap := (normalized2Heap heap position).allocate expandedNeed
def activatedHeap (heap : Heap) (position : Nat) : Heap := (expandedHeap heap position).allocate expandedNeed
def projected2Heap (heap : Heap) (position : Nat) : Heap := (activatedHeap heap position).allocate projected2Need
def hiddenHeap (heap : Heap) (position : Nat) : Heap := (projected2Heap heap position).allocate projectionNeed
def cacheHeap (heap : Heap) (position : Nat) : Heap := (hiddenHeap heap position).allocate cacheNeed

def normalizedNode (heap : Heap) : FreeNode := LayerNorm.outputNode heap 1
def qkvNode (heap : Heap) : FreeNode := allocatedNode (normalizedHeap heap).top qkvNeed (normalizedHeap heap).nodes
def attentionNode (heap : Heap) (position : Nat) : FreeNode := CachedAttention.outputNode (qkvHeap heap) position
def projectionNode (heap : Heap) (position : Nat) : FreeNode :=
  allocatedNode (attentionHeap heap position).top projectionNeed (attentionHeap heap position).nodes
def residualNode (heap : Heap) (position : Nat) : FreeNode :=
  allocatedNode (projectionHeap heap position).top projectionNeed (projectionHeap heap position).nodes
def normalized2Node (heap : Heap) (position : Nat) : FreeNode := LayerNorm.outputNode (residualHeap heap position) 1
def expandedNode (heap : Heap) (position : Nat) : FreeNode :=
  allocatedNode (normalized2Heap heap position).top expandedNeed (normalized2Heap heap position).nodes
def activatedNode (heap : Heap) (position : Nat) : FreeNode :=
  allocatedNode (expandedHeap heap position).top expandedNeed (expandedHeap heap position).nodes
def projected2Node (heap : Heap) (position : Nat) : FreeNode :=
  allocatedNode (activatedHeap heap position).top projected2Need (activatedHeap heap position).nodes
def hiddenNode (heap : Heap) (position : Nat) : FreeNode :=
  allocatedNode (projected2Heap heap position).top projectionNeed (projected2Heap heap position).nodes
def cacheNode (heap : Heap) (position : Nat) : FreeNode :=
  allocatedNode (hiddenHeap heap position).top cacheNeed (hiddenHeap heap position).nodes

def temporaryItems (heap : Heap) (position : Nat) (values : Tensors) : List PackedReleaseMany.Item :=
  [⟨139, projected2Node heap position, values.projected2⟩,
   ⟨122, activatedNode heap position, values.activated⟩,
   ⟨113, expandedNode heap position, values.expanded⟩,
   ⟨96, normalized2Node heap position, values.normalized2⟩,
   ⟨81, residualNode heap position, values.residual⟩,
   ⟨69, projectionNode heap position, values.projected⟩,
   ⟨52, attentionNode heap position, values.mixed⟩,
   ⟨38, qkvNode heap, values.qkv⟩,
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

structure Resources (heap : Heap) (position pageCapacity : Nat) : Prop where
  normalized : LayerNorm.Resources heap 1 pageCapacity
  qkv : AllocationFits (normalizedHeap heap) qkvNeed pageCapacity
  attention : CachedAttention.Resources (qkvHeap heap) position pageCapacity
  projection : AllocationFits (attentionHeap heap position) projectionNeed pageCapacity
  residual : AllocationFits (projectionHeap heap position) projectionNeed pageCapacity
  normalized2 : LayerNorm.Resources (residualHeap heap position) 1 pageCapacity
  expanded : AllocationFits (normalized2Heap heap position) expandedNeed pageCapacity
  activated : AllocationFits (expandedHeap heap position) expandedNeed pageCapacity
  projected2 : AllocationFits (activatedHeap heap position) projected2Need pageCapacity
  hidden : AllocationFits (projected2Heap heap position) projectionNeed pageCapacity
  cache : AllocationFits (hiddenHeap heap position) cacheNeed pageCapacity

structure WeightExtents (weights : ByteArray) (base : Nat) : Prop where
  normalized : (base + 1536) * 4 ≤ weights.size
  qkv : (base + qkvBiasOffset + 2304) * 4 ≤ weights.size
  projection : (base + attnBiasOffset + 768) * 4 ≤ weights.size
  normalized2 : (base + ln2BiasOffset + 768) * 4 ≤ weights.size
  expanded : (base + fcBiasOffset + 3072) * 4 ≤ weights.size
  projected2 : (base + mlpBiasOffset + 768) * 4 ≤ weights.size

theorem weightExtents (weights : ByteArray) (base : Nat)
    (h : (base + blockWords) * 4 ≤ weights.size) : WeightExtents weights base := by
  have lower (offset : Nat) (hOffset : offset ≤ blockWords) : (base + offset) * 4 ≤ weights.size :=
    (Nat.mul_le_mul_right 4 (Nat.add_le_add_left hOffset base)).trans h
  refine ⟨lower 1536 (by decide), ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [Nat.add_assoc] <;> exact lower _ (by decide)

end Project.Gpt2CachedStep.Frozen.CachedBlock
