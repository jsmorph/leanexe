import Project.Gpt2CachedStep.CachedHidden.FrozenLayerOldRelease
import Project.Gpt2CachedStep.CachedBlock.FrozenResources

namespace Project.Gpt2CachedStep.Frozen.CachedHidden
open Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

def updatesNeed (layer : Nat) : UInt64 := PackedCapacity.capacity (UInt64.ofNat (layer * 6144 + 6144))

def updatesNode (heap : Heap) (position layer : Nat) : FreeNode :=
  allocatedNode (CachedBlock.finalHeap heap position).top (updatesNeed layer) (CachedBlock.finalHeap heap position).nodes

def appendHeap (heap : Heap) (position layer : Nat) : Heap :=
  (CachedBlock.finalHeap heap position).allocate (updatesNeed layer)

def cacheReleasedHeap (heap : Heap) (position layer : Nat) : Heap :=
  (appendHeap heap position layer).release (CachedBlock.cacheNode heap position)

def stepHeap (heap : Heap) (input updates : FreeNode) (position layer : Nat) : Heap :=
  oldReleaseHeap (cacheReleasedHeap heap position layer) input updates layer

structure LayerResources (heap : Heap) (position layer pageCap : Nat) : Prop where
  block : CachedBlock.Resources heap position pageCap
  append : LayerNorm.AllocationFits (CachedBlock.finalHeap heap position) (updatesNeed layer) pageCap

end Project.Gpt2CachedStep.Frozen.CachedHidden
