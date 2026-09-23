import Project.Gpt2QuantizedCached.CachedBlock.Tensors
import Project.Gpt2QuantizedCached.GroupedProjection.Budget
import Project.Gpt2CachedStep.CachedAttention.Budget

namespace Project.Gpt2QuantizedCached.CachedBlock
open Project.ProofKit Project.EulerRiemann.Execution
open GroupedProjection

def residualNeed : UInt64 := PackedCapacity.capacity 3072
def activatedNeed : UInt64 := PackedCapacity.capacity 12288
def cacheNeed : UInt64 := PackedCapacity.capacity 6144

def normalizedHeap (heap : Heap) : Heap := Gpt2CachedStep.LayerNorm.finalHeap heap 1
def qkvHeap (heap : Heap) : Heap := Projection.outputHeap (normalizedHeap heap) 768 2304 1
def attentionHeap (heap : Heap) (position : Nat) : Heap :=
  Gpt2CachedStep.CachedAttention.finalHeap (qkvHeap heap) position
def projectionHeap (heap : Heap) (position : Nat) : Heap :=
  Projection.outputHeap (attentionHeap heap position) 768 768 1
def residualHeap (heap : Heap) (position : Nat) : Heap :=
  (projectionHeap heap position).allocate residualNeed
def normalized2Heap (heap : Heap) (position : Nat) : Heap :=
  Gpt2CachedStep.LayerNorm.finalHeap (residualHeap heap position) 1
def expandedHeap (heap : Heap) (position : Nat) : Heap :=
  Projection.outputHeap (normalized2Heap heap position) 768 3072 1
def activatedHeap (heap : Heap) (position : Nat) : Heap :=
  (expandedHeap heap position).allocate activatedNeed
def projected2Heap (heap : Heap) (position : Nat) : Heap :=
  Projection.outputHeap (activatedHeap heap position) 3072 768 1
def hiddenHeap (heap : Heap) (position : Nat) : Heap :=
  (projected2Heap heap position).allocate residualNeed
def cacheHeap (heap : Heap) (position : Nat) : Heap :=
  (hiddenHeap heap position).allocate cacheNeed

structure Resources (heap : Heap) (position pageCapacity : Nat) : Prop where
  normalized : Gpt2CachedStep.LayerNorm.Resources heap 1 pageCapacity
  qkv : Projection.Resources (normalizedHeap heap) 768 2304 1 pageCapacity
  attention : Gpt2CachedStep.CachedAttention.Resources (qkvHeap heap) position pageCapacity
  projection : Projection.Resources (attentionHeap heap position) 768 768 1 pageCapacity
  residual : Gpt2CachedStep.LayerNorm.AllocationFits (projectionHeap heap position) residualNeed pageCapacity
  normalized2 : Gpt2CachedStep.LayerNorm.Resources (residualHeap heap position) 1 pageCapacity
  expanded : Projection.Resources (normalized2Heap heap position) 768 3072 1 pageCapacity
  activated : Gpt2CachedStep.LayerNorm.AllocationFits (expandedHeap heap position) activatedNeed pageCapacity
  projected2 : Projection.Resources (activatedHeap heap position) 3072 768 1 pageCapacity
  hidden : Gpt2CachedStep.LayerNorm.AllocationFits (projected2Heap heap position) residualNeed pageCapacity
  cache : Gpt2CachedStep.LayerNorm.AllocationFits (hiddenHeap heap position) cacheNeed pageCapacity

end Project.Gpt2QuantizedCached.CachedBlock
