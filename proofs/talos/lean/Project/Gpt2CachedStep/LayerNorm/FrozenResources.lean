import Project.Gpt2CachedStep.LayerNorm.FrozenCleanup

namespace Project.Gpt2CachedStep.Frozen.LayerNorm
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

def meansHeap (heap : Heap) (rows : Nat) : Heap := heap.allocate (temporaryNeed rows)

def inversesHeap (heap : Heap) (rows : Nat) : Heap := (meansHeap heap rows).allocate (temporaryNeed rows)

def outputHeap (heap : Heap) (rows : Nat) : Heap := (inversesHeap heap rows).allocate (outputNeed rows)

def meansNode (heap : Heap) (rows : Nat) : FreeNode :=
  allocatedNode heap.top (temporaryNeed rows) heap.nodes

def inversesNode (heap : Heap) (rows : Nat) : FreeNode :=
  allocatedNode (meansHeap heap rows).top (temporaryNeed rows) (meansHeap heap rows).nodes

def outputNode (heap : Heap) (rows : Nat) : FreeNode :=
  allocatedNode (inversesHeap heap rows).top (outputNeed rows) (inversesHeap heap rows).nodes

def finalHeap (heap : Heap) (rows : Nat) : Heap :=
  ((outputHeap heap rows).release (inversesNode heap rows)).release (meansNode heap rows)

def AllocationFits (heap : Heap) (need : UInt64) (pageCapacity : Nat) : Prop :=
  takeFirstFitFrom 0 need heap.nodes = none →
    heap.top.toNat + 48 + need.toNat < 4294967296 ∧
    FixedArrayBump.requiredPages heap.top need ≤ pageCapacity

structure Resources (heap : Heap) (rows pageCapacity : Nat) : Prop where
  means : AllocationFits heap (temporaryNeed rows) pageCapacity
  inverses : AllocationFits (meansHeap heap rows) (temporaryNeed rows) pageCapacity
  output : AllocationFits (inversesHeap heap rows) (outputNeed rows) pageCapacity

end Project.Gpt2CachedStep.Frozen.LayerNorm
