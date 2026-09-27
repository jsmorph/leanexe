import Project.Gpt2CachedStep.CachedAttention.Cleanup
import Project.Gpt2CachedStep.LayerNorm.Resources

namespace Project.Gpt2CachedStep.CachedAttention
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open Project.Gpt2CachedStep.LayerNorm (AllocationFits)

def scoresHeap (heap : Heap) (position : Nat) : Heap := heap.allocate (scoresNeed position)
def maximaHeap (heap : Heap) (position : Nat) : Heap := (scoresHeap heap position).allocate maximaNeed
def exponentialsHeap (heap : Heap) (position : Nat) : Heap := (maximaHeap heap position).allocate (scoresNeed position)
def sumsHeap (heap : Heap) (position : Nat) : Heap := (exponentialsHeap heap position).allocate maximaNeed
def probabilitiesHeap (heap : Heap) (position : Nat) : Heap := (sumsHeap heap position).allocate (scoresNeed position)
def outputHeap (heap : Heap) (position : Nat) : Heap := (probabilitiesHeap heap position).allocate mixedNeed

def scoresNode (heap : Heap) (position : Nat) : FreeNode := allocatedNode heap.top (scoresNeed position) heap.nodes

def maximaNode (heap : Heap) (position : Nat) : FreeNode :=
  allocatedNode (scoresHeap heap position).top maximaNeed (scoresHeap heap position).nodes

def exponentialsNode (heap : Heap) (position : Nat) : FreeNode :=
  allocatedNode (maximaHeap heap position).top (scoresNeed position) (maximaHeap heap position).nodes

def sumsNode (heap : Heap) (position : Nat) : FreeNode :=
  allocatedNode (exponentialsHeap heap position).top maximaNeed (exponentialsHeap heap position).nodes

def probabilitiesNode (heap : Heap) (position : Nat) : FreeNode :=
  allocatedNode (sumsHeap heap position).top (scoresNeed position) (sumsHeap heap position).nodes

def outputNode (heap : Heap) (position : Nat) : FreeNode :=
  allocatedNode (probabilitiesHeap heap position).top mixedNeed (probabilitiesHeap heap position).nodes

def finalHeap (heap : Heap) (position : Nat) : Heap :=
  cleanupHeap (outputHeap heap position) (scoresNode heap position) (maximaNode heap position)
    (exponentialsNode heap position) (sumsNode heap position) (probabilitiesNode heap position)

structure Resources (heap : Heap) (position pageCapacity : Nat) : Prop where
  scores : AllocationFits heap (scoresNeed position) pageCapacity
  maxima : AllocationFits (scoresHeap heap position) maximaNeed pageCapacity
  exponentials : AllocationFits (maximaHeap heap position) (scoresNeed position) pageCapacity
  sums : AllocationFits (exponentialsHeap heap position) maximaNeed pageCapacity
  probabilities : AllocationFits (sumsHeap heap position) (scoresNeed position) pageCapacity
  output : AllocationFits (probabilitiesHeap heap position) mixedNeed pageCapacity

end Project.Gpt2CachedStep.CachedAttention
