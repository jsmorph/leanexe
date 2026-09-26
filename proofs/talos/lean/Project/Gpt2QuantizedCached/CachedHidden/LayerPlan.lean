import Project.Gpt2QuantizedCached.CachedBlock.SourceOutputs
import Project.Gpt2QuantizedCached.CachedBlock.ExecutionBudget
import Project.ProofKit.PackedAppend

namespace Project.Gpt2QuantizedCached.CachedHidden
open Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open Project.Gpt2CachedStep.LayerNorm (AllocationFits)

def appendedHeap (heap : Heap) (position : Nat) (values : CachedBlock.Tensors)
    (updates : ByteArray) (output : HiddenResult) : Heap :=
  (CachedBlock.executionHeap heap position values).allocate (PackedAppend.need updates output.cache)

def updatesNode (heap : Heap) (position : Nat) (values : CachedBlock.Tensors)
    (updates : ByteArray) (output : HiddenResult) : FreeNode :=
  allocatedNode (CachedBlock.executionHeap heap position values).top
    (PackedAppend.need updates output.cache) (CachedBlock.executionHeap heap position values).nodes

def cacheReleasedHeap (heap : Heap) (position : Nat) (values : CachedBlock.Tensors)
    (updates : ByteArray) (output : HiddenResult) : Heap :=
  if output.status = 0 then
    (appendedHeap heap position values updates output).release (CachedBlock.cacheNode heap position)
  else appendedHeap heap position values updates output

def oldReleasedHeap (heap : Heap) (input updates : FreeNode) (layer : Nat) : Heap :=
  if layer = 0 then heap else (heap.release updates).release input

def activeHeap (heap : Heap) (inputNode oldUpdates : FreeNode) (position layer : Nat)
    (values : CachedBlock.Tensors) (updates : ByteArray) (output : HiddenResult) : Heap :=
  oldReleasedHeap (cacheReleasedHeap heap position values updates output) inputNode oldUpdates layer

structure LayerResources (heap : Heap) (position : Nat) (values : CachedBlock.Tensors)
    (updates : ByteArray) (output : HiddenResult) (pageCap : Nat) : Prop where
  block : CachedBlock.Resources heap position pageCap
  append : AllocationFits (CachedBlock.executionHeap heap position values)
    (PackedAppend.need updates output.cache) pageCap

theorem oldReleasedHeap_top (heap : Heap) (input updates : FreeNode) (layer : Nat) :
    (oldReleasedHeap heap input updates layer).top = heap.top := by
  simp only [oldReleasedHeap, apply_ite, Heap.release_top, ite_self]

theorem cacheReleasedHeap_top (heap : Heap) (position : Nat) (values : CachedBlock.Tensors)
    (updates : ByteArray) (output : HiddenResult) :
    (cacheReleasedHeap heap position values updates output).top =
      (appendedHeap heap position values updates output).top := by
  simp only [cacheReleasedHeap, apply_ite, Heap.release_top, ite_self]

#print axioms oldReleasedHeap_top
#print axioms cacheReleasedHeap_top
end Project.Gpt2QuantizedCached.CachedHidden
