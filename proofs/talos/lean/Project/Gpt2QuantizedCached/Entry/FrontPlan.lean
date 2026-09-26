import Project.Gpt2QuantizedCached.Entry.Gate

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open LeanExe.Models.Gpt2 (cachePositionWords)

def cacheResult (weights cache : ByteArray) (token : UInt32) (position : Nat) : CachedResult :=
  selectResult (!finiteWords cache 0 (position * cachePositionWords)) 3
    (hiddenStageResult weights (cachedHidden weights cache token position) position)

def cacheHeap (heap : Heap) (weights cache : ByteArray) (token : UInt32) (position : Nat) : Heap :=
  selectHeap (!finiteWords cache 0 (position * cachePositionWords)) heap (acceptedHeap heap weights cache token position)

def inputResult (weights cache : ByteArray) (token : UInt32) (position : Nat) : CachedResult :=
  selectResult (invalidInput cache token position) 3 (cacheResult weights cache token position)

def inputHeap (heap : Heap) (weights cache : ByteArray) (token : UInt32) (position : Nat) : Heap :=
  selectHeap (invalidInput cache token position) heap (cacheHeap heap weights cache token position)

def finalHeap (heap : Heap) (weights cache : ByteArray) (token : UInt32) (position : Nat) : Heap :=
  selectHeap (!validHeader weights) heap (inputHeap heap weights cache token position)

theorem cachedStep_selected (weights cache : ByteArray) (token : UInt32) (position : Nat) :
    cachedStep weights cache token position = selectResult (!validHeader weights) 1 (inputResult weights cache token position) := by
  rw [cachedStep_eq]
  unfold selectResult inputResult cacheResult
  rw [hiddenStageResult_eq]
  rfl

#print axioms cachedStep_selected
end Project.Gpt2QuantizedCached.Entry
