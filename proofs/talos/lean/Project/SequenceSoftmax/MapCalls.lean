import Project.SequenceSoftmax.Weights
import Project.SequenceSoftmax.Normalize
import Project.SequenceSoftmax.AllocationState

namespace Project.SequenceSoftmax.Spec
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

def MapPost (heap : Heap) (initial : Store Unit) (output : Array UInt64)
    (remaining pageLimit : Nat) (final : Store Unit) (values : List Value) : Prop :=
  values = [.i64 (mapRoot heap output.size), .i64 (mapRoot heap output.size)] ∧
  (heap.allocate (mapCapacity output.size)).At final ∧
  (heap.allocate (mapCapacity output.size)).OwnsWords final
    (allocatedNode heap.top (mapCapacity output.size) heap.nodes) output ∧
  (∀ source input, heap.OwnsWords initial source input →
    (heap.allocate (mapCapacity output.size)).OwnsWords final source input) ∧
  OutputBudget final (heap.allocate (mapCapacity output.size)) remaining pageLimit module

theorem weights_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (owner maximum : UInt64) (source : FreeNode) (input : Array UInt64)
    (remaining pageLimit : Nat) (hHeap : heap.At initial)
    (hInput : heap.OwnsWords initial source input)
    (hBudget : OutputBudget initial heap (48+(mapCapacity input.size).toNat+remaining) pageLimit module) :
    TerminatesWith env module 6 initial [.i64 maximum, .i64 source.root, .i64 owner]
      (MapPost heap initial (weights input maximum) remaining pageLimit) := by
  have hCapacity := map_capacity initial source.root input hInput.buffer.values
  have hBump := hBudget.bump (mapCapacity input.size) (by omega)
  have hSize : (weights input maximum).size = input.size := by simp [weights]
  apply (weights_exact env initial heap owner maximum source input hHeap hInput
    (fun h => ⟨(hBump h).1.le, (hBump h).2⟩)
    (hBudget.pages.trans hBudget.pageLimitBound)).mono
  rintro final values ⟨hValues, hOutput, hWrites⟩
  exact ⟨by simpa only [hSize] using hValues,
    map_finish module heap initial final (weights input maximum) remaining pageLimit hHeap
      (by simpa only [hSize] using hBudget) (by simpa only [hSize] using hCapacity.1)
      (by simpa only [hSize] using hOutput) (by simpa only [hSize] using hWrites)⟩

theorem normalize_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (owner denominator : UInt64) (source : FreeNode) (input : Array UInt64)
    (remaining pageLimit : Nat) (hHeap : heap.At initial)
    (hInput : heap.OwnsWords initial source input)
    (hBudget : OutputBudget initial heap (48+(mapCapacity input.size).toNat+remaining) pageLimit module) :
    TerminatesWith env module 9 initial [.i64 denominator, .i64 source.root, .i64 owner]
      (MapPost heap initial (normalize input denominator) remaining pageLimit) := by
  have hCapacity := map_capacity initial source.root input hInput.buffer.values
  have hBump := hBudget.bump (mapCapacity input.size) (by omega)
  have hSize : (normalize input denominator).size = input.size := by simp [normalize]
  apply (normalize_exact env initial heap owner denominator source input hHeap hInput
    (fun h => ⟨(hBump h).1.le, (hBump h).2⟩)
    (hBudget.pages.trans hBudget.pageLimitBound)).mono
  rintro final values ⟨hValues, hOutput, hWrites⟩
  exact ⟨by simpa only [hSize] using hValues,
    map_finish module heap initial final (normalize input denominator) remaining pageLimit hHeap
      (by simpa only [hSize] using hBudget) (by simpa only [hSize] using hCapacity.1)
      (by simpa only [hSize] using hOutput) (by simpa only [hSize] using hWrites)⟩

#print axioms weights_owned
#print axioms normalize_owned
end Project.SequenceSoftmax.Spec
