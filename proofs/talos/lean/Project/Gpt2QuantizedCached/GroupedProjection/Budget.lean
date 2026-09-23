import Project.Gpt2QuantizedCached.GroupedProjection.Linear
import Project.Gpt2CachedStep.LayerNorm.Budget

namespace Project.Gpt2QuantizedCached.GroupedProjection.Projection
open Project.ProofKit Project.EulerRiemann.Execution Project.Gpt2QuantizedLinearRows
open Project.Gpt2CachedStep.LayerNorm (AllocationFits)

structure Resources (heap : Heap) (width outputWidth rows pageCapacity : Nat) : Prop where
  scales : AllocationFits heap (QuantizeRows.scaleNeed (rows * (width / 64))) pageCapacity
  values : AllocationFits (heap.allocate (QuantizeRows.scaleNeed (rows * (width / 64))))
    (QuantizeRows.byteNeed 64 (rows * (width / 64))) pageCapacity
  output : AllocationFits (QuantizeRows.outputHeap heap 64 (rows * (width / 64)))
    (need outputWidth rows) pageCapacity

def allocationBudget (width outputWidth rows : Nat) : Nat :=
  144 + (QuantizeRows.scaleNeed (rows * (width / 64))).toNat +
    (QuantizeRows.byteNeed 64 (rows * (width / 64))).toNat + (need outputWidth rows).toNat

theorem outputHeap_top (heap : Heap) (width outputWidth rows : Nat) :
    (outputHeap heap width outputWidth rows).top.toNat ≤
      heap.top.toNat + allocationBudget width outputWidth rows := by
  have hScale := heap.allocate_top_le (QuantizeRows.scaleNeed (rows * (width / 64)))
  have hByte := (heap.allocate (QuantizeRows.scaleNeed (rows * (width / 64)))).allocate_top_le
    (QuantizeRows.byteNeed 64 (rows * (width / 64)))
  have hOutput := (QuantizeRows.outputHeap heap 64 (rows * (width / 64))).allocate_top_le
    (need outputWidth rows)
  simp only [QuantizeRows.outputHeap] at hOutput
  simp only [outputHeap, Heap.release_top, QuantizeRows.outputHeap, allocationBudget]
  omega

theorem budget (heap : Heap) (width outputWidth rows : Nat)
    (h : heap.top.toNat + allocationBudget width outputWidth rows < 4294967296) :
    Resources heap width outputWidth rows 65536 := by
  have hScale := heap.allocate_top_le (QuantizeRows.scaleNeed (rows * (width / 64)))
  have hByte := (heap.allocate (QuantizeRows.scaleNeed (rows * (width / 64)))).allocate_top_le
    (QuantizeRows.byteNeed 64 (rows * (width / 64)))
  simp only [allocationBudget] at h
  constructor <;> apply AllocationFits.of_bound
  · omega
  · omega
  · simp only [QuantizeRows.outputHeap]
    omega

#print axioms outputHeap_top
#print axioms budget
end Project.Gpt2QuantizedCached.GroupedProjection.Projection
