import Project.EulerGridStep.WriterPool
import Project.EulerGridStep.BufferResults

namespace Project.EulerGridStep.Execution
open Wasm

def reusePool (roots : Nat → UInt64) (count : Nat) : List UInt64 :=
  (List.range 6).drop count |>.map (fun k => roots (k + 1))

theorem reusePool_head (roots : Nat → UInt64) (count : Nat) (h : count < 6) :
    reusePool roots count = roots (count + 1) :: reusePool roots (count + 1) := by
  interval_cases count <;> rfl

theorem reusePool_separate (roots : Nat → UInt64) (size slot count : Nat)
    (hSlot : slot ≤ count) (hCount : count ≤ 6)
    (hSlots : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b → ObjectsSeparate (roots a) size (roots b) size) :
    ∀ other ∈ reusePool roots count, ObjectsSeparate (roots slot) size other size := by
  intro other hOther
  simp only [reusePool, List.mem_map] at hOther
  obtain ⟨k, hk, rfl⟩ := hOther
  have hRange : count ≤ k ∧ k < 6 := by
    interval_cases count <;> simp_all [List.range_succ] <;> omega
  exact hSlots slot (by omega) (k + 1) (by omega) (by omega)

def reusedChoice (roots : Nat → UInt64) (allocs : UInt64) (count field : Nat) : FieldAllocation :=
  .reuse (roots (field + 1)) (fieldRequest count)
    ((reusePool roots (field + 1)).headD 0) (allocs + UInt64.ofNat field)

structure ReusedCellState (current : Store Unit) (heapTop : UInt64) (roots : Nat → UInt64)
    (output : Array UInt64) (index : Nat) (cell : Project.EulerCellStep.Model.CheckedCell)
    (field : Nat) (allocs releases frees : UInt64) : Prop where
  buffers : BufferState current output.size (cellLive roots output index cell field)
    (reusePool roots field) (allocs + UInt64.ofNat field) releases frees
  heap : current.globals.globals[0]? = some (.i64 heapTop)

#print axioms reusePool_head
#print axioms reusePool_separate
end Project.EulerGridStep.Execution
