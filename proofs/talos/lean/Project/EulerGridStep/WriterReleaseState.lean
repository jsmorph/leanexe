import Project.EulerGridStep.CellReleaseHeap
import Project.EulerGridStep.WriterPool

namespace Project.EulerGridStep.Execution
open Wasm

/-- Release-stage storage, exact heap/page state, and a framed observation. -/
structure ReleasingCellState (current : Store Unit) (heap : UInt64) (roots : Nat → UInt64)
    (output : Array UInt64) (index : Nat) (cell : Project.EulerCellStep.Model.CheckedCell)
    (count : Nat) (allocs releases frees : UInt64) (pages : Nat) (P : Store Unit → Prop) : Prop where
  buffers : BufferState current output.size (cellKept roots output index cell count)
    (writerPool roots count) allocs (releases + UInt64.ofNat (5 - count)) (frees + UInt64.ofNat (5 - count))
  heap : current.globals.globals[0]? = some (.i64 heap)
  pages : current.mem.pages = pages
  observed : P current

/-- The six completed writes supply the first release state and all non-null guards. -/
theorem releasing_cell_start (current : Store Unit) (heap : UInt64) (roots : Nat → UInt64)
    (output : Array UInt64) (index : Nat) (cell : Project.EulerCellStep.Model.CheckedCell)
    (allocs releases frees : UInt64) (pages : Nat) (P : Store Unit → Prop)
    (hBuffers : BufferState current output.size (cellLive roots output index cell 6) [] allocs releases frees)
    (hHeap : current.globals.globals[0]? = some (.i64 heap))
    (hPages : current.mem.pages = pages) (hP : P current) :
    ReleasingCellState current heap roots output index cell 5 allocs releases frees pages P ∧
      ∀ count, 1 ≤ count → count ≤ 5 → roots count ≠ 0 := by
  refine ⟨⟨?_, hHeap, hPages, hP⟩, ?_⟩
  · change BufferState current output.size (cellLive roots output index cell 6) [] allocs
      (releases + 0) (frees + 0)
    simpa only [UInt64.add_zero] using hBuffers
  · intro count _ hHi hz
    have hLive := hBuffers.liveAt ⟨roots count, cellPrefix output index cell count⟩
      (cellLive_contains roots output index cell 6 count (by omega))
    have h48 := hLive.2.1.root48
    rw [hz] at h48
    simp at h48

/-- One exact release advances the shared release invariant without moving the heap. -/
theorem releasing_cell_call {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (heap allocs releases frees : UInt64)
    (roots : Nat → UInt64) (output : Array UInt64) (index count : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (pages : Nat) (P : Store Unit → Prop)
    (hLo : 1 ≤ count) (hHi : count ≤ 5)
    (hState : ReleasingCellState initial heap roots output index cell count allocs releases frees pages P)
    (hSlots : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b → ObjectsSeparate (roots a) output.size (roots b) output.size)
    (hPreserve : ∀ final, ReleaseResult initial final (roots count) (fieldRequest output.size)
      ((writerPool roots count).headD 0) (cellPrefix output index cell count) → P final) :
    TerminatesWith env m 40 initial [.i64 (roots count)]
      (fun final values => values = [] ∧
        ReleasingCellState final heap roots output index cell (count - 1) allocs releases frees pages P) := by
  have hCall := cell_release_call_heap layout env initial allocs
    (releases + UInt64.ofNat (5 - count)) (frees + UInt64.ofNat (5 - count)) roots output index count
    cell (writerPool roots count) hLo hHi hState.buffers hSlots
    (writerPool_separate roots output.size count count (by omega) hHi hSlots)
  apply hCall.mono
  rintro final values ⟨hValues, hResult, hBuffers, hHeap⟩
  refine ⟨hValues, ⟨?_, hHeap.trans hState.heap, hResult.pages.trans hState.pages, hPreserve final hResult⟩⟩
  have hCount : 5 - (count - 1) = (5 - count) + 1 := by omega
  simpa only [writerPool_release roots count hLo hHi, hCount, UInt64.ofNat_add,
    show UInt64.ofNat 1 = 1 from rfl, UInt64.add_assoc] using hBuffers

#print axioms releasing_cell_start
#print axioms releasing_cell_call
end Project.EulerGridStep.Execution
