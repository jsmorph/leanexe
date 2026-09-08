import Project.EulerGridStep.MixedCellState
import Project.EulerGridStep.WriterAcceptedSequence
import Project.EulerGridStep.WriterReleaseState

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Complete five-reused/one-fresh writer, retaining a framed property and exact heap/pages. -/
theorem writeCell_mixed_framed {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (unused heapTop allocs releases frees : UInt64)
    (roots : Nat → UInt64) (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell)
    (hAccepted : cell.status = 0) (hi : 1 + 6 * index + 5 < output.size)
    (hState : MixedCellState initial heapTop roots output index cell 0 allocs releases frees)
    (hRoot : roots 6 = heapTop + 48)
    (hSlots : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b → ObjectsSeparate (roots a) output.size (roots b) output.size)
    (P : Store Unit → Prop) (hP : P initial)
    (hWriteFrame : ∀ field < 6, ∀ current final, P current →
      FieldResult (mixedChoice roots heapTop allocs output.size field) current final
        (roots field) (cellPrefix output index cell field) (1 + 6 * index + field)
        ((Model.payload cell).getD field 0) → P final)
    (hReleaseFrame : ∀ count, 1 ≤ count → count ≤ 5 → ∀ current final, P current →
      ReleaseResult current final (roots count) (fieldRequest output.size)
        ((writerPool roots count).headD 0) (cellPrefix output index cell count) → P final) :
    TerminatesWith env m 34 initial
      [.i64 cell.courant, .i64 cell.alpha, .i64 cell.pressure, .i64 cell.energy,
        .i64 cell.momentum, .i64 cell.density, .i64 cell.status, .i64 (UInt64.ofNat index),
        .i64 (roots 0), .i64 unused]
      (fun final values => values = [.i64 (roots 6), .i64 (roots 6)] ∧
        BufferState final output.size
          [⟨roots 6, Model.putCell output index cell⟩, ⟨roots 0, output⟩]
          [roots 1, roots 2, roots 3, roots 4, roots 5]
          (allocs + 6) (releases + 5) (frees + 5) ∧
        final.globals.globals[0]? = some (.i64 (heapTop + 48 + fieldRequest output.size)) ∧
        final.mem.pages = initial.mem.pages ∧ P final) := by
  let W := fun field current =>
    MixedCellState current heapTop roots output index cell field allocs releases frees ∧
      P current ∧ current.mem.pages = initial.mem.pages
  let R := fun count current => ReleasingCellState current (heapTop + 48 + fieldRequest output.size)
    roots output index cell count (allocs + 6) releases frees initial.mem.pages P
  have hRun := writer_accepted_sequence layout env initial unused roots index cell W R hAccepted
    ⟨hState, hP, rfl⟩ (by
      intro field hField current ⟨hCurrent, hObserved, hPages⟩
      apply (mixed_cell_field_call layout env current (writerCallUnused unused roots field)
        heapTop allocs releases frees roots output index field cell hField hi hCurrent hRoot hSlots).mono
      rintro final values ⟨hValues, hNext, hResult⟩
      exact ⟨hValues, hNext, hWriteFrame field hField current final hObserved hResult,
        hResult.pages.trans hPages⟩) (by
      intro current ⟨hCurrent, hObserved, hPages⟩
      apply releasing_cell_start current (heapTop + 48 + fieldRequest output.size) roots output index cell
        (allocs + 6) releases frees initial.mem.pages P
      · simpa only [writerPool, List.drop_succ_cons, List.drop_nil,
          show UInt64.ofNat 6 = 6 from rfl] using hCurrent.buffers
      · simpa [mixedHeap] using hCurrent.heap
      · exact hPages
      · exact hObserved) (by
      intro count hLo hHi current hCurrent
      exact releasing_cell_call layout env current (heapTop + 48 + fieldRequest output.size)
        (allocs + 6) releases frees roots output index count cell initial.mem.pages P hLo hHi
        hCurrent hSlots (fun final hResult =>
          hReleaseFrame count hLo hHi current final hCurrent.observed hResult))
  apply hRun.mono
  intro final values ⟨hValues, hFinal⟩
  have hKept : cellKept roots output index cell 0 =
      [⟨roots 6, Model.putCell output index cell⟩, ⟨roots 0, output⟩] := by
    change ([⟨roots 6, cellPrefix output index cell 6⟩, ⟨roots 0, output⟩] : List LiveBuffer) = _
    rw [cellPrefix_six]
  exact ⟨hValues, by simpa only [hKept, writerPool, List.drop_zero, Nat.sub_zero,
    show UInt64.ofNat 5 = 5 from rfl] using hFinal.buffers,
    hFinal.heap, hFinal.pages, hFinal.observed⟩

#print axioms writeCell_mixed_framed
end Project.EulerGridStep.Execution
