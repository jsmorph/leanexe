import Project.EulerGridStep.FreshCellState
import Project.EulerGridStep.WriterAcceptedSequence
import Project.EulerGridStep.WriterReleaseState

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Complete first accepted writer with exact heap/pages and a property framed through every call. -/
theorem writeCell_fresh_framed {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (unused allocs releases frees : UInt64)
    (base : Nat) (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell)
    (hAccepted : cell.status = 0) (hi : 1 + 6 * index + 5 < output.size)
    (hState : FreshCellState initial base output index cell 0 allocs releases frees)
    (P : Store Unit → Prop) (hP : P initial)
    (hWriteFrame : ∀ field < 6, ∀ current final, P current →
      FieldResult (.fresh (arenaHeap base output.size (field + 1)) (allocs + UInt64.ofNat field)) current final
        (arenaRoot base output.size field) (cellPrefix output index cell field) (1 + 6 * index + field)
        ((Model.payload cell).getD field 0) → P final)
    (hReleaseFrame : ∀ count, 1 ≤ count → count ≤ 5 → ∀ current final, P current →
      ReleaseResult current final (arenaRoot base output.size count) (fieldRequest output.size)
        ((writerPool (arenaRoot base output.size) count).headD 0) (cellPrefix output index cell count) → P final) :
    TerminatesWith env m 34 initial
      [.i64 cell.courant, .i64 cell.alpha, .i64 cell.pressure, .i64 cell.energy,
        .i64 cell.momentum, .i64 cell.density, .i64 cell.status, .i64 (UInt64.ofNat index),
        .i64 (arenaRoot base output.size 0), .i64 unused]
      (fun final values =>
        values = [.i64 (arenaRoot base output.size 6), .i64 (arenaRoot base output.size 6)] ∧
        BufferState final output.size
          [⟨arenaRoot base output.size 6, Model.putCell output index cell⟩,
            ⟨arenaRoot base output.size 0, output⟩]
          [arenaRoot base output.size 1, arenaRoot base output.size 2, arenaRoot base output.size 3,
            arenaRoot base output.size 4, arenaRoot base output.size 5]
          (allocs + 6) (releases + 5) (frees + 5) ∧
        final.globals.globals[0]? = some (.i64 (arenaHeap base output.size 7)) ∧
        final.mem.pages = initial.mem.pages ∧ P final) := by
  let roots := arenaRoot base output.size
  have hBudget := hState.budget
  have hPages := hState.buffers.pages
  have hBudget32 : base + 7 * arenaObjectSize output.size ≤ 4294967296 := by omega
  have hSlots : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b →
      ObjectsSeparate (roots a) output.size (roots b) output.size := by
    intro a ha b hb hne
    exact arena_roots_separate base output.size a b ha hb hne hBudget32
  let W := fun field current =>
    FreshCellState current base output index cell field allocs releases frees ∧
      P current ∧ current.mem.pages = initial.mem.pages
  let R := fun count current => ReleasingCellState current (arenaHeap base output.size 7)
    roots output index cell count (allocs + 6) releases frees initial.mem.pages P
  have hRun := writer_accepted_sequence layout env initial unused roots index cell W R hAccepted
    ⟨hState, hP, rfl⟩ (by
      intro field hField current ⟨hCurrent, hObserved, hPages⟩
      apply (fresh_cell_field_call layout env current (writerCallUnused unused roots field)
        allocs releases frees base output index field cell hField hi hCurrent).mono
      rintro final values ⟨hValues, hNext, hResult⟩
      exact ⟨hValues, hNext, hWriteFrame field hField current final hObserved hResult,
        hResult.pages.trans hPages⟩) (by
      intro current ⟨hCurrent, hObserved, hPages⟩
      apply releasing_cell_start current (arenaHeap base output.size 7) roots output index cell
        (allocs + 6) releases frees initial.mem.pages P
      · simpa only [show UInt64.ofNat 6 = 6 from rfl] using hCurrent.buffers
      · exact hCurrent.heap
      · exact hPages
      · exact hObserved) (by
      intro count hLo hHi current hCurrent
      exact releasing_cell_call layout env current (arenaHeap base output.size 7)
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


#print axioms writeCell_fresh_framed
end Project.EulerGridStep.Execution
