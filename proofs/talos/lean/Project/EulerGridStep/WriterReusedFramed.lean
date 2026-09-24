import Project.EulerGridStep.WriterStatus
import Project.EulerGridStep.WriterCopiesFramed
import Project.EulerGridStep.WriterReleasesFramed

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Six reused allocations and five releases preserve any property framed through their exact memory results. -/
theorem writeCell_reused_framed {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (unused allocs releases frees : UInt64)
    (roots : Nat → UInt64) (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (free : List UInt64)
    (hAccepted : cell.status = 0) (hi : 1 + 6 * index + 5 < output.size)
    (hState : BufferState initial output.size (cellLive roots output index cell 0)
      ([roots 1, roots 2, roots 3, roots 4, roots 5, roots 6] ++ free) allocs releases frees)
    (hSlots : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b →
      ObjectsSeparate (roots a) output.size (roots b) output.size)
    (hFree : ∀ a ≤ 6, ∀ other ∈ free, ObjectsSeparate (roots a) output.size other output.size)
    (P : Store Unit → Prop) (hP : P initial)
    (hWriteFrame : ∀ field < 6, ∀ (current final : Store Unit) (next count : UInt64),
      P current → FieldResult (.reuse (roots (field + 1)) (fieldRequest output.size) next count)
        current final (roots field) (cellPrefix output index cell field)
        (1 + 6 * index + field) ((Model.payload cell).getD field 0) → P final)
    (hReleaseFrame : ∀ count, 1 ≤ count → count ≤ 5 →
      ∀ (current final : Store Unit) (next : UInt64), P current →
      ReleaseResult current final (roots count) (fieldRequest output.size) next
        (cellPrefix output index cell count) → P final) :
    TerminatesWith env m 34 initial
      [.i64 cell.courant, .i64 cell.alpha, .i64 cell.pressure, .i64 cell.energy,
        .i64 cell.momentum, .i64 cell.density, .i64 cell.status, .i64 (UInt64.ofNat index),
        .i64 (roots 0), .i64 unused]
      (fun final values => values = [.i64 (roots 6), .i64 (roots 6)] ∧
        BufferState final output.size
          [⟨roots 6, Model.putCell output index cell⟩, ⟨roots 0, output⟩]
          ([roots 1, roots 2, roots 3, roots 4, roots 5] ++ free)
          (allocs + 6) (releases + 5) (frees + 5) ∧
        P final) := by
  refine TerminatesWith.of_wp_entry_for (f := func34Def)
    (by simpa [layout.noImports] using layout.writeCell) ?_ (by simp [layout.noImports])
  change wp m func34 _ initial (writerEntryFrame unused (roots 0) index cell) env
  rw [writer_function_shape, writer_status_shape]
  apply writer_status_spec m env initial (writerEntryFrame unused (roots 0) index cell) cell.status
    (by simp [writerEntryFrame, writerParameters, Locals.get]) rfl
  simp only [hAccepted, ite_true]
  apply wp_iff_cons rfl
  rw [ite_eq_left (by decide : (1 : UInt32) ≠ 0)]
  change wp m (writerAcceptedBody ++ []) _ initial (writerEntryFrame unused (roots 0) index cell) env
  apply writer_copies_framed_spec layout env initial unused allocs releases frees
    roots output index cell free hi hState hSlots hFree
    P hP hWriteFrame _ []
  intro current hCurrent hPCurrent
  change wp m (writerReleaseTail ++ []) _ current (writerStageFrame roots unused index cell 5) env
  apply writer_releases_framed_spec layout env current unused (allocs + 6) releases frees
    roots output index cell free hCurrent hSlots hFree
    P hPCurrent hReleaseFrame _ []
  intro final hFinal hPFinal
  have hOutput := writerReleaseFrame_output roots unused index cell
  rw [wp_nil]
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    writerReleaseFrame_values, copyFrame_ofParts _ (writerReleaseFrame_values roots unused index cell)]
  simp only [wp_localGet_cons, hOutput.1, copyFrame_get_withValues, hOutput.2, wp_nil,
    writerReleaseFrame_values]
  constructor
  · rfl
  · have hKept : cellKept roots output index cell 0 =
        [⟨roots 6, Model.putCell output index cell⟩, ⟨roots 0, output⟩] := by
      change ([⟨roots 6, cellPrefix output index cell 6⟩, ⟨roots 0, output⟩] : List LiveBuffer) = _
      rw [cellPrefix_six]
    exact ⟨by simpa only [hKept] using hFinal, hPFinal⟩

#print axioms writeCell_reused_framed
end Project.EulerGridStep.Execution
