import Project.EulerGridStep.WriterStatus
import Project.EulerGridStep.WriterSequence
import Project.EulerGridStep.WriterReleaseSequence

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Complete accepted writer control, parameterized by proved write and release invariants. -/
theorem writer_accepted_sequence {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (unused : UInt64)
    (roots : Nat → UInt64) (index : Nat) (cell : Project.EulerCellStep.Model.CheckedCell)
    (W R : Nat → Store Unit → Prop) (hAccepted : cell.status = 0) (hInitial : W 0 initial)
    (hWrite : ∀ field < 6, ∀ current, W field current →
      TerminatesWith env m 27 current
        [.i64 ((Model.payload cell).getD field 0), .i64 (UInt64.ofNat field),
          .i64 (UInt64.ofNat index), .i64 (roots field), .i64 (writerCallUnused unused roots field)]
        (fun final values => values = [.i64 (roots (field + 1)), .i64 (roots (field + 1))] ∧
          W (field + 1) final))
    (hBridge : ∀ current, W 6 current → R 5 current ∧
      ∀ count, 1 ≤ count → count ≤ 5 → roots count ≠ 0)
    (hRelease : ∀ count, 1 ≤ count → count ≤ 5 → ∀ current, R count current →
      TerminatesWith env m 40 current [.i64 (roots count)]
        (fun final values => values = [] ∧ R (count - 1) final)) :
    TerminatesWith env m 34 initial
      [.i64 cell.courant, .i64 cell.alpha, .i64 cell.pressure, .i64 cell.energy,
        .i64 cell.momentum, .i64 cell.density, .i64 cell.status, .i64 (UInt64.ofNat index),
        .i64 (roots 0), .i64 unused]
      (fun final values => values = [.i64 (roots 6), .i64 (roots 6)] ∧ R 0 final) := by
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
  apply writer_sequence_spec m env initial unused roots index cell W hInitial hWrite _ []
  intro current hCurrent
  obtain ⟨hReady, hNonzero⟩ := hBridge current hCurrent
  change wp m (writerReleaseTail ++ []) _ current (writerStageFrame roots unused index cell 5) env
  apply writer_release_sequence_spec m env current unused roots index cell R hReady hNonzero
    hRelease _ []
  intro final hFinal
  have hOutput := writerReleaseFrame_output roots unused index cell
  rw [wp_nil]
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    writerReleaseFrame_values, copyFrame_ofParts _ (writerReleaseFrame_values roots unused index cell)]
  simp only [wp_localGet_cons, hOutput.1, copyFrame_get_withValues, hOutput.2, wp_nil,
    writerReleaseFrame_values]
  exact ⟨rfl, hFinal⟩

#print axioms writer_accepted_sequence
end Project.EulerGridStep.Execution
