import Project.EulerGridStep.WriterReusedFramed
import Project.EulerGridStep.ProtectedBuffer

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- A writer using six free buffers preserves both the input grid and the separately owned initial output. -/
theorem writeCell_reused_protected {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (unused allocs releases frees : UInt64)
    (roots : Nat → UInt64) (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell)
    (hAccepted : cell.status = 0) (hi : 1 + 6 * index + 5 < output.size)
    (hState : BufferState initial output.size (cellLive roots output index cell 0)
      [roots 1, roots 2, roots 3, roots 4, roots 5, roots 6] allocs releases frees)
    (hSlots : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b → ObjectsSeparate (roots a) output.size (roots b) output.size)
    (observedRoot : UInt64) (observed : Array UInt64)
    (hObserved : UInt64Array.At initial observedRoot observed)
    (hSeparate : ∀ a ≤ 6, ObjectsSeparate (roots a) output.size observedRoot observed.size)
    (protectedBuffer : LiveBuffer) (hProtected : protectedBuffer.At initial output.size)
    (hProtectedSeparate : ∀ a, 1 ≤ a → a ≤ 6 → ObjectsSeparate (roots a) output.size protectedBuffer.root output.size) :
    TerminatesWith env m 34 initial
      [.i64 cell.courant, .i64 cell.alpha, .i64 cell.pressure, .i64 cell.energy,
        .i64 cell.momentum, .i64 cell.density, .i64 cell.status, .i64 (UInt64.ofNat index),
        .i64 (roots 0), .i64 unused]
      (fun final values => values = [.i64 (roots 6), .i64 (roots 6)] ∧
        BufferState final output.size
          [⟨roots 6, Model.putCell output index cell⟩, ⟨roots 0, output⟩]
          [roots 1, roots 2, roots 3, roots 4, roots 5]
          (allocs + 6) (releases + 5) (frees + 5) ∧
        final.mem.pages = initial.mem.pages ∧ UInt64Array.At final observedRoot observed ∧
        protectedBuffer.At final output.size) := by
  apply writeCell_reused_framed layout env initial unused allocs releases frees roots output index
    cell [] hAccepted hi (by simpa using hState) hSlots (by simp)
    (fun current => current.mem.pages = initial.mem.pages ∧
      UInt64Array.At current observedRoot observed ∧ protectedBuffer.At current output.size)
    ⟨rfl, hObserved, hProtected⟩
  · intro field hField current final next count hOld hResult
    refine ⟨hResult.pages.trans hOld.1, ?_, ?_⟩
    · apply hResult.preserves_array observedRoot observed hOld.2.1
      simpa only [cellPrefix_size, FieldAllocation.root] using hSeparate (field + 1) (by omega)
    · apply hResult.preserves_buffer protectedBuffer output.size hOld.2.2
      simpa only [cellPrefix_size, FieldAllocation.root]
        using hProtectedSeparate (field + 1) (by omega) (by omega)
  · intro count hLo hHi current final next hOld hResult
    refine ⟨hResult.pages.trans hOld.1, ?_, ?_⟩
    · apply hResult.preserves_array observedRoot observed hOld.2.1
      simpa only [cellPrefix_size] using hSeparate count (by omega)
    · apply hResult.preserves_buffer protectedBuffer output.size hOld.2.2
      simpa only [cellPrefix_size] using hProtectedSeparate count hLo (by omega)

#print axioms writeCell_reused_protected
end Project.EulerGridStep.Execution
