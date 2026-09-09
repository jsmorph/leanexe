import Project.EulerGridStep.MixedWriterAccepted
import Project.EulerGridStep.ProtectedBuffer

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- The complete later writer also preserves a separately owned buffer for final release. -/
theorem writeCell_mixed_protected {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (unused heapTop allocs releases frees : UInt64)
    (roots : Nat → UInt64) (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell)
    (hAccepted : cell.status = 0) (hi : 1 + 6 * index + 5 < output.size)
    (hState : MixedCellState initial heapTop roots output index cell 0 allocs releases frees)
    (hRoot : roots 6 = heapTop + 48)
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
        final.globals.globals[0]? = some (.i64 (heapTop + 48 + fieldRequest output.size)) ∧
        final.mem.pages = initial.mem.pages ∧ UInt64Array.At final observedRoot observed ∧
        protectedBuffer.At final output.size) := by
  apply writeCell_mixed_framed layout env initial unused heapTop allocs releases frees roots output index
    cell hAccepted hi hState hRoot hSlots (fun current => UInt64Array.At current observedRoot observed ∧ protectedBuffer.At current output.size)
    ⟨hObserved, hProtected⟩
  · intro field hField current final hOld hResult
    refine ⟨?_, ?_⟩
    · apply hResult.preserves_array observedRoot observed hOld.1
      simpa only [cellPrefix_size, mixedChoice_root roots heapTop allocs output.size field hField hRoot]
        using hSeparate (field + 1) (by omega)
    · apply hResult.preserves_buffer protectedBuffer output.size hOld.2
      simpa only [cellPrefix_size, mixedChoice_root roots heapTop allocs output.size field hField hRoot]
        using hProtectedSeparate (field + 1) (by omega) (by omega)
  · intro count hLo hHi current final hOld hResult
    refine ⟨?_, ?_⟩
    · apply hResult.preserves_array observedRoot observed hOld.1
      simpa only [cellPrefix_size] using hSeparate count (by omega)
    · apply hResult.preserves_buffer protectedBuffer output.size hOld.2
      simpa only [cellPrefix_size] using hProtectedSeparate count hLo (by omega)

#print axioms writeCell_mixed_protected
end Project.EulerGridStep.Execution
