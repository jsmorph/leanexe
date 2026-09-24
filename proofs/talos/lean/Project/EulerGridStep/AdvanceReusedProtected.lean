import Project.EulerGridStep.AdvanceExecution
import Project.EulerGridStep.WriterReusedProtected

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- An accepted advance reuses all six available buffers while preserving its source and initial output. -/
theorem advanceAt_reused_protected {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused allocs releases frees : UInt64)
    (roots : Nat → UInt64) (input output : Array UInt64) (index : Nat)
    (hInput : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (hAccepted : (Model.cellAt ratio input index).status = 0)
    (hOutputIndex : 1 + 6 * index + 5 < output.size)
    (hState : BufferState initial output.size (cellLive roots output index (Model.cellAt ratio input index) 0)
      [roots 1, roots 2, roots 3, roots 4, roots 5, roots 6] allocs releases frees)
    (hSlots : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b → ObjectsSeparate (roots a) output.size (roots b) output.size)
    (hSeparate : ∀ a ≤ 6, ObjectsSeparate (roots a) output.size pointer input.size)
    (protectedBuffer : LiveBuffer) (hProtected : protectedBuffer.At initial output.size)
    (hProtectedSeparate : ∀ a, 1 ≤ a → a ≤ 6 → ObjectsSeparate (roots a) output.size protectedBuffer.root output.size) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat index), .i64 (roots 0), .i64 unused, .i64 pointer, .i64 inputUnused, .i64 ratio]
      (fun final values => values = [.i64 (roots 6), .i64 (roots 6)] ∧
        BufferState final output.size
          [⟨roots 6, Model.advanceAt ratio input output index⟩, ⟨roots 0, output⟩]
          [roots 1, roots 2, roots 3, roots 4, roots 5]
          (allocs + 6) (releases + 5) (frees + 5) ∧
        final.mem.pages = initial.mem.pages ∧ UInt64Array.At final pointer input ∧
        protectedBuffer.At final output.size) := by
  apply advanceAt_with_writer layout env initial ratio inputUnused pointer unused (roots 0) (roots 6)
    input index hInput hi
  have hWriter := writeCell_reused_protected layout env initial unused allocs releases frees
    roots output index (Model.cellAt ratio input index) hAccepted hOutputIndex hState hSlots
    pointer input hInput hSeparate protectedBuffer hProtected hProtectedSeparate
  simpa [advanceCellResult, Model.advanceAt, hAccepted] using hWriter

#print axioms advanceAt_reused_protected
end Project.EulerGridStep.Execution
