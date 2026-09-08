import Project.EulerGridStep.AdvanceExecution
import Project.EulerGridStep.MixedWriterAccepted

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Full later accepted advance uses five reusable objects and one fresh final output. -/
theorem advanceAt_mixed_accepted {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused heapTop allocs releases frees : UInt64)
    (roots : Nat → UInt64) (input output : Array UInt64) (index : Nat)
    (hInput : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (hAccepted : (Model.cellAt ratio input index).status = 0)
    (hOutputIndex : 1 + 6 * index + 5 < output.size)
    (hState : MixedCellState initial heapTop roots output index (Model.cellAt ratio input index)
      0 allocs releases frees)
    (hRoot : roots 6 = heapTop + 48)
    (hSlots : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b → ObjectsSeparate (roots a) output.size (roots b) output.size)
    (hSeparate : ∀ a ≤ 6, ObjectsSeparate (roots a) output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat index), .i64 (roots 0), .i64 unused, .i64 pointer, .i64 inputUnused, .i64 ratio]
      (fun final values => values = [.i64 (roots 6), .i64 (roots 6)] ∧
        BufferState final output.size
          [⟨roots 6, Model.advanceAt ratio input output index⟩, ⟨roots 0, output⟩]
          [roots 1, roots 2, roots 3, roots 4, roots 5]
          (allocs + 6) (releases + 5) (frees + 5) ∧
        final.globals.globals[0]? = some (.i64 (heapTop + 48 + fieldRequest output.size)) ∧
        final.mem.pages = initial.mem.pages ∧ UInt64Array.At final pointer input) := by
  apply advanceAt_with_writer layout env initial ratio inputUnused pointer unused (roots 0) (roots 6)
    input index hInput hi
  have hWriter := writeCell_mixed_accepted_exact_in_module layout env initial unused heapTop allocs releases frees
    roots output index (Model.cellAt ratio input index) hAccepted hOutputIndex hState hRoot hSlots
    pointer input hInput hSeparate
  simpa [advanceCellResult, Model.advanceAt, hAccepted] using hWriter

#print axioms advanceAt_mixed_accepted
end Project.EulerGridStep.Execution
