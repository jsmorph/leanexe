import Project.EulerGridStep.AdvanceExecution
import Project.EulerGridStep.WriterProtected
import Project.EulerGridStep.FreshWriterAccepted

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Full accepted advance with six reusable output buffers and an unchanged old grid. -/
theorem advanceAt_reused_accepted {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused allocs releases frees : UInt64)
    (roots : Nat → UInt64) (input output : Array UInt64) (index : Nat) (free : List UInt64)
    (hInput : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (hAccepted : (Model.cellAt ratio input index).status = 0)
    (hOutputIndex : 1 + 6 * index + 5 < output.size)
    (hState : BufferState initial output.size
      (cellLive roots output index (Model.cellAt ratio input index) 0)
      ([roots 1, roots 2, roots 3, roots 4, roots 5, roots 6] ++ free) allocs releases frees)
    (hSlots : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b → ObjectsSeparate (roots a) output.size (roots b) output.size)
    (hFree : ∀ a ≤ 6, ∀ other ∈ free, ObjectsSeparate (roots a) output.size other output.size)
    (hSeparate : ∀ a ≤ 6, ObjectsSeparate (roots a) output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat index), .i64 (roots 0), .i64 unused, .i64 pointer, .i64 inputUnused, .i64 ratio]
      (fun final values => values = [.i64 (roots 6), .i64 (roots 6)] ∧
        BufferState final output.size
          [⟨roots 6, Model.advanceAt ratio input output index⟩, ⟨roots 0, output⟩]
          ([roots 1, roots 2, roots 3, roots 4, roots 5] ++ free)
          (allocs + 6) (releases + 5) (frees + 5) ∧ UInt64Array.At final pointer input) := by
  apply advanceAt_with_writer layout env initial ratio inputUnused pointer unused (roots 0) (roots 6)
    input index hInput hi
  have hWriter := writeCell_accepted_preserves_array_in_module layout env initial unused allocs releases frees
    roots output index (Model.cellAt ratio input index) free hAccepted hOutputIndex hState hSlots hFree
    pointer input hInput hSeparate
  simpa [advanceCellResult, Model.advanceAt, hAccepted] using hWriter

/-- Full first accepted advance allocates six fresh slots after the initialized output. -/
theorem advanceAt_fresh_accepted {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused allocs releases frees : UInt64)
    (base : Nat) (input output : Array UInt64) (index : Nat)
    (hInput : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (hAccepted : (Model.cellAt ratio input index).status = 0)
    (hOutputIndex : 1 + 6 * index + 5 < output.size)
    (hState : FreshCellState initial base output index (Model.cellAt ratio input index) 0 allocs releases frees)
    (hSeparate : ∀ a ≤ 6, ObjectsSeparate (arenaRoot base output.size a) output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat index), .i64 (arenaRoot base output.size 0), .i64 unused,
        .i64 pointer, .i64 inputUnused, .i64 ratio]
      (fun final values => values = [.i64 (arenaRoot base output.size 6), .i64 (arenaRoot base output.size 6)] ∧
        BufferState final output.size
          [⟨arenaRoot base output.size 6, Model.advanceAt ratio input output index⟩,
            ⟨arenaRoot base output.size 0, output⟩]
          [arenaRoot base output.size 1, arenaRoot base output.size 2, arenaRoot base output.size 3,
            arenaRoot base output.size 4, arenaRoot base output.size 5]
          (allocs + 6) (releases + 5) (frees + 5) ∧ UInt64Array.At final pointer input) := by
  apply advanceAt_with_writer layout env initial ratio inputUnused pointer unused
    (arenaRoot base output.size 0) (arenaRoot base output.size 6) input index hInput hi
  have hWriter := writeCell_fresh_accepted_exact_in_module layout env initial unused allocs releases frees
    base output index (Model.cellAt ratio input index) hAccepted hOutputIndex hState pointer input hInput hSeparate
  simpa [advanceCellResult, Model.advanceAt, hAccepted] using hWriter

#print axioms advanceAt_reused_accepted
#print axioms advanceAt_fresh_accepted
end Project.EulerGridStep.Execution
