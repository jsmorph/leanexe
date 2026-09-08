import Project.EulerGridStep.MixedReuseCall
import Project.EulerGridStep.MixedFreshCall

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Each exact mixed write consumes a reusable node or, on the sixth field, fresh memory. -/
theorem mixed_cell_field_call {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (unused heapTop allocs releases frees : UInt64)
    (roots : Nat → UInt64) (output : Array UInt64) (index field : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell)
    (hField : field < 6) (hi : 1 + 6 * index + 5 < output.size)
    (hState : MixedCellState initial heapTop roots output index cell field allocs releases frees)
    (hRoot : roots 6 = heapTop + 48)
    (hSlots : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b → ObjectsSeparate (roots a) output.size (roots b) output.size) :
    TerminatesWith env m 27 initial
      [.i64 ((Model.payload cell).getD field 0), .i64 (UInt64.ofNat field),
        .i64 (UInt64.ofNat index), .i64 (roots field), .i64 unused]
      (fun final values => values = [.i64 (roots (field + 1)), .i64 (roots (field + 1))] ∧
        MixedCellState final heapTop roots output index cell (field + 1) allocs releases frees ∧
        FieldResult (mixedChoice roots heapTop allocs output.size field) initial final
          (roots field) (cellPrefix output index cell field) (1 + 6 * index + field)
          ((Model.payload cell).getD field 0)) := by
  by_cases hReuse : field < 5
  · exact mixed_cell_reuse_call layout env initial unused heapTop allocs releases frees roots
      output index field cell hField hi hState hRoot hSlots hReuse
  · exact mixed_cell_fresh_call layout env initial unused heapTop allocs releases frees roots
      output index field cell hField hi hState hRoot hSlots (by omega)

#print axioms mixed_cell_field_call
end Project.EulerGridStep.Execution
