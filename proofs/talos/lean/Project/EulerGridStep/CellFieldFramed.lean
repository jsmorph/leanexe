import Project.EulerGridStep.CellPrefixes

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- A field call carries any extra postcondition justified by its exact memory result. -/
theorem cell_field_call_framed {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (unused allocs releases frees : UInt64)
    (roots : Nat → UInt64) (output : Array UInt64) (index field : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (rest : List UInt64)
    (hField : field < 6) (hi : 1 + 6 * index + 5 < output.size)
    (hState : BufferState initial output.size (cellLive roots output index cell field)
      (roots (field + 1) :: rest) allocs releases frees)
    (hSlots : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b →
      ObjectsSeparate (roots a) output.size (roots b) output.size)
    (hRest : ∀ other ∈ rest, ObjectsSeparate (roots (field + 1)) output.size other output.size)
    (P : Store Unit → Prop)
    (hPreserve : ∀ final,
      FieldResult (.reuse (roots (field + 1)) (fieldRequest output.size) (rest.headD 0) allocs)
        initial final (roots field) (cellPrefix output index cell field)
        (1 + 6 * index + field) ((Model.payload cell).getD field 0) → P final) :
    TerminatesWith env m 27 initial
      [.i64 ((Model.payload cell).getD field 0), .i64 (UInt64.ofNat field),
        .i64 (UInt64.ofNat index), .i64 (roots field), .i64 unused]
      (fun final values => values = [.i64 (roots (field + 1)), .i64 (roots (field + 1))] ∧
        BufferState final output.size (cellLive roots output index cell (field + 1)) rest
          (allocs + 1) releases frees ∧ P final) := by
  have hCurrent := hState.liveAt ⟨roots field, cellPrefix output index cell field⟩
    (cellLive_contains roots output index cell field field (by omega))
  have hSource : ObjectsSeparate (roots (field + 1)) output.size (roots field) output.size :=
    hSlots (field + 1) (by omega) field (by omega) (by omega)
  have hLive : ∀ buffer ∈ cellLive roots output index cell field,
      ObjectsSeparate (roots (field + 1)) output.size buffer.root output.size := by
    apply cellLive_separate roots output index cell field (field + 1)
    intro k hk
    exact hSlots (field + 1) (by omega) k (by omega) (by omega)
  have hCall := writeCellField_buffer_state layout env initial unused (roots field)
    (roots (field + 1)) allocs releases frees (cellPrefix output index cell field)
    (cellLive roots output index cell field) rest index field ((Model.payload cell).getD field 0)
    hCurrent.2.2 (by rw [cellPrefix_size]; omega)
    (by simpa only [cellPrefix_size] using hState)
    (by simpa only [cellPrefix_size] using hSource)
    (by simpa only [cellPrefix_size] using hLive)
    (by simpa only [cellPrefix_size] using hRest)
  apply hCall.mono
  rintro final values ⟨hValues, hResult, hFinal⟩
  refine ⟨hValues, ?_, hPreserve final ?_⟩
  · simpa only [cellPrefix_size, cellLive, cellPrefix] using hFinal
  · simpa only [cellPrefix_size] using hResult

#print axioms cell_field_call_framed
end Project.EulerGridStep.Execution
