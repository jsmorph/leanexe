import Project.EulerGridStep.FreshRejectedClone
import Project.EulerGridStep.WriterStatus

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayCopy
open Project.ProofKit.FixedArrayAllocatorWindow
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Full rejected writer from an empty free list allocates a fresh clone and writes status one. -/
theorem writeCell_fresh_rejected_exact_in_module {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (unused source heapTop allocs : UInt64) (input : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell)
    (hRejected : cell.status ≠ 0)
    (hInput : UInt64Array.At initial source input) (hNonempty : 0 < input.size)
    (hValid : (FieldAllocation.fresh heapTop allocs).Valid initial source input)
    (hPages : initial.mem.pages ≤ 65536) :
    TerminatesWith env m 34 initial
      [.i64 cell.courant, .i64 cell.alpha, .i64 cell.pressure, .i64 cell.energy,
        .i64 cell.momentum, .i64 cell.density, .i64 cell.status, .i64 (UInt64.ofNat index),
        .i64 source, .i64 unused]
      (fun final values => values = [.i64 (heapTop + 48), .i64 (heapTop + 48)] ∧
        FieldResult (.fresh heapTop allocs) initial final source input 0 1) := by
  refine TerminatesWith.of_wp_entry_for (f := func34Def)
    (by simpa [layout.noImports] using layout.writeCell) ?_ (by simp [layout.noImports])
  change wp m func34 _ initial (writerEntryFrame unused source index cell) env
  rw [writer_function_shape, writer_status_shape]
  apply writer_status_spec m env initial (writerEntryFrame unused source index cell) cell.status
    (by simp [writerEntryFrame, writerParameters, Locals.get]) rfl
  simp only [hRejected, ite_false]
  apply wp_iff_cons rfl
  rw [ite_eq_right (by decide : ¬ ((0 : UInt32) ≠ 0))]
  change wp m (writerRejectedBody ++ []) _ initial (writerEntryFrame unused source index cell) env
  rw [rejected_branch_shape]
  simp only [List.append_assoc]
  apply rejected_prefix_spec m env initial (writerEntryFrame unused source index cell)
    unused source input index cell rfl rfl rfl hInput hNonempty
  simp only [List.cons_append, List.nil_append]
  rw [Wasm.wp_iff_control_types]
  apply wp_iff_cons rfl
  rw [ite_eq_left (by decide : (1 : UInt32) ≠ 0)]
  change wp m (rejectedCloneBody ++ []) _ initial
    { rejectedPrefixFrame (writerEntryFrame unused source index cell) source input.size with values := [] } env
  apply rejected_fresh_clone_spec m env initial unused source heapTop allocs input index cell
    hInput hNonempty hValid hPages layout.memory32 _ []
  intro final hWrite
  have hResult := field_result_of_write (.fresh heapTop allocs) initial final source input 0 1
    hInput hValid hWrite
  have hFrame := rejected_fresh_allocated_frame unused source heapTop input.size index cell
  have hParams : (rejectedFreshReturnedFrame unused source heapTop input.size index cell).params.length = 10 := by
    simpa only [rejectedFreshReturnedFrame, counterFrame_params_length] using hFrame.params
  have hLocals : (rejectedFreshReturnedFrame unused source heapTop input.size index cell).locals.length = 72 := by
    simpa only [rejectedFreshReturnedFrame, counterFrame_locals_length] using hFrame.locals
  rw [wp_nil]
  simp only [rejectedFreshReturnedFrame, List.take_succ_cons, List.take_zero, List.drop_zero, List.append_nil]
  wp_alloc_window_lists [rejectedFinish, func34Def, hParams, hLocals, hFrame.params, hFrame.locals]
  exact hResult

#print axioms writeCell_fresh_rejected_exact_in_module
end Project.EulerGridStep.Execution
