import Project.EulerGridStep.FieldBody
import Project.EulerGridStep.Helpers

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayCopy
open Project.ProofKit.FixedArrayAllocatorWindow
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Exact generated outer branch and return boundary. -/
theorem field_function_shape : func27 = func27.take 44 ++
    [.iff 0 1 fieldAcceptedBody [.unreachable] [] [.i64]] ++ func27.drop 45 := rfl

/-- Logical clone/update, owned result metadata and a complete physical object footprint. -/
structure FieldResult (choice : FieldAllocation) (initial final : Store Unit)
    (source : UInt64) (input : Array UInt64) (index : Nat) (value : UInt64) : Prop where
  write : FieldWriteState (choice.store initial input.size) source choice.root input index value final
  header : OwnedHeader final choice.root (choice.capacity input.size)
  pages : final.mem.pages = initial.mem.pages
  outside : ∀ address, address < choice.root.toNat - 48 ∨
      choice.root.toNat + 8 * (input.size + 1) ≤ address →
    final.mem.bytes address = initial.mem.bytes address

theorem field_result_of_write (choice : FieldAllocation) (initial final : Store Unit)
    (source : UInt64) (input : Array UInt64) (index : Nat) (value : UInt64)
    (hInput : UInt64Array.At initial source input) (hValid : choice.Valid initial source input)
    (hWrite : FieldWriteState (choice.store initial input.size) source choice.root input index value final) :
    FieldResult choice initial final source input index value := by
  have hRegion := field_allocation_region choice initial source input hInput hValid
  exact ⟨hWrite, fieldWrite_preserves_header _ _ _ _ _ _ _ _ hRegion.header hWrite,
    hWrite.pages.trans hRegion.pages,
    fun address hOutside => field_write_bytes_outside_object _ _ _ _ _ _ _ _ _
      hRegion hWrite address hOutside⟩

/-- Full generated field function, for a bounded index and either supported allocation path. -/
theorem writeCellField_exact_in_module {m : Wasm.Module} (layout : Layout m)
    (choice : FieldAllocation) (env : HostEnv Unit) (initial : Store Unit)
    (unused source : UInt64) (input : Array UInt64) (index field : Nat) (value : UInt64)
    (hInput : UInt64Array.At initial source input) (hi : 1 + 6 * index + field < input.size)
    (hValid : choice.Valid initial source input) (hPages : initial.mem.pages ≤ 65536) :
    TerminatesWith env m 27 initial
      [.i64 value, .i64 (UInt64.ofNat field), .i64 (UInt64.ofNat index), .i64 source, .i64 unused]
      (fun final values => values = [.i64 choice.root, .i64 choice.root] ∧
        FieldResult choice initial final source input (1 + 6 * index + field) value) := by
  refine TerminatesWith.of_wp_entry_for (f := func27Def)
    (by simpa [layout.noImports] using layout.writeField) ?_ (by simp [layout.noImports])
  change wp m func27 _ initial (fieldEntryFrame unused source index field value) env
  rw [field_function_shape]
  simp only [List.append_assoc]
  apply field_prefix_spec m env initial unused source input index field value hInput hi
  simp only [List.cons_append, List.nil_append]
  rw [Wasm.wp_iff_control_types]
  apply wp_iff_cons rfl
  rw [ite_eq_left (by decide : (1 : UInt32) ≠ 0)]
  change wp m (fieldAcceptedBody ++ []) _ initial
    { fieldPrefixFrame unused source input.size index field value with values := [] } env
  apply field_accepted_spec choice m env initial unused source input index field value
    hInput hi hValid hPages layout.memory32 _ []
  intro final hWrite
  have hResult := field_result_of_write choice initial final source input
    (1 + 6 * index + field) value hInput hValid hWrite
  have hFrame := field_allocated_frame choice unused source input.size index field value
  have hParams : (fieldReturnedFrame choice unused source input.size index field value).params.length = 5 := by
    simpa only [fieldReturnedFrame, counterFrame_params_length] using hFrame.params
  have hLocals : (fieldReturnedFrame choice unused source input.size index field value).locals.length = 20 := by
    simpa only [fieldReturnedFrame, counterFrame_locals_length] using hFrame.locals
  rw [wp_nil]
  simp only [fieldReturnedFrame, List.take_succ_cons, List.take_zero, List.drop_zero,
    List.append_nil]
  wp_alloc_window_lists [func27, func27Def, List.drop, hParams, hLocals, hFrame.params, hFrame.locals]
  exact hResult

#print axioms field_function_shape
#print axioms field_result_of_write
#print axioms writeCellField_exact_in_module
end Project.EulerGridStep.Execution
