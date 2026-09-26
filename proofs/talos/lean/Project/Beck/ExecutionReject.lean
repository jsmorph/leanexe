import Project.Beck.ExecutionHeap

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def rejectTail : Wasm.Program :=
  [.localGet 17, .localSet 8, .localGet 8, .wrapI64, .constI64 0, .store64 0,
    .localGet 8, .localSet 6, .localGet 6, .localSet 7,
    .localGet 2, .localGet 3, .localGet 4, .localGet 5, .localGet 6, .localGet 7]

theorem reject_program : func0 = func0.take 8 ++ FixedArrayCapacity.constantProgram 0 1 12 ++
    FixedArrayAllocate.program 12 1 ++ rejectTail := by rfl

set_option maxHeartbeats 600000 in
theorem reject_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (status : UInt64)
    (valid : heap.At initial)
    (space : takeFirstFitFrom 0 8 heap.nodes = none →
      heap.top.toNat + 48 + 8 < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top 8 ≤ initial.memoryCap Project.Beck.«module» 0)
    (pages : initial.mem.pages ≤ 65536) :
    TerminatesWith env Project.Beck.«module» 0 initial [.i64 status]
      (fun final values => final = emptyWords heap initial ∧
        values = inputValues (reject status) (allocatedRoot heap.top 8 heap.nodes)
          (allocatedRoot heap.top 8 heap.nodes)) := by
  refine TerminatesWith.of_wp_entry_for (f := func0Def) rfl ?_
  change wp Project.Beck.«module» func0 _ initial
    { params := [.i64 status], locals := List.replicate 17 (.i64 0) } env
  rw [reject_program]
  simp only [func0, List.take, FixedArrayCapacity.constantProgram, List.cons_append, List.nil_append]
  wp_fixed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide), wp_nil]
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  change wp Project.Beck.«module» (FixedArrayAllocate.program 12 1 ++ rejectTail) _ initial
    (FixedArraySearch.frame [.i64 status]
      [.i64 0, .i64 status, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
      [] 8 0 0 0 0 0) env
  apply allocation_exact env initial heap _ _ [] 12 rfl 8 0 0 0 0 0 valid
    (fun h => ⟨(space h).1.le, (space h).2⟩) pages
  intro previous current capacity next
  have bounds := emptyWords_bounds heap initial valid (fun h => (space h).1.le)
  have memory : (allocatedRoot heap.top 8 heap.nodes).toUInt32.toNat + 8 ≤
      (heap.allocateArrayStore initial 8 1).mem.pages * 65536 := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
    exact bounds.2
  simp only [rejectTail, FixedArraySearch.frame, List.cons_append, List.nil_append]
  wp_fixed_frame_step
  wp_fixed_frame_step
  refine FixedArrayResult.lengthStore_spec Project.Beck.«module» env _ _
    (allocatedRoot heap.top 8 heap.nodes) 0 8 rfl rfl memory _ _ ?_
  wp_fixed_frame [func0Def, inputValues, reject, emptyWords]
  simp

theorem reject_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (status : UInt64)
    (valid : heap.At initial)
    (space : takeFirstFitFrom 0 8 heap.nodes = none →
      heap.top.toNat + 48 + 8 < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top 8 ≤ initial.memoryCap Project.Beck.«module» 0)
    (pages : initial.mem.pages ≤ 65536) :
    TerminatesWith env Project.Beck.«module» 0 initial [.i64 status]
      (fun final values =>
        values = inputValues (reject status) (allocatedRoot heap.top 8 heap.nodes)
          (allocatedRoot heap.top 8 heap.nodes) ∧
        (heap.allocate 8).At final ∧
        (heap.allocate 8).OwnsWords final (allocatedNode heap.top 8 heap.nodes) #[] ∧
        heap.Frame initial (heap.allocate 8) final) := by
  apply (reject_exact env initial heap status valid space pages).mono
  rintro final values ⟨rfl, result⟩
  obtain ⟨heapValid, owned⟩ := emptyWords_owned heap initial valid (fun h => (space h).1)
  exact ⟨result, heapValid, owned,
    emptyWords_frame heap initial valid (fun h => (space h).1.le)⟩

#print axioms reject_exact
#print axioms reject_owned

end Project.Beck.Execution
