import Project.TinyGpt2Checked.InitialAllocation
import Project.TinyGpt2Checked.OutputLoop

namespace Project.TinyGpt2Checked.Spec
open Project.TinyGpt2Infer
open Wasm Project.TinyGpt2 Project.ProofKit ArrayPushLayout FixedArrayFold

def initialSetupMoves : Wasm.Program :=
  [.localGet 51, .localSet 22, .localGet 22, .localSet 23,
   .constI64 0, .localSet 51, .constI64 256, .localSet 52, .constI64 1, .localSet 53,
   .localGet 22, .localSet 24, .localGet 23, .localSet 25, .localGet 24, .localSet 72]

theorem initial_setup_shape : (func84.drop 67).take 22 =
    [.localGet 60, .localSet 51] ++ FixedArrayResult.lengthStoreProgram 51 0 ++ initialSetupMoves := rfl

def initialReadyFrame (owner pointer t0 t1 t2 t3 : UInt64) (x : Row) (start : Nat)
    (previous : UInt64) : Locals :=
  [(51, (node start 0).root), (22, (node start 0).root), (23, (node start 0).root),
    (51, 0), (52, 256), (53, 1), (24, (node start 0).root), (25, (node start 0).root), (72, (node start 0).root)].foldl
    (fun frame assignment => resultFrame frame assignment.1 assignment.2)
    (initialAllocatedFrame owner pointer t0 t1 t2 t3 x start previous)

theorem initialReadyFrame_locals (owner pointer t0 t1 t2 t3 : UInt64) (x : Row) (start : Nat)
    (previous : UInt64) :
    OutputLoopLocals owner pointer (node start 0).root x (node start 0).root 0
      (initialReadyFrame owner pointer t0 t1 t2 t3 x start previous) := by
  simp only [initialReadyFrame, List.foldl, resultFrame, initialAllocatedFrame, initialAllocationFrame,
    inferenceParams, inferenceSaved, FixedArraySearch.frame, List.length_cons, List.length_nil,
    Nat.reduceSub, List.set, List.replicate, List.cons_append, List.nil_append]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩, rfl, rfl, rfl, rfl⟩
  intro index hLow hHigh
  interval_cases index <;> exact ⟨0, rfl⟩

theorem initial_setup_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer t0 t1 t2 t3 : UInt64) (x : Row) (start : Nat) (allocations previous : UInt64)
    (hFit : top start 0 < 4294967296)
    (hMemory : top start 0 ≤ initial.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q (OutputMemory.prepare initial start 0 allocations)
      (initialReadyFrame owner pointer t0 t1 t2 t3 x start previous) env) :
    wp module ((func84.drop 67).take 22 ++ rest) Q (OutputMemory.allocate initial start 0 allocations)
      (initialAllocatedFrame owner pointer t0 t1 t2 t3 x start previous) env := by
  have hNode := node_toNat start 0 hFit
  have hBound : (node start 0).root.toUInt32.toNat + 8 ≤
      (OutputMemory.allocate initial start 0 allocations).mem.pages * 65536 := by
    rw [UInt64.toNat_toUInt32, hNode.1, Nat.mod_eq_of_lt
      ((Nat.le_add_right _ _).trans_lt hFit),
      OutputMemory.allocate_pages initial start 0 allocations hFit hMemory]
    exact hMemory
  rw [initial_setup_shape]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  wp_fixed_frame [initialAllocatedFrame, initialAllocationFrame, inferenceParams, inferenceSaved,
    FixedArraySearch.frame, List.replicate, List.cons_append, List.nil_append]
  apply FixedArrayResult.lengthStore_spec module env _ _ (node start 0).root 0 51 rfl rfl hBound
  simp only [initialSetupMoves, List.cons_append, List.nil_append]
  wp_fixed_frame
  simpa only [initialReadyFrame, List.foldl, resultFrame, initialAllocatedFrame, initialAllocationFrame,
    inferenceParams, inferenceSaved, FixedArraySearch.frame, List.length_cons, List.length_nil,
    Nat.reduceSub, List.set, List.replicate, List.cons_append, List.nil_append,
    List.append_nil, OutputMemory.prepare, show UInt64.ofNat 0 = 0 from rfl] using hNext

#print axioms initialReadyFrame_locals
#print axioms initial_setup_spec
end Project.TinyGpt2Checked.Spec
