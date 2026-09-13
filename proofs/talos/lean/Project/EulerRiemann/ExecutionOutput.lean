import Project.EulerRiemann.OutputFields
import Project.EulerRiemann.OutputTail
import Project.EulerRiemann.OutputModel

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit

def outputEntryFrame (n : Nat) (time status root : UInt64) : Locals :=
  func99Def.toLocals [.i64 (UInt64.ofNat n), .i64 time, .i64 status, .i64 root, .i64 root]

theorem output_entry_scratch (n : Nat) (time status root : UInt64) :
    I64LocalRange (outputEntryFrame n time status root) 42 57 := by
  intro index hFirst hLast
  refine ⟨0, ?_⟩
  have hParams : (outputEntryFrame n time status root).params.length = 5 := rfl
  have hLocals : (outputEntryFrame n time status root).locals = List.replicate 52 (.i64 0) := rfl
  simp only [Locals.get, hParams, hLocals, List.length_replicate,
    ite_eq_right (show ¬index < 5 by omega), ite_eq_left (show index < 5 + 52 by omega),
    List.getElem?_replicate, ite_eq_left (show index - 5 < 52 by omega)]

theorem output_pack_words (n : Nat) (time status : UInt64) (grid : Array Traversal.Cell) :
    Output.pack n time status grid = outputHeaderWords (UInt64.ofNat n) time status ++
      (outputMapResult false grid ++ outputMapResult true grid) := rfl

theorem output_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n pageLimit : Nat) (time status : UInt64)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid) (hSize : grid.size ≤ 640000)
    (hBudget : OutputBudget initial heap (outputBytes grid.size) pageLimit) :
    TerminatesWith env module 99 initial
      [.i64 source.root, .i64 source.root, .i64 status, .i64 time, .i64 (UInt64.ofNat n)]
      (fun final values => ∃ (finalHeap : Heap) (result : FreeNode),
        values = [.i64 result.root, .i64 result.root] ∧ finalHeap.At final ∧
        finalHeap.OwnsWords final result (Output.pack n time status grid) ∧ final.mem.pages ≤ pageLimit) := by
  refine TerminatesWith.of_wp_entry_for (f := func99Def) rfl ?_ (by decide)
  change wp module func99 _ initial (outputEntryFrame n time status source.root) env
  have hSplit : func99 = outputFieldsProgram ++ outputTailProgram :=
    (List.take_append_drop 185 func99).symm
  rw [hSplit]
  apply output_fields_spec env initial heap (outputEntryFrame n time status source.root) source grid pageLimit
    rfl rfl rfl (output_entry_scratch n time status source.root) rfl hHeap hOwner hSize hBudget
  intro current currentHeap fields frame hCurrentHeap hFields hCurrentBudget hParams hLocals hValues hScratch
    hOwnerLocal hPointerLocal hPreserved
  have hN : frame.get 0 = some (.i64 (UInt64.ofNat n)) := hPreserved 0 (by decide)
  have hTime : frame.get 1 = some (.i64 time) := hPreserved 1 (by decide)
  have hStatus : frame.get 2 = some (.i64 status) := hPreserved 2 (by decide)
  have hCount : (outputMapResult false grid ++ outputMapResult true grid).size = grid.size + grid.size := by
    simp [outputMapResult]
  have hTailBudget : OutputBudget current currentHeap
      (8 * (outputMapResult false grid ++ outputMapResult true grid).size + 176) pageLimit := by
    rw [hCount, show 8 * (grid.size + grid.size) + 176 = 16 * grid.size + 176 by omega]
    exact hCurrentBudget
  rw [← List.append_nil outputTailProgram]
  apply output_tail_spec env current currentHeap frame fields
    (outputMapResult false grid ++ outputMapResult true grid) (UInt64.ofNat n) time status pageLimit
    hParams hLocals hValues hScratch hN hTime hStatus hOwnerLocal hPointerLocal hCurrentHeap hFields
    (by rw [hCount]; omega) hTailBudget
  intro final finalHeap result resultFrame hFinalHeap hResultOwner hFinalBudget hResultValues
  simp only [wp_nil]
  refine ⟨finalHeap, result, ?_, hFinalHeap, ?_, hFinalBudget.pages⟩
  · change resultFrame.values.take 2 ++ [] = [.i64 result.root, .i64 result.root]
    rw [hResultValues]
    rfl
  · simpa only [output_pack_words] using hResultOwner

#print axioms output_entry_scratch
#print axioms output_pack_words
#print axioms output_exact

end Project.EulerRiemann.Execution
