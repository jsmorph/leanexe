import Project.Beck.ExecutionInputValidate
import Project.Beck.Encoding
import Project.ProofKit.Sequence

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem readInput_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (pointer : UInt64) (words : Array UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial) (wordsAt : UInt64Array.At initial pointer words)
    (wordsProtected : heap.Protects pointer.toNat (pointer.toNat + 8 * (words.size + 1)))
    (nonzero : pointer ≠ 0) (accepted : (readInput words).status = 0)
    (budget : OutputBudget initial heap (112 + 1520 * words[0]!.toNat + remaining) pageLimit Project.Beck.«module») :
    TerminatesWith env Project.Beck.«module» 6 initial [.i64 pointer, .i64 pointer]
      (fun final values => ∃ finalHeap node owner,
        values = inputValues (readInput words) owner node.root ∧
        finalHeap.At final ∧ finalHeap.OwnsWords final node (readInput words).incidence ∧
        heap.Frame initial finalHeap final ∧ OutputBudget final finalHeap remaining pageLimit Project.Beck.«module») := by
  have lengthBound := Encoding.accepted_header words accepted
  obtain ⟨out, parsed, terminal, countBound, categoryBound, source⟩ := Parser.accepted_data words accepted
  refine TerminatesWith.of_wp_entry_for (f := func6Def) rfl ?_
  change wp Project.Beck.«module» func6 _ initial (inputFrame pointer (fun _ => .i64 0) (fun _ => 0)) env
  rw [← List.take_append_drop 8 func6]
  apply Sequence.wp_append (P := fun final frame => ∃ finalHeap node owner,
    finalHeap.At final ∧ finalHeap.OwnsWords final node out.incidence ∧ heap.Frame initial finalHeap final ∧
    OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» ∧
    InputResult frame ⟨0, words[0]!.toNat, words[1]!.toNat, out.overlap, out.incidence⟩ owner node.root)
  · apply inputValidate_exact env initial pointer _ _ words wordsAt lengthBound countBound categoryBound
    intro saved tail
    apply inputEligible_exact env initial heap pointer saved tail words out remaining pageLimit
      valid wordsAt wordsProtected nonzero lengthBound countBound categoryBound parsed terminal budget
    intro final finalHeap node owner finalValid owned preserved finalBudget frame result
    exact ⟨finalHeap, node, owner, finalValid, owned, preserved, finalBudget,
      ⟨rfl, result.status, result.jobs, result.categories, result.overlap, result.owner, result.pointer⟩⟩
  · rintro final frame ⟨finalHeap, node, owner, finalValid, owned, preserved, finalBudget, result⟩
    simp only [func6, List.drop]
    simp only [wp_simp, Frame.withValues_get, result.values, result.status, result.jobs,
      result.categories, result.overlap, result.owner, result.pointer]
    exact ⟨finalHeap, node, owner, by simp [inputValues, source, func6Def, Wasm.Function.numParams], finalValid, by simpa only [source] using owned,
      preserved, finalBudget⟩

#print axioms readInput_exact

end Project.Beck.Execution
