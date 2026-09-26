import Project.Beck.ExecutionJobLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem readJobs_exact {rowOwner : UInt64} (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (count categories : Nat) (wordsPointer : UInt64) (node : FreeNode)
    (state out : ParseState) (words : Array UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial) (owned : heap.OwnsWords initial node state.incidence)
    (wordsAt : UInt64Array.At initial wordsPointer words)
    (wordsProtected : heap.Protects wordsPointer.toNat (wordsPointer.toNat + 8 * (words.size + 1)))
    (inputDifferent : node.root ≠ wordsPointer) (ownerNonzero : wordsPointer ≠ 0)
    (countBound : count ≤ 6) (categoryBound : categories ≤ 8)
    (positionBound : state.position ≤ words.size) (overlapBound : state.overlap ≤ 8)
    (incidenceBound : state.incidence.size + count * categories ≤ 48)
    (accepted : readJobs count words categories state = some out)
    (budget : OutputBudget initial heap (1520 * count + remaining) pageLimit Project.Beck.«module») :
    TerminatesWith env Project.Beck.«module» 5 initial (jobParams (rowOwner := rowOwner) count categories wordsPointer node.root state).reverse
      (fun final values => ∃ finalHeap finalNode,
        values = [.i64 finalNode.root, .i64 (if count = 0 then rowOwner else finalNode.root), .i64 out.overlap.toUInt64, .i64 out.position.toUInt64, .i64 1] ∧
        finalHeap.At final ∧ finalHeap.OwnsWords final finalNode out.incidence ∧ heap.Frame initial finalHeap final ∧
        OutputBudget final finalHeap remaining pageLimit Project.Beck.«module») := by
  refine TerminatesWith.of_wp_entry_for (f := func5Def) rfl ?_
  change wp Project.Beck.«module» func5 _ initial
    { params := jobParams (rowOwner := rowOwner) count categories wordsPointer node.root state
      locals := List.replicate 60 (.i64 0) } env
  simp only [func5, jobParams]
  wp_fixed_frame
  change wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 jobBody]] ++ func5.drop 7) _ initial
    (jobFrame (rowOwner := rowOwner) count categories wordsPointer node.root 0 state (fun _ => .i64 0) (fun _ => 0)) env
  apply jobLoop_exact env initial heap count categories wordsPointer node state out _ _ words remaining pageLimit
    valid owned wordsAt wordsProtected inputDifferent ownerNonzero countBound categoryBound positionBound overlapBound incidenceBound accepted budget
  intro final finalHeap finalNode finalValid finalOwned finalFrame finalBudget internal saved tail
  simp only [func5, List.drop, jobFrame, jobParams, jobPrefix, jobSaved, jobTail,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, or_false, false_or, reduceIte,
    List.cons_append, List.nil_append]
  wp_fixed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by decide)]
  wp_fixed_frame [List.take, List.drop, List.append_nil, func5Def]
  exact ⟨finalHeap, finalNode, rfl, finalValid, finalOwned, finalFrame, finalBudget⟩

#print axioms readJobs_exact

end Project.Beck.Execution
