import Project.Beck.ExecutionRoundsReturn

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
theorem rounds_function_shape : func34 = func34.take 6 ++
    ([.block 0 0 [.loop 0 0 roundsBody]] ++ func34.drop 7) := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem rounds_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (fuel : Nat) (input : Input) (point : Point) (inputNode pointNode : FreeNode) (pointOwner : UInt64)
    (roundNumber remaining pageLimit : Nat)
    (valid : heap.At initial) (supported : Project.Beck.State.Supported input)
    (pointValid : Project.Beck.State.Valid input.jobs point roundNumber) (roundBudget : roundNumber + fuel ≤ 6)
    (enough : (Project.Beck.Counting.live input point).card ≤ fuel)
    (pointOwned : heap.OwnsWords initial pointNode point.numerators)
    (inputOwned : heap.OwnsWords initial inputNode input.incidence) (different : pointNode.root ≠ inputNode.root)
    (inputSize : input.incidence.size = input.jobs * input.categories)
    (categories : input.categories ≤ 8) (overlap : input.overlap ≤ 8)
    (budget : OutputBudget initial heap (roundMaxBytes * fuel + remaining) pageLimit Project.Beck.«module») :
    TerminatesWith env Project.Beck.«module» 34 initial (roundsParams fuel input point inputNode.root pointOwner pointNode.root).reverse
      (fun final values => ∃ finalHeap resultNode resultOwner, finalHeap.At final ∧
        finalHeap.OwnsWords final resultNode (rounds fuel input point).numerators ∧
        heap.Frame initial finalHeap final ∧ (resultNode = pointNode ∨ FreshFor heap resultNode) ∧
        resultNode.root ≠ inputNode.root ∧ OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» ∧
        values = pointValues (rounds fuel input point) resultOwner resultNode.root) := by
  let params := roundsParams fuel input point inputNode.root pointOwner pointNode.root
  have paramsSize : params.length = 10 := by simp [params, roundsParams, matrixParams, inputValues, pointValues]
  refine TerminatesWith.of_wp_entry_for (f := func34Def) rfl ?_
  change wp Project.Beck.«module» func34 _ initial { params := params, locals := List.replicate 61 (.i64 0) } env
  rw [rounds_function_shape]
  refine Sequence.wp_append (P := fun store frame => store = initial ∧ frame = { params := params, locals := List.replicate 61 (.i64 0) }) ?_ ?_
  · exact roundsEntry_exact env initial params paramsSize _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  apply roundsLoop_exact env initial heap (List.replicate 61 (.i64 0)) fuel input point inputNode pointNode pointOwner
    roundNumber remaining pageLimit (roundsEntry_state point pointOwner pointNode.root) valid supported pointValid roundBudget enough
    pointOwned inputOwned different inputSize categories overlap budget
  intro final finalHeap finalFuel resultNode resultOwner internal stopped nextLocals finalValid finalOwned finalFrame output finalDifferent frozen finalBudget finalState
  apply roundsReturn_exact env final nextLocals finalFuel input (rounds fuel input point) inputNode.root resultOwner resultNode.root internal
    stopped finalState finalOwned.buffer.values frozen
  intro returnedFrame correct
  refine ⟨finalHeap, resultNode, resultOwner, finalValid, finalOwned, finalFrame, output, finalDifferent, finalBudget, ?_⟩
  simp only [func34Def, correct, pointValues]
  rfl

#print axioms rounds_exact

end Project.Beck.Execution
