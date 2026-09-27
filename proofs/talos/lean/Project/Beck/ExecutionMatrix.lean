import Project.Beck.ExecutionMatrixEmpty
import Project.Beck.ExecutionMatrixReturn

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem protectedMatrix_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial)
    (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (pointProtected : heap.Protects pointPointer.toNat (pointPointer.toNat + 8 * (point.numerators.size + 1)))
    (inputArray : UInt64Array.At initial inputPointer input.incidence)
    (inputProtected : heap.Protects inputPointer.toNat (inputPointer.toNat + 8 * (input.incidence.size + 1)))
    (pointSize : input.jobs ≤ point.numerators.size) (inputSize : input.incidence.size = input.jobs * input.categories)
    (jobs : input.jobs ≤ 6) (categories : input.categories ≤ 8) (overlap : input.overlap ≤ 8)
    (budget : OutputBudget initial heap (56 + 448 * input.jobs * input.categories + remaining) pageLimit Project.Beck.«module») :
    TerminatesWith env Project.Beck.«module» 19 initial
      (pointValues point pointOwner pointPointer ++ inputValues input inputOwner inputPointer)
      (fun final values => ∃ finalHeap node,
        values = [.i64 node.root, .i64 node.root] ∧ finalHeap.At final ∧
        finalHeap.OwnsWords final node (protectedMatrix input point) ∧ heap.Frame initial finalHeap final ∧
        FreshFor heap node ∧ OutputBudget final finalHeap remaining pageLimit Project.Beck.«module») := by
  have space := budget.bump 8 (by change 56 ≤ 56 + 448 * input.jobs * input.categories + remaining; omega)
  have emptyFresh := allocated_fresh heap heap initial initial (Heap.Frame.refl heap initial) 8 (fun h => (space h).1.le)
  refine TerminatesWith.of_wp_entry_for (f := func19Def) rfl ?_
  change wp Project.Beck.«module» func19 _ initial
    { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer,
      locals := List.replicate 89 (.i64 0) } env
  rw [← List.take_append_drop 53 func19]
  apply matrixEmpty_exact env initial heap input point inputOwner inputPointer pointOwner pointPointer
    (448 * input.jobs * input.categories + remaining) pageLimit valid (by simpa only [Nat.add_assoc] using budget)
  dsimp only
  intro emptyValid emptyOwned emptyFrame emptyBudget previous cursor capacity afterAllocation
  change wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 matrixBody]] ++ func19.drop 54) _ (emptyWords heap initial) _ env
  apply matrixOuterLoop_exact env (emptyWords heap initial) (heap.allocate 8) input point inputOwner inputPointer pointOwner pointPointer
    (allocatedNode heap.top 8 heap.nodes) _ _ _ remaining pageLimit emptyValid emptyOwned
    (emptyFrame.words pointProtected pointArray) (emptyFrame.protects _ _ pointProtected)
    (emptyFrame.words inputProtected inputArray) (emptyFrame.protects _ _ inputProtected)
    pointSize inputSize jobs categories overlap emptyBudget
  intro middle current node currentValid currentOwned currentFrame active currentBudget saved tail after
  have fresh : FreshFor heap node := by
    rcases active with rfl | fresh
    · exact emptyFresh
    · exact fun lower upper protectedRegion => fresh lower upper (emptyFrame.protects _ _ protectedRegion)
  have separated : node = allocatedNode heap.top 8 heap.nodes ∨
      regionsDisjoint (allocatedNode heap.top 8 heap.nodes).region node.region := by
    rcases active with same | fresh
    · exact Or.inl same
    · apply Or.inr
      have h := fresh _ _ emptyOwned.protects
      simp only [regionsDisjoint, FreeNode.region]
      have oldRoot := emptyOwned.buffer.rootBound
      have newRoot := currentOwned.buffer.rootBound
      omega
  apply matrixReturn_exact env initial middle heap current input point inputOwner inputPointer pointOwner pointPointer
    (allocatedNode heap.top 8 heap.nodes) node (protectedMatrix input point) saved tail after remaining pageLimit
    currentValid (currentFrame.ownsWords currentValid emptyOwned) currentOwned (emptyFrame.trans currentFrame)
    emptyFresh separated currentBudget
  intro final finalHeap finalValid finalOwned finalFrame finalBudget frame values
  exact ⟨finalHeap, node, by simp [values, func19Def, Wasm.Function.numParams, pointValues, inputValues], finalValid, finalOwned, finalFrame, fresh, finalBudget⟩

#print axioms protectedMatrix_exact

end Project.Beck.Execution
