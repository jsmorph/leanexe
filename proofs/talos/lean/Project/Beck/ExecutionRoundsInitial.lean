import Project.Beck.ExecutionRoundsZero
import Project.Beck.Result

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

theorem rounds_initial_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (input : Input) (inputNode pointNode : FreeNode) (inputOwner pointOwner : UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial) (supported : Project.Beck.State.Supported input)
    (pointOwned : heap.OwnsWords initial pointNode (Array.replicate input.jobs 0))
    (inputOwned : heap.OwnsWords initial inputNode input.incidence) (different : pointNode.root ≠ inputNode.root)
    (ownerMode : input.jobs = 0 ∨ inputOwner = inputNode.root)
    (inputSize : input.incidence.size = input.jobs * input.categories)
    (categories : input.categories ≤ 8) (overlap : input.overlap ≤ 8)
    (budget : OutputBudget initial heap (roundMaxBytes * input.jobs + remaining) pageLimit Project.Beck.«module») :
    TerminatesWith env Project.Beck.«module» 34 initial
      (roundsParams (inputOwner := inputOwner) input.jobs input ⟨1, Array.replicate input.jobs 0⟩
        inputNode.root pointOwner pointNode.root).reverse
      (fun final values => ∃ finalHeap resultNode resultOwner, finalHeap.At final ∧
        finalHeap.OwnsWords final resultNode (Project.Beck.Result.finalPoint input).numerators ∧
        heap.Frame initial finalHeap final ∧ (resultNode = pointNode ∨ FreshFor heap resultNode) ∧
        resultNode.root ≠ inputNode.root ∧ OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» ∧
        values = pointValues (Project.Beck.Result.finalPoint input) resultOwner resultNode.root) := by
  by_cases empty : input.jobs = 0
  · have frozen : allFrozen ⟨1, Array.replicate input.jobs 0⟩ = true := by
      simp [Project.Beck.Loop.allFrozen_iff, empty]
    have source : Project.Beck.Result.finalPoint input = ⟨1, Array.replicate input.jobs 0⟩ := by
      have frozenZero := frozen
      rw [empty] at frozenZero
      simp only [Project.Beck.Result.finalPoint, empty, rounds, frozenZero, reduceIte]
    have call := rounds_zero_exact env initial input ⟨1, Array.replicate input.jobs 0⟩ inputOwner inputNode.root
      pointOwner pointNode.root pointOwned.buffer.values frozen
    rw [show input.jobs = 0 from empty]
    rw [empty] at call
    obtain ⟨bound, runs⟩ := call
    refine ⟨bound, ?_⟩
    intro fuel enough
    obtain ⟨values, final, run, same, result⟩ := runs fuel enough
    subst final
    refine ⟨values, initial, run, heap, pointNode, pointOwner, valid, ?_, Heap.Frame.refl heap initial,
      Or.inl rfl, different, ?_, ?_⟩
    · simpa only [source] using pointOwned
    · simpa only [empty, Nat.mul_zero, Nat.zero_add] using budget
    · simpa only [source, empty] using result
  · have ownerEq := ownerMode.resolve_left empty
    rw [ownerEq]
    have liveBound : (Project.Beck.Counting.live input ⟨1, Array.replicate input.jobs 0⟩).card ≤ input.jobs :=
      (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
    exact rounds_exact env initial heap input.jobs input ⟨1, Array.replicate input.jobs 0⟩ inputNode pointNode pointOwner
      0 remaining pageLimit valid supported (Project.Beck.State.initial input.jobs) (by simpa using supported.capacity)
      liveBound pointOwned inputOwned different inputSize categories overlap budget

#print axioms rounds_initial_exact

end Project.Beck.Execution
