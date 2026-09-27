import Project.Beck.ExecutionComputeGroup
import Project.Beck.ExecutionComputePush

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
theorem compute_append_shape : (computeOutputBody.drop 4).take 98 =
    (computeOutputBody.drop 4).take 31 ++ (computeOutputBody.drop 35).take 67 := rfl

set_option maxRecDepth 4096 in
theorem computeAppend_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (pointer : UInt64) (input : Input) (point : Point) (words : Array UInt64)
    (initialOwner initialPointer pointRoot original current : UInt64) (index remaining pageLimit : Nat)
    (state : ComputeOutputLocals locals input.jobs input.overlap initialOwner initialPointer pointRoot original current index)
    (valid : heap.At initial) (bound : words.size ≤ 55)
    (pointAt : UInt64Array.At initial pointRoot point.numerators) (inside : index < point.numerators.size)
    (represented : UInt64Array.At initial current words)
    (protects : heap.Protects current.toNat (current.toNat + 8 * (words.size + 1)))
    (budget : OutputBudget initial heap (48 + 8 * (words.size + 2) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final,
      let need := UInt64.ofNat (8 * (words.size + 2))
      let node := allocatedNode heap.top need heap.nodes
      (heap.allocate need).At final → (heap.allocate need).OwnsWords final node (words.push (Project.Beck.Result.group point index)) →
      heap.Frame initial (heap.allocate need) final → FreshFor heap node →
      OutputBudget final (heap.allocate need) remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, ComputeOutputLocals nextLocals input.jobs input.overlap initialOwner initialPointer pointRoot original current index →
      Q (.Fallthrough final { params := [.i64 pointer], locals := nextLocals, values := [.i64 node.root] })) :
    wp Project.Beck.«module» ((computeOutputBody.drop 4).take 98) Q initial
      { params := [.i64 pointer], locals := locals } env := by
  let prepared := computeGroupLocals locals current pointRoot point index
  have preparedState := computeGroup_state state point
  rw [compute_append_shape]
  refine Sequence.wp_append (P := fun store frame => store = initial ∧ frame = { params := [.i64 pointer], locals := prepared }) ?_ ?_
  · exact computeGroup_exact env initial locals pointer current pointRoot point index state.size
      state.position state.currentPointer state.pointPointer pointAt inside _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  apply computePush_exact env initial heap [.i64 pointer] prepared preparedState.words rfl preparedState.size
    current (Project.Beck.Result.group point index) words
  · simp [prepared, computeGroupLocals, state.size]
  · simp [prepared, computeGroupLocals, state.size]
  · exact valid
  · exact bound
  · exact represented
  · exact protects
  · exact budget
  · intro final
    dsimp only
    intro finalValid owned preserved fresh finalBudget nextLocals changed
    exact next final finalValid owned preserved fresh finalBudget nextLocals
      (preparedState.preserved changed.size changed.words (fun k bound => changed.keeps k (by omega)))

#print axioms computeAppend_exact

end Project.Beck.Execution
