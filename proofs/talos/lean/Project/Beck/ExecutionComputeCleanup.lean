import Project.Beck.ExecutionComputeOutput
import Project.Beck.ExecutionDirectionCleanup

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def computeCleanupEntries (ownerNode pointNode : FreeNode) (words : Array UInt64) : List ReleaseEntry :=
  [⟨27, [55], pointNode, words⟩, ⟨26, [27, 55], ownerNode, words⟩]

set_option maxRecDepth 4096 in
theorem compute_cleanup_shape (ownerNode pointNode : FreeNode) (words : Array UInt64) :
    computeAccepted.drop 149 = releasePlanProgram (computeCleanupEntries ownerNode pointNode words) := rfl

theorem computeCleanup_exact (env : HostEnv Unit) (initial middle : Store Unit) (original heap : Heap)
    (pointer : UInt64) (locals : List Value) (ownerNode pointNode resultNode : FreeNode) (words resultWords : Array UInt64)
    (state : ComputeResultLocals locals ownerNode.root pointNode.root resultNode.root)
    (remaining pageLimit : Nat) (valid : heap.At middle)
    (ownerOwned : heap.OwnsWords middle ownerNode words) (pointOwned : heap.OwnsWords middle pointNode words)
    (resultOwned : heap.OwnsWords middle resultNode resultWords) (preserved : original.Frame initial heap middle)
    (ownerFresh : FreshFor original ownerNode) (pointFresh : FreshFor original pointNode)
    (separated : regionsDisjoint ownerNode.region pointNode.region)
    (ownerResult : regionsDisjoint ownerNode.region resultNode.region)
    (pointResult : regionsDisjoint pointNode.region resultNode.region)
    (budget : OutputBudget middle heap remaining pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap, finalHeap.At final → finalHeap.OwnsWords final resultNode resultWords →
      original.Frame initial finalHeap final → OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      Q (.Fallthrough final { params := [.i64 pointer], locals := locals })) :
    wp Project.Beck.«module» (computeAccepted.drop 149) Q middle { params := [.i64 pointer], locals := locals } env := by
  let frame : Locals := { params := [.i64 pointer], locals := locals }
  have r26 : frame.get 26 = some (.i64 ownerNode.root) := by
    simpa only [frame, Locals.get, List.length_cons, List.length_nil, state.size,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte] using state.initialOwner
  have r27 : frame.get 27 = some (.i64 pointNode.root) := by
    simpa only [frame, Locals.get, List.length_cons, List.length_nil, state.size,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte] using state.initialPointer
  have r55 : frame.get 55 = some (.i64 resultNode.root) := by
    simpa only [frame, Locals.get, List.length_cons, List.length_nil, state.size,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte] using state.owner
  rw [compute_cleanup_shape ownerNode pointNode words]
  apply releasePlan_exact env initial middle original heap frame (computeCleanupEntries ownerNode pointNode words)
    resultNode resultWords remaining pageLimit valid
  · intro entry member
    simp only [computeCleanupEntries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact pointOwned
    · exact ownerOwned
  · exact resultOwned
  · exact preserved
  · intro entry member
    simp only [computeCleanupEntries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact pointFresh
    · exact ownerFresh
  · simp [computeCleanupEntries, List.pairwise_cons, regionsDisjoint_symm separated]
  · intro entry member
    simp only [computeCleanupEntries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact pointResult
    · exact ownerResult
  · exact budget
  · rfl
  · intro entry member
    simp only [computeCleanupEntries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact r27
    · exact r26
  · intro entry member other avoided
    simp only [computeCleanupEntries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simp only [List.mem_singleton] at avoided
      subst other
      exact ⟨_, r55, ownedRoots_ne pointOwned resultOwned pointResult⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at avoided
      rcases avoided with rfl | rfl
      · exact ⟨_, r27, ownedRoots_ne ownerOwned pointOwned separated⟩
      · exact ⟨_, r55, ownedRoots_ne ownerOwned resultOwned ownerResult⟩
  · exact next

#print axioms computeCleanup_exact

end Project.Beck.Execution
