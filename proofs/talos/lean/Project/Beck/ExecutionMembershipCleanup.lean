import Project.Beck.ExecutionMembershipState

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

theorem membershipCleanup_exact (env : HostEnv Unit) (initial middle : Store Unit) (original current : Heap)
    (frame : Locals) (oldNode newNode : FreeNode) (oldRow newRow : Array UInt64) (internal wordOwner : UInt64)
    (remaining pageLimit : Nat) (valid : current.At middle)
    (oldOwned : current.OwnsWords middle oldNode oldRow) (newOwned : current.OwnsWords middle newNode newRow)
    (preserved : original.Frame initial current middle)
    (active : internal = 0 ∨ internal = oldNode.root ∧ FreshFor original oldNode)
    (separated : regionsDisjoint oldNode.region newNode.region)
    (inputDifferent : oldNode.root ≠ wordOwner)
    (budget : OutputBudget middle current remaining pageLimit Project.Beck.«module»)
    (values : frame.values = []) (r7 : frame.get 7 = some (.i64 internal)) (r8 : frame.get 8 = some (.i64 0))
    (r14 : frame.get 14 = some (.i64 wordOwner)) (r21 : frame.get 21 = some (.i64 newNode.root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap, finalHeap.At final → finalHeap.OwnsWords final newNode newRow →
      original.Frame initial finalHeap final →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      wp Project.Beck.«module» rest Q final frame env) :
    wp Project.Beck.«module» (membershipRelease ++ rest) Q middle frame env := by
  rw [membership_release_shape]
  exact previousCleanup_exact env initial middle original current frame 7 8 21 14 oldNode newNode oldRow newRow internal wordOwner
    remaining pageLimit valid oldOwned newOwned preserved active separated inputDifferent budget values r7 r8 r14 r21 Q rest next

#print axioms membershipCleanup_exact

end Project.Beck.Execution
