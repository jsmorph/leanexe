import Project.Beck.ExecutionJobAppendCapacity

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

set_option maxRecDepth 2048 in
theorem job_release_shape : (jobAccepted.drop 104).take 15 = previousReleaseProgram 8 9 40 35 := rfl

theorem jobCleanup_exact (env : HostEnv Unit) (initial middle : Store Unit) (original current : Heap)
    (frame : Locals) (oldNode newNode : FreeNode) (oldRow newRow : Array UInt64) (internal wordOwner : UInt64)
    (remaining pageLimit : Nat) (valid : current.At middle)
    (oldOwned : current.OwnsWords middle oldNode oldRow) (newOwned : current.OwnsWords middle newNode newRow)
    (preserved : original.Frame initial current middle)
    (active : internal = 0 ∨ internal = oldNode.root ∧ FreshFor original oldNode)
    (separated : regionsDisjoint oldNode.region newNode.region) (inputDifferent : oldNode.root ≠ wordOwner)
    (budget : OutputBudget middle current remaining pageLimit Project.Beck.«module»)
    (values : frame.values = []) (r8 : frame.get 8 = some (.i64 internal)) (r9 : frame.get 9 = some (.i64 0))
    (r35 : frame.get 35 = some (.i64 wordOwner)) (r40 : frame.get 40 = some (.i64 newNode.root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap, finalHeap.At final → finalHeap.OwnsWords final newNode newRow →
      original.Frame initial finalHeap final →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      wp Project.Beck.«module» rest Q final frame env) :
    wp Project.Beck.«module» ((jobAccepted.drop 104).take 15 ++ rest) Q middle frame env := by
  rw [job_release_shape]
  exact previousCleanup_exact env initial middle original current frame 8 9 40 35 oldNode newNode oldRow newRow internal wordOwner
    remaining pageLimit valid oldOwned newOwned preserved active separated inputDifferent budget values r8 r9 r35 r40 Q rest next

#print axioms jobCleanup_exact

end Project.Beck.Execution
