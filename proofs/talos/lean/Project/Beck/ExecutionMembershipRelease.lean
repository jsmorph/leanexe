import Project.Beck.ExecutionMembershipBase
import Project.Beck.ExecutionPreviousRelease

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def membershipRelease : Wasm.Program := (membershipFresh.drop 39).take 15

set_option maxRecDepth 2048 in
theorem membership_release_shape : membershipRelease =
    [.localGet 7, .constI64 0, .eqI64, .eqz,
      .iff 0 1 [.localGet 7, .localGet 21, .eqI64, .eqz] [.const 0] [] [.i32],
      .iff 0 1 [.localGet 7, .localGet 14, .eqI64, .eqz] [.const 0] [] [.i32],
      .iff 0 0 [.localGet 7, .call 39] [],
      .localGet 8, .constI64 0, .eqI64, .eqz,
      .iff 0 1 [.localGet 8, .localGet 7, .eqI64, .eqz] [.const 0] [] [.i32],
      .iff 0 1 [.localGet 8, .localGet 21, .eqI64, .eqz] [.const 0] [] [.i32],
      .iff 0 1 [.localGet 8, .localGet 14, .eqI64, .eqz] [.const 0] [] [.i32],
      .iff 0 0 [.localGet 8, .call 39] []] := rfl

theorem membershipRelease_none (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (values : frame.values = []) (r7 : frame.get 7 = some (.i64 0)) (r8 : frame.get 8 = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program) (next : wp Project.Beck.«module» rest Q initial frame env) :
    wp Project.Beck.«module» (membershipRelease ++ rest) Q initial frame env := by
  rw [membership_release_shape]
  exact previousRelease_none env initial frame 7 8 21 14 values r7 r8 Q rest next

theorem membershipRelease_owned (env : HostEnv Unit) (initial middle : Store Unit) (original current : Heap)
    (frame : Locals) (node : FreeNode) (words : Array UInt64) (newRoot wordOwner : UInt64)
    (remaining pageLimit : Nat) (valid : current.At middle) (owned : current.OwnsWords middle node words)
    (preserved : original.Frame initial current middle) (fresh : FreshFor original node)
    (budget : OutputBudget middle current remaining pageLimit Project.Beck.«module»)
    (newDifferent : node.root ≠ newRoot) (inputDifferent : node.root ≠ wordOwner)
    (values : frame.values = []) (r7 : frame.get 7 = some (.i64 node.root)) (r8 : frame.get 8 = some (.i64 0))
    (r14 : frame.get 14 = some (.i64 wordOwner)) (r21 : frame.get 21 = some (.i64 newRoot))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : (current.release node).At (current.releaseStore middle node) →
      original.Frame initial (current.release node) (current.releaseStore middle node) →
      OutputBudget (current.releaseStore middle node) (current.release node) remaining pageLimit Project.Beck.«module» →
      wp Project.Beck.«module» rest Q (current.releaseStore middle node) frame env) :
    wp Project.Beck.«module» (membershipRelease ++ rest) Q middle frame env := by
  rw [membership_release_shape]
  exact previousRelease_owned env initial middle original current frame 7 8 21 14 node words newRoot wordOwner
    remaining pageLimit valid owned preserved fresh budget newDifferent inputDifferent values r7 r8 r14 r21 Q rest next

#print axioms membershipRelease_none
#print axioms membershipRelease_owned

end Project.Beck.Execution
