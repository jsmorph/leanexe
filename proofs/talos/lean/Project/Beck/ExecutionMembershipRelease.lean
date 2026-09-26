import Project.Beck.ExecutionMembershipBase
import Project.Beck.ExecutionFresh

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
  have frameEq : ({frame with values := []} : Locals) = frame := Frame.ext _ _ rfl rfl values.symm
  rw [membership_release_shape]
  simp only [List.cons_append, List.nil_append]
  repeat' ((try simp only [wp_simp, Frame.withValues_get, r7, r8, values, frameEq,
      List.take, List.drop, List.append_nil, reduceIte, ne_eq, not_true_eq_false]) <;>
    (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
  simpa only [wp_simp, Frame.withValues_get, r7, r8, values, frameEq, List.take, List.drop, List.append_nil,
    reduceIte, ne_eq, not_true_eq_false] using next

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
  have frameEq : ({frame with values := []} : Locals) = frame := Frame.ext _ _ rfl rfl values.symm
  have nonzero : node.root ≠ 0 := by
    intro equal
    have := owned.buffer.rootBound
    rw [equal] at this
    contradiction
  have call := releaseWords_budget env initial middle original current node words remaining pageLimit
    valid owned preserved fresh budget
  rw [membership_release_shape]
  simp only [List.cons_append, List.nil_append]
  repeat' ((try simp only [wp_simp, Frame.withValues_get, r7, r8, r14, r21, values, frameEq,
      nonzero, newDifferent, inputDifferent, List.take, List.drop, List.append_nil, reduceIte,
      ne_eq, not_true_eq_false, not_false_eq_true]) <;>
    (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
  simp only [wp_simp, Frame.withValues_get, r7, values, List.take, List.drop, List.append_nil]
  refine wp_call_tw call ?_
  rintro final returned ⟨rfl, rfl, finalValid, finalFrame, finalBudget⟩
  repeat' ((try simp only [wp_simp, Frame.withValues_get, r7, r8, r14, r21, values, frameEq,
      List.take, List.drop, List.append_nil, reduceIte, ne_eq, not_true_eq_false]) <;>
    (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
  simpa only [wp_simp, Frame.withValues_get, r7, r8, values, frameEq, List.take, List.drop, List.append_nil,
    reduceIte, ne_eq, not_true_eq_false] using next finalValid finalFrame finalBudget

#print axioms membershipRelease_none
#print axioms membershipRelease_owned

end Project.Beck.Execution
