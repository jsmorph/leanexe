import Project.Beck.ExecutionFresh

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def keptReleaseProgram (oldLocal resultLocal : Nat) : Wasm.Program :=
  [.localGet oldLocal, .constI64 0, .eqI64, .eqz,
    .iff 0 1 [.localGet oldLocal, .localGet resultLocal, .eqI64, .eqz] [.const 0] [] [.i32],
    .iff 0 0 [.localGet oldLocal, .call 39] []]

theorem keptRelease_exact (env : HostEnv Unit) (initial middle : Store Unit) (original heap : Heap)
    (frame : Locals) (oldLocal resultLocal : Nat) (oldNode resultNode : FreeNode) (oldWords resultWords : Array UInt64)
    (remaining pageLimit : Nat) (valid : heap.At middle)
    (oldOwned : heap.OwnsWords middle oldNode oldWords) (resultOwned : heap.OwnsWords middle resultNode resultWords)
    (preserved : original.Frame initial heap middle) (fresh : FreshFor original oldNode)
    (separated : oldNode.root ≠ resultNode.root → regionsDisjoint oldNode.region resultNode.region)
    (budget : OutputBudget middle heap remaining pageLimit Project.Beck.«module»)
    (values : frame.values = []) (oldRead : frame.get oldLocal = some (.i64 oldNode.root))
    (resultRead : frame.get resultLocal = some (.i64 resultNode.root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap, finalHeap.At final → finalHeap.OwnsWords final resultNode resultWords →
      original.Frame initial finalHeap final → OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      wp Project.Beck.«module» rest Q final frame env) :
    wp Project.Beck.«module» (keptReleaseProgram oldLocal resultLocal ++ rest) Q middle frame env := by
  have frameEq : ({frame with values := []} : Locals) = frame := Frame.ext _ _ rfl rfl values.symm
  have nonzero : oldNode.root ≠ 0 := by
    intro equal
    have := oldOwned.buffer.rootBound
    rw [equal] at this
    contradiction
  rw [keptReleaseProgram]
  simp only [List.cons_append, List.nil_append]
  by_cases same : oldNode.root = resultNode.root
  · have resultNonzero : resultNode.root ≠ 0 := by simpa only [same] using nonzero
    repeat' ((try simp only [wp_simp, Frame.withValues_get, oldRead, resultRead, values, frameEq,
        nonzero, same, resultNonzero, List.take, List.drop, List.append_nil, reduceIte, ne_eq, not_true_eq_false, not_false_eq_true]) <;>
      (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
    simpa only [wp_simp, List.take, List.drop, List.append_nil, frameEq, values] using
      next middle heap valid resultOwned preserved budget
  · have call := releaseWords_budget env initial middle original heap oldNode oldWords remaining pageLimit valid oldOwned preserved fresh budget
    repeat' ((try simp only [wp_simp, Frame.withValues_get, oldRead, resultRead, values, frameEq,
        nonzero, same, List.take, List.drop, List.append_nil, reduceIte, ne_eq, not_true_eq_false, not_false_eq_true]) <;>
      (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
    simp only [wp_simp, Frame.withValues_get, oldRead, values, List.take, List.drop, List.append_nil]
    refine wp_call_tw call ?_
    rintro final returned ⟨rfl, rfl, finalValid, finalFrame, finalBudget⟩
    have retained := resultOwned.released oldNode oldOwned.buffer.rootBound
      (by have := oldOwned.buffer.addressBound; omega) (regionsDisjoint_symm (separated same))
    simpa only [wp_simp, List.take, List.drop, List.append_nil, frameEq, values] using
      next _ _ finalValid retained finalFrame finalBudget

#print axioms keptRelease_exact

end Project.Beck.Execution
