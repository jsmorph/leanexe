import Project.Beck.ExecutionMatrixFrame
import Project.Beck.ExecutionFresh

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

set_option maxRecDepth 2048 in
theorem matrix_release_shape : (matrixRowBody.drop 118).take 12 =
    [.localGet 27, .constI64 0, .neI64, .localGet 27, .localGet 91, .neI64, .and,
      .localGet 27, .localGet 89, .neI64, .and, .iff 0 0 [.localGet 27, .call 39] []] := rfl

def loopArrayCleanupProgram (oldLocal initialLocal newLocal : Nat) : Wasm.Program :=
  [.localGet oldLocal, .constI64 0, .neI64, .localGet oldLocal, .localGet initialLocal, .neI64, .and,
    .localGet oldLocal, .localGet newLocal, .neI64, .and, .iff 0 0 [.localGet oldLocal, .call 39] []]

theorem loopArrayCleanup_exact (env : HostEnv Unit) (initial middle : Store Unit) (original current : Heap)
    (frame : Locals) (oldLocal initialLocal newLocal : Nat)
    (oldNode newNode : FreeNode) (oldWords newWords : Array UInt64) (initialOwner : UInt64)
    (remaining pageLimit : Nat) (valid : current.At middle)
    (oldOwned : current.OwnsWords middle oldNode oldWords) (newOwned : current.OwnsWords middle newNode newWords)
    (preserved : original.Frame initial current middle)
    (active : oldNode.root = initialOwner ∨ FreshFor original oldNode)
    (separated : regionsDisjoint oldNode.region newNode.region)
    (budget : OutputBudget middle current remaining pageLimit Project.Beck.«module»)
    (values : frame.values = []) (oldRead : frame.get oldLocal = some (.i64 oldNode.root))
    (initialRead : frame.get initialLocal = some (.i64 initialOwner)) (newRead : frame.get newLocal = some (.i64 newNode.root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap, finalHeap.At final → finalHeap.OwnsWords final newNode newWords →
      original.Frame initial finalHeap final → OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      wp Project.Beck.«module» rest Q final frame env) :
    wp Project.Beck.«module» (loopArrayCleanupProgram oldLocal initialLocal newLocal ++ rest) Q middle frame env := by
  have frameEq : ({frame with values := []} : Locals) = frame := Frame.ext _ _ rfl rfl values.symm
  have nonzero : oldNode.root ≠ 0 := by
    intro equal
    have := oldOwned.buffer.rootBound
    rw [equal] at this
    contradiction
  have different : oldNode.root ≠ newNode.root := by
    intro equal
    have oldRoot := oldOwned.buffer.rootBound
    have newRoot := newOwned.buffer.rootBound
    have oldCapacity := oldOwned.buffer.capacity
    have newCapacity := newOwned.buffer.capacity
    simp only [regionsDisjoint, FreeNode.region, equal] at separated
    rw [equal] at oldRoot
    omega
  unfold loopArrayCleanupProgram
  by_cases same : oldNode.root = initialOwner
  · simp only [List.cons_append, List.nil_append, wp_simp, Frame.withValues_get, oldRead, initialRead, newRead,
      values, frameEq, nonzero, different, same, reduceIte, ne_eq, not_true_eq_false, not_false_eq_true]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simp)]
    simpa only [wp_simp, List.take, List.drop, List.append_nil, frameEq, values] using
      next middle current valid newOwned preserved budget
  · have fresh := active.resolve_left same
    have call := releaseWords_budget env initial middle original current oldNode oldWords remaining pageLimit
      valid oldOwned preserved fresh budget
    simp only [List.cons_append, List.nil_append, wp_simp, Frame.withValues_get, oldRead, initialRead, newRead,
      values, frameEq, nonzero, different, same, reduceIte, ne_eq, not_true_eq_false, not_false_eq_true]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by decide)]
    simp only [wp_simp, Frame.withValues_get, oldRead, values, List.take, List.drop, List.append_nil]
    refine wp_call_tw call ?_
    rintro final returned ⟨rfl, rfl, finalValid, finalFrame, finalBudget⟩
    have retained := newOwned.released oldNode oldOwned.buffer.rootBound
      (by have := oldOwned.buffer.addressBound; omega) (regionsDisjoint_symm separated)
    simpa only [wp_simp, List.take, List.drop, List.append_nil, frameEq, values] using
      next _ _ finalValid retained finalFrame finalBudget

theorem matrixCleanup_exact (env : HostEnv Unit) (initial middle : Store Unit) (original current : Heap)
    (frame : Locals) (oldNode newNode : FreeNode) (oldWords newWords : Array UInt64) (initialOwner : UInt64)
    (remaining pageLimit : Nat) (valid : current.At middle)
    (oldOwned : current.OwnsWords middle oldNode oldWords) (newOwned : current.OwnsWords middle newNode newWords)
    (preserved : original.Frame initial current middle)
    (active : oldNode.root = initialOwner ∨ FreshFor original oldNode)
    (separated : regionsDisjoint oldNode.region newNode.region)
    (budget : OutputBudget middle current remaining pageLimit Project.Beck.«module»)
    (values : frame.values = []) (oldRead : frame.get 27 = some (.i64 oldNode.root))
    (initialRead : frame.get 91 = some (.i64 initialOwner)) (newRead : frame.get 89 = some (.i64 newNode.root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap, finalHeap.At final → finalHeap.OwnsWords final newNode newWords →
      original.Frame initial finalHeap final → OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      wp Project.Beck.«module» rest Q final frame env) :
    wp Project.Beck.«module» ((matrixRowBody.drop 118).take 12 ++ rest) Q middle frame env := by
  rw [matrix_release_shape]
  exact loopArrayCleanup_exact env initial middle original current frame 27 91 89 oldNode newNode oldWords newWords initialOwner
    remaining pageLimit valid oldOwned newOwned preserved active separated budget values oldRead initialRead newRead Q rest next

#print axioms loopArrayCleanup_exact
#print axioms matrixCleanup_exact

end Project.Beck.Execution
