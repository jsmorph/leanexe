import Project.Beck.ExecutionFresh

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def previousReleaseProgram (oldLocal extraLocal newLocal inputLocal : Nat) : Wasm.Program :=
  [.localGet oldLocal, .constI64 0, .eqI64, .eqz,
    .iff 0 1 [.localGet oldLocal, .localGet newLocal, .eqI64, .eqz] [.const 0] [] [.i32],
    .iff 0 1 [.localGet oldLocal, .localGet inputLocal, .eqI64, .eqz] [.const 0] [] [.i32],
    .iff 0 0 [.localGet oldLocal, .call 39] [],
    .localGet extraLocal, .constI64 0, .eqI64, .eqz,
    .iff 0 1 [.localGet extraLocal, .localGet oldLocal, .eqI64, .eqz] [.const 0] [] [.i32],
    .iff 0 1 [.localGet extraLocal, .localGet newLocal, .eqI64, .eqz] [.const 0] [] [.i32],
    .iff 0 1 [.localGet extraLocal, .localGet inputLocal, .eqI64, .eqz] [.const 0] [] [.i32],
    .iff 0 0 [.localGet extraLocal, .call 39] []]

theorem previousRelease_none (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (oldLocal extraLocal newLocal inputLocal : Nat)
    (values : frame.values = []) (oldRead : frame.get oldLocal = some (.i64 0)) (extraRead : frame.get extraLocal = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program) (next : wp Project.Beck.«module» rest Q initial frame env) :
    wp Project.Beck.«module» (previousReleaseProgram oldLocal extraLocal newLocal inputLocal ++ rest) Q initial frame env := by
  have frameEq : ({frame with values := []} : Locals) = frame := Frame.ext _ _ rfl rfl values.symm
  rw [previousReleaseProgram]
  simp only [List.cons_append, List.nil_append]
  repeat' ((try simp only [wp_simp, Frame.withValues_get, oldRead, extraRead, values, frameEq,
      List.take, List.drop, List.append_nil, reduceIte, ne_eq, not_true_eq_false]) <;>
    (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
  simpa only [wp_simp, Frame.withValues_get, oldRead, extraRead, values, frameEq, List.take, List.drop, List.append_nil,
    reduceIte, ne_eq, not_true_eq_false] using next

theorem previousRelease_owned (env : HostEnv Unit) (initial middle : Store Unit) (original current : Heap)
    (frame : Locals) (oldLocal extraLocal newLocal inputLocal : Nat)
    (node : FreeNode) (words : Array UInt64) (newRoot wordOwner : UInt64)
    (remaining pageLimit : Nat) (valid : current.At middle) (owned : current.OwnsWords middle node words)
    (preserved : original.Frame initial current middle) (fresh : FreshFor original node)
    (budget : OutputBudget middle current remaining pageLimit Project.Beck.«module»)
    (newDifferent : node.root ≠ newRoot) (inputDifferent : node.root ≠ wordOwner)
    (values : frame.values = []) (oldRead : frame.get oldLocal = some (.i64 node.root)) (extraRead : frame.get extraLocal = some (.i64 0))
    (inputRead : frame.get inputLocal = some (.i64 wordOwner)) (newRead : frame.get newLocal = some (.i64 newRoot))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : (current.release node).At (current.releaseStore middle node) →
      original.Frame initial (current.release node) (current.releaseStore middle node) →
      OutputBudget (current.releaseStore middle node) (current.release node) remaining pageLimit Project.Beck.«module» →
      wp Project.Beck.«module» rest Q (current.releaseStore middle node) frame env) :
    wp Project.Beck.«module» (previousReleaseProgram oldLocal extraLocal newLocal inputLocal ++ rest) Q middle frame env := by
  have frameEq : ({frame with values := []} : Locals) = frame := Frame.ext _ _ rfl rfl values.symm
  have nonzero : node.root ≠ 0 := by
    intro equal
    have := owned.buffer.rootBound
    rw [equal] at this
    contradiction
  have call := releaseWords_budget env initial middle original current node words remaining pageLimit
    valid owned preserved fresh budget
  rw [previousReleaseProgram]
  simp only [List.cons_append, List.nil_append]
  repeat' ((try simp only [wp_simp, Frame.withValues_get, oldRead, inputRead, newRead, values, frameEq,
      nonzero, newDifferent, inputDifferent, List.take, List.drop, List.append_nil, reduceIte,
      ne_eq, not_true_eq_false, not_false_eq_true]) <;>
    (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
  simp only [wp_simp, Frame.withValues_get, oldRead, values, List.take, List.drop, List.append_nil]
  refine wp_call_tw call ?_
  rintro final returned ⟨rfl, rfl, finalValid, finalFrame, finalBudget⟩
  repeat' ((try simp only [wp_simp, Frame.withValues_get, oldRead, extraRead, inputRead, newRead, values, frameEq,
      List.take, List.drop, List.append_nil, reduceIte, ne_eq, not_true_eq_false]) <;>
    (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
  simpa only [wp_simp, Frame.withValues_get, oldRead, extraRead, values, frameEq, List.take, List.drop, List.append_nil,
    reduceIte, ne_eq, not_true_eq_false] using next finalValid finalFrame finalBudget

theorem previousCleanup_exact (env : HostEnv Unit) (initial middle : Store Unit) (original current : Heap)
    (frame : Locals) (oldLocal extraLocal newLocal inputLocal : Nat) (oldNode newNode : FreeNode) (oldRow newRow : Array UInt64) (internal wordOwner : UInt64)
    (remaining pageLimit : Nat) (valid : current.At middle)
    (oldOwned : current.OwnsWords middle oldNode oldRow) (newOwned : current.OwnsWords middle newNode newRow)
    (preserved : original.Frame initial current middle)
    (active : internal = 0 ∨ internal = oldNode.root ∧ FreshFor original oldNode)
    (separated : regionsDisjoint oldNode.region newNode.region)
    (inputDifferent : oldNode.root ≠ wordOwner)
    (budget : OutputBudget middle current remaining pageLimit Project.Beck.«module»)
    (values : frame.values = []) (r7 : frame.get oldLocal = some (.i64 internal)) (r8 : frame.get extraLocal = some (.i64 0))
    (r14 : frame.get inputLocal = some (.i64 wordOwner)) (r21 : frame.get newLocal = some (.i64 newNode.root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap, finalHeap.At final → finalHeap.OwnsWords final newNode newRow →
      original.Frame initial finalHeap final →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      wp Project.Beck.«module» rest Q final frame env) :
    wp Project.Beck.«module» (previousReleaseProgram oldLocal extraLocal newLocal inputLocal ++ rest) Q middle frame env := by
  rcases active with zero | ⟨rfl, fresh⟩
  · apply previousRelease_none env middle frame oldLocal extraLocal newLocal inputLocal values (by simpa only [zero] using r7) r8
    exact next middle current valid newOwned preserved budget
  · have different : oldNode.root ≠ newNode.root := by
      intro equal
      have oldRoot := oldOwned.buffer.rootBound
      have newRoot := newOwned.buffer.rootBound
      have oldCapacity := oldOwned.buffer.capacity
      have newCapacity := newOwned.buffer.capacity
      simp only [regionsDisjoint, FreeNode.region, equal] at separated
      rw [equal] at oldRoot
      omega
    apply previousRelease_owned env initial middle original current frame oldLocal extraLocal newLocal inputLocal oldNode oldRow newNode.root wordOwner
      remaining pageLimit valid oldOwned preserved fresh budget different inputDifferent values r7 r8 r14 r21
    intro finalValid finalFrame finalBudget
    exact next _ _ finalValid
      (newOwned.released oldNode oldOwned.buffer.rootBound (by have := oldOwned.buffer.addressBound; omega)
        (regionsDisjoint_symm separated)) finalFrame finalBudget

#print axioms previousCleanup_exact
#print axioms previousRelease_none
#print axioms previousRelease_owned

end Project.Beck.Execution
