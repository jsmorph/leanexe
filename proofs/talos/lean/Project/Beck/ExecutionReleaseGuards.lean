import Project.Beck.ExecutionKeptRelease
import Project.ProofKit.Sequence

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def releaseAliasGuard (owner other : Nat) : Wasm.Program :=
  [.iff 0 1 [.localGet owner, .localGet other, .eqI64, .eqz] [.const 0] [] [.i32]]

def releaseAliasGuards (owner : Nat) (others : List Nat) : Wasm.Program :=
  others.flatMap (releaseAliasGuard owner)

theorem releaseAliasGuard_exact (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (owner other : Nat) (root pointer : UInt64)
    (ownerRead : frame.get owner = some (.i64 root)) (otherRead : frame.get other = some (.i64 pointer))
    (different : root ≠ pointer) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { frame with values := [.i32 1] })) :
    wp Project.Beck.«module» (releaseAliasGuard owner other) Q initial { frame with values := [.i32 1] } env := by
  simp only [releaseAliasGuard, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_false_eq_true, reduceIte]
  simpa only [wp_simp, Frame.withValues_get, ownerRead, otherRead, different,
    List.take, List.drop, List.append_nil, reduceIte] using next

theorem releaseAliasGuards_exact (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (owner : Nat) (others : List Nat) (root : UInt64)
    (ownerRead : frame.get owner = some (.i64 root))
    (otherReads : ∀ other ∈ others, ∃ pointer, frame.get other = some (.i64 pointer) ∧ root ≠ pointer)
    (Q : Assertion Unit) (next : Q (.Fallthrough initial { frame with values := [.i32 1] })) :
    wp Project.Beck.«module» (releaseAliasGuards owner others) Q initial { frame with values := [.i32 1] } env := by
  induction others with
  | nil => simpa only [releaseAliasGuards, List.flatMap_nil, wp_nil] using next
  | cons other others ih =>
    obtain ⟨pointer, otherRead, different⟩ := otherReads other (by simp)
    change wp Project.Beck.«module» (releaseAliasGuard owner other ++ releaseAliasGuards owner others) Q initial _ env
    refine Sequence.wp_append (P := fun store after => store = initial ∧ after = { frame with values := [.i32 1] }) ?_ ?_
    · exact releaseAliasGuard_exact env initial frame owner other root pointer ownerRead otherRead different _ ⟨rfl, rfl⟩
    rintro store after ⟨rfl, rfl⟩
    exact ih (fun k member => otherReads k (List.mem_cons_of_mem _ member))

def knownReleaseProgram (owner : Nat) (others : List Nat) : Wasm.Program :=
  [.localGet owner, .constI64 0, .eqI64, .eqz] ++ releaseAliasGuards owner others ++
    [.iff 0 0 [.localGet owner, .call 39] []]

theorem knownRelease_exact (env : HostEnv Unit) (initial middle : Store Unit) (original heap : Heap)
    (frame : Locals) (owner : Nat) (others : List Nat) (node : FreeNode) (words : Array UInt64)
    (remaining pageLimit : Nat) (valid : heap.At middle) (owned : heap.OwnsWords middle node words)
    (preserved : original.Frame initial heap middle) (fresh : FreshFor original node)
    (budget : OutputBudget middle heap remaining pageLimit Project.Beck.«module»)
    (values : frame.values = []) (ownerRead : frame.get owner = some (.i64 node.root))
    (otherReads : ∀ other ∈ others, ∃ pointer, frame.get other = some (.i64 pointer) ∧ node.root ≠ pointer)
    (Q : Assertion Unit)
    (next : (heap.release node).At (heap.releaseStore middle node) →
      original.Frame initial (heap.release node) (heap.releaseStore middle node) →
      OutputBudget (heap.releaseStore middle node) (heap.release node) remaining pageLimit Project.Beck.«module» →
      Q (.Fallthrough (heap.releaseStore middle node) frame)) :
    wp Project.Beck.«module» (knownReleaseProgram owner others) Q middle frame env := by
  have frameEq : ({ frame with values := [] } : Locals) = frame := Frame.ext _ _ rfl rfl values.symm
  have nonzero : node.root ≠ 0 := by
    intro equal
    have := owned.buffer.rootBound
    rw [equal] at this
    contradiction
  simp only [knownReleaseProgram, List.append_assoc, List.cons_append, List.nil_append,
    wp_simp, Frame.withValues_get, ownerRead, values, nonzero, reduceIte]
  refine Sequence.wp_append (P := fun store after => store = middle ∧ after = { frame with values := [.i32 1] }) ?_ ?_
  · exact releaseAliasGuards_exact env middle frame owner others node.root ownerRead otherReads _ ⟨rfl, rfl⟩
  rintro store after ⟨same, frameSame⟩
  subst store after
  refine wp_iff_cons rfl ?_
  simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_false_eq_true, reduceIte,
    wp_simp, Frame.withValues_get, ownerRead]
  refine wp_call_tw (releaseWords_budget env initial middle original heap node words remaining pageLimit valid owned preserved fresh budget) ?_
  rintro final returned ⟨rfl, rfl, finalValid, finalFrame, finalBudget⟩
  simpa only [wp_simp, List.take, List.drop, List.append_nil, frameEq] using next finalValid finalFrame finalBudget

#print axioms knownRelease_exact

end Project.Beck.Execution
