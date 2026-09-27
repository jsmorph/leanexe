import Project.Beck.ExecutionComputeAppend
import Project.Beck.ExecutionMatrixRelease
import Project.ProofKit.CheckedNatAddArithmetic

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def computeResultLocals (locals : List Value) (root : UInt64) : List Value :=
  let l := (((locals.set 46 (.i64 root)).set 47 (.i64 root)).set 48 (.i64 root)).set 49 (.i64 root)
  ((l.set 75 (.i64 root)).set 76 (.i64 root)).set 74 (.i64 0)

def computeAdvanceLocals (locals : List Value) (root : UInt64) (index : Nat) : List Value :=
  let l := (((locals.set 37 (.i64 root)).set 38 (.i64 root)).set 59 (.i64 index.toUInt64)).set 60 (.i64 1)
  (l.set 61 (.i64 (index + 1).toUInt64)).set 56 (.i64 (index + 1).toUInt64)

theorem computeResult_state {locals : List Value} {jobs overlap index : Nat}
    {initialOwner initialPointer pointRoot original current : UInt64}
    (state : ComputeOutputLocals locals jobs overlap initialOwner initialPointer pointRoot original current index) (root : UInt64) :
    ComputeOutputLocals (computeResultLocals locals root) jobs overlap initialOwner initialPointer pointRoot original current index := by
  apply state.preserved
  · simp [computeResultLocals]
  · unfold computeResultLocals
    repeat' apply WordLocals.set
    exact state.words
  · intro k bound
    simp (discharger := omega) only [computeResultLocals, List.getElem?_set_ne]

set_option maxRecDepth 4096 in
theorem computeResult_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (root : UInt64) (paramsSize : params.length = 1) (localsSize : locals.length = 79)
    (Q : Assertion Unit) (next : Q (.Fallthrough initial { params := params, locals := computeResultLocals locals root })) :
    wp Project.Beck.«module» ((computeOutputBody.drop 102).take 13) Q initial
      { params := params, locals := locals, values := [.i64 root] } env := by
  simp only [computeOutputBody, computeOutput, computeAccepted, func35, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem compute_previous_release_shape : (computeOutputBody.drop 115).take 12 = loopArrayCleanupProgram 38 78 76 := rfl

set_option maxRecDepth 4096 in
theorem computeAdvance_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (root : UInt64) (index : Nat) (indexBound : index < 6)
    (paramsSize : params.length = 1) (localsSize : locals.length = 79)
    (ownerRead : locals[75]? = some (.i64 root)) (pointerRead : locals[76]? = some (.i64 root))
    (flagRead : locals[74]? = some (.i64 0)) (indexRead : locals[56]? = some (.i64 index.toUInt64))
    (stepRead : locals[58]? = some (.i64 1)) (Q : Assertion Unit)
    (next : Q (.Break 0 initial { params := params, locals := computeAdvanceLocals locals root index })) :
    wp Project.Beck.«module» (computeOutputBody.drop 127) Q initial { params := params, locals := locals } env := by
  have fits : index + 1 < UInt64.size := by change index + 1 < 18446744073709551616; omega
  have guard : ¬index.toUInt64 + 1 < index.toUInt64 := CheckedNatAdd.guard_of_fits index 1 fits
  have increment : index.toUInt64 + 1 = (index + 1).toUInt64 := (UInt64.ofNat_add _ _).symm
  simp only [computeOutputBody, computeOutput, computeAccepted, func35, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop]
  repeat' first
    | wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
        Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, ownerRead, pointerRead, flagRead, indexRead, stepRead,
        guard, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte]
    | (try simp only [wp_iff_control_types]
       refine wp_iff_cons rfl ?_
       simp only [ne_eq, not_true_eq_false, reduceIte])
  simpa only [computeAdvanceLocals, increment, List.append_nil] using next

theorem computeAdvance_state {locals : List Value} {jobs overlap index : Nat}
    {initialOwner initialPointer pointRoot original current : UInt64}
    (state : ComputeOutputLocals locals jobs overlap initialOwner initialPointer pointRoot original current index) (root : UInt64) :
    ComputeOutputLocals (computeAdvanceLocals locals root index) jobs overlap initialOwner initialPointer pointRoot original root (index + 1) := by
  constructor
  · simp [computeAdvanceLocals, state.size]
  · unfold computeAdvanceLocals
    repeat' apply WordLocals.set
    exact state.words
  all_goals simp only [computeAdvanceLocals, List.length_set, List.getElem?_set, state.size, Nat.reduceLT, Nat.reduceEqDiff, reduceIte,
    state.jobs, state.overlap, state.initialOwner, state.initialPointer, state.pointPointer, state.firstOwner, state.firstPointer,
    state.limit, state.step, state.originalOwner]

#print axioms computeAdvance_exact

end Project.Beck.Execution
