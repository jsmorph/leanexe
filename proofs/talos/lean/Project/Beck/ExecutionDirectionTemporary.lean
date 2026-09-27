import Project.Beck.ExecutionDirectionCofactor

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def directionResultLocals (locals : List Value) (root : UInt64) : List Value :=
  ((((locals.set 77 (.i64 root)).set 78 (.i64 root)).set 79 (.i64 root)).set 80 (.i64 root)).set 81 (.i64 0)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem directionTemporaryGuard_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (temporary current result : UInt64) (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (temporaryRead : locals[62]? = some (.i64 temporary)) (currentRead : locals[54]? = some (.i64 current))
    (nonzero : temporary ≠ 0) (notCurrent : temporary ≠ current) (notResult : temporary ≠ result)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := directionResultLocals locals result, values := [.i32 1] })) :
    wp Project.Beck.«module» ((directionBody.drop 90).take 16) Q initial
      { params := params, locals := locals, values := [.i64 result] } env := by
  simp only [directionBody, directionEligible, func30, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  repeat' first
    | wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
        Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, temporaryRead, currentRead,
        nonzero, notCurrent, notResult, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte]
    | (try simp only [wp_iff_control_types]
       refine wp_iff_cons rfl ?_
       simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_false_eq_true, reduceIte])
  exact next

set_option maxRecDepth 4096 in
theorem direction_temporary_shape : (directionBody.drop 90).take 17 =
    (directionBody.drop 90).take 16 ++ [.iff 0 0 [.localGet 71, .call 39, .globalGet 5, .localSet 91] []] := rfl

theorem directionTemporaryRelease_exact (env : HostEnv Unit) (initial middle : Store Unit) (original heap : Heap)
    (params locals : List Value) (temporary result : FreeNode) (temporaryWords resultWords : Array UInt64) (current : UInt64)
    (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (temporaryRead : locals[62]? = some (.i64 temporary.root)) (currentRead : locals[54]? = some (.i64 current))
    (notCurrent : temporary.root ≠ current) (separated : regionsDisjoint temporary.region result.region)
    (remaining pageLimit : Nat) (valid : heap.At middle)
    (temporaryOwned : heap.OwnsWords middle temporary temporaryWords) (resultOwned : heap.OwnsWords middle result resultWords)
    (preserved : original.Frame initial heap middle) (fresh : FreshFor original temporary)
    (budget : OutputBudget middle heap remaining pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : (heap.release temporary).At (heap.releaseStore middle temporary) →
      (heap.release temporary).OwnsWords (heap.releaseStore middle temporary) result resultWords →
      original.Frame initial (heap.release temporary) (heap.releaseStore middle temporary) →
      OutputBudget (heap.releaseStore middle temporary) (heap.release temporary) remaining pageLimit Project.Beck.«module» →
      Q (.Fallthrough (heap.releaseStore middle temporary)
        { params := params, locals := (directionResultLocals locals result.root).set 82 (.i64 (heap.frees + 1)) })) :
    wp Project.Beck.«module» ((directionBody.drop 90).take 17) Q middle
      { params := params, locals := locals, values := [.i64 result.root] } env := by
  have nonzero : temporary.root ≠ 0 := by
    intro equal
    have := temporaryOwned.buffer.rootBound
    rw [equal] at this
    contradiction
  have notResult : temporary.root ≠ result.root := by
    intro equal
    have root := temporaryOwned.buffer.rootBound
    have resultRoot := resultOwned.buffer.rootBound
    have capacity := temporaryOwned.buffer.capacity
    have resultCapacity := resultOwned.buffer.capacity
    simp only [regionsDisjoint, FreeNode.region, equal] at separated
    rw [equal] at root
    omega
  let prepared := directionResultLocals locals result.root
  have preparedSize : prepared.length = 112 := by simp [prepared, directionResultLocals, localsSize]
  have preparedRead : prepared[62]? = some (.i64 temporary.root) := by
    simpa only [prepared, directionResultLocals, List.getElem?_set, List.length_set,
      localsSize, Nat.reduceLT, Nat.reduceEqDiff, reduceIte] using temporaryRead
  rw [direction_temporary_shape]
  refine Sequence.wp_append (P := fun store frame => store = middle ∧
    frame = { params := params, locals := prepared, values := [.i32 1] }) ?_ ?_
  · exact directionTemporaryGuard_exact env middle params locals temporary.root current result.root paramsSize localsSize
      temporaryRead currentRead nonzero notCurrent notResult _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  refine wp_iff_cons rfl ?_
  simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_false_eq_true, reduceIte]
  wp_run [paramsSize, preparedSize, Nat.reduceLT, Nat.reduceSub, preparedRead, reduceIte]
  refine wp_call_tw (releaseWords_budget env initial middle original heap temporary temporaryWords remaining pageLimit
    valid temporaryOwned preserved fresh budget) ?_
  rintro final values ⟨rfl, rfl, finalValid, finalFrame, finalBudget⟩
  have retained := resultOwned.released temporary temporaryOwned.buffer.rootBound
    (by have := temporaryOwned.buffer.addressBound; omega) (regionsDisjoint_symm separated)
  have globalRead : (heap.releaseStore middle temporary).globals.globals[5]? = some (.i64 (heap.frees + 1)) := by
    simp [finalValid.globals, Heap.globals, Heap.release]
  wp_run [paramsSize, preparedSize, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, globalRead, List.take, List.drop, List.append_nil, reduceIte]
  simpa only [List.take, List.drop, List.append_nil] using next finalValid retained finalFrame finalBudget

#print axioms directionTemporaryRelease_exact

end Project.Beck.Execution
