import Project.Beck.ExecutionDirectionTemporary
import Project.Beck.ExecutionMatrixRelease
import Project.ProofKit.CheckedNatAddArithmetic

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def directionHandoffLocals (locals : List Value) (root : UInt64) : List Value :=
  ((locals.set 108 (.i64 root)).set 109 (.i64 root)).set 107 (.i64 0)

def directionAdvanceLocals (locals : List Value) (root : UInt64) (index : Nat) : List Value :=
  let l := (((locals.set 54 (.i64 root)).set 55 (.i64 root)).set 92 (.i64 index.toUInt64)).set 93 (.i64 1)
  (l.set 94 (.i64 (index + 1).toUInt64)).set 89 (.i64 (index + 1).toUInt64)

theorem directionTemporary_state {locals : List Value} {matrix sro srp sco scp : UInt64}
    {basis : Basis} {ro rp co cp original current : UInt64} {free index : Nat}
    (state : DirectionLoopLocals locals matrix sro srp sco scp basis ro rp co cp original current free index)
    (result frees : UInt64) :
    DirectionLoopLocals ((directionResultLocals locals result).set 82 (.i64 frees))
      matrix sro srp sco scp basis ro rp co cp original current free index := by
  apply state.preserved
  · simp [directionResultLocals]
  · unfold directionResultLocals
    repeat' apply WordLocals.set
    exact state.words
  · intro k bound
    simp (discharger := omega) only [directionResultLocals, List.getElem?_set_ne]

theorem directionHandoff_state {locals : List Value} {matrix sro srp sco scp : UInt64}
    {basis : Basis} {ro rp co cp original current : UInt64} {free index : Nat}
    (state : DirectionLoopLocals locals matrix sro srp sco scp basis ro rp co cp original current free index) (result : UInt64) :
    DirectionLoopLocals (directionHandoffLocals locals result)
      matrix sro srp sco scp basis ro rp co cp original current free index := by
  apply state.preserved
  · simp [directionHandoffLocals]
  · unfold directionHandoffLocals
    repeat' apply WordLocals.set
    exact state.words
  · intro k bound
    simp (discharger := omega) only [directionHandoffLocals, List.getElem?_set_ne]

set_option maxRecDepth 4096 in
theorem directionHandoff_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (root : UInt64) (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (ownerRead : locals[79]? = some (.i64 root)) (pointerRead : locals[80]? = some (.i64 root))
    (flagRead : locals[81]? = some (.i64 0)) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := directionHandoffLocals locals root })) :
    wp Project.Beck.«module» ((directionBody.drop 107).take 6) Q initial { params := params, locals := locals } env := by
  simp only [directionBody, directionEligible, func30, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, ownerRead, pointerRead, flagRead, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem direction_previous_release_shape : (directionBody.drop 113).take 12 = loopArrayCleanupProgram 63 119 117 := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem directionAdvance_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (root : UInt64) (index : Nat) (indexBound : index < 6)
    (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (ownerRead : locals[108]? = some (.i64 root)) (pointerRead : locals[109]? = some (.i64 root))
    (flagRead : locals[107]? = some (.i64 0)) (indexRead : locals[89]? = some (.i64 index.toUInt64))
    (stepRead : locals[91]? = some (.i64 1)) (Q : Assertion Unit)
    (next : Q (.Break 0 initial { params := params, locals := directionAdvanceLocals locals root index })) :
    wp Project.Beck.«module» (directionBody.drop 125) Q initial { params := params, locals := locals } env := by
  have fits : index + 1 < UInt64.size := by change index + 1 < 18446744073709551616; omega
  have guard : ¬index.toUInt64 + 1 < index.toUInt64 := CheckedNatAdd.guard_of_fits index 1 fits
  have increment : index.toUInt64 + 1 = (index + 1).toUInt64 := by
    exact (UInt64.ofNat_add index 1).symm
  simp only [directionBody, directionEligible, func30, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop]
  repeat' first
    | wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
        Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, ownerRead, pointerRead, flagRead, indexRead, stepRead,
        guard, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte]
    | (try simp only [wp_iff_control_types]
       refine wp_iff_cons rfl ?_
       simp only [ne_eq, not_true_eq_false, reduceIte])
  simpa only [directionAdvanceLocals, increment, List.append_nil] using next

theorem directionAdvance_state {locals : List Value} {matrix sro srp sco scp : UInt64}
    {basis : Basis} {ro rp co cp original current : UInt64} {free index : Nat}
    (state : DirectionLoopLocals locals matrix sro srp sco scp basis ro rp co cp original current free index) (root : UInt64) :
    DirectionLoopLocals (directionAdvanceLocals locals root index)
      matrix sro srp sco scp basis ro rp co cp original root free (index + 1) := by
  have update : WordUpdate locals (directionAdvanceLocals locals root index) 54 41 := by
    unfold directionAdvanceLocals
    exact ((((((WordUpdate.refl state.words 54 41).set 54 root (by omega) (by omega)).set 55 root (by omega) (by omega)).set
      92 index.toUInt64 (by omega) (by omega)).set 93 1 (by omega) (by omega)).set
      94 (index + 1).toUInt64 (by omega) (by omega)).set 89 (index + 1).toUInt64 (by omega) (by omega)
  refine ⟨state.toDirectionSearchLocals.updated update (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [directionAdvanceLocals, List.length_set, List.getElem?_set, state.size,
    Nat.reduceLT, Nat.reduceEqDiff, reduceIte, state.freeColumn, state.firstOwner, state.firstPointer,
    state.limit, state.step, state.originalOwner]

#print axioms directionAdvance_exact

end Project.Beck.Execution
