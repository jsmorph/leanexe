import Project.Beck.ExecutionRoundAppend
import Project.Beck.ExecutionMatrixRelease
import Project.ProofKit.CheckedNatAddArithmetic

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def roundResultLocals (locals : List Value) (root : UInt64) : List Value :=
  let l := (((locals.set 43 (.i64 root)).set 44 (.i64 root)).set 45 (.i64 root)).set 46 (.i64 root)
  ((l.set 73 (.i64 root)).set 74 (.i64 root)).set 72 (.i64 0)

def roundAdvanceLocals (locals : List Value) (root : UInt64) (index : Nat) : List Value :=
  let l := (((locals.set 36 (.i64 root)).set 37 (.i64 root)).set 57 (.i64 index.toUInt64)).set 58 (.i64 1)
  (l.set 59 (.i64 (index + 1).toUInt64)).set 54 (.i64 (index + 1).toUInt64)

theorem roundResult_state {locals : List Value} {directionRoot distance speed denominator original current : UInt64}
    {index jobs : Nat} (state : RoundLoopLocals locals directionRoot distance speed denominator original current index jobs) (root : UInt64) :
    RoundLoopLocals (roundResultLocals locals root) directionRoot distance speed denominator original current index jobs := by
  apply state.preserved
  · simp [roundResultLocals]
  · unfold roundResultLocals
    repeat' apply WordLocals.set
    exact state.words
  · intro k bound
    simp (discharger := omega) only [roundResultLocals, List.getElem?_set_ne]

set_option maxRecDepth 4096 in
theorem roundResult_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (root : UInt64) (paramsSize : params.length = 9) (localsSize : locals.length = 77)
    (Q : Assertion Unit) (next : Q (.Fallthrough initial { params := params, locals := roundResultLocals locals root })) :
    wp Project.Beck.«module» ((roundBody.drop 105).take 13) Q initial
      { params := params, locals := locals, values := [.i64 root] } env := by
  simp only [roundBody, roundUpdating, roundUsable, func33, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem round_previous_release_shape : (roundBody.drop 118).take 12 = loopArrayCleanupProgram 45 84 82 := rfl

set_option maxRecDepth 4096 in
theorem roundAdvance_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (root : UInt64) (index : Nat) (indexBound : index < 6)
    (paramsSize : params.length = 9) (localsSize : locals.length = 77)
    (ownerRead : locals[73]? = some (.i64 root)) (pointerRead : locals[74]? = some (.i64 root))
    (flagRead : locals[72]? = some (.i64 0)) (indexRead : locals[54]? = some (.i64 index.toUInt64))
    (stepRead : locals[56]? = some (.i64 1)) (Q : Assertion Unit)
    (next : Q (.Break 0 initial { params := params, locals := roundAdvanceLocals locals root index })) :
    wp Project.Beck.«module» (roundBody.drop 130) Q initial { params := params, locals := locals } env := by
  have fits : index + 1 < UInt64.size := by change index + 1 < 18446744073709551616; omega
  have guard : ¬index.toUInt64 + 1 < index.toUInt64 := CheckedNatAdd.guard_of_fits index 1 fits
  have increment : index.toUInt64 + 1 = (index + 1).toUInt64 := (UInt64.ofNat_add _ _).symm
  simp only [roundBody, roundUpdating, roundUsable, func33, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop]
  repeat' first
    | wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
        Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, ownerRead, pointerRead, flagRead, indexRead, stepRead,
        guard, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte]
    | (try simp only [wp_iff_control_types]
       refine wp_iff_cons rfl ?_
       simp only [ne_eq, not_true_eq_false, reduceIte])
  simpa only [roundAdvanceLocals, increment, List.append_nil] using next

theorem roundAdvance_state {locals : List Value} {directionRoot distance speed denominator original current : UInt64}
    {index jobs : Nat} (state : RoundLoopLocals locals directionRoot distance speed denominator original current index jobs) (root : UInt64) :
    RoundLoopLocals (roundAdvanceLocals locals root index) directionRoot distance speed denominator original root (index + 1) jobs := by
  have update : WordUpdate locals (roundAdvanceLocals locals root index) 36 24 := by
    unfold roundAdvanceLocals
    exact ((((((WordUpdate.refl state.words 36 24).set 36 root (by omega) (by omega)).set 37 root (by omega) (by omega)).set
      57 index.toUInt64 (by omega) (by omega)).set 58 1 (by omega) (by omega)).set
      59 (index + 1).toUInt64 (by omega) (by omega)).set 54 (index + 1).toUInt64 (by omega) (by omega)
  refine ⟨state.toRoundBaseLocals.preserved update.size update.words (fun k bound => update.keeps k (Or.inl (by omega))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [roundAdvanceLocals, List.length_set, List.getElem?_set, state.size,
    Nat.reduceLT, Nat.reduceEqDiff, reduceIte, state.denominator, state.firstOwner, state.firstPointer,
    state.limit, state.step, state.originalOwner]

#print axioms roundAdvance_exact

end Project.Beck.Execution
