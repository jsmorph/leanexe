import Project.Beck.ExecutionRoundsCall

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def roundsContinuePrepared (locals : List Value) (input : Input) (point : Point) (inputRoot root : UInt64) : List Value :=
  let l := (((locals.set 26 (.i64 input.status)).set 27 (.i64 input.jobs.toUInt64)).set 28 (.i64 input.categories.toUInt64)).set 29 (.i64 input.overlap.toUInt64)
  let l := (((l.set 30 (.i64 inputRoot)).set 31 (.i64 inputRoot)).set 32 (.i64 point.denominator)).set 33 (.i64 root)
  l.set 34 (.i64 root)

def roundsContinuedLocals (locals : List Value) (input : Input) (point : Point) (inputRoot root : UInt64) : List Value :=
  let l := (((locals.set 35 (.i64 input.status)).set 36 (.i64 input.jobs.toUInt64)).set 37 (.i64 input.categories.toUInt64)).set 38 (.i64 input.overlap.toUInt64)
  let l := (((l.set 39 (.i64 inputRoot)).set 40 (.i64 inputRoot)).set 41 (.i64 point.denominator)).set 42 (.i64 root)
  let l := (((l.set 43 (.i64 root)).set 44 (.i64 root)).set 45 (.i64 0)).set 0 (.i64 root)
  l.set 1 (.i64 0)

set_option maxRecDepth 4096 in
theorem roundsContinuePrepare_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (fuel : Nat) (input : Input) (point nextPoint : Point) (inputRoot pointRoot nextRoot : UInt64)
    (size : locals.length = 61) (denRead : locals[22]? = some (.i64 nextPoint.denominator))
    (ownerRead : locals[23]? = some (.i64 nextRoot)) (pointerRead : locals[24]? = some (.i64 nextRoot))
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := roundsParams fuel input point inputRoot pointRoot
        locals := roundsContinuePrepared locals input nextPoint inputRoot nextRoot })) :
    wp Project.Beck.«module» (roundsContinue.take 18) Q initial
      { params := roundsParams fuel input point inputRoot pointRoot, locals := locals } env := by
  simp only [roundsContinue, roundsAdvancing, roundsBody, func34, List.getElem?_cons_zero, List.getElem?_cons_succ, List.take]
  wp_run [roundsParams, matrixParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, denRead, ownerRead, pointerRead]
  exact next

set_option maxRecDepth 4096 in
theorem rounds_continue_shape : roundsContinue = roundsContinue.take 18 ++
    (previousReleaseProgram 10 11 43 40 ++ roundsContinue.drop 33) := rfl

theorem roundsContinuePrepared_state {locals : List Value} {stopped : Bool} {point : Point} {root internal : UInt64}
    (state : RoundsLocals locals stopped point root internal) (input : Input) (nextPoint : Point) (inputRoot nextRoot : UInt64) :
    RoundsLocals (roundsContinuePrepared locals input nextPoint inputRoot nextRoot) stopped point root internal := by
  apply state.preserved
  · simp [roundsContinuePrepared]
  · intro k bound
    simp (discharger := omega) only [roundsContinuePrepared, List.getElem?_set_ne]

theorem roundsContinued_state {locals : List Value} {point : Point} {root internal : UInt64}
    (state : RoundsLocals locals false point root internal) (input : Input) (nextPoint : Point) (inputRoot nextRoot : UInt64) :
    RoundsLocals (roundsContinuedLocals locals input nextPoint inputRoot nextRoot) false nextPoint nextRoot nextRoot := by
  constructor
  · simp [roundsContinuedLocals, state.size]
  · simp [roundsContinuedLocals, state.size]
  · simp [roundsContinuedLocals, state.size]
  · simpa [roundsContinuedLocals] using state.flag
  · simp

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem roundsAdvance_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (fuel : Nat) (input : Input) (point nextPoint : Point) (inputRoot pointRoot nextRoot internal : UInt64)
    (size : locals.length = 61) (owner : locals[0]? = some (.i64 internal)) (extra : locals[1]? = some (.i64 0))
    (inputNonzero : inputRoot ≠ 0) (inputDifferent : inputRoot ≠ internal)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := roundsParams fuel input nextPoint inputRoot nextRoot
        locals := roundsContinuedLocals (roundsContinuePrepared locals input nextPoint inputRoot nextRoot) input nextPoint inputRoot nextRoot })) :
    wp Project.Beck.«module» (roundsContinue.drop 33) Q initial
      { params := roundsParams (fuel + 1) input point inputRoot pointRoot
        locals := roundsContinuePrepared locals input nextPoint inputRoot nextRoot } env := by
  have subtract : (fuel + 1).toUInt64 - 1 = fuel.toUInt64 := by
    change UInt64.ofNat (fuel + 1) - 1 = UInt64.ofNat fuel
    rw [UInt64.ofNat_add]
    exact UInt64.add_sub_cancel _ _
  simp only [roundsContinue, roundsAdvancing, roundsBody, func34, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop]
  repeat' first
    | wp_run [roundsParams, matrixParams, inputValues, pointValues, roundsContinuePrepared,
        List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append, size, List.length_set, List.getElem?_set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
        Nat.reduceEqDiff, List.append_nil, owner, extra, inputNonzero, inputDifferent,
        show (1 : UInt64) ≠ 0 by decide, show (1 : UInt32) ≠ 0 by decide,
        ne_eq, not_true_eq_false, not_false_eq_true, reduceIte, List.take, List.drop]
    | (try simp only [wp_iff_control_types]
       refine wp_iff_cons rfl ?_
       simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  simpa only [roundsContinuedLocals, roundsContinuePrepared, roundsParams, matrixParams, inputValues, pointValues,
    List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append, subtract] using next

#print axioms roundsAdvance_exact

end Project.Beck.Execution
