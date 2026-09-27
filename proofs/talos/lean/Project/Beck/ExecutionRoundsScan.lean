import Project.Beck.ExecutionRoundsState
import Project.Beck.ExecutionScan

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def roundsScanPrepared (locals : List Value) (point : Point) (root : UInt64) : List Value :=
  ((locals.set 6 (.i64 point.denominator)).set 7 (.i64 root)).set 8 (.i64 root)

def roundsScanLocals (locals : List Value) (point : Point) (root : UInt64) : List Value :=
  (roundsScanPrepared locals point root).set 9 (.i64 (boolWord (allFrozen point)))

set_option maxRecDepth 4096 in
theorem roundsScanPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (fuel : Nat) (input : Input) (point : Point) (inputRoot pointRoot : UInt64) (size : locals.length = 61)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := roundsParams fuel input point inputRoot pointRoot, locals := roundsScanPrepared locals point pointRoot, values := pointValues point pointRoot pointRoot })) :
    wp Project.Beck.«module» ((roundsBody.drop 7).take 9) Q initial
      { params := roundsParams fuel input point inputRoot pointRoot, locals := locals } env := by
  simp only [roundsBody, func34, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [roundsParams, matrixParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem roundsScanResult_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (found : Bool) (paramsSize : params.length = 10) (size : locals.length = 61) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := locals.set 9 (.i64 (boolWord found)), values := [.i32 (if found then 1 else 0)] })) :
    wp Project.Beck.«module» ((roundsBody.drop 17).take 8) Q initial
      { params := params, locals := locals, values := [.i64 (boolWord found)] } env := by
  cases found
  all_goals
    simp only [roundsBody, func34, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
    repeat' first
      | wp_run [paramsSize, size, boolWord, Bool.false_eq_true,
          List.length_set, List.getElem?_set, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff,
          show (1 : UInt64) ≠ 0 by decide, show (0 : UInt64) ≠ 1 by decide, show (1 : UInt32) ≠ 0 by decide,
          ne_eq, not_true_eq_false, not_false_eq_true, List.take, List.drop, List.append_nil, reduceIte]
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
    exact next

set_option maxRecDepth 4096 in
theorem rounds_scan_shape : (roundsBody.drop 7).take 18 =
    (roundsBody.drop 7).take 9 ++ (.call 13 :: (roundsBody.drop 17).take 8) := rfl

theorem roundsScan_state {locals : List Value} {stopped : Bool} {point : Point} {root internal : UInt64}
    (state : RoundsLocals locals stopped point root internal) :
    RoundsLocals (roundsScanLocals locals point root) stopped point root internal := by
  apply state.preserved
  · simp [roundsScanLocals, roundsScanPrepared]
  · intro k bound
    simp (discharger := omega) only [roundsScanLocals, roundsScanPrepared, List.getElem?_set_ne]

set_option maxRecDepth 4096 in
theorem roundsScan_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (fuel : Nat) (input : Input) (point : Point) (inputRoot pointRoot : UInt64) (size : locals.length = 61)
    (represented : UInt64Array.At initial pointRoot point.numerators) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := roundsParams fuel input point inputRoot pointRoot, locals := roundsScanLocals locals point pointRoot, values := [.i32 (if allFrozen point then 1 else 0)] })) :
    wp Project.Beck.«module» ((roundsBody.drop 7).take 18) Q initial
      { params := roundsParams fuel input point inputRoot pointRoot, locals := locals } env := by
  rw [rounds_scan_shape]
  refine Sequence.wp_append (P := fun store frame => store = initial ∧ frame =
    { params := roundsParams fuel input point inputRoot pointRoot, locals := roundsScanPrepared locals point pointRoot,
      values := pointValues point pointRoot pointRoot }) ?_ ?_
  · exact roundsScanPrepare_exact env initial locals fuel input point inputRoot pointRoot size _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  refine wp_call_tw (allFrozen_exact env initial point pointRoot pointRoot represented) ?_
  rintro final values ⟨same, rfl⟩
  subst final
  exact roundsScanResult_exact env initial _ _ (allFrozen point)
    (by simp [roundsParams, matrixParams, inputValues, pointValues])
    (by simp [roundsScanPrepared, size]) Q next

def roundsStoppedLocals (locals : List Value) (point : Point) (root : UInt64) : List Value :=
  (((locals.set 2 (.i64 point.denominator)).set 3 (.i64 root)).set 4 (.i64 root)).set 5 (.i64 1)

theorem roundsStopped_state {locals : List Value} {point : Point} {root internal : UInt64}
    (state : RoundsLocals locals false point root internal) :
    RoundsLocals (roundsStoppedLocals locals point root) true point root internal := by
  constructor
  · simp [roundsStoppedLocals, state.size]
  · simpa [roundsStoppedLocals] using state.owner
  · simpa [roundsStoppedLocals] using state.extra
  · simp [roundsStoppedLocals, state.size]
  · simp [roundsStoppedLocals, state.size]

set_option maxRecDepth 4096 in
theorem roundsStop_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (fuel : Nat) (input : Input) (point : Point) (inputRoot pointRoot : UInt64) (size : locals.length = 61)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := roundsParams fuel input point inputRoot pointRoot, locals := roundsStoppedLocals locals point pointRoot })) :
    wp Project.Beck.«module» [.localGet 7, .localSet 12, .localGet 8, .localSet 13,
      .localGet 9, .localSet 14, .constI64 1, .localSet 15] Q initial
      { params := roundsParams fuel input point inputRoot pointRoot, locals := locals } env := by
  wp_run [roundsParams, matrixParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  exact next

#print axioms roundsScan_exact
#print axioms roundsStop_exact

end Project.Beck.Execution
