import Project.Beck.ExecutionRoundsState
import Project.Beck.ExecutionScan

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def roundsFinishScanPrepared (locals : List Value) (point : Point) (pointOwner root : UInt64) : List Value :=
  ((locals.set 46 (.i64 point.denominator)).set 47 (.i64 pointOwner)).set 48 (.i64 root)

def roundsFinishScanLocals (locals : List Value) (point : Point) (pointOwner root : UInt64) : List Value :=
  (roundsFinishScanPrepared locals point pointOwner root).set 49 (.i64 (boolWord (allFrozen point)))

set_option maxRecDepth 4096 in
theorem roundsFinishScanPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (fuel : Nat) (input : Input) (point : Point) (inputRoot pointOwner pointRoot : UInt64) (size : locals.length = 61)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := roundsParams fuel input point inputRoot pointOwner pointRoot, locals := roundsFinishScanPrepared locals point pointOwner pointRoot, values := pointValues point pointOwner pointRoot })) :
    wp Project.Beck.«module» (roundsFinish.take 9) Q initial
      { params := roundsParams fuel input point inputRoot pointOwner pointRoot, locals := locals } env := by
  simp only [roundsFinish, func34, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [roundsParams, matrixParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem roundsFinishScanResult_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (found : Bool) (paramsSize : params.length = 10) (size : locals.length = 61) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := locals.set 49 (.i64 (boolWord found)), values := [.i32 (if found then 1 else 0)] })) :
    wp Project.Beck.«module» ((roundsFinish.drop 10).take 8) Q initial
      { params := params, locals := locals, values := [.i64 (boolWord found)] } env := by
  cases found
  all_goals
    simp only [roundsFinish, func34, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
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
theorem rounds_finish_scan_shape : roundsFinish.take 18 =
    roundsFinish.take 9 ++ (.call 13 :: (roundsFinish.drop 10).take 8) := rfl

set_option maxRecDepth 4096 in
theorem roundsFinishScan_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (fuel : Nat) (input : Input) (point : Point) (inputRoot pointOwner pointRoot : UInt64) (size : locals.length = 61)
    (represented : UInt64Array.At initial pointRoot point.numerators) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := roundsParams fuel input point inputRoot pointOwner pointRoot, locals := roundsFinishScanLocals locals point pointOwner pointRoot, values := [.i32 (if allFrozen point then 1 else 0)] })) :
    wp Project.Beck.«module» (roundsFinish.take 18) Q initial
      { params := roundsParams fuel input point inputRoot pointOwner pointRoot, locals := locals } env := by
  rw [rounds_finish_scan_shape]
  refine Sequence.wp_append (P := fun store frame => store = initial ∧ frame =
    { params := roundsParams fuel input point inputRoot pointOwner pointRoot, locals := roundsFinishScanPrepared locals point pointOwner pointRoot,
      values := pointValues point pointOwner pointRoot }) ?_ ?_
  · exact roundsFinishScanPrepare_exact env initial locals fuel input point inputRoot pointOwner pointRoot size _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  refine wp_call_tw (allFrozen_exact env initial point pointOwner pointRoot represented) ?_
  rintro final values ⟨same, rfl⟩
  subst final
  exact roundsFinishScanResult_exact env initial _ _ (allFrozen point)
    (by simp [roundsParams, matrixParams, inputValues, pointValues])
    (by simp [roundsFinishScanPrepared, size]) Q next

#print axioms roundsFinishScan_exact

end Project.Beck.Execution
