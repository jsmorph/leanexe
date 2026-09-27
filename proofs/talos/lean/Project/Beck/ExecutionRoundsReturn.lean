import Project.Beck.ExecutionRoundsLoop
import Project.Beck.ExecutionRoundsFinishScan

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def roundsUnfinished : Wasm.Program := match (roundsFinish[18]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

set_option maxRecDepth 4096 in
theorem rounds_return_shape : func34.drop 7 =
    [.localGet 15, .constI64 0, .eqI64, .iff 0 0 roundsFinish [], .localGet 12, .localGet 13, .localGet 14] := rfl

set_option maxRecDepth 4096 in
theorem rounds_finish_shape : roundsFinish = roundsFinish.take 18 ++
    [.iff 0 0 [.localGet 7, .localSet 12, .localGet 8, .localSet 13, .localGet 9, .localSet 14] roundsUnfinished] := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem roundsReturn_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (fuel : Nat) (input : Input) (point : Point) (inputRoot pointOwner pointRoot internal : UInt64) (stopped : Bool)
    (state : RoundsLocals locals stopped point pointOwner pointRoot internal)
    (represented : UInt64Array.At initial pointRoot point.numerators) (frozen : allFrozen point = true)
    (Q : Assertion Unit)
    (next : ∀ finalFrame, finalFrame.values = pointValues point pointOwner pointRoot → Q (.Fallthrough initial finalFrame)) :
    wp Project.Beck.«module» (func34.drop 7) Q initial
      { params := roundsParams fuel input point inputRoot pointOwner pointRoot, locals := locals } env := by
  have paramsSize : (roundsParams fuel input point inputRoot pointOwner pointRoot).length = 10 := by
    simp [roundsParams, matrixParams, inputValues, pointValues]
  rw [rounds_return_shape]
  cases stopped
  · wp_run [paramsSize, state.size, state.flag, Bool.false_eq_true, reduceIte]
    refine wp_iff_cons rfl ?_
    simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_false_eq_true, reduceIte]
    rw [rounds_finish_shape]
    refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
      [.iff 0 0 [.localGet 7, .localSet 12, .localGet 8, .localSet 13, .localGet 9, .localSet 14] roundsUnfinished]
      _ store frame env) ?_ (fun _ _ h => h)
    apply roundsFinishScan_exact env initial locals fuel input point inputRoot pointOwner pointRoot state.size represented
    dsimp only [Sequence.Fallthrough]
    simp only [frozen, reduceIte]
    refine wp_iff_cons rfl ?_
    simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_false_eq_true, reduceIte]
    wp_run [roundsParams, matrixParams, inputValues, pointValues, roundsFinishScanLocals, roundsFinishScanPrepared,
      List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append, state.size, List.length_set, List.getElem?_set,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff,
      List.take, List.drop, List.append_nil, reduceIte]
    exact next _ rfl
  · obtain ⟨denRead, ownerRead, pointerRead⟩ := state.result rfl
    wp_run [paramsSize, state.size, state.flag, reduceIte, show (1 : UInt64) ≠ 0 by decide]
    refine wp_iff_cons rfl ?_
    simp only [show (1 : UInt64) ≠ 0 by decide, show (1 : UInt32) ≠ 0 by decide,
      ne_eq, not_true_eq_false, reduceIte]
    wp_run [paramsSize, state.size, denRead, ownerRead, pointerRead, List.take, List.drop, List.append_nil,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
    exact next _ rfl

#print axioms roundsReturn_exact

end Project.Beck.Execution
