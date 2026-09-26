import Project.Drone.ExecutionUnwindReversePrepare
import Project.Drone.ExecutionUnwindReverseFinish
import Project.Drone.ExecutionReverseBudget
import Project.Drone.ExecutionArrayResult

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

set_option maxRecDepth 32768 in
set_option maxHeartbeats 350000 in
theorem unwind_reverse_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (index state remaining pageLimit : Nat) (terrain history : UInt64) (node : FreeNode)
    (tracked : Bool) (out0 out1 : UInt64) (aux : List Value) (s : Scratch) (input : Array UInt64)
    (hAux : aux.length = 36) (h33 : aux[33]? = some (.i64 0)) (h35 : aux[35]? = some (.i64 0))
    (hInput : heap.OwnsWords store node input) (hHeap : heap.At store)
    (hBudget : Budget store heap (reverseCost input.size + remaining) pageLimit) (hSize : 1 < input.size)
    (P : Store Unit → List Value → Prop)
    (hNext : ∀ final values, FreshArrayResult heap store input.reverse remaining pageLimit final values → P final values) :
    wp Project.Drone.«module» (func24.drop 9)
      (fun c => match c with
        | .Fallthrough final frame => P final (frame.values.take 2)
        | .Return final values => P final (values.take 2)
        | _ => False)
      store (unwindFrame 0 index state terrain history node.root tracked out0 out1 aux s) env := by
  have hCode : func24.drop 9 = [.localGet 14, .constI64 0, .eqI64,
      .iff 0 0 unwindReverseBody []] ++ func24.drop 13 := rfl
  rw [hCode]
  wp_unwind_frame [hAux]
  refine wp_iff_cons rfl ?_
  simp only [ne_eq, eq_self_iff_true, show (1 : UInt32) ≠ 0 by decide, ↓reduceIte]
  rw [unwind_reverse_shape]
  have hPrepare : unwindReverseBody.take 11 = unwindReverseBody.take 8 ++
      [.localGet 52, .constI64 1, .leUI64] := rfl
  rw [hPrepare]
  simp only [List.append_assoc]
  apply unwind_reverse_prepare_spec env store index state terrain history node.root tracked out0 out1 aux s input
    hAux h33 h35 (borrow_owned hInput).values
  have hPrefix : (aux.take 33).length = 33 := by simp [hAux]
  have hLarge : ¬ UInt64.ofNat input.size ≤ 1 := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' (borrow_owned hInput).values.size_lt]
    exact Nat.not_le.mpr hSize
  wp_unwind_frame [frame, unwindReverseSaved, unwindReverseTail, unwindReverseScratch, hPrefix]
  refine wp_iff_cons rfl ?_
  simp only [hLarge, ↓reduceIte, eq_self_iff_true, not_true_eq_false]
  have hBase : (unwindParams 0 index state terrain history node.root).length +
      (unwindReverseSaved node.root tracked out0 out1 aux).length = 48 := by
    simp [unwindParams, unwindReverseSaved, hPrefix]
  rw [← hBase]
  apply word_reverse_budget_spec env store heap (unwindParams 0 index state terrain history node.root)
    (unwindReverseSaved node.root tracked out0 out1 aux) (unwindReverseTail s)
    (unwindReverseScratch s node.root input.size) node input remaining pageLimit rfl rfl
    (borrow_owned hInput) hHeap hBudget
  intro final previous current capacity next hFinalHeap hFinalBudget hOutput hPreserve hFresh
  simp only [wp_nil, List.take, List.drop_zero, List.append_nil]
  have hResult := hNext final _ ⟨_, _, hFinalHeap, hFinalBudget, hOutput, hPreserve, hFresh, rfl⟩
  convert unwind_reverse_finish_spec env final index state terrain history node.root
    (allocatedRoot heap.top (reverseNeed input.size) heap.nodes) tracked out0 out1 aux (unwindReverseTail s)
    (reversedScratch (unwindReverseScratch s node.root input.size) input.size
      (allocatedRoot heap.top (reverseNeed input.size) heap.nodes) previous current capacity next)
    input hAux rfl rfl (hPreserve.owned _ _ hInput |> borrow_owned).values hSize P hResult using 1
  funext c
  cases c with
  | Break k store frame => cases k <;> rfl
  | _ => rfl

#print axioms unwind_reverse_spec
end Project.Drone.Execution
