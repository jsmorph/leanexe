import Project.Drone.ExecutionAppendFrame
import Project.ProofKit.ConstIf

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

elab "append_wp_goal" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainTarget
  unless goal.isAppOf ``Wasm.wp do
    throwError "append instruction execution reached its postcondition"

macro "append_controls" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (repeat' ((try wp_append_frame [$ts,*]) <;> (append_wp_goal; first
    | (refine wp_constIf rfl ?_)
    | (refine wp_iff_cons rfl ?_;
       simp only [$ts,*, ne_eq, eq_self_iff_true,
         show (1 : UInt32) ≠ 0 by decide,
         show (1 : UInt64) ≠ 0 by decide,
         not_false_eq_true, not_true_eq_false, UInt64.lt_irrefl, ↓reduceIte])))
   try wp_append_frame [$ts,*]))

set_option maxHeartbeats 300000 in
set_option maxRecDepth 32768 in
theorem append_tail_zero_spec (env : HostEnv Unit) (store : Store Unit)
    (fuel state : Nat) (layerOwner layerPointer historyOwner historyPointer
      resultOwner resultPointer root : UInt64) (aux : List Value) (s : Scratch) (extra : UInt64)
    (hAux : aux.length = 14) (hFuel : fuel + 1 < UInt64.size) (hLayer : layerOwner ≠ 0)
    (hState : aux[0]? = some (.i64 (UInt64.ofNat (state + 1))))
    (hOwner : aux[1]? = some (.i64 layerOwner)) (hPointer : aux[2]? = some (.i64 layerPointer))
    (Q : Assertion Unit)
    (hNext : ∀ nextAux : List Value, nextAux.length = 14 →
      Q (.Break 0 store (appendFrame fuel (state + 1) layerOwner layerPointer root root root
        resultOwner resultPointer nextAux s extra))) :
    wp Project.Drone.«module» (appendBody.drop 122) Q store
      { appendFrame (fuel + 1) state layerOwner layerPointer historyOwner historyPointer 0
          resultOwner resultPointer aux s extra with values := [.i64 root] } env := by
  have hSub : UInt64.ofNat (fuel + 1) - 1 = UInt64.ofNat fuel := by
    rw [UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl, UInt64.add_sub_cancel]
  simp only [appendBody, func21, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop]
  append_controls [hAux, hState, hOwner, hPointer, hLayer, hSub]
  apply hNext
  simp [hAux]

#print axioms append_tail_zero_spec
end Project.Drone.Execution
