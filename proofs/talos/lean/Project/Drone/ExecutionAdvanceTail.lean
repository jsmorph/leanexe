import Project.Drone.ExecutionAdvanceFrame

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

macro "advance_controls" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (repeat' ((try wp_advance_frame [$ts,*]) <;> (advance_wp_goal; first
    | (refine wp_constIf rfl ?_)
    | (refine wp_iff_cons rfl ?_;
       simp only [$ts,*, ne_eq, eq_self_iff_true,
         show (1 : UInt32) ≠ 0 by decide,
         show (1 : UInt64) ≠ 0 by decide,
         Bool.false_eq_true, Bool.true_eq_false,
         not_false_eq_true, not_true_eq_false, UInt64.lt_irrefl, ↓reduceIte])))
   try wp_advance_frame [$ts,*]))

set_option maxHeartbeats 300000 in
set_option maxRecDepth 32768 in
theorem advance_tail_zero_spec (env : HostEnv Unit) (store : Store Unit)
    (fuel target : Nat) (r0 r1 : UInt64) (last : Bool)
    (previousOwner previousPointer rowOwner rowPointer resultOwner resultPointer root : UInt64)
    (aux : List Value) (s : Scratch) (hAux : aux.length = 38) (hPrevious : previousOwner ≠ 0)
    (hTarget : aux[16]? = some (.i64 (UInt64.ofNat (target + 1))))
    (hR0 : aux[17]? = some (.i64 r0)) (hR1 : aux[18]? = some (.i64 r1))
    (hLast : aux[19]? = some (.i64 (if last then 1 else 0)))
    (hOwner : aux[20]? = some (.i64 previousOwner)) (hPointer : aux[21]? = some (.i64 previousPointer))
    (Q : Assertion Unit)
    (hNext : ∀ nextAux : List Value, nextAux.length = 38 →
      Q (.Break 0 store (advanceFrame fuel (target + 1) r0 r1 last previousOwner previousPointer
        root root root resultOwner resultPointer nextAux s))) :
    wp Project.Drone.«module» (advanceLoopBody.drop 260) Q store
      { advanceFrame (fuel + 1) target r0 r1 last previousOwner previousPointer rowOwner rowPointer
          0 resultOwner resultPointer aux s with values := [.i64 root] } env := by
  have hSub : UInt64.ofNat (fuel + 1) - 1 = UInt64.ofNat fuel := by
    rw [UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl, UInt64.add_sub_cancel]
  simp only [advanceLoopBody, func18, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop]
  advance_controls [hAux, hTarget, hR0, hR1, hLast, hOwner, hPointer, hPrevious, hSub]
  apply hNext
  simp [hAux]

#print axioms advance_tail_zero_spec
end Project.Drone.Execution
