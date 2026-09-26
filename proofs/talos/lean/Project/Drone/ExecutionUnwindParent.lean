import Project.Drone.ExecutionUnwindFrame
import Project.ProofKit.NatSub
import Project.ProofKit.CheckedNatAdd
import Project.ProofKit.CheckedNatMul
import Project.ProofKit.CheckedArrayGet

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

def unwindParent (index state : Nat) (parents : Array UInt64) : Nat :=
  if 0 < index then parents[(index - 1) * 45 + state]!.toNat else state

set_option maxRecDepth 32768 in
set_option maxHeartbeats 300000 in
theorem unwind_parent_spec (env : HostEnv Unit) (store : Store Unit)
    (fuel index state : Nat) (terrain history row root : UInt64) (tracked : Bool)
    (out0 out1 : UInt64) (aux : List Value) (s : Scratch) (parents : Array UInt64)
    (hAux : aux.length = 36) (hIndex : index < UInt64.size) (hState : state < UInt64.size)
    (hParents : UInt64Array.At store history parents)
    (hRead : 0 < index → (index - 1) * 45 + state < parents.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (nextAux : List Value) (nextScratch : Scratch), nextAux.length = 36 →
      nextAux[12]? = some (.i64 root) → nextAux[13]? = some (.i64 root) →
      nextAux[14]? = some (.i64 (UInt64.ofNat (unwindParent index state parents))) →
      wp Project.Drone.«module» rest Q store
        (unwindFrame fuel index state terrain history row tracked out0 out1 nextAux nextScratch) env) :
    wp Project.Drone.«module» ((unwindLoopBody.drop 176).take 8 ++ rest) Q store
      { unwindFrame fuel index state terrain history row tracked out0 out1 aux s with values := [.i64 root] } env := by
  simp only [unwindLoopBody, func24, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.take, List.cons_append, List.nil_append]
  wp_unwind_frame [hAux]
  refine wp_iff_cons rfl ?_
  by_cases hPositive : 0 < index
  · have hWord : (0 : UInt64) < UInt64.ofNat index := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hIndex]
      exact hPositive
    simp [hWord]
    wp_unwind_frame [hAux]
    refine NatSub.guard_spec 58 59 _ _ _ _ index 1 [] rfl ?_ ?_ hIndex (by decide) _ _ ?_
    · simp [Locals.get, hAux]
    · simp [Locals.get, hAux]
    wp_unwind_frame [hAux]
    change wp _ (CheckedNatMul.guardProgram 56 57 ++ _) _ _ _ _
    refine CheckedNatMul.guard_spec 56 57 _ _ _ _ (UInt64.ofNat (index - 1)) 45 [] rfl ?_ ?_ ?_ _ _ ?_
    · simp [Locals.get, hAux]
    · simp [Locals.get, hAux]
    · rw [UInt64.toNat_ofNat_of_lt' (show index - 1 < UInt64.size by omega)]
      have := hParents.size_lt
      have := hRead hPositive
      change (index - 1) * 45 < UInt64.size
      omega
    wp_unwind_frame [hAux]
    have hFit : (index - 1) * 45 + state < UInt64.size := lt_trans (hRead hPositive) hParents.size_lt
    refine CheckedNatAdd.guard_spec 55 _ _ _ _ ((index - 1) * 45) state [] ?_ ?_ hFit _ _ ?_
    · simp only [UInt64.ofNat_mul, show UInt64.ofNat 45 = 45 from rfl]
    · simp [Locals.get, hAux, UInt64.ofNat_add, UInt64.ofNat_mul]
    wp_fixed_frame_step
    simp only [List.length_append, List.length_set, List.length_cons, List.length_nil,
      hAux, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte, List.set_append, Nat.reduceSub, List.set]
    change wp _ (CheckedArrayGet.checkedGetCore 51 52 ++ _) _ _ _ _
    refine CheckedArrayGet.checkedGetCore_spec 51 52 _ _ _ _ history parents ((index - 1) * 45 + state) []
      ?_ ?_ rfl hParents (hRead hPositive) _ _ ?_
    · simp [Locals.get, hAux]
    · simp [Locals.get, hAux, UInt64.ofNat_add, UInt64.ofNat_mul]
    wp_unwind_frame [hAux]
    refine hNext _ { s with
        source := history
        length := UInt64.ofNat ((index - 1) * 45 + state)
        count := UInt64.ofNat (index - 1) * 45
        nextLength := UInt64.ofNat state
        target := UInt64.ofNat (index - 1) * 45 + UInt64.ofNat state
        counter := UInt64.ofNat (index - 1)
        value := 45
        spare0 := UInt64.ofNat index
        spare1 := 1 }
      ?_ ?_ ?_ ?_ <;> simp [hAux, unwindParent, hPositive,
        getElem!_pos parents ((index - 1) * 45 + state) (hRead hPositive)]
  · have hZero : index = 0 := by omega
    subst index
    simp
    wp_unwind_frame [hAux]
    refine hNext _ s ?_ ?_ ?_ ?_ <;> simp [hAux, unwindParent]

#print axioms unwind_parent_spec
end Project.Drone.Execution
