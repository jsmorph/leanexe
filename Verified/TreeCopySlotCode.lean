import Verified.TreeCopyAdvanceCode
import Verified.TreeCopyDescendCode
import Verified.TreeReadCode
import Verified.TreeTestCode

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_treeCopySlot {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {heap0 heap : Heap} {initial store : Store Unit} {shape : TreeShape}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit base : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {s0 s : Locals}
    {rest : Program} {Q : Assertion Unit}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat current.next)))
    (hBound : current.next < current.slots.length)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q)
    (hNext : ∀ heap' store' s' next parents',
      CopyInv shape heap0 initial root result limit heap' store' next parents' →
      CopyLocals base s0 result next.pointer s' →
      CopyWork.Step (current.work parents) (next.work parents') → wp m rest Q store' s' host) :
    wp m (treeCopySlot shape base ++ rest) Q store s host := by
  let copyWord := treeSlotAddress (base + 1) (base + 2) ++
    [.localGet (base + 4), .store64 0] ++ treeCopyAdvance (base + 1) (base + 2)
  let descend := treeCopyAllocate shape (base + 4) (base + 5) ++
    treeCopyBegin shape (base + 4) (base + 5) [.localGet (base + 4)] [.localGet (base + 1)] ++
    [.localGet (base + 5), .localSet (base + 1)]
  change wp m (treeCopyRead base ++ treeCopyTest shape base ++
    [.iff 0 0 descend copyWord] ++ rest) Q store s host
  rw [List.append_assoc, List.append_assoc]
  refine wp_treeCopyRead h.frames.current h.step.at_ hBound hLow hHigh hLocals.current hIndex ?_
  intro sRead hFrame hResult hCurrent hIndex' hSource hWord hValues
  have hReadLocals := hLocals.ofRead hFrame hResult hCurrent hValues
  have hLowRead : sRead.params.length ≤ base := by rw [hFrame.params]; exact hLow
  have hHighRead : base + 6 ≤ sRead.positions := by rw [hFrame.positions]; exact hHigh
  refine wp_treeCopyTest (h.frames.current.maskPushes h.step.at_ hSource) hIndex' hWord ?_
  rw [treeCopyCondition_spec h.frames.current hBound]
  let post : Assertion Unit := fun cont => match cont with
    | .Fallthrough store' s' => wp m rest Q store' { s' with values := sRead.values } host
    | .Break 0 store' s' => wp m rest Q store' { s' with values := sRead.values } host
    | .Break (k + 1) store' s' => Q (.Break k store' s')
    | other => Q other
  have hAfter (heap' : Heap) (store' : Store Unit) (s' : Locals) (next : CopyRecord)
      (parents' : List CopyRecord)
      (hInv : CopyInv shape heap0 initial root result limit heap' store' next parents')
      (hVars : CopyLocals base s0 result next.pointer s')
      (hWork : CopyWork.Step (current.work parents) (next.work parents')) :
      wp m [] post store' s' host := by
    rw [wp_nil]
    change wp m rest Q store' { s' with values := sRead.values } host
    have hStack : sRead.values = s'.values := hReadLocals.values.trans hVars.values.symm
    rw [hStack]
    exact hNext heap' store' s' next parents' hInv hVars hWork
  have hBorrow := SlotsBorrowed.get current.slots 0 h.frames.current.borrowed.2 current.next hBound
  simp only [Nat.zero_add] at hBorrow
  cases hSlot : current.slots[current.next] with
  | word word =>
    refine wp_iff_cons rfl ?_
    simp (config := { decide := true }) only [copyBranch,
      ite_false, List.take_zero, List.drop_zero, List.append_eq, List.nil_append]
    refine wp.conseq (Q := post) ?_ ?_
    · intro c hc
      cases c with
      | Break k _ _ => cases k <;> exact hc
      | _ => exact hc
    change wp m copyWord post store sRead host
    have hValue : (current.slots[current.next]).ValueOwned heap store
        (store.mem.read64 (slotAddress current.source current.next)) := by
      rw [hSlot] at hBorrow ⊢
      exact hBorrow.1
    have hWork := CopyRecord.work_advance (parents := parents) hBound hSlot
    have hCharge : (current.work parents).charge = 0 := by
      unfold CopyRecord.work
      rw [List.drop_eq_getElem_cons hBound, hSlot]
      rfl
    apply wp_treeCopyAdvanceInv (rest := []) h hReadLocals hIndex' hWord hBound hValue
      (by rw [hSlot]; rfl) hWork hCharge
    intro store' hInv
    exact hAfter heap store' sRead _ parents hInv hReadLocals hWork
  | child value =>
    cases value with
    | null =>
      refine wp_iff_cons rfl ?_
      simp (config := { decide := true }) only [
        ite_false, List.take_zero, List.drop_zero, List.append_eq, List.nil_append]
      refine wp.conseq (Q := post) ?_ ?_
      · intro c hc
        cases c with
        | Break k _ _ => cases k <;> exact hc
        | _ => exact hc
      change wp m copyWord post store sRead host
      have hValue : (current.slots[current.next]).ValueOwned heap store
          (store.mem.read64 (slotAddress current.source current.next)) := by
        rw [hSlot] at hBorrow ⊢
        exact hBorrow.1
      have hWork := CopyRecord.work_null (parents := parents) hBound hSlot
      have hCharge : (current.work parents).charge = 0 := by
        unfold CopyRecord.work
        rw [List.drop_eq_getElem_cons hBound, hSlot]
        rfl
      apply wp_treeCopyAdvanceInv (rest := []) h hReadLocals hIndex' hWord hBound hValue
        (by rw [hSlot]; rfl) hWork hCharge
      intro store' hInv
      exact hAfter heap store' sRead _ parents hInv hReadLocals hWork
    | record children =>
      refine wp_iff_cons rfl ?_
      simp (config := { decide := true }) only [copyBranch,
        ite_true, List.take_zero, List.drop_zero, List.append_eq, List.nil_append]
      refine wp.conseq (Q := post) ?_ ?_
      · intro c hc
        cases c with
        | Break k _ _ => cases k <;> exact hc
        | _ => exact hc
      change wp m descend post store sRead host
      rw [← List.append_nil descend]
      apply wp_treeCopyDescendInv hm (rest := []) (Q := post) h hReadLocals hWord hBound hSlot
        hLowRead hHighRead hCap (hTrap.imp (Q' := post) (fun _ h => h))
      intro heap' store' ptr s' hInv hVars
      exact hAfter heap' store' s' _ (current :: parents) hInv hVars
        (CopyRecord.work_descend (parents := parents) hBound hSlot rfl)

#print axioms wp_treeCopySlot

end Verified
