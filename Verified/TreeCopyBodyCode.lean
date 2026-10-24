import Verified.TreeCopySlotCode
import Verified.TreeCopyFinishCode

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

/-- The loop bound pushes the width of the record being copied. -/
theorem CopyRecord.Holds.widthPushes {m : Module} {host : HostEnv Unit} {shape : TreeShape}
    {heap : Heap} {store : Store Unit} {parent : UInt64} {record : CopyRecord} {s : Locals}
    {base : Nat} (h : record.Holds shape heap store parent) (hHeap : heap.At store)
    (hPtr : s.get (base + 1) = some (.i64 record.pointer)) :
    PushesWord m host (treeCopyWidth shape base) store s
      (UInt64.ofNat record.slots.length) := by
  obtain ⟨r, hLength, -, -, -⟩ := id h.layout
  unfold treeCopyWidth
  cases hT : shape.tagged with
  | true =>
    have hBase := h.storage.base
    have hAddress := h.storage.address
    have hBelow := h.storage.below
    have hTop := hHeap.top
    intro vs rest Q hNext
    simp only [ite_true]
    refine wp_headerLoad hPtr ?_ ?_
    · rw [headerAddress_toNat (by change 16 ≤ record.pointer.toNat; omega) (by omega)]
      change record.pointer.toNat - 16 + 8 ≤ store.mem.pages * 65536
      omega
    · rw [h.width hT]
      exact hNext
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [shape.selectCode_untagged hT r, ← hLength]
    exact PushesWord.const

theorem wp_treeCopyBody {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {heap0 heap : Heap} {initial store : Store Unit} {shape : TreeShape}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit base : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {s0 s : Locals} {Q : Assertion Unit}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q)
    (hNext : ∀ heap' store' s' next parents',
      CopyInv shape heap0 initial root result limit heap' store' next parents' →
      CopyLocals base s0 result next.pointer s' →
      CopyWork.Step (current.work parents) (next.work parents') → Q (.Break 0 store' s'))
    (hRoot : ∀ store' s', NodeOwned heap store' result (.record root) →
      (Node.blocks store' result (.record root)).Pairwise regionsDisjoint →
      Step heap0 initial (fun _ => True) heap store' (Node.blocks store' result (.record root)) →
      heap.top.toNat ≤ limit → CopyLocals base s0 result current.pointer s' → Q (.Break 1 store' s')) :
    wp m (treeCopyBody shape base) Q store s host := by
  have hCurrent := h.frames.current
  have hBase := hCurrent.storage.base
  have hAddress := hCurrent.storage.address
  have hBelow := hCurrent.storage.below
  have hTop := h.step.at_.top
  have hShort : current.slots.length ≤ 64 := by
    obtain ⟨r, hLength, -, -, -⟩ := id hCurrent.layout
    rw [hLength]
    exact shape.width_le r
  have hBound := hCurrent.bound
  have hIndexNat : (UInt64.ofNat current.next).toNat = current.next :=
    UInt64.toNat_ofNat_of_lt' (by change current.next < 18446744073709551616; omega)
  have hCountNat : (UInt64.ofNat current.slots.length).toNat = current.slots.length :=
    UInt64.toNat_ofNat_of_lt' (by change current.slots.length < 18446744073709551616; omega)
  have hCompare : (UInt64.ofNat current.next < UInt64.ofNat current.slots.length) ↔
      current.next < current.slots.length := by
    rw [UInt64.lt_iff_toNat_lt, hIndexNat, hCountNat]
  have hLow2 : s.params.length ≤ base + 2 := by omega
  have hHigh2 : base + 2 < s.params.length + s.locals.length := Locals.lt_total (by omega)
  simp only [treeCopyBody, List.cons_append, List.nil_append]
  refine wp_headerLoad hLocals.current ?_ ?_
  · rw [headerAddress_toNat (by change 8 ≤ current.pointer.toNat; omega) (by omega)]
    change current.pointer.toNat - 8 + 8 ≤ store.mem.pages * 65536
    omega
  rw [hCurrent.index]
  refine wp_localSet_local hLow2 hHigh2 ?_
  let sIndex := setLocal s (base + 2) (.i64 (UInt64.ofNat current.next))
  have hIndexLocals : CopyLocals base s0 result current.pointer sIndex :=
    hLocals.scratch hLow2 (by omega) (by omega)
  have hIndex : sIndex.get (base + 2) = some (.i64 (UInt64.ofNat current.next)) :=
    Locals.get_setLocal_same hLow2 hHigh2
  have hLowIndex : sIndex.params.length ≤ base := hLow
  have hHighIndex : base + 6 ≤ sIndex.positions := by
    simpa only [sIndex, Locals.positions_setLocal] using hHigh
  change wp m (.localGet (base + 2) :: (treeCopyWidth shape base ++ [.ltUI64,
    .iff 0 0 (treeCopySlot shape base) (treeCopyFinish shape base), .br 0])) Q store sIndex host
  simp only [wp_localGet_cons, hIndex]
  apply hCurrent.widthPushes h.step.at_ hIndexLocals.current
  simp only [wp_ltUI64_cons]
  let post : Assertion Unit := fun cont => match cont with
    | .Fallthrough store' s' => wp m [.br 0] Q store' { s' with values := sIndex.values } host
    | .Break 0 store' s' => wp m [.br 0] Q store' { s' with values := sIndex.values } host
    | .Break (k + 1) store' s' => Q (.Break k store' s')
    | other => Q other
  have hAfter (heap' : Heap) (store' : Store Unit) (s' : Locals) (next : CopyRecord)
      (parents' : List CopyRecord)
      (hInv : CopyInv shape heap0 initial root result limit heap' store' next parents')
      (hVars : CopyLocals base s0 result next.pointer s')
      (hWork : CopyWork.Step (current.work parents) (next.work parents')) :
      wp m [] post store' s' host := by
    rw [wp_nil]
    change wp m [.br 0] Q store' { s' with values := sIndex.values } host
    have hStack : sIndex.values = s'.values := hIndexLocals.values.trans hVars.values.symm
    rw [hStack]
    simpa only [wp_br_cons] using hNext heap' store' s' next parents' hInv hVars hWork
  by_cases hMore : current.next < current.slots.length
  · rw [ite_eq_left (hCompare.mpr hMore)]
    refine wp_iff_cons rfl ?_
    simp (config := { decide := true }) only [ite_true, List.take_zero, List.drop_zero, List.nil_append]
    refine wp.conseq (Q := post) ?_ ?_
    · intro c hc
      cases c with
      | Break k _ _ => cases k <;> exact hc
      | _ => exact hc
    change wp m (treeCopySlot shape base) post store sIndex host
    simpa only [List.append_nil] using wp_treeCopySlot hm (rest := []) h hIndexLocals hIndex hMore
      hLowIndex hHighIndex hCap (hTrap.imp (Q' := post) (fun _ h => h)) hAfter
  · have hDone : current.next = current.slots.length := by omega
    rw [ite_eq_right (fun hLess => hMore (hCompare.mp hLess))]
    refine wp_iff_cons rfl ?_
    simp (config := { decide := true }) only [ite_false, List.take_zero, List.drop_zero, List.nil_append]
    refine wp.conseq (Q := post) ?_ ?_
    · intro c hc
      cases c with
      | Break k _ _ => cases k <;> exact hc
      | _ => exact hc
    change wp m (treeCopyFinish shape base) post store sIndex host
    simpa only [List.append_nil] using wp_treeCopyFinish (rest := []) h hIndexLocals hDone
      hLowIndex hHighIndex (fun store' s' next parents' hInv hVars hWork =>
        hAfter heap store' s' next parents' hInv hVars hWork)
      (fun store' s' hOwned hApart hStep hBudget hVars =>
        hRoot store' s' hOwned hApart hStep hBudget hVars)

#print axioms wp_treeCopyBody

end Verified
