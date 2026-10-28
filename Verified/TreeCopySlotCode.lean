import Verified.TreeCopyAdvanceCode
import Verified.TreeCopyDescendCode
import Verified.TreeReadCode
import Verified.TreeTestCode
import Verified.TreeCopyBufferCode

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

/-- The copy of a slot that is not an array slot: a word or a null child goes into the copy as it
is, and a record child starts the copy of its record. -/
theorem wp_treeCopyOther {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {heap0 heap : Heap} {initial store : Store Unit} {shape : TreeShape}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit base : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {s0 sRead : Locals}
    {rest : Program} {Q : Assertion Unit}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hReadLocals : CopyLocals base s0 result current.pointer sRead)
    (hIndex' : sRead.get (base + 2) = some (.i64 (UInt64.ofNat current.next)))
    (hSource : sRead.get (base + 3) = some (.i64 current.source))
    (hWord : sRead.get (base + 4) =
      some (.i64 (store.mem.read64 (slotAddress current.source current.next))))
    (hBound : current.next < current.slots.length)
    (hNotArray : ∀ words, current.slots[current.next] ≠ .array words)
    (hNotBytes : ∀ data, current.slots[current.next] ≠ .bytes data)
    (hLowRead : sRead.params.length ≤ base) (hHighRead : base + 6 ≤ sRead.positions)
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q)
    (hNext : ∀ heap' store' s' next parents',
      CopyInv shape heap0 initial root result limit heap' store' next parents' →
      CopyLocals base s0 result next.pointer s' →
      CopyWork.Step (current.work parents) (next.work parents') → wp m rest Q store' s' host) :
    wp m (treeCopyTest shape base ++
      [.iff 0 0 (treeCopyAllocate shape (base + 4) (base + 5) ++
          treeCopyBegin shape (base + 4) (base + 5) [.localGet (base + 4)] [.localGet (base + 1)] ++
          [.localGet (base + 5), .localSet (base + 1)])
        (treeSlotAddress (base + 1) (base + 2) ++ [.localGet (base + 4), .store64 0] ++
          treeCopyAdvance (base + 1) (base + 2))] ++ rest) Q store sRead host := by
  let copyWord := treeSlotAddress (base + 1) (base + 2) ++
    [.localGet (base + 4), .store64 0] ++ treeCopyAdvance (base + 1) (base + 2)
  let descend := treeCopyAllocate shape (base + 4) (base + 5) ++
    treeCopyBegin shape (base + 4) (base + 5) [.localGet (base + 4)] [.localGet (base + 1)] ++
    [.localGet (base + 5), .localSet (base + 1)]
  rw [List.append_assoc]
  refine wp_treeCopyTest (h.frames.current.maskPushes h.step.at_ hSource) hIndex' hWord ?_
  rw [treeCopyCondition_spec h.frames.current hBound hNotArray hNotBytes]
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
  | array words => exact absurd hSlot (hNotArray words)
  | bytes data => exact absurd hSlot (hNotBytes data)

/-- The copy of a slot that is not an array slot: for a shape with buffer fields, a buffer's root
goes to the buffer step, and any other slot to `wp_treeCopyOther`. -/
theorem wp_treeCopyNonArray {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {heap0 heap : Heap} {initial store : Store Unit} {shape : TreeShape}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit base : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {s0 sRead : Locals}
    {rest : Program} {Q : Assertion Unit}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hReadLocals : CopyLocals base s0 result current.pointer sRead)
    (hIndex' : sRead.get (base + 2) = some (.i64 (UInt64.ofNat current.next)))
    (hSource : sRead.get (base + 3) = some (.i64 current.source))
    (hWord : sRead.get (base + 4) =
      some (.i64 (store.mem.read64 (slotAddress current.source current.next))))
    (hBound : current.next < current.slots.length)
    (hNotArray : ∀ words, current.slots[current.next] ≠ .array words)
    (hLowRead : sRead.params.length ≤ base) (hHighRead : base + 6 ≤ sRead.positions)
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q)
    (hNext : ∀ heap' store' s' next parents',
      CopyInv shape heap0 initial root result limit heap' store' next parents' →
      CopyLocals base s0 result next.pointer s' →
      CopyWork.Step (current.work parents) (next.work parents') → wp m rest Q store' s' host) :
    wp m ((if shape.hasBuffers then
        treeCopyBufferTest shape base ++ [.iff 0 0 (treeCopyBuffer base)
          (treeCopyTest shape base ++
            [.iff 0 0 (treeCopyAllocate shape (base + 4) (base + 5) ++
                treeCopyBegin shape (base + 4) (base + 5) [.localGet (base + 4)]
                  [.localGet (base + 1)] ++
                [.localGet (base + 5), .localSet (base + 1)])
              (treeSlotAddress (base + 1) (base + 2) ++ [.localGet (base + 4), .store64 0] ++
                treeCopyAdvance (base + 1) (base + 2))])]
      else treeCopyTest shape base ++
        [.iff 0 0 (treeCopyAllocate shape (base + 4) (base + 5) ++
            treeCopyBegin shape (base + 4) (base + 5) [.localGet (base + 4)]
              [.localGet (base + 1)] ++
            [.localGet (base + 5), .localSet (base + 1)])
          (treeSlotAddress (base + 1) (base + 2) ++ [.localGet (base + 4), .store64 0] ++
            treeCopyAdvance (base + 1) (base + 2))]) ++ rest) Q store sRead host := by
  cases hB : shape.hasBuffers with
  | false =>
    rw [if_neg Bool.false_ne_true]
    exact wp_treeCopyOther hm h hReadLocals hIndex' hSource hWord hBound hNotArray
      (h.frames.current.layout.not_bytes hB current.next hBound) hLowRead hHighRead hCap hTrap
      hNext
  | true =>
    rw [if_pos rfl, List.append_assoc]
    refine wp_treeCopyBufferTest (h.frames.current.bufferMaskPushes h.step.at_ hSource)
      hIndex' ?_
    rw [treeCopyBufferCondition_spec h.frames.current hBound]
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
    by_cases hBytes : ∃ data, current.slots[current.next] = .bytes data
    · obtain ⟨data, hSlot⟩ := hBytes
      rw [hSlot]
      refine wp_iff_cons rfl ?_
      simp (config := { decide := true }) only [bufferBranch,
        ite_true, List.take_zero, List.drop_zero, List.append_eq, List.nil_append]
      refine wp.conseq (Q := post) ?_ ?_
      · intro c hc
        cases c with
        | Break k _ _ => cases k <;> exact hc
        | _ => exact hc
      change wp m (treeCopyBuffer base) post store sRead host
      rw [← List.append_nil (treeCopyBuffer base)]
      exact wp_treeCopyBufferInv hm (rest := []) (Q := post) h hReadLocals hIndex' hSource hWord
        hBound hSlot hLowRead hHighRead hCap (hTrap.imp (Q' := post) (fun _ h => h))
        (fun heap' store' s' hInv hVars => hAfter heap' store' s' _ parents hInv hVars
          (CopyRecord.work_bytes (parents := parents) hBound hSlot))
    · have hNotBytes : ∀ data, current.slots[current.next] ≠ .bytes data :=
        fun data he => hBytes ⟨data, he⟩
      have hBranch : bufferBranch current.slots[current.next] = 0 := by
        cases hS : current.slots[current.next] with
        | bytes data => exact absurd hS (hNotBytes data)
        | _ => rfl
      rw [hBranch]
      refine wp_iff_cons rfl ?_
      simp (config := { decide := true }) only [
        ite_false, List.take_zero, List.drop_zero, List.append_eq, List.nil_append]
      refine wp.conseq (Q := post) ?_ ?_
      · intro c hc
        cases c with
        | Break k _ _ => cases k <;> exact hc
        | _ => exact hc
      have hRun := wp_treeCopyOther hm (rest := []) (Q := post) h hReadLocals hIndex' hSource
        hWord hBound hNotArray hNotBytes hLowRead hHighRead hCap
        (hTrap.imp (Q' := post) (fun _ h => h)) hAfter
      simpa only [List.append_nil, List.append_assoc] using hRun

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
  simp only [treeCopySlot]
  rw [List.append_assoc]
  refine wp_treeCopyRead h.frames.current h.step.at_ hBound hLow hHigh hLocals.current hIndex ?_
  intro sRead hFrame hResult hCurrent hIndex' hSource hWord hValues
  have hReadLocals := hLocals.ofRead hFrame hResult hCurrent hValues
  have hLowRead : sRead.params.length ≤ base := by rw [hFrame.params]; exact hLow
  have hHighRead : base + 6 ≤ sRead.positions := by rw [hFrame.positions]; exact hHigh
  cases hA : shape.hasArrays with
  | false =>
    rw [if_neg Bool.false_ne_true]
    exact wp_treeCopyNonArray hm h hReadLocals hIndex' hSource hWord hBound
      (h.frames.current.layout.not_array hA current.next hBound) hLowRead hHighRead hCap hTrap
      hNext
  | true =>
    rw [if_pos rfl, List.append_assoc]
    refine wp_treeCopyArrayTest (h.frames.current.arrayMaskPushes h.step.at_ hSource) hIndex' ?_
    rw [treeCopyArrayCondition_spec h.frames.current hBound]
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
    by_cases hArray : ∃ xs, current.slots[current.next] = .array xs
    · obtain ⟨xs, hSlot⟩ := hArray
      rw [hSlot]
      refine wp_iff_cons rfl ?_
      simp (config := { decide := true }) only [arrayBranch,
        ite_true, List.take_zero, List.drop_zero, List.append_eq, List.nil_append]
      refine wp.conseq (Q := post) ?_ ?_
      · intro c hc
        cases c with
        | Break k _ _ => cases k <;> exact hc
        | _ => exact hc
      change wp m (treeCopyArray base) post store sRead host
      rw [← List.append_nil (treeCopyArray base)]
      exact wp_treeCopyArrayInv hm (rest := []) (Q := post) h hReadLocals hWord hBound hSlot
        hLowRead hHighRead hCap (hTrap.imp (Q' := post) (fun _ h => h))
        (fun heap' store' s' hInv hVars => hAfter heap' store' s' _ parents hInv hVars
          (CopyRecord.work_array (parents := parents) hBound hSlot))
    · have hNotArray : ∀ words, current.slots[current.next] ≠ .array words :=
        fun words he => hArray ⟨words, he⟩
      have hBranch : arrayBranch current.slots[current.next] = 0 := by
        cases hS : current.slots[current.next] with
        | array words => exact absurd hS (hNotArray words)
        | _ => rfl
      rw [hBranch]
      refine wp_iff_cons rfl ?_
      simp (config := { decide := true }) only [
        ite_false, List.take_zero, List.drop_zero, List.append_eq, List.nil_append]
      refine wp.conseq (Q := post) ?_ ?_
      · intro c hc
        cases c with
        | Break k _ _ => cases k <;> exact hc
        | _ => exact hc
      have hRun := wp_treeCopyNonArray hm (rest := []) (Q := post) h hReadLocals hIndex' hSource
        hWord hBound hNotArray hLowRead hHighRead hCap (hTrap.imp (Q' := post) (fun _ h => h))
        hAfter
      simpa only [List.append_nil, List.append_assoc] using hRun

#print axioms wp_treeCopyOther
#print axioms wp_treeCopyNonArray
#print axioms wp_treeCopySlot

end Verified
