import Verified.AlignedTreeCopyBuffer
import Verified.TreeSlotCode
import Verified.LocalFrame
import Verified.TreeCopyInvariant
import Verified.TreeAdvance
import Verified.TreeCopyLocals
import Verified.TreeAllocate
import Verified.TreeCopyCode
import Verified.TreeStorage
import Verified.TreeInitialize
import Verified.TreeSelect
import Verified.TreeBeginState
import Verified.TreeCopyStartInv
import Verified.TreeTestCode
import Verified.TreeCopyBufferCode
import Verified.TreeRestore
import Verified.TreeNodeLayout
import Verified.TreeCopyCompleteInv

/-!
The copy of one slot and the end of a record's copy under the flag: the ports of
`wp_treeCopyOther`, `wp_treeCopyNonArray`, `wp_treeCopySlot`, and `wp_treeCopyFinish`, which
dispatch to the word, descent, array, and buffer steps and to the ascent, and of
`CopyCompleted.root`, whose flagged form adds the alignment of the finished copy's blocks.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

/-- `CopyCompleted.root` with the alignment of the copy's blocks and of the heap. -/
theorem CopyCompleted.rootX {strict : Bool} {shape : TreeShape} {heap0 heap : Heap}
    {initial store : Store Unit} {root : List LeanExe.Pipeline.Slot} {result : UInt64}
    {limit : Nat} {current : CopyRecord}
    (hX : CopyCompletedX strict shape heap0 initial root result limit heap store current []) :
    NodeOwned heap store result (.record root) ∧
      (Node.blocks store result (.record root)).Pairwise regionsDisjoint ∧
      Step heap0 initial (fun _ => True) heap store (Node.blocks store result (.record root)) ∧
      heap.top.toNat ≤ limit ∧
      (strict = true → heap.Aligned ∧
        ∀ b ∈ Node.blocks store result (.record root), b.1 % 8 = 0 ∧ b.2 % 8 = 0) := by
  obtain ⟨h, hA⟩ := hX
  cases h.path with
  | root hSlots hPointer =>
    have hBlocks : copyBlocks store current [] = Node.blocks store result (.record root) := by
      simp only [copyBlocks, List.flatMap_nil, List.append_nil, current.blocks_done store h.done,
        hSlots, hPointer]
    refine ⟨?_, ?_, ?_, ?_, fun hs => ⟨(hA hs).heap, by rw [← hBlocks]; exact (hA hs).blocks⟩⟩
    · simpa only [hSlots, hPointer] using h.owned
    · simpa only [hBlocks] using h.apart
    · simpa only [hBlocks] using h.step
    · have := h.budget
      omega

theorem CopyCompleted.root {shape : TreeShape} {heap0 heap : Heap} {initial store : Store Unit}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit : Nat} {current : CopyRecord}
    (h : CopyCompleted shape heap0 initial root result limit heap store current []) :
    NodeOwned heap store result (.record root) ∧
      (Node.blocks store result (.record root)).Pairwise regionsDisjoint ∧
      Step heap0 initial (fun _ => True) heap store (Node.blocks store result (.record root)) ∧
      heap.top.toNat ≤ limit :=
  have r := CopyCompleted.rootX (strict := false) ⟨h, nofun⟩
  ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1⟩
#print axioms CopyCompleted.root

theorem wpX_treeCopyOther {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit}
    {heap0 heap : Heap} {initial store : Store Unit} {shape : TreeShape}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit base : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {s0 sRead : Locals}
    {rest : Program} {Q : Assertion Unit}
    (hX : CopyInvX strict shape heap0 initial root result limit heap store current parents)
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
      CopyInvX strict shape heap0 initial root result limit heap' store' next parents' →
      CopyLocals base s0 result next.pointer s' →
      CopyWork.Step (current.work parents) (next.work parents') → wpX strict m rest Q store' s' host) :
    wpX strict m (treeCopyTest shape base ++
      [.iff 0 0 (treeCopyAllocate shape (base + 4) (base + 5) ++
          treeCopyBegin shape (base + 4) (base + 5) [.localGet (base + 4)] [.localGet (base + 1)] ++
          [.localGet (base + 5), .localSet (base + 1)])
        (treeSlotAddress (base + 1) (base + 2) ++ [.localGet (base + 4), .store64 0] ++
          treeCopyAdvance (base + 1) (base + 2))] ++ rest) Q store sRead host := by
  have h := hX.1
  let copyWord := treeSlotAddress (base + 1) (base + 2) ++
    [.localGet (base + 4), .store64 0] ++ treeCopyAdvance (base + 1) (base + 2)
  let descend := treeCopyAllocate shape (base + 4) (base + 5) ++
    treeCopyBegin shape (base + 4) (base + 5) [.localGet (base + 4)] [.localGet (base + 1)] ++
    [.localGet (base + 5), .localSet (base + 1)]
  rw [List.append_assoc]
  refine wpX_treeCopyTest (h.frames.current.maskPushesX h.step.at_ hSource hX.sourceAl) hIndex' hWord ?_
  rw [treeCopyCondition_spec h.frames.current hBound hNotArray hNotBytes]
  let post : Assertion Unit := fun cont => match cont with
    | .Fallthrough store' s' => wpX strict m rest Q store' { s' with values := sRead.values } host
    | .Break 0 store' s' => wpX strict m rest Q store' { s' with values := sRead.values } host
    | .Break (k + 1) store' s' => Q (.Break k store' s')
    | other => Q other
  have hAfter (heap' : Heap) (store' : Store Unit) (s' : Locals) (next : CopyRecord)
      (parents' : List CopyRecord)
      (hInv : CopyInvX strict shape heap0 initial root result limit heap' store' next parents')
      (hVars : CopyLocals base s0 result next.pointer s')
      (hWork : CopyWork.Step (current.work parents) (next.work parents')) :
      wpX strict m [] post store' s' host := by
    rw [wpX_nil]
    change wpX strict m rest Q store' { s' with values := sRead.values } host
    have hStack : sRead.values = s'.values := hReadLocals.values.trans hVars.values.symm
    rw [hStack]
    exact hNext heap' store' s' next parents' hInv hVars hWork
  have hBorrow := SlotsBorrowed.get current.slots 0 h.frames.current.borrowed.2 current.next hBound
  simp only [Nat.zero_add] at hBorrow
  cases hSlot : current.slots[current.next] with
  | word word =>
    refine wpX_iff_cons rfl ?_
    simp (config := { decide := true }) only [copyBranch,
      ite_false, List.take_zero, List.drop_zero, List.append_eq, List.nil_append]
    refine wpX.conseq (Q := post) ?_ ?_
    · intro c hc
      cases c with
      | Break k _ _ => cases k <;> exact hc
      | _ => exact hc
    change wpX strict m copyWord post store sRead host
    have hValue : (current.slots[current.next]).ValueOwned heap store
        (store.mem.read64 (slotAddress current.source current.next)) := by
      rw [hSlot] at hBorrow ⊢
      exact hBorrow.1
    have hWork := CopyRecord.work_advance (parents := parents) hBound hSlot
    have hCharge : (current.work parents).charge = 0 := by
      unfold CopyRecord.work
      rw [List.drop_eq_getElem_cons hBound, hSlot]
      rfl
    apply wpX_treeCopyAdvanceInv (rest := []) hX hReadLocals hIndex' hWord hBound hValue
      (by rw [hSlot]; rfl) hWork hCharge
    intro store' hInv
    exact hAfter heap store' sRead _ parents hInv hReadLocals hWork
  | child value =>
    cases value with
    | null =>
      refine wpX_iff_cons rfl ?_
      simp (config := { decide := true }) only [
        ite_false, List.take_zero, List.drop_zero, List.append_eq, List.nil_append]
      refine wpX.conseq (Q := post) ?_ ?_
      · intro c hc
        cases c with
        | Break k _ _ => cases k <;> exact hc
        | _ => exact hc
      change wpX strict m copyWord post store sRead host
      have hValue : (current.slots[current.next]).ValueOwned heap store
          (store.mem.read64 (slotAddress current.source current.next)) := by
        rw [hSlot] at hBorrow ⊢
        exact hBorrow.1
      have hWork := CopyRecord.work_null (parents := parents) hBound hSlot
      have hCharge : (current.work parents).charge = 0 := by
        unfold CopyRecord.work
        rw [List.drop_eq_getElem_cons hBound, hSlot]
        rfl
      apply wpX_treeCopyAdvanceInv (rest := []) hX hReadLocals hIndex' hWord hBound hValue
        (by rw [hSlot]; rfl) hWork hCharge
      intro store' hInv
      exact hAfter heap store' sRead _ parents hInv hReadLocals hWork
    | record children =>
      refine wpX_iff_cons rfl ?_
      simp (config := { decide := true }) only [copyBranch,
        ite_true, List.take_zero, List.drop_zero, List.append_eq, List.nil_append]
      refine wpX.conseq (Q := post) ?_ ?_
      · intro c hc
        cases c with
        | Break k _ _ => cases k <;> exact hc
        | _ => exact hc
      change wpX strict m descend post store sRead host
      rw [← List.append_nil descend]
      apply wpX_treeCopyDescendInv hm hRt (rest := []) (Q := post) hX hReadLocals hWord hBound hSlot
        hLowRead hHighRead hCap (hTrap.imp (Q' := post) (fun _ h => h))
      intro heap' store' ptr s' hInv hVars
      exact hAfter heap' store' s' _ (current :: parents) hInv hVars
        (CopyRecord.work_descend (parents := parents) hBound hSlot rfl)
  | array words => exact absurd hSlot (hNotArray words)
  | bytes data => exact absurd hSlot (hNotBytes data)

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
          treeCopyAdvance (base + 1) (base + 2))] ++ rest) Q store sRead host :=
  wpX_treeCopyOther (strict := false) hm nofun ⟨h, nofun⟩ hReadLocals hIndex' hSource hWord hBound
    hNotArray hNotBytes hLowRead hHighRead hCap hTrap
    (fun heap' store' s' next parents' a1 a2 a3 => hNext heap' store' s' next parents' a1.1 a2 a3)
#print axioms wp_treeCopyOther

theorem wpX_treeCopyNonArray {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit}
    {heap0 heap : Heap} {initial store : Store Unit} {shape : TreeShape}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit base : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {s0 sRead : Locals}
    {rest : Program} {Q : Assertion Unit}
    (hX : CopyInvX strict shape heap0 initial root result limit heap store current parents)
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
      CopyInvX strict shape heap0 initial root result limit heap' store' next parents' →
      CopyLocals base s0 result next.pointer s' →
      CopyWork.Step (current.work parents) (next.work parents') → wpX strict m rest Q store' s' host) :
    wpX strict m ((if shape.hasBuffers then
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
  have h := hX.1
  cases hB : shape.hasBuffers with
  | false =>
    rw [ite_eq_right Bool.false_ne_true]
    exact wpX_treeCopyOther hm hRt hX hReadLocals hIndex' hSource hWord hBound hNotArray
      (h.frames.current.layout.not_bytes hB current.next hBound) hLowRead hHighRead hCap hTrap
      hNext
  | true =>
    rw [ite_eq_left rfl, List.append_assoc]
    refine wpX_treeCopyBufferTest (h.frames.current.bufferMaskPushesX h.step.at_ hSource hX.sourceAl)
      hIndex' ?_
    rw [treeCopyBufferCondition_spec h.frames.current hBound]
    let post : Assertion Unit := fun cont => match cont with
      | .Fallthrough store' s' => wpX strict m rest Q store' { s' with values := sRead.values } host
      | .Break 0 store' s' => wpX strict m rest Q store' { s' with values := sRead.values } host
      | .Break (k + 1) store' s' => Q (.Break k store' s')
      | other => Q other
    have hAfter (heap' : Heap) (store' : Store Unit) (s' : Locals) (next : CopyRecord)
        (parents' : List CopyRecord)
        (hInv : CopyInvX strict shape heap0 initial root result limit heap' store' next parents')
        (hVars : CopyLocals base s0 result next.pointer s')
        (hWork : CopyWork.Step (current.work parents) (next.work parents')) :
        wpX strict m [] post store' s' host := by
      rw [wpX_nil]
      change wpX strict m rest Q store' { s' with values := sRead.values } host
      have hStack : sRead.values = s'.values := hReadLocals.values.trans hVars.values.symm
      rw [hStack]
      exact hNext heap' store' s' next parents' hInv hVars hWork
    by_cases hBytes : ∃ data, current.slots[current.next] = .bytes data
    · obtain ⟨data, hSlot⟩ := hBytes
      rw [hSlot]
      refine wpX_iff_cons rfl ?_
      simp (config := { decide := true }) only [bufferBranch,
        ite_true, List.take_zero, List.drop_zero, List.append_eq, List.nil_append]
      refine wpX.conseq (Q := post) ?_ ?_
      · intro c hc
        cases c with
        | Break k _ _ => cases k <;> exact hc
        | _ => exact hc
      change wpX strict m (treeCopyBuffer base) post store sRead host
      rw [← List.append_nil (treeCopyBuffer base)]
      exact wpX_treeCopyBufferInv hm hRt (rest := []) (Q := post) hX hReadLocals hIndex' hSource hWord
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
      refine wpX_iff_cons rfl ?_
      simp (config := { decide := true }) only [
        ite_false, List.take_zero, List.drop_zero, List.append_eq, List.nil_append]
      refine wpX.conseq (Q := post) ?_ ?_
      · intro c hc
        cases c with
        | Break k _ _ => cases k <;> exact hc
        | _ => exact hc
      have hRun := wpX_treeCopyOther hm hRt (rest := []) (Q := post) hX hReadLocals hIndex' hSource
        hWord hBound hNotArray hNotBytes hLowRead hHighRead hCap
        (hTrap.imp (Q' := post) (fun _ h => h)) hAfter
      simpa only [List.append_nil, List.append_assoc] using hRun

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
            treeCopyAdvance (base + 1) (base + 2))]) ++ rest) Q store sRead host :=
  wpX_treeCopyNonArray (strict := false) hm nofun ⟨h, nofun⟩ hReadLocals hIndex' hSource hWord
    hBound hNotArray hLowRead hHighRead hCap hTrap
    (fun heap' store' s' next parents' a1 a2 a3 => hNext heap' store' s' next parents' a1.1 a2 a3)
#print axioms wp_treeCopyNonArray

theorem wpX_treeCopySlot {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit}
    {heap0 heap : Heap} {initial store : Store Unit} {shape : TreeShape}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit base : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {s0 s : Locals}
    {rest : Program} {Q : Assertion Unit}
    (hX : CopyInvX strict shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat current.next)))
    (hBound : current.next < current.slots.length)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q)
    (hNext : ∀ heap' store' s' next parents',
      CopyInvX strict shape heap0 initial root result limit heap' store' next parents' →
      CopyLocals base s0 result next.pointer s' →
      CopyWork.Step (current.work parents) (next.work parents') → wpX strict m rest Q store' s' host) :
    wpX strict m (treeCopySlot shape base ++ rest) Q store s host := by
  have h := hX.1
  simp only [treeCopySlot]
  rw [List.append_assoc]
  refine wpX_treeCopyRead h.frames.current h.step.at_ hBound hLow hHigh hLocals.current hIndex
    (fun hs => ⟨hX.pointerAl hs, hX.sourceAl hs⟩) ?_
  intro sRead hFrame hResult hCurrent hIndex' hSource hWord hValues
  have hReadLocals := hLocals.ofRead hFrame hResult hCurrent hValues
  have hLowRead : sRead.params.length ≤ base := by rw [hFrame.params]; exact hLow
  have hHighRead : base + 6 ≤ sRead.positions := by rw [hFrame.positions]; exact hHigh
  cases hA : shape.hasArrays with
  | false =>
    rw [ite_eq_right Bool.false_ne_true]
    exact wpX_treeCopyNonArray hm hRt hX hReadLocals hIndex' hSource hWord hBound
      (h.frames.current.layout.not_array hA current.next hBound) hLowRead hHighRead hCap hTrap
      hNext
  | true =>
    rw [ite_eq_left rfl, List.append_assoc]
    refine wpX_treeCopyArrayTest (h.frames.current.arrayMaskPushesX h.step.at_ hSource hX.sourceAl) hIndex' ?_
    rw [treeCopyArrayCondition_spec h.frames.current hBound]
    let post : Assertion Unit := fun cont => match cont with
      | .Fallthrough store' s' => wpX strict m rest Q store' { s' with values := sRead.values } host
      | .Break 0 store' s' => wpX strict m rest Q store' { s' with values := sRead.values } host
      | .Break (k + 1) store' s' => Q (.Break k store' s')
      | other => Q other
    have hAfter (heap' : Heap) (store' : Store Unit) (s' : Locals) (next : CopyRecord)
        (parents' : List CopyRecord)
        (hInv : CopyInvX strict shape heap0 initial root result limit heap' store' next parents')
        (hVars : CopyLocals base s0 result next.pointer s')
        (hWork : CopyWork.Step (current.work parents) (next.work parents')) :
        wpX strict m [] post store' s' host := by
      rw [wpX_nil]
      change wpX strict m rest Q store' { s' with values := sRead.values } host
      have hStack : sRead.values = s'.values := hReadLocals.values.trans hVars.values.symm
      rw [hStack]
      exact hNext heap' store' s' next parents' hInv hVars hWork
    by_cases hArray : ∃ xs, current.slots[current.next] = .array xs
    · obtain ⟨xs, hSlot⟩ := hArray
      rw [hSlot]
      refine wpX_iff_cons rfl ?_
      simp (config := { decide := true }) only [arrayBranch,
        ite_true, List.take_zero, List.drop_zero, List.append_eq, List.nil_append]
      refine wpX.conseq (Q := post) ?_ ?_
      · intro c hc
        cases c with
        | Break k _ _ => cases k <;> exact hc
        | _ => exact hc
      change wpX strict m (treeCopyArray base) post store sRead host
      rw [← List.append_nil (treeCopyArray base)]
      exact wpX_treeCopyArrayInv hm hRt (rest := []) (Q := post) hX hReadLocals hWord hBound hSlot
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
      refine wpX_iff_cons rfl ?_
      simp (config := { decide := true }) only [
        ite_false, List.take_zero, List.drop_zero, List.append_eq, List.nil_append]
      refine wpX.conseq (Q := post) ?_ ?_
      · intro c hc
        cases c with
        | Break k _ _ => cases k <;> exact hc
        | _ => exact hc
      have hRun := wpX_treeCopyNonArray hm hRt (rest := []) (Q := post) hX hReadLocals hIndex' hSource
        hWord hBound hNotArray hLowRead hHighRead hCap (hTrap.imp (Q' := post) (fun _ h => h))
        hAfter
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
    wp m (treeCopySlot shape base ++ rest) Q store s host :=
  wpX_treeCopySlot (strict := false) hm nofun ⟨h, nofun⟩ hLocals hIndex hBound hLow hHigh hCap hTrap
    (fun heap' store' s' next parents' a1 a2 a3 => hNext heap' store' s' next parents' a1.1 a2 a3)
#print axioms wp_treeCopySlot

theorem wpX_treeCopyFinish {strict : Bool} {m : Module} {host : HostEnv Unit} {heap0 heap : Heap}
    {initial store : Store Unit} {shape : TreeShape} {root : List LeanExe.Pipeline.Slot}
    {result : UInt64} {limit base : Nat} {current : CopyRecord} {parents : List CopyRecord}
    {s0 s : Locals} {rest : Program} {Q : Assertion Unit}
    (hX : CopyInvX strict shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hDone : current.next = current.slots.length)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hNext : ∀ store' s' next parents',
      CopyInvX strict shape heap0 initial root result limit heap store' next parents' →
      CopyLocals base s0 result next.pointer s' →
      CopyWork.Step (current.work parents) (next.work parents') → wpX strict m rest Q store' s' host)
    (hRoot : ∀ store' s', NodeOwned heap store' result (.record root) →
      (Node.blocks store' result (.record root)).Pairwise regionsDisjoint →
      Step heap0 initial (fun _ => True) heap store' (Node.blocks store' result (.record root)) →
      heap.top.toNat ≤ limit → CopyLocals base s0 result current.pointer s' →
      (strict = true → heap.Aligned ∧
        ∀ b ∈ Node.blocks store' result (.record root), b.1 % 8 = 0 ∧ b.2 % 8 = 0) →
      Q (.Break 2 store' s')) :
    wpX strict m (treeCopyFinish shape base ++ rest) Q store s host := by
  have h := hX.1
  simp only [treeCopyFinish, List.append_assoc]
  refine wpX_treeCopyComplete hX hLocals hDone hLow hHigh ?_
  intro store' s' hCompleted hVars hParent
  cases parents with
  | nil =>
    change s'.get (base + 5) = some (.i64 0) at hParent
    simp only [Locals.get] at hParent
    obtain ⟨hOwned, hApart, hStep, hBudget, hRootAl⟩ := CopyCompleted.rootX hCompleted
    simpa [hParent] using hRoot store' s' hOwned hApart hStep hBudget hVars hRootAl
  | cons parent parents =>
    change s'.get (base + 5) = some (.i64 parent.pointer) at hParent
    have hParentFrames : CopyFrames shape heap store' parent parents := hCompleted.1.parents
    have hParentBase := hParentFrames.current.storage.base
    have hNonzero : parent.pointer ≠ 0 := by
      intro hZero
      rw [hZero] at hParentBase
      simp at hParentBase
    have hLow' : s'.params.length ≤ base := by
      rw [hVars.frame.params, ← hLocals.frame.params]
      exact hLow
    have hHigh' : base + 6 ≤ s'.positions := by
      rw [hVars.frame.positions, ← hLocals.frame.positions]
      exact hHigh
    have hAdvance := wpX_treeCopyAscendInv (rest := rest) hCompleted hVars hParent hLow' hHigh'
      (fun store'' s'' hInv hLocals' =>
        hNext store'' s'' _ parents hInv hLocals'
          (CopyRecord.work_ascend (parent := parent) (parents := parents) hDone))
    simpa only [List.append_assoc, List.cons_append, List.nil_append, wpX_localGet_cons, Locals.get_values,
      hParent, wpX_eqzI64_cons, hNonzero, ite_false, wpX_br_if_cons,
      ne_eq, not_true_eq_false] using hAdvance

theorem wp_treeCopyFinish {m : Module} {host : HostEnv Unit} {heap0 heap : Heap}
    {initial store : Store Unit} {shape : TreeShape} {root : List LeanExe.Pipeline.Slot}
    {result : UInt64} {limit base : Nat} {current : CopyRecord} {parents : List CopyRecord}
    {s0 s : Locals} {rest : Program} {Q : Assertion Unit}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hDone : current.next = current.slots.length)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hNext : ∀ store' s' next parents',
      CopyInv shape heap0 initial root result limit heap store' next parents' →
      CopyLocals base s0 result next.pointer s' →
      CopyWork.Step (current.work parents) (next.work parents') → wp m rest Q store' s' host)
    (hRoot : ∀ store' s', NodeOwned heap store' result (.record root) →
      (Node.blocks store' result (.record root)).Pairwise regionsDisjoint →
      Step heap0 initial (fun _ => True) heap store' (Node.blocks store' result (.record root)) →
      heap.top.toNat ≤ limit → CopyLocals base s0 result current.pointer s' → Q (.Break 2 store' s')) :
    wp m (treeCopyFinish shape base ++ rest) Q store s host :=
  wpX_treeCopyFinish (strict := false) ⟨h, nofun⟩ hLocals hDone hLow hHigh
    (fun store' s' next parents' a1 a2 a3 => hNext store' s' next parents' a1.1 a2 a3)
    (fun store' s' a1 a2 a3 a4 a5 _ => hRoot store' s' a1 a2 a3 a4 a5)
#print axioms wp_treeCopyFinish

end Verified
