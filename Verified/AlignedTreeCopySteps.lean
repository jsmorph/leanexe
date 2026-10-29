import Verified.AlignedTreeCopyNew
import Verified.LocalFrame
import Verified.TreeAllocate
import Verified.TreeSlotCode

/-!
The moves of the tree copy between records under the flag: the ports of `wp_restoreRecord`,
`wp_restoreOwnedRecord`, `wp_treeCopyDescendInv`, `wp_treeCopyComplete`, and
`wp_treeCopyAscendInv`.  A descent allocates the child's record and starts its copy, the end of a
record rewrites its header words at its pointer minus 40, 24, 16, and 8 and reads its tag, and an
ascent reads the parent's next index and stores the child's pointer into the parent's slot.  The
pointers of the records on the copy's path are multiples of 8 by `CopyAligned`, and so is the
child's source, whose regions are regions of its parent's source.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

/-- The pointer of the parent of the record being copied. -/
theorem CopyAligned.parent {heap : Heap} {initial store : Store Unit} {current parent : CopyRecord}
    {parents : List CopyRecord} (h : CopyAligned heap initial store current (parent :: parents))
    (hBase : 48 ≤ parent.pointer.toNat) : parent.pointer.toNat % 8 = 0 := by
  have hb := h.blocks (block store parent.pointer) (by simp [copyBlocks, CopyRecord.blocks])
  simp only [block] at hb
  omega

theorem wpX_restoreRecord {strict : Bool} {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} (r : Fin shape.records) {store : Store Unit} {s : Locals} {ptr : Nat}
    {p : UInt64} {slots : List LeanExe.Pipeline.Slot} {rest : Program} {Q : Assertion Unit}
    (hRaw : RecordStorage slots.length heap store p) (hHeap : heap.At store)
    (hPtr : s.get ptr = some (.i64 p)) (hWidth : shape.width r = slots.length)
    (hMask : shape.mask r = maskOf slots)
    (hTag : shape.tagged = true → store.mem.read64 p.toUInt32 = UInt64.ofNat (shape.ctorIndex r))
    (hAl : strict = true → p.toNat % 8 = 0)
    (hNext : wpX strict m rest Q (restoreRecordStore store p slots) s host) :
    wpX strict m (restoreRecordCode shape ptr ++ rest) Q store s host := by
  have hBase := hRaw.base
  have hAddress := hRaw.address
  have hBelow := hRaw.below
  have hCapacity := hRaw.capacity
  have hTop := hHeap.top
  have hPos := shape.width_pos r
  have hNat : p.toUInt32.toNat = p.toNat := by
    rw [UInt64.toNat_toUInt32]
    omega
  have hRoom (back : UInt64) (h8 : 8 ≤ back.toNat) (h40 : back.toNat ≤ 40) :
      (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [headerAddress_toNat (by omega) (by omega)]
    omega
  have hSlotRoom : p.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [hNat]
    omega
  obtain ⟨hAt1, hRaw1, -⟩ := hRaw.writeHeader hHeap (back := 40) (value := 1) (by decide)
  obtain ⟨-, hRaw2, -⟩ := hRaw1.writeHeader hAt1 (back := 24) (value := 1) (by decide)
  have hTag2 (ht : shape.tagged = true) :
      (recordHeaderWrite (recordHeaderWrite store p 40 1) p 24 1).mem.read64 p.toUInt32 =
        UInt64.ofNat (shape.ctorIndex r) := by
    rw [hRaw1.readSlot_write (back := 24) (value := 1) (by decide),
      hRaw.readSlot_write (back := 40) (value := 1) (by decide)]
    exact hTag ht
  have hTag3 (ht : shape.tagged = true) :
      (recordHeaderWrite (recordHeaderWrite (recordHeaderWrite store p 40 1) p 24 1) p 16
        (UInt64.ofNat (shape.width r))).mem.read64 p.toUInt32 =
        UInt64.ofNat (shape.ctorIndex r) := by
    rw [hRaw2.readSlot_write (back := 16) (value := UInt64.ofNat (shape.width r)) (by decide)]
    exact hTag2 ht
  simp only [restoreRecordCode, List.append_assoc]
  refine wpX_headerStoreWord hPtr (hRoom 40 (by decide) (by decide)) (fun hs => ⟨hAl hs, rfl⟩) ?_
  refine wpX_headerStoreWord hPtr ?_ (fun hs => ⟨hAl hs, rfl⟩) ?_
  · simpa only [Mem.write64_pages] using hRoom 24 (by decide) (by decide)
  refine wpX_headerStorePushes hPtr ?_ (fun hs => ⟨hAl hs, rfl⟩)
    (PushesWordX.selectCode r (fun r => UInt64.ofNat (shape.width r))
      (PushesWordX.tag hPtr (by simpa only [Mem.write64_pages] using hSlotRoom) hAl) hTag2) ?_
  · simpa only [Mem.write64_pages] using hRoom 16 (by decide) (by decide)
  refine wpX_headerStorePushes hPtr ?_ (fun hs => ⟨hAl hs, rfl⟩)
    (PushesWordX.selectCode r shape.mask
      (PushesWordX.tag hPtr (by simpa only [Mem.write64_pages] using hSlotRoom) hAl) hTag3) ?_
  · simpa only [Mem.write64_pages] using hRoom 8 (by decide) (by decide)
  simp only [restoreRecordStore, recordHeaderWrite] at hNext
  rw [← hWidth, ← hMask] at hNext
  exact hNext

theorem wp_restoreRecord {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} (r : Fin shape.records) {store : Store Unit} {s : Locals} {ptr : Nat}
    {p : UInt64} {slots : List LeanExe.Pipeline.Slot} {rest : Program} {Q : Assertion Unit}
    (hRaw : RecordStorage slots.length heap store p) (hHeap : heap.At store)
    (hPtr : s.get ptr = some (.i64 p)) (hWidth : shape.width r = slots.length)
    (hMask : shape.mask r = maskOf slots)
    (hTag : shape.tagged = true → store.mem.read64 p.toUInt32 = UInt64.ofNat (shape.ctorIndex r))
    (hNext : wp m rest Q (restoreRecordStore store p slots) s host) :
    wp m (restoreRecordCode shape ptr ++ rest) Q store s host :=
  wpX_restoreRecord (strict := false) r hRaw hHeap hPtr hWidth hMask hTag nofun hNext

theorem wpX_restoreOwnedRecord {strict : Bool} {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} {store : Store Unit} {s : Locals} {ptr : Nat} {p : UInt64}
    {slots : List LeanExe.Pipeline.Slot} {rest : Program} {Q : Assertion Unit}
    (hRaw : RecordStorage slots.length heap store p) (hHeap : heap.At store)
    (hPtr : s.get ptr = some (.i64 p)) (hLayout : NodeLayout shape (.record slots))
    (hSlots : SlotsOwned heap store p 0 slots)
    (hApart : (Node.blocks store p (.record slots)).Pairwise regionsDisjoint)
    (hAl : strict = true → p.toNat % 8 = 0)
    (hNext : ∀ store',
      Memory.WritesRange store store' (p.toNat - 40) p.toNat → heap.At store' →
      NodeOwned heap store' p (.record slots) →
      Node.blocks store' p (.record slots) = Node.blocks store p (.record slots) →
      wpX strict m rest Q store' s host) :
    wpX strict m (restoreRecordCode shape ptr ++ rest) Q store s host := by
  obtain ⟨r, hLength, hMask, hPrefix, -⟩ := id hLayout
  obtain ⟨hWrites, hAt, hOwned, hBlocks, _⟩ :=
    hRaw.restore hHeap (by rw [hLength]; exact shape.width_le r) hSlots (NodeLayout.lengths hLayout)
      hApart
  exact wpX_restoreRecord r hRaw hHeap hPtr hLength.symm hMask.symm
    (fun ht => SlotsOwned.tag hSlots hPrefix ht) hAl (hNext _ hWrites hAt hOwned hBlocks)

theorem wp_restoreOwnedRecord {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} {store : Store Unit} {s : Locals} {ptr : Nat} {p : UInt64}
    {slots : List LeanExe.Pipeline.Slot} {rest : Program} {Q : Assertion Unit}
    (hRaw : RecordStorage slots.length heap store p) (hHeap : heap.At store)
    (hPtr : s.get ptr = some (.i64 p)) (hLayout : NodeLayout shape (.record slots))
    (hSlots : SlotsOwned heap store p 0 slots)
    (hApart : (Node.blocks store p (.record slots)).Pairwise regionsDisjoint)
    (hNext : ∀ store',
      Memory.WritesRange store store' (p.toNat - 40) p.toNat → heap.At store' →
      NodeOwned heap store' p (.record slots) →
      Node.blocks store' p (.record slots) = Node.blocks store p (.record slots) →
      wp m rest Q store' s host) :
    wp m (restoreRecordCode shape ptr ++ rest) Q store s host :=
  wpX_restoreOwnedRecord (strict := false) hRaw hHeap hPtr hLayout hSlots hApart nofun hNext
#print axioms wp_restoreOwnedRecord

theorem wpX_treeCopyDescendInv {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit}
    {heap0 heap : Heap} {initial store : Store Unit} {shape : TreeShape}
    {root children : List LeanExe.Pipeline.Slot} {result : UInt64} {limit base : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {s0 s : Locals}
    {rest : Program} {Q : Assertion Unit}
    (h : CopyInvX strict shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hWord : s.get (base + 4) =
      some (.i64 (store.mem.read64 (slotAddress current.source current.next))))
    (hBound : current.next < current.slots.length)
    (hSlot : current.slots[current.next] = .child (.record children))
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q)
    (hNext : ∀ heap' store' ptr s',
      CopyInvX strict shape heap0 initial root result limit heap' store'
        ⟨store.mem.read64 (slotAddress current.source current.next), ptr, children, 0⟩
        (current :: parents) →
      CopyLocals base s0 result ptr s' → wpX strict m rest Q store' s' host) :
    wpX strict m (treeCopyAllocate shape (base + 4) (base + 5) ++
      treeCopyBegin shape (base + 4) (base + 5) [.localGet (base + 4)] [.localGet (base + 1)] ++
      [.localGet (base + 5), .localSet (base + 1)] ++ rest) Q store s host := by
  have hCurrent := h.1.frames.current
  have hLayout : NodeLayout shape (.record children) := by
    obtain ⟨-, -, -, -, hSlots, -⟩ := id hCurrent.layout
    exact SlotsLayout.child (slots := current.slots) hSlots current.next hBound
      (.record children) hSlot
  have hBorrow := SlotsBorrowed.get current.slots 0 hCurrent.borrowed.2 current.next hBound
  rw [hSlot] at hBorrow
  simp only [Nat.zero_add] at hBorrow
  have hInitialChild := h.1.step.childSource (h.1.sources current List.mem_cons_self).2 hBound hSlot
  have hRead := h.1.step.recordRead (h.1.sources current List.mem_cons_self).2 hBound
  have hChildAl : strict = true →
      (store.mem.read64 (slotAddress current.source current.next)).toNat % 8 = 0 := fun hs => by
    have hm := slotRegions_child (store := initial) (p := current.source) hBound hSlot
      ((initial.mem.read64 (slotAddress current.source current.next)).toNat, 8 * children.length)
      (by simp [Node.slotRegions])
    rw [hRead]
    exact (h.2 hs).sources current List.mem_cons_self _ hm
  have hCharge : allocCost (8 * children.length) ≤ (current.work parents).cost := by
    unfold CopyRecord.work CopyWork.cost
    rw [List.drop_eq_getElem_cons hBound, hSlot]
    simp only [slotsCopyCost, nodeCopyCost]
    omega
  have hLow5 : s.params.length ≤ base + 5 := by omega
  have hHigh5 : base + 5 < s.params.length + s.locals.length := Locals.lt_total (by omega)
  have hLow1 : s.params.length ≤ base + 1 := by omega
  have hHigh1 : base + 1 < s.params.length + s.locals.length := Locals.lt_total (by omega)
  rw [List.append_assoc]
  refine wpX_treeCopyNew hm hRt (shape := shape) (dst := base + 5) (input := base + 4)
    (parent := some (base + 1)) (slots := children)
    (rest := [.localGet (base + 5), .localSet (base + 1)] ++ rest) h.1.step.at_ ?_
    (h.1.toCopyProgress.trap hCharge hTrap) hLayout hBorrow.1 hWord hLocals.current
    (by omega) ?_ hLow5 hHigh5 (fun hs => (h.2 hs).heap) hChildAl ?_
  · rw [h.1.step.cap m]
    exact hCap
  · intro pos hp
    simp only [Option.some.injEq] at hp
    omega
  intro heap' store' ptr hNew hChild hTop hAlloc
  have hInv := CopyInv.descendX h
    (child := ⟨store.mem.read64 (slotAddress current.source current.next), ptr, children, 0⟩)
    hBound hSlot rfl hInitialChild (fun _ => hRead) hNew hChild hTop hAlloc
  let sFresh := setLocal s (base + 5) (.i64 ptr)
  have hFreshLocals : CopyLocals base s0 result current.pointer sFresh :=
    hLocals.scratch hLow5 (by omega) (by omega)
  have hFresh : sFresh.get (base + 5) = some (.i64 ptr) :=
    Locals.get_setLocal_same hLow5 hHigh5
  have hLow1Fresh : sFresh.params.length ≤ base + 1 := hLow1
  have hHigh1Fresh : base + 1 < sFresh.params.length + sFresh.locals.length := by
    simpa only [sFresh, setLocal, List.length_set] using hHigh1
  have hNextLocals := hFreshLocals.setCurrent (next := ptr) hLow1Fresh
    (by rw [hFreshLocals.frame.positions]; rw [← hLocals.frame.positions]; omega)
  change wpX strict m ([.localGet (base + 5), .localSet (base + 1)] ++ rest) Q store' sFresh host
  simp only [List.cons_append, List.nil_append, wpX_localGet_cons, hFresh]
  exact wpX_localSet_local hLow1Fresh hHigh1Fresh (hNext heap' store' ptr _ hInv hNextLocals)

theorem wp_treeCopyDescendInv {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {heap0 heap : Heap} {initial store : Store Unit} {shape : TreeShape}
    {root children : List LeanExe.Pipeline.Slot} {result : UInt64} {limit base : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {s0 s : Locals}
    {rest : Program} {Q : Assertion Unit}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hWord : s.get (base + 4) =
      some (.i64 (store.mem.read64 (slotAddress current.source current.next))))
    (hBound : current.next < current.slots.length)
    (hSlot : current.slots[current.next] = .child (.record children))
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q)
    (hNext : ∀ heap' store' ptr s',
      CopyInv shape heap0 initial root result limit heap' store'
        ⟨store.mem.read64 (slotAddress current.source current.next), ptr, children, 0⟩
        (current :: parents) →
      CopyLocals base s0 result ptr s' → wp m rest Q store' s' host) :
    wp m (treeCopyAllocate shape (base + 4) (base + 5) ++
      treeCopyBegin shape (base + 4) (base + 5) [.localGet (base + 4)] [.localGet (base + 1)] ++
      [.localGet (base + 5), .localSet (base + 1)] ++ rest) Q store s host :=
  wpX_treeCopyDescendInv (strict := false) hm nofun ⟨h, nofun⟩ hLocals hWord hBound hSlot hLow hHigh
    hCap hTrap (fun heap' store' ptr s' a1 a2 => hNext heap' store' ptr s' a1.1 a2)
#print axioms wp_treeCopyDescendInv

theorem wpX_treeCopyComplete {strict : Bool} {m : Module} {host : HostEnv Unit} {heap0 heap : Heap}
    {initial store : Store Unit} {shape : TreeShape} {root : List LeanExe.Pipeline.Slot}
    {result : UInt64} {limit base : Nat} {current : CopyRecord} {parents : List CopyRecord}
    {s0 s : Locals} {rest : Program} {Q : Assertion Unit}
    (h : CopyInvX strict shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hDone : current.next = current.slots.length)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hNext : ∀ store' s',
      CopyCompletedX strict shape heap0 initial root result limit heap store' current parents →
      CopyLocals base s0 result current.pointer s' →
      s'.get (base + 5) = some (.i64 ((parents.head?.map CopyRecord.pointer).getD 0)) →
      wpX strict m rest Q store' s' host) :
    wpX strict m (headerLoad (base + 1) 40 ++ [.localSet (base + 5)] ++
      restoreRecordCode shape (base + 1) ++ rest) Q store s host := by
  have hCurrent := h.1.frames.current
  have hBase := hCurrent.storage.base
  have hAddress := hCurrent.storage.address
  have hBelow := hCurrent.storage.below
  have hTop := h.1.step.at_.top
  have hLow5 : s.params.length ≤ base + 5 := by omega
  have hHigh5 : base + 5 < s.params.length + s.locals.length := Locals.lt_total (by omega)
  have hSlots : SlotsOwned heap store current.pointer 0 current.slots := by
    simpa only [hDone, List.take_length] using hCurrent.filled
  have hNodeApart : (Node.blocks store current.pointer (.record current.slots)).Pairwise
      regionsDisjoint := by
    rw [← current.blocks_done store hDone]
    exact (List.pairwise_append.mp h.1.apart).1
  simp only [List.append_assoc]
  refine wpX_headerLoad hLocals.current ?_ (fun hs => ⟨h.pointerAl hs, rfl⟩) ?_
  · rw [headerAddress_toNat (by change 40 ≤ current.pointer.toNat; omega) (by omega)]
    change current.pointer.toNat - 40 + 8 ≤ store.mem.pages * 65536
    omega
  rw [hCurrent.parent]
  refine wpX_localSet_local hLow5 hHigh5 ?_
  let sFresh := setLocal s (base + 5) (.i64 ((parents.head?.map CopyRecord.pointer).getD 0))
  have hFreshLocals : CopyLocals base s0 result current.pointer sFresh :=
    hLocals.scratch hLow5 (by omega) (by omega)
  have hFresh : sFresh.get (base + 5) = some (.i64 ((parents.head?.map CopyRecord.pointer).getD 0)) :=
    Locals.get_setLocal_same hLow5 hHigh5
  refine wpX_restoreOwnedRecord hCurrent.storage h.1.step.at_ hFreshLocals.current hCurrent.layout
    hSlots hNodeApart h.pointerAl ?_
  intro store' hWrites hAt hOwned hBlocks
  exact hNext store' sFresh (CopyInv.completeX h hDone hWrites hAt hOwned hBlocks) hFreshLocals hFresh

theorem wp_treeCopyComplete {m : Module} {host : HostEnv Unit} {heap0 heap : Heap}
    {initial store : Store Unit} {shape : TreeShape} {root : List LeanExe.Pipeline.Slot}
    {result : UInt64} {limit base : Nat} {current : CopyRecord} {parents : List CopyRecord}
    {s0 s : Locals} {rest : Program} {Q : Assertion Unit}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hDone : current.next = current.slots.length)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hNext : ∀ store' s', CopyCompleted shape heap0 initial root result limit heap store' current parents →
      CopyLocals base s0 result current.pointer s' →
      s'.get (base + 5) = some (.i64 ((parents.head?.map CopyRecord.pointer).getD 0)) →
      wp m rest Q store' s' host) :
    wp m (headerLoad (base + 1) 40 ++ [.localSet (base + 5)] ++
      restoreRecordCode shape (base + 1) ++ rest) Q store s host :=
  wpX_treeCopyComplete (strict := false) ⟨h, nofun⟩ hLocals hDone hLow hHigh
    (fun store' s' a1 a2 a3 => hNext store' s' a1.1 a2 a3)
#print axioms wp_treeCopyComplete

theorem wpX_treeCopyAscendInv {strict : Bool} {m : Module} {host : HostEnv Unit} {heap0 heap : Heap}
    {initial store : Store Unit} {shape : TreeShape} {root : List LeanExe.Pipeline.Slot}
    {result : UInt64} {limit base : Nat} {current parent : CopyRecord} {parents : List CopyRecord}
    {s0 s : Locals} {rest : Program} {Q : Assertion Unit}
    (hX : CopyCompletedX strict shape heap0 initial root result limit heap store current
      (parent :: parents))
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hFresh : s.get (base + 5) = some (.i64 parent.pointer))
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hNext : ∀ store' s', CopyInvX strict shape heap0 initial root result limit heap store'
      { parent with next := parent.next + 1 } parents →
      CopyLocals base s0 result parent.pointer s' → wpX strict m rest Q store' s' host) :
    wpX strict m (headerLoad (base + 5) 8 ++ [.localSet (base + 2)] ++
      treeSlotAddress (base + 5) (base + 2) ++ [.localGet (base + 1), .store64 0] ++
      treeCopyAdvance (base + 5) (base + 2) ++
      [.localGet (base + 5), .localSet (base + 1)] ++ rest) Q store s host := by
  have h := hX.1
  have hParents : CopyFrames shape heap store parent parents := h.parents
  have hParent := hParents.current
  have hBase := hParent.storage.base
  have hAddress := hParent.storage.address
  have hBelow := hParent.storage.below
  have hTop := h.step.at_.top
  have hApartTail : (copyBlocks store parent parents).Pairwise regionsDisjoint :=
    (List.pairwise_append.mp h.apart).2.1
  have hLow2 : s.params.length ≤ base + 2 := by omega
  have hHigh2 : base + 2 < s.params.length + s.locals.length := Locals.lt_total (by omega)
  cases h.path with
  | child hBound hSlot hPath =>
    have hValue : (parent.slots[parent.next]).ValueOwned heap store current.pointer := by
      rw [hSlot]
      exact h.owned
    have hSourceApart : ∀ r ∈ (Node.record parent.slots).slotRegions store parent.source,
        regionsDisjoint r (block store parent.pointer) := by
      intro r hr
      exact h.sources.apart h.step (by simp) r hr _ (by simp [copyBlocks, CopyRecord.blocks])
    have hPrefixApart : ∀ b ∈ slotsBlocks store parent.pointer 0 (parent.slots.take parent.next),
        regionsDisjoint b (block store parent.pointer) := by
      intro b hb
      exact regionsDisjoint_symm ((List.pairwise_cons.mp hApartTail).1 b (List.mem_append_left _ hb))
    have hValueApart : ∀ b ∈ (parent.slots[parent.next]).valueBlocks store current.pointer,
        regionsDisjoint b (block store parent.pointer) := by
      intro b hb
      rw [hSlot] at hb
      change b ∈ Node.blocks store current.pointer (.record current.slots) at hb
      rw [← current.blocks_done store h.done] at hb
      exact (List.pairwise_append.mp h.apart).2.2 b hb _ (by simp [CopyRecord.blocks])
    simp only [List.append_assoc]
    have hParentAl : strict = true → parent.pointer.toNat % 8 = 0 := fun hs => (hX.2 hs).parent (by omega)
    refine wpX_headerLoad hFresh ?_ (fun hs => ⟨hParentAl hs, rfl⟩) ?_
    · rw [headerAddress_toNat (by change 8 ≤ parent.pointer.toNat; omega) (by omega)]
      change parent.pointer.toNat - 8 + 8 ≤ store.mem.pages * 65536
      omega
    rw [hParent.index]
    refine wpX_localSet_local hLow2 hHigh2 ?_
    let sIndex := setLocal s (base + 2) (.i64 (UInt64.ofNat parent.next))
    have hIndexLocals : CopyLocals base s0 result current.pointer sIndex :=
      hLocals.scratch hLow2 (by omega) (by omega)
    have hParentLocal : sIndex.get (base + 5) = some (.i64 parent.pointer) := by
      rw [Locals.get_setLocal_ne hLow2 (by omega)]
      exact hFresh
    have hIndex : sIndex.get (base + 2) = some (.i64 (UInt64.ofNat parent.next)) :=
      Locals.get_setLocal_same hLow2 hHigh2
    refine wpX_copyRecordAdvance (rest := [.localGet (base + 5), .localSet (base + 1)] ++ rest)
      hParent h.step.at_ hBound hValue hSourceApart hPrefixApart hValueApart
      hParentLocal hIndex hIndexLocals.current hParentAl ?_
    intro store' hParent' hWrite hBlocks
    simp only [hSlot, LeanExe.Pipeline.Slot.valueBlocks] at hBlocks
    have hInv := CopyCompleted.ascendX hX hParent' hWrite hBlocks
    have hLow1 : sIndex.params.length ≤ base + 1 := by change s.params.length ≤ base + 1; omega
    have hHigh1 : base + 1 < sIndex.params.length + sIndex.locals.length := by
      simp only [sIndex, setLocal, List.length_set]
      exact Locals.lt_total (by omega)
    have hNextLocals := hIndexLocals.setCurrent (next := parent.pointer) hLow1
      (by rw [hIndexLocals.frame.positions, ← hLocals.frame.positions]; omega)
    change wpX strict m ([.localGet (base + 5), .localSet (base + 1)] ++ rest) Q store' sIndex host
    simp only [List.cons_append, List.nil_append, wpX_localGet_cons, hParentLocal]
    exact wpX_localSet_local hLow1 hHigh1 (hNext store' _ hInv hNextLocals)

theorem wp_treeCopyAscendInv {m : Module} {host : HostEnv Unit} {heap0 heap : Heap}
    {initial store : Store Unit} {shape : TreeShape} {root : List LeanExe.Pipeline.Slot}
    {result : UInt64} {limit base : Nat} {current parent : CopyRecord} {parents : List CopyRecord}
    {s0 s : Locals} {rest : Program} {Q : Assertion Unit}
    (h : CopyCompleted shape heap0 initial root result limit heap store current (parent :: parents))
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hFresh : s.get (base + 5) = some (.i64 parent.pointer))
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hNext : ∀ store' s', CopyInv shape heap0 initial root result limit heap store'
      { parent with next := parent.next + 1 } parents →
      CopyLocals base s0 result parent.pointer s' → wp m rest Q store' s' host) :
    wp m (headerLoad (base + 5) 8 ++ [.localSet (base + 2)] ++
      treeSlotAddress (base + 5) (base + 2) ++ [.localGet (base + 1), .store64 0] ++
      treeCopyAdvance (base + 5) (base + 2) ++
      [.localGet (base + 5), .localSet (base + 1)] ++ rest) Q store s host :=
  wpX_treeCopyAscendInv (strict := false) ⟨h, nofun⟩ hLocals hFresh hLow hHigh
    (fun store' s' a1 a2 => hNext store' s' a1.1 a2)
#print axioms wp_treeCopyAscendInv

end Verified
