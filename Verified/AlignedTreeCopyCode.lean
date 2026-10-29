import Verified.AlignedTreeCopyInv
import LeanExe.ProofKit.AlignedTransfer
import Verified.TreeSlotCode

/-!
The reads and the word steps of the tree copy under the flag: the ports of
`wp_copyRecordAdvance`, `wp_treeCopyRead`, and `wp_treeCopyAdvanceInv`.  The copy stores a word
into the slot of the record being copied at its pointer plus 8 times the slot's index and the next
index into its header at its pointer minus 8, and it reads the record's source from its header at
its pointer minus 24 and the slot of the source.  Each access is aligned when the record's pointer
and source are, which `CopyAligned` gives.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

/-- The pointer of the record being copied. -/
theorem CopyInvX.pointerAl {strict : Bool} {shape : TreeShape} {heap0 heap : Heap}
    {initial store : Store Unit} {root : List LeanExe.Pipeline.Slot} {result : UInt64}
    {limit : Nat} {current : CopyRecord} {parents : List CopyRecord}
    (h : CopyInvX strict shape heap0 initial root result limit heap store current parents) :
    strict = true → current.pointer.toNat % 8 = 0 := fun hs =>
  ((h.2 hs).current (by have := h.1.frames.current.storage.base; omega)).1

/-- The source of the record being copied. -/
theorem CopyInvX.sourceAl {strict : Bool} {shape : TreeShape} {heap0 heap : Heap}
    {initial store : Store Unit} {root : List LeanExe.Pipeline.Slot} {result : UInt64}
    {limit : Nat} {current : CopyRecord} {parents : List CopyRecord}
    (h : CopyInvX strict shape heap0 initial root result limit heap store current parents) :
    strict = true → current.source.toNat % 8 = 0 := fun hs =>
  (h.2 hs).source current List.mem_cons_self


theorem wpX_copyRecordAdvance {strict : Bool} {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} {store : Store Unit} {s : Locals} {ptr index value : Nat}
    {parent word : UInt64} {record : CopyRecord} {rest : Program} {Q : Assertion Unit}
    (h : record.Holds shape heap store parent) (hAt : heap.At store)
    (hBound : record.next < record.slots.length)
    (hValue : (record.slots[record.next]).ValueOwned heap store word)
    (hSourceApart : ∀ r ∈ (Node.record record.slots).slotRegions store record.source,
      regionsDisjoint r (block store record.pointer))
    (hPrefixApart : ∀ b ∈ slotsBlocks store record.pointer 0 (record.slots.take record.next),
      regionsDisjoint b (block store record.pointer))
    (hValueApart : ∀ b ∈ (record.slots[record.next]).valueBlocks store word,
      regionsDisjoint b (block store record.pointer))
    (hPtr : s.get ptr = some (.i64 record.pointer))
    (hIndex : s.get index = some (.i64 (UInt64.ofNat record.next)))
    (hWord : s.get value = some (.i64 word))
    (hAl : strict = true → record.pointer.toNat % 8 = 0)
    (hNext : ∀ store',
      CopyRecord.Holds shape heap store' parent { record with next := record.next + 1 } →
      Step heap store (fun r => regionsDisjoint r (block store record.pointer)) heap store' [] →
      ({ record with next := record.next + 1 } : CopyRecord).blocks store' =
        record.blocks store ++ (record.slots[record.next]).valueBlocks store word →
      wpX strict m rest Q store' s host) :
    wpX strict m (treeSlotAddress ptr index ++ [.localGet value, .store64 0] ++
      treeCopyAdvance ptr index ++ rest) Q store s host := by
  obtain ⟨hRecord, hStep, hBlocks⟩ := h.advance hAt hBound hValue
    hSourceApart hPrefixApart hValueApart
  have hBase := h.storage.base
  have hAddress := h.storage.address
  have hCapacity := h.storage.capacity
  have hBelow := h.storage.below
  have hTop := hAt.top
  rw [List.append_assoc, List.append_assoc]
  refine wpX_treeSlotStore hPtr hIndex hWord ?_ hAl ?_
  · rw [slotAddress_toNat (by omega)]
    omega
  refine wpX_treeCopyAdvance hPtr hIndex ?_ hAl (hNext _ hRecord hStep hBlocks)
  simp only [Mem.write64_pages]
  rw [headerAddress_toNat (by change 8 ≤ record.pointer.toNat; omega) (by omega)]
  change record.pointer.toNat - 8 + 8 ≤ store.mem.pages * 65536
  omega

theorem wp_copyRecordAdvance {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} {store : Store Unit} {s : Locals} {ptr index value : Nat}
    {parent word : UInt64} {record : CopyRecord} {rest : Program} {Q : Assertion Unit}
    (h : record.Holds shape heap store parent) (hAt : heap.At store)
    (hBound : record.next < record.slots.length)
    (hValue : (record.slots[record.next]).ValueOwned heap store word)
    (hSourceApart : ∀ r ∈ (Node.record record.slots).slotRegions store record.source,
      regionsDisjoint r (block store record.pointer))
    (hPrefixApart : ∀ b ∈ slotsBlocks store record.pointer 0 (record.slots.take record.next),
      regionsDisjoint b (block store record.pointer))
    (hValueApart : ∀ b ∈ (record.slots[record.next]).valueBlocks store word,
      regionsDisjoint b (block store record.pointer))
    (hPtr : s.get ptr = some (.i64 record.pointer))
    (hIndex : s.get index = some (.i64 (UInt64.ofNat record.next)))
    (hWord : s.get value = some (.i64 word))
    (hNext : ∀ store',
      CopyRecord.Holds shape heap store' parent { record with next := record.next + 1 } →
      Step heap store (fun r => regionsDisjoint r (block store record.pointer)) heap store' [] →
      ({ record with next := record.next + 1 } : CopyRecord).blocks store' =
        record.blocks store ++ (record.slots[record.next]).valueBlocks store word →
      wp m rest Q store' s host) :
    wp m (treeSlotAddress ptr index ++ [.localGet value, .store64 0] ++
      treeCopyAdvance ptr index ++ rest) Q store s host :=
  wpX_copyRecordAdvance (strict := false) h hAt hBound hValue hSourceApart hPrefixApart hValueApart
    hPtr hIndex hWord nofun hNext
#print axioms wp_copyRecordAdvance

theorem wpX_treeCopyRead {strict : Bool} {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {record : CopyRecord} {parent : UInt64} {base : Nat}
    {rest : Program} {Q : Assertion Unit} (h : record.Holds shape heap store parent)
    (hAt : heap.At store) (hBound : record.next < record.slots.length)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hPtr : s.get (base + 1) = some (.i64 record.pointer))
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat record.next)))
    (hAl : strict = true → record.pointer.toNat % 8 = 0 ∧ record.source.toNat % 8 = 0)
    (hNext : ∀ s', Frame base s s' → s'.get base = s.get base →
      s'.get (base + 1) = some (.i64 record.pointer) →
      s'.get (base + 2) = some (.i64 (UInt64.ofNat record.next)) →
      s'.get (base + 3) = some (.i64 record.source) →
      s'.get (base + 4) = some (.i64 (store.mem.read64 (slotAddress record.source record.next))) →
      s'.values = s.values → wpX strict m rest Q store s' host) :
    wpX strict m (treeCopyRead base ++ rest) Q store s host := by
  have hBase := h.storage.base
  have hAddress := h.storage.address
  have hBelow := h.storage.below
  have hTop := hAt.top
  have hSrcAddress := h.borrowed.1.address
  have hSrcBelow := h.borrowed.1.below
  have hLow3 : s.params.length ≤ base + 3 := by omega
  have hLow4 : s.params.length ≤ base + 4 := by omega
  have hHigh3 : base + 3 < s.params.length + s.locals.length := Locals.lt_total (by omega)
  have hHigh4 : base + 4 < s.params.length + s.locals.length := Locals.lt_total (by omega)
  let word := store.mem.read64 (slotAddress record.source record.next)
  let sSource := setLocal s (base + 3) (.i64 record.source)
  let sValue := setLocal sSource (base + 4) (.i64 word)
  have hLow4Source : sSource.params.length ≤ base + 4 := hLow4
  have hHigh4Source : base + 4 < sSource.params.length + sSource.locals.length := by
    simpa only [sSource, setLocal, List.length_set] using hHigh4
  have hSourceLocal : sSource.get (base + 3) = some (.i64 record.source) :=
    Locals.get_setLocal_same hLow3 hHigh3
  have hIndexLocal : sSource.get (base + 2) = some (.i64 (UInt64.ofNat record.next)) := by
    rw [Locals.get_setLocal_ne hLow3 (by omega)]
    exact hIndex
  have hFrameSource : Frame base s sSource := Frame.set hLow3 (by omega) (by omega)
  have hFrameValue : Frame base sSource sValue := Frame.set hLow4Source (by omega)
    (by rw [hFrameSource.positions]; omega)
  simp only [treeCopyRead, List.append_assoc]
  refine wpX_headerLoad hPtr ?_ (fun hs => ⟨(hAl hs).1, rfl⟩) ?_
  · rw [headerAddress_toNat (by change 24 ≤ record.pointer.toNat; omega) (by omega)]
    change record.pointer.toNat - 24 + 8 ≤ store.mem.pages * 65536
    omega
  rw [h.source]
  refine wpX_localSet_local hLow3 hHigh3 ?_
  refine wpX_treeSlotLoad hSourceLocal hIndexLocal ?_ (fun hs => (hAl hs).2) ?_
  · rw [slotAddress_toNat (by omega)]
    omega
  refine wpX_localSet_local hLow4Source hHigh4Source ?_
  apply hNext sValue (hFrameSource.trans hFrameValue)
  · dsimp only [sValue]
    rw [Locals.get_setLocal_ne hLow4Source (by omega), Locals.get_setLocal_ne hLow3 (by omega)]
  · dsimp only [sValue]
    rw [Locals.get_setLocal_ne hLow4Source (by omega), Locals.get_setLocal_ne hLow3 (by omega)]
    exact hPtr
  · dsimp only [sValue]
    rw [Locals.get_setLocal_ne hLow4Source (by omega)]
    exact hIndexLocal
  · dsimp only [sValue]
    rw [Locals.get_setLocal_ne hLow4Source (by omega)]
    exact hSourceLocal
  · exact Locals.get_setLocal_same hLow4Source hHigh4Source
  · rfl

theorem wp_treeCopyRead {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {record : CopyRecord} {parent : UInt64} {base : Nat}
    {rest : Program} {Q : Assertion Unit} (h : record.Holds shape heap store parent)
    (hAt : heap.At store) (hBound : record.next < record.slots.length)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hPtr : s.get (base + 1) = some (.i64 record.pointer))
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat record.next)))
    (hNext : ∀ s', Frame base s s' → s'.get base = s.get base →
      s'.get (base + 1) = some (.i64 record.pointer) →
      s'.get (base + 2) = some (.i64 (UInt64.ofNat record.next)) →
      s'.get (base + 3) = some (.i64 record.source) →
      s'.get (base + 4) = some (.i64 (store.mem.read64 (slotAddress record.source record.next))) →
      s'.values = s.values → wp m rest Q store s' host) :
    wp m (treeCopyRead base ++ rest) Q store s host :=
  wpX_treeCopyRead (strict := false) h hAt hBound hLow hHigh hPtr hIndex nofun hNext
#print axioms wp_treeCopyRead

theorem wpX_treeCopyAdvanceInv {strict : Bool} {m : Module} {host : HostEnv Unit} {heap0 heap : Heap}
    {initial store : Store Unit} {shape : TreeShape} {root : List LeanExe.Pipeline.Slot}
    {result : UInt64} {limit base : Nat} {current : CopyRecord} {parents : List CopyRecord}
    {s0 s : Locals} {word : UInt64} {rest : Program} {Q : Assertion Unit}
    (h : CopyInvX strict shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat current.next)))
    (hWord : s.get (base + 4) = some (.i64 word)) (hBound : current.next < current.slots.length)
    (hValue : (current.slots[current.next]).ValueOwned heap store word)
    (hNoBlocks : (current.slots[current.next]).valueBlocks store word = [])
    (hWork : CopyWork.Step (current.work parents)
      ({ current with next := current.next + 1 }.work parents))
    (hCharge : (current.work parents).charge = 0)
    (hNext : ∀ store', CopyInvX strict shape heap0 initial root result limit heap store'
      { current with next := current.next + 1 } parents → wpX strict m rest Q store' s host) :
    wpX strict m (treeSlotAddress (base + 1) (base + 2) ++ [.localGet (base + 4), .store64 0] ++
      treeCopyAdvance (base + 1) (base + 2) ++ rest) Q store s host := by
  refine wpX_copyRecordAdvance h.1.frames.current h.1.step.at_ hBound hValue h.1.sourceApart
    h.1.prefixApart (by rw [hNoBlocks]; exact nofun) hLocals.current hIndex hWord h.pointerAl ?_
  intro store' hCurrent hWrite hBlocks
  rw [hNoBlocks, List.append_nil] at hBlocks
  exact hNext store' (CopyInv.advanceStepX h hCurrent hWrite hBlocks hWork hCharge)

theorem wp_treeCopyAdvanceInv {m : Module} {host : HostEnv Unit} {heap0 heap : Heap}
    {initial store : Store Unit} {shape : TreeShape} {root : List LeanExe.Pipeline.Slot}
    {result : UInt64} {limit base : Nat} {current : CopyRecord} {parents : List CopyRecord}
    {s0 s : Locals} {word : UInt64} {rest : Program} {Q : Assertion Unit}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat current.next)))
    (hWord : s.get (base + 4) = some (.i64 word)) (hBound : current.next < current.slots.length)
    (hValue : (current.slots[current.next]).ValueOwned heap store word)
    (hNoBlocks : (current.slots[current.next]).valueBlocks store word = [])
    (hWork : CopyWork.Step (current.work parents)
      ({ current with next := current.next + 1 }.work parents))
    (hCharge : (current.work parents).charge = 0)
    (hNext : ∀ store', CopyInv shape heap0 initial root result limit heap store'
      { current with next := current.next + 1 } parents → wp m rest Q store' s host) :
    wp m (treeSlotAddress (base + 1) (base + 2) ++ [.localGet (base + 4), .store64 0] ++
      treeCopyAdvance (base + 1) (base + 2) ++ rest) Q store s host :=
  wpX_treeCopyAdvanceInv (strict := false) ⟨h, nofun⟩ hLocals hIndex hWord hBound hValue hNoBlocks
    hWork hCharge (fun store' a1 => hNext store' a1.1)
#print axioms wp_treeCopyAdvanceInv

end Verified
