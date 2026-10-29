import Verified.AlignedTreeCopyCode
import Verified.TreeTestCode
import Verified.TreeNewCode

/-!
The slot tests and the start of a record's copy under the flag: the ports of the mask lemmas and
the tests of `TreeTestCode.lean`, of `wp_treeCopyBegin`, and of `wp_treeCopyNew`.  A test reads
the tag of the source record at its pointer, and the start of a copy allocates the new record,
reading the tag for its width, and writes its header words at its pointer minus 16, 40, 24, and
8.  The reads are aligned when the source's pointer is, and the writes when the new record's
pointer is, which `wpX_treeCopyAllocate` gives with its capacity and the heap after it.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem CopyRecord.Holds.maskPushesX {strict : Bool} {m : Module} {host : HostEnv Unit} {shape : TreeShape}
    {heap : Heap} {store : Store Unit} {parent : UInt64} {record : CopyRecord} {s : Locals}
    {src : Nat} (h : record.Holds shape heap store parent) (hHeap : heap.At store)
    (hSrc : s.get src = some (.i64 record.source))
    (hAl : strict = true → record.source.toNat % 8 = 0) :
    PushesWordX strict m host (shape.selectCode (treeTagCode src) shape.mask) store s
      (maskOf record.slots) := by
  obtain ⟨r, -, hMask, hPrefix, -⟩ := id h.layout
  have hSlotted : record.slots ≠ [] := (NodeLayout.slotted h.layout).1
  obtain ⟨-, hRoom⟩ := NodeBorrowed.tagRoom h.borrowed hHeap hSlotted
  rw [hMask]
  exact PushesWordX.selectCode r shape.mask (PushesWordX.tag hSrc hRoom hAl)
    (fun ht => NodeBorrowed.tag h.borrowed hPrefix ht)

/-- The mask code of the slot test pushes the mask of the record whose source is at local
`src`. -/
theorem CopyRecord.Holds.maskPushes {m : Module} {host : HostEnv Unit} {shape : TreeShape}
    {heap : Heap} {store : Store Unit} {parent : UInt64} {record : CopyRecord} {s : Locals}
    {src : Nat} (h : record.Holds shape heap store parent) (hHeap : heap.At store)
    (hSrc : s.get src = some (.i64 record.source)) :
    PushesWord m host (shape.selectCode (treeTagCode src) shape.mask) store s
      (maskOf record.slots) :=
  CopyRecord.Holds.maskPushesX (strict := false) h hHeap hSrc nofun
#print axioms CopyRecord.Holds.maskPushes

theorem CopyRecord.Holds.arrayMaskPushesX {strict : Bool} {m : Module} {host : HostEnv Unit} {shape : TreeShape}
    {heap : Heap} {store : Store Unit} {parent : UInt64} {record : CopyRecord} {s : Locals}
    {src : Nat} (h : record.Holds shape heap store parent) (hHeap : heap.At store)
    (hSrc : s.get src = some (.i64 record.source))
    (hAl : strict = true → record.source.toNat % 8 = 0) :
    PushesWordX strict m host (shape.selectCode (treeTagCode src) shape.arrayMask) store s
      (arrayMaskOf record.slots) := by
  obtain ⟨r, -, -, hPrefix, -, hArrays, -⟩ := id h.layout
  have hSlotted : record.slots ≠ [] := (NodeLayout.slotted h.layout).1
  obtain ⟨-, hRoom⟩ := NodeBorrowed.tagRoom h.borrowed hHeap hSlotted
  rw [hArrays]
  exact PushesWordX.selectCode r shape.arrayMask (PushesWordX.tag hSrc hRoom hAl)
    (fun ht => NodeBorrowed.tag h.borrowed hPrefix ht)

/-- The mask code of the array test pushes the array mask of the record whose source is at local
`src`. -/
theorem CopyRecord.Holds.arrayMaskPushes {m : Module} {host : HostEnv Unit} {shape : TreeShape}
    {heap : Heap} {store : Store Unit} {parent : UInt64} {record : CopyRecord} {s : Locals}
    {src : Nat} (h : record.Holds shape heap store parent) (hHeap : heap.At store)
    (hSrc : s.get src = some (.i64 record.source)) :
    PushesWord m host (shape.selectCode (treeTagCode src) shape.arrayMask) store s
      (arrayMaskOf record.slots) :=
  CopyRecord.Holds.arrayMaskPushesX (strict := false) h hHeap hSrc nofun
#print axioms CopyRecord.Holds.arrayMaskPushes

theorem wpX_treeCopyArrayTest {strict : Bool} {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {base i : Nat} {mask : UInt64}
    {rest : Program} {Q : Assertion Unit}
    (hMask : PushesWordX strict m host (shape.selectCode (treeTagCode (base + 3)) shape.arrayMask) store
      s mask)
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat i)))
    (hNext : wpX strict m rest Q store
      { s with values := .i32 (treeCopyArrayCondition mask i) :: s.values } host) :
    wpX strict m (treeCopyArrayTest shape base ++ rest) Q store s host := by
  rw [treeCopyArrayTest, List.append_assoc]
  apply hMask s.values
  simp only [Locals.get] at hIndex
  by_cases hBit : ((mask >>> (UInt64.ofNat i % 64)) &&& 1) = 0 <;>
    simpa [hIndex, treeCopyArrayCondition, hBit] using hNext

theorem wp_treeCopyArrayTest {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {base i : Nat} {mask : UInt64}
    {rest : Program} {Q : Assertion Unit}
    (hMask : PushesWord m host (shape.selectCode (treeTagCode (base + 3)) shape.arrayMask) store
      s mask)
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat i)))
    (hNext : wp m rest Q store
      { s with values := .i32 (treeCopyArrayCondition mask i) :: s.values } host) :
    wp m (treeCopyArrayTest shape base ++ rest) Q store s host :=
  wpX_treeCopyArrayTest (strict := false) hMask hIndex hNext
#print axioms wp_treeCopyArrayTest

theorem CopyRecord.Holds.bufferMaskPushesX {strict : Bool} {m : Module} {host : HostEnv Unit} {shape : TreeShape}
    {heap : Heap} {store : Store Unit} {parent : UInt64} {record : CopyRecord} {s : Locals}
    {src : Nat} (h : record.Holds shape heap store parent) (hHeap : heap.At store)
    (hSrc : s.get src = some (.i64 record.source))
    (hAl : strict = true → record.source.toNat % 8 = 0) :
    PushesWordX strict m host (shape.selectCode (treeTagCode src) shape.bufferMask) store s
      (bufferMaskOf record.slots) := by
  obtain ⟨r, -, -, hPrefix, -, -, hBuffers⟩ := id h.layout
  have hSlotted : record.slots ≠ [] := (NodeLayout.slotted h.layout).1
  obtain ⟨-, hRoom⟩ := NodeBorrowed.tagRoom h.borrowed hHeap hSlotted
  rw [hBuffers]
  exact PushesWordX.selectCode r shape.bufferMask (PushesWordX.tag hSrc hRoom hAl)
    (fun ht => NodeBorrowed.tag h.borrowed hPrefix ht)

/-- The mask code of the buffer test pushes the buffer mask of the record whose source is at local
`src`. -/
theorem CopyRecord.Holds.bufferMaskPushes {m : Module} {host : HostEnv Unit} {shape : TreeShape}
    {heap : Heap} {store : Store Unit} {parent : UInt64} {record : CopyRecord} {s : Locals}
    {src : Nat} (h : record.Holds shape heap store parent) (hHeap : heap.At store)
    (hSrc : s.get src = some (.i64 record.source)) :
    PushesWord m host (shape.selectCode (treeTagCode src) shape.bufferMask) store s
      (bufferMaskOf record.slots) :=
  CopyRecord.Holds.bufferMaskPushesX (strict := false) h hHeap hSrc nofun
#print axioms CopyRecord.Holds.bufferMaskPushes

theorem wpX_treeCopyBufferTest {strict : Bool} {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {base i : Nat} {mask : UInt64}
    {rest : Program} {Q : Assertion Unit}
    (hMask : PushesWordX strict m host (shape.selectCode (treeTagCode (base + 3)) shape.bufferMask) store
      s mask)
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat i)))
    (hNext : wpX strict m rest Q store
      { s with values := .i32 (treeCopyBufferCondition mask i) :: s.values } host) :
    wpX strict m (treeCopyBufferTest shape base ++ rest) Q store s host := by
  rw [treeCopyBufferTest, List.append_assoc]
  apply hMask s.values
  simp only [Locals.get] at hIndex
  by_cases hBit : ((mask >>> (UInt64.ofNat i % 64)) &&& 1) = 0 <;>
    simpa [hIndex, treeCopyBufferCondition, hBit] using hNext

theorem wp_treeCopyBufferTest {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {base i : Nat} {mask : UInt64}
    {rest : Program} {Q : Assertion Unit}
    (hMask : PushesWord m host (shape.selectCode (treeTagCode (base + 3)) shape.bufferMask) store
      s mask)
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat i)))
    (hNext : wp m rest Q store
      { s with values := .i32 (treeCopyBufferCondition mask i) :: s.values } host) :
    wp m (treeCopyBufferTest shape base ++ rest) Q store s host :=
  wpX_treeCopyBufferTest (strict := false) hMask hIndex hNext
#print axioms wp_treeCopyBufferTest

theorem wpX_treeCopyTest {strict : Bool} {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {base i : Nat} {word mask : UInt64}
    {rest : Program} {Q : Assertion Unit}
    (hMask : PushesWordX strict m host (shape.selectCode (treeTagCode (base + 3)) shape.mask) store s mask)
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat i)))
    (hWord : s.get (base + 4) = some (.i64 word))
    (hNext : wpX strict m rest Q store
      { s with values := .i32 (treeCopyCondition mask i word) :: s.values } host) :
    wpX strict m (treeCopyTest shape base ++ rest) Q store s host := by
  rw [treeCopyTest, List.append_assoc]
  apply hMask s.values
  simp only [Locals.get] at hIndex hWord
  by_cases hBit : ((mask >>> (UInt64.ofNat i % 64)) &&& 1) = 0 <;>
    by_cases hZero : word = 0 <;>
    simpa [hIndex, hWord, treeCopyCondition, hBit, hZero] using hNext

theorem wp_treeCopyTest {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {base i : Nat} {word mask : UInt64}
    {rest : Program} {Q : Assertion Unit}
    (hMask : PushesWord m host (shape.selectCode (treeTagCode (base + 3)) shape.mask) store s mask)
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat i)))
    (hWord : s.get (base + 4) = some (.i64 word))
    (hNext : wp m rest Q store
      { s with values := .i32 (treeCopyCondition mask i word) :: s.values } host) :
    wp m (treeCopyTest shape base ++ rest) Q store s host :=
  wpX_treeCopyTest (strict := false) hMask hIndex hWord hNext
#print axioms wp_treeCopyTest

theorem wpX_treeCopyBegin {strict : Bool} {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} (r : Fin shape.records) {width size : Nat} {store : Store Unit}
    {s : Locals} {ptr input : Nat} {parent : Option Nat} {p source parentValue : UInt64}
    {rest : Program} {Q : Assertion Unit} (hRaw : RecordStorage width heap store p)
    (hHeap : heap.At store) (hPtr : s.get ptr = some (.i64 p))
    (hInput : s.get input = some (.i64 source))
    (hSourceRoom : source.toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hTagged : shape.tagged = true →
      store.mem.read64 source.toUInt32 = UInt64.ofNat (shape.ctorIndex r))
    (hSize : shape.width r = size)
    (hParent : parent.elim (parentValue = 0) (fun pos => s.get pos = some (.i64 parentValue)))
    (hAl : strict = true → p.toNat % 8 = 0 ∧ source.toNat % 8 = 0)
    (hNext : wpX strict m rest Q (beginRecordStore shape.tagged store p source parentValue size) s host) :
    wpX strict m (treeCopyBegin shape input ptr [.localGet input]
      (parent.elim [.constI64 0] (fun pos => [.localGet pos])) ++ rest)
      Q store s host := by
  subst hSize
  have hBase := hRaw.base
  have hAddress := hRaw.address
  have hBelow := hRaw.below
  have hTop := hHeap.top
  have hRoom (back : UInt64) (h8 : 8 ≤ back.toNat) (h40 : back.toNat ≤ 40) :
      (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [headerAddress_toNat (by omega) (by omega)]
    omega
  have hLink (store0 : Store Unit) (hPages : store0.mem.pages = store.mem.pages)
      (hNext0 : wpX strict m rest Q (linkRecordStore store0 p source parentValue) s host) :
      wpX strict m (headerStore ptr 40 (parent.elim [.constI64 0] (fun pos => [.localGet pos])) ++
        (headerStore ptr 24 [.localGet input] ++ (headerStore ptr 8 [.constI64 0] ++ rest)))
        Q store0 s host := by
    have hTail : wpX strict m (headerStore ptr 24 [.localGet input] ++
        (headerStore ptr 8 [.constI64 0] ++ rest)) Q
        (recordHeaderWrite store0 p 40 parentValue) s host := by
      refine wpX_headerStoreLocal hPtr hInput ?_ (fun hs => ⟨(hAl hs).1, rfl⟩) ?_
      · simpa only [recordHeaderWrite, Mem.write64_pages, hPages] using
          hRoom 24 (by decide) (by decide)
      refine wpX_headerStoreWord hPtr ?_ (fun hs => ⟨(hAl hs).1, rfl⟩) hNext0
      simpa only [recordHeaderWrite, Mem.write64_pages, hPages] using
        hRoom 8 (by decide) (by decide)
    have hRoom40 : (p - 40).toUInt32.toNat + 8 ≤ store0.mem.pages * 65536 := by
      rw [hPages]
      exact hRoom 40 (by decide) (by decide)
    cases parent with
    | none =>
      subst parentValue
      exact wpX_headerStoreWord hPtr hRoom40 (fun hs => ⟨(hAl hs).1, rfl⟩) hTail
    | some pos =>
      exact wpX_headerStoreLocal hPtr hParent hRoom40 (fun hs => ⟨(hAl hs).1, rfl⟩) hTail
  simp only [treeCopyBegin, List.append_assoc]
  cases hT : shape.tagged with
  | false =>
    rw [hT] at hNext
    simpa only [Bool.false_eq_true, ite_false, List.nil_append] using hLink store rfl hNext
  | true =>
    rw [hT] at hNext
    simp only [ite_true]
    refine wpX_headerStorePushes hPtr (hRoom 16 (by decide) (by decide))
      (fun hs => ⟨(hAl hs).1, rfl⟩)
      (PushesWordX.selectCode r (fun r => UInt64.ofNat (shape.width r))
        (PushesWordX.tag hInput hSourceRoom (fun hs => (hAl hs).2)) (fun h => hTagged h)) ?_
    exact hLink _ (Mem.write64_pages ..) hNext

theorem wp_treeCopyBegin {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} (r : Fin shape.records) {width size : Nat} {store : Store Unit}
    {s : Locals} {ptr input : Nat} {parent : Option Nat} {p source parentValue : UInt64}
    {rest : Program} {Q : Assertion Unit} (hRaw : RecordStorage width heap store p)
    (hHeap : heap.At store) (hPtr : s.get ptr = some (.i64 p))
    (hInput : s.get input = some (.i64 source))
    (hSourceRoom : source.toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hTagged : shape.tagged = true →
      store.mem.read64 source.toUInt32 = UInt64.ofNat (shape.ctorIndex r))
    (hSize : shape.width r = size)
    (hParent : parent.elim (parentValue = 0) (fun pos => s.get pos = some (.i64 parentValue)))
    (hNext : wp m rest Q (beginRecordStore shape.tagged store p source parentValue size) s host) :
    wp m (treeCopyBegin shape input ptr [.localGet input]
      (parent.elim [.constI64 0] (fun pos => [.localGet pos])) ++ rest)
      Q store s host :=
  wpX_treeCopyBegin (strict := false) r hRaw hHeap hPtr hInput hSourceRoom hTagged hSize hParent
    nofun hNext
#print axioms wp_treeCopyBegin

theorem wpX_treeCopyNew {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit}
    {shape : TreeShape} {heap : Heap} {store : Store Unit} {s : Locals} {dst input : Nat}
    {parent : Option Nat} {source parentValue : UInt64} {slots : List LeanExe.Pipeline.Slot}
    {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (heap.Within store m (allocCost (8 * slots.length)))) Q)
    (hLayout : NodeLayout shape (.record slots)) (hSource : NodeBorrowed heap store source (.record slots))
    (hInput : s.get input = some (.i64 source))
    (hParent : parent.elim (parentValue = 0) (fun pos => s.get pos = some (.i64 parentValue)))
    (hInputNe : input ≠ dst) (hParentNe : ∀ pos, parent = some pos → pos ≠ dst)
    (hLow : s.params.length ≤ dst) (hHigh : dst < s.params.length + s.locals.length)
    (hHeapAl : strict = true → heap.Aligned) (hSrcAl : strict = true → source.toNat % 8 = 0)
    (hNext : ∀ heap' store' ptr,
      Step heap store (fun _ => True) heap' store' [block store' ptr] →
      CopyRecord.Holds shape heap' store' parentValue ⟨source, ptr, slots, 0⟩ →
      heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * slots.length) →
      (strict = true → heap'.Aligned ∧ ptr.toNat % 8 = 0 ∧ capacityAt store' ptr % 8 = 0) →
      wpX strict m rest Q store' (setLocal s dst (.i64 ptr)) host) :
    wpX strict m (treeCopyAllocate shape input dst ++ treeCopyBegin shape input dst [.localGet input]
      (parent.elim [.constI64 0] (fun pos => [.localGet pos])) ++ rest)
      Q store s host := by
  obtain ⟨r, hLength, -, hPrefix, -⟩ := id hLayout
  have hSlotted : slots ≠ [] := (NodeLayout.slotted hLayout).1
  obtain ⟨-, hSourceRoom⟩ := NodeBorrowed.tagRoom hSource hAt hSlotted
  rw [List.append_assoc]
  refine wpX_treeCopyAllocate hm hRt r hAt hHeapAl hCap (PushesWordX.tag hInput hSourceRoom hSrcAl)
    (fun ht => NodeBorrowed.tag hSource hPrefix ht) (by rw [← hLength]; exact hTrap) hLow hHigh ?_
  intro heap' store' ptr hStep hRaw _ hTop hAlloc
  rw [← hLength] at hRaw hTop
  obtain ⟨-, -, -, hCapacity, -⟩ := hRaw.beginRecord shape.tagged slots.length hStep.at_
    (source := source) (parent := parentValue)
  have hSource' := (hStep.nodeBorrowed hSource hLayout.slotted).1
  obtain ⟨-, hSourceRoom'⟩ := NodeBorrowed.tagRoom hSource' hStep.at_ hSlotted
  obtain ⟨hRecord, hAll⟩ := CopyRecord.Holds.beginRecord hLayout hSource hStep hRaw
    (parent := parentValue)
  have hPtr := Locals.get_setLocal_same (s := s) (v := .i64 ptr) hLow hHigh
  have hInput' : (setLocal s dst (.i64 ptr)).get input = some (.i64 source) := by
    rw [Locals.get_setLocal_ne hLow hInputNe]
    exact hInput
  have hParent' : parent.elim (parentValue = 0)
      (fun pos => (setLocal s dst (.i64 ptr)).get pos = some (.i64 parentValue)) := by
    cases parent with
    | none => exact hParent
    | some pos =>
      change (setLocal s dst (.i64 ptr)).get pos = some (.i64 parentValue)
      rw [Locals.get_setLocal_ne hLow (hParentNe pos rfl)]
      exact hParent
  exact wpX_treeCopyBegin (parent := parent) r hRaw hStep.at_ hPtr hInput' hSourceRoom'
    (fun ht => NodeBorrowed.tag hSource' hPrefix ht) hLength.symm hParent'
    (fun hs => ⟨(hAlloc hs).1, hSrcAl hs⟩)
    (hNext heap' _ ptr hAll hRecord hTop fun hs => ⟨(hAlloc hs).2.2, (hAlloc hs).1, by
      rw [hCapacity]; exact (hAlloc hs).2.1⟩)

theorem wp_treeCopyNew {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {shape : TreeShape} {heap : Heap} {store : Store Unit} {s : Locals} {dst input : Nat}
    {parent : Option Nat} {source parentValue : UInt64} {slots : List LeanExe.Pipeline.Slot}
    {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (heap.Within store m (allocCost (8 * slots.length)))) Q)
    (hLayout : NodeLayout shape (.record slots)) (hSource : NodeBorrowed heap store source (.record slots))
    (hInput : s.get input = some (.i64 source))
    (hParent : parent.elim (parentValue = 0) (fun pos => s.get pos = some (.i64 parentValue)))
    (hInputNe : input ≠ dst) (hParentNe : ∀ pos, parent = some pos → pos ≠ dst)
    (hLow : s.params.length ≤ dst) (hHigh : dst < s.params.length + s.locals.length)
    (hNext : ∀ heap' store' ptr,
      Step heap store (fun _ => True) heap' store' [block store' ptr] →
      CopyRecord.Holds shape heap' store' parentValue ⟨source, ptr, slots, 0⟩ →
      heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * slots.length) →
      wp m rest Q store' (setLocal s dst (.i64 ptr)) host) :
    wp m (treeCopyAllocate shape input dst ++ treeCopyBegin shape input dst [.localGet input]
      (parent.elim [.constI64 0] (fun pos => [.localGet pos])) ++ rest)
      Q store s host :=
  wpX_treeCopyNew (strict := false) hm nofun hAt hCap hTrap hLayout hSource hInput hParent hInputNe
    hParentNe hLow hHigh nofun nofun
    (fun heap' store' ptr a1 a2 a3 _ => hNext heap' store' ptr a1 a2 a3)
#print axioms wp_treeCopyNew

end Verified
