import Verified.AlignedTreeCopyArray
import Verified.TreeCopyBufferCode
import Verified.AlignedBytes

/-!
The copy of a buffer slot under the flag: the ports of `CopyInv.freshStep` and
`wp_treeCopyBufferInv`.  The copy reads the buffer's length from the next slot of the source
record, which is aligned with the record, copies the buffer's bytes by `Bytes.wpX_copyOwned`,
whose new object has an aligned root and capacity, and stores the new root into the slot of the
record being copied as a word does.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

/-- `CopyInv.freshStep` with the alignment: the fresh blocks and the heap after them are aligned. -/
theorem CopyInv.freshStepX {strict : Bool} {shape : TreeShape} {heap0 heap heap' : Heap}
    {initial store store1 store' : Store Unit} {root : List LeanExe.Pipeline.Slot}
    {result : UInt64} {limit : Nat} {current : CopyRecord} {parents : List CopyRecord}
    {fresh : List (Nat × Nat)}
    (hX : CopyInvX strict shape heap0 initial root result limit heap store current parents)
    (hWork : CopyWork.Step (current.work parents)
      ({ current with next := current.next + 1 }.work parents))
    (hNew : Step heap store (fun _ => True) heap' store1 fresh)
    (hFreshApart : fresh.Pairwise regionsDisjoint)
    (hTop : heap'.top.toNat ≤ heap.top.toNat + (current.work parents).charge)
    (hCurrent : CopyRecord.Holds shape heap' store'
      ((parents.head?.map CopyRecord.pointer).getD 0) { current with next := current.next + 1 })
    (hWrite : Step heap' store1 (fun r => regionsDisjoint r (block store1 current.pointer))
      heap' store' [])
    (hBlocks : ({ current with next := current.next + 1 } : CopyRecord).blocks store' =
      current.blocks store1 ++ fresh)
    (hAl : strict = true → heap'.Aligned ∧ ∀ b ∈ fresh, b.1 % 8 = 0 ∧ b.2 % 8 = 0) :
    CopyInvX strict shape heap0 initial root result limit heap' store'
      { current with next := current.next + 1 } parents := by
  obtain ⟨h, hA⟩ := hX
  obtain ⟨hFrames1, hSame1, hFresh1⟩ := h.frames.step hNew
  have hStep1 : Step heap0 initial (fun _ => True) heap' store1
      (copyBlocks store1 current parents ++ fresh) := by
    rw [hSame1]
    exact h.step.transBoth hNew (fun _ _ => ⟨trivial, fun _ => trivial⟩)
  have hApart1 : (copyBlocks store1 current parents).Pairwise regionsDisjoint := by
    rw [hSame1]
    exact h.apart
  have hKeep := h.sources.parentsKept
    (hStep1.mono (fun _ h => h) (fun b hb => List.mem_append_left _ hb)) hApart1
  have hFrames := hFrames1.replaceCurrent hWrite hKeep hCurrent
  have hParentBlocks : parents.flatMap (fun record => record.blocks store') =
      parents.flatMap (fun record => record.blocks store1) := by
    cases parents with
    | nil => rfl
    | cons parent parents =>
      have hTail := (hFrames1.2.stepKeeping hWrite hKeep).2.1
      simpa only [copyBlocks, List.flatMap_cons, List.append_eq] using hTail
  have hCopyBlocks : copyBlocks store' { current with next := current.next + 1 } parents =
      current.blocks store1 ++
        (fresh ++ parents.flatMap (fun record => record.blocks store1)) := by
    simp only [copyBlocks, hBlocks, hParentBlocks, List.append_assoc]
  have hAll := hStep1.writeFresh hWrite (by simp [copyBlocks, CopyRecord.blocks])
  have hOld (b : Nat × Nat) (hb : b ∈ current.blocks store1 ∨
      b ∈ parents.flatMap (fun record => record.blocks store1)) :
      b ∈ copyBlocks store current parents := by
    rw [← hSame1]
    simp only [copyBlocks, List.mem_append]
    exact hb
  refine ⟨?_, fun hs => ⟨(hAl hs).1, ?_, ?_⟩⟩
  · refine {
      frames := hFrames
      path := h.path.advance _
      sources := h.sources.advance _
      step := hAll.mono (fun _ _ => trivial) (fun b hb => ?_)
      apart := ?_
      budget := ?_
    }
    · rw [hCopyBlocks] at hb
      simp only [copyBlocks, List.mem_append] at hb ⊢
      rcases hb with hb | hb | hb
      · exact Or.inl (Or.inl hb)
      · exact Or.inr hb
      · exact Or.inl (Or.inr hb)
    · rw [hCopyBlocks]
      have hOldApart : (current.blocks store1 ++
          parents.flatMap (fun record => record.blocks store1)).Pairwise regionsDisjoint :=
        hApart1
      obtain ⟨hA, hB, hAB⟩ := List.pairwise_append.mp hOldApart
      refine List.pairwise_append.mpr ⟨hA, List.pairwise_append.mpr ⟨hFreshApart, hB, ?_⟩, ?_⟩
      · intro f hf b hb
        exact regionsDisjoint_symm (hFresh1 b (hOld b (Or.inr hb)) f hf)
      · intro a ha b hb
        rcases List.mem_append.mp hb with hb | hb
        · exact hFresh1 a (hOld a (Or.inl ha)) b hb
        · exact hAB a ha b hb
    · exact hWork.cost_bound hTop h.budget
  · rw [hCopyBlocks]
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact (hA hs).blocks b (hOld b (Or.inl hb))
    · rcases List.mem_append.mp hb with hb | hb
      · exact (hAl hs).2 b hb
      · exact (hA hs).blocks b (hOld b (Or.inr hb))
  · intro record hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (hA hs).sources current List.mem_cons_self
    · exact (hA hs).sources record (List.mem_cons_of_mem current hr)

theorem wpX_treeCopyBufferInv {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit}
    {heap0 heap : Heap} {initial store : Store Unit} {shape : TreeShape}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit base : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {s0 s : Locals} {data : LeanExe.Bytes}
    {rest : Program} {Q : Assertion Unit}
    (h : CopyInvX strict shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat current.next)))
    (hSource : s.get (base + 3) = some (.i64 current.source))
    (hWord : s.get (base + 4) =
      some (.i64 (store.mem.read64 (slotAddress current.source current.next))))
    (hBound : current.next < current.slots.length)
    (hSlot : current.slots[current.next] = .bytes data)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q)
    (hNext : ∀ heap' store' s',
      CopyInvX strict shape heap0 initial root result limit heap' store'
        { current with next := current.next + 1 } parents →
      CopyLocals base s0 result current.pointer s' → wpX strict m rest Q store' s' host) :
    wpX strict m (treeCopyBuffer base ++ rest) Q store s host := by
  have hCurrent := h.1.frames.current
  obtain ⟨-, -, -, -, hLayout, -⟩ := id hCurrent.layout
  obtain ⟨hNextBound, hLengthSlot⟩ := hLayout.bytes_next current.next hBound data hSlot
  have hBorrows := hCurrent.borrowed.2
  have hRootBorrow := SlotsBorrowed.get current.slots 0 hBorrows current.next hBound
  rw [hSlot] at hRootBorrow
  simp only [Nat.zero_add] at hRootBorrow
  have hLengthBorrow := SlotsBorrowed.get current.slots 0 hBorrows (current.next + 1) hNextBound
  rw [hLengthSlot] at hLengthBorrow
  simp only [Nat.zero_add] at hLengthBorrow
  let rootWord := store.mem.read64 (slotAddress current.source current.next)
  let length := UInt64.ofNat data.data.size
  have hLengthRead : store.mem.read64 (slotAddress current.source (current.next + 1)) = length :=
    hLengthBorrow.1
  have hSourceRep : Bytes.Rep heap store rootWord length data := by
    rcases hRootBorrow.1 with hEmpty | ⟨_, hBuffer⟩
    · refine ⟨?_, Or.inl hEmpty⟩
      show (UInt64.ofNat data.data.size).toNat = data.data.size
      rw [hEmpty.2]
      rfl
    · have hAt := hBuffer.toAt h.1.step.at_
      have := hAt.address
      exact ⟨UInt64.toNat_ofNat_of_lt' (by
        change data.data.size < 18446744073709551616
        omega), Or.inr hBuffer⟩
  have hCharge : Bytes.allocationCost data.data.size ≤ (current.work parents).cost := by
    unfold CopyRecord.work CopyWork.cost
    rw [List.drop_eq_getElem_cons hBound, hSlot]
    simp only [slotsCopyCost]
    omega
  have hBase := hCurrent.storage.base
  have hSrcAddress := hCurrent.borrowed.1.address
  have hSrcBelow := hCurrent.borrowed.1.below
  have hTopAt := h.1.step.at_.top
  have hLow5 : s.params.length ≤ base + 5 := by omega
  have hHigh5 : base + 5 < s.params.length + s.locals.length := Locals.lt_total (by omega)
  have hLow2 : s.params.length ≤ base + 2 := by omega
  have hHigh2 : base + 2 < s.params.length + s.locals.length := Locals.lt_total (by omega)
  have hLow3 : s.params.length ≤ base + 3 := by omega
  have hHigh3 : base + 3 < s.params.length + s.locals.length := Locals.lt_total (by omega)
  -- The index of the length slot, in local `base + 5`.
  simp only [treeCopyBuffer, List.append_assoc, List.cons_append, List.nil_append]
  simp only [wpX_localGet_cons, hIndex, wpX_constI64_cons, wpX_addI64_cons]
  refine wpX_localSet_local hLow5 hHigh5 ?_
  let s1 := setLocal s (base + 5) (.i64 (UInt64.ofNat current.next + 1))
  change wpX strict m _ Q store s1 host
  have hPositions1 : s1.positions = s.positions := by
    simp only [s1, Locals.positions_setLocal]
  have hSource1 : s1.get (base + 3) = some (.i64 current.source) := by
    show (setLocal s (base + 5) _).get (base + 3) = _
    rw [Locals.get_setLocal_ne (s := s) hLow5 (by omega)]
    exact hSource
  have hIndex1 : s1.get (base + 5) = some (.i64 (UInt64.ofNat (current.next + 1))) := by
    show (setLocal s (base + 5) _).get (base + 5) = _
    rw [Locals.get_setLocal_same (s := s) hLow5 hHigh5, UInt64.ofNat_add, UInt64.ofNat_one]
  -- The length, from the source record's slot after the root.
  refine wpX_treeSlotLoad hSource1 hIndex1 ?_ h.sourceAl ?_
  · rw [slotAddress_toNat (by omega)]
    omega
  rw [hLengthRead]
  have hHigh5s1 : base + 5 < s1.params.length + s1.locals.length :=
    Locals.lt_total (by rw [hPositions1]; omega)
  refine wpX_localSet_local (s := s1) hLow5 hHigh5s1 ?_
  let s2 := setLocal s1 (base + 5) (.i64 length)
  change wpX strict m _ Q store s2 host
  have hPositions2 : s2.positions = s.positions := by
    simp only [s2, Locals.positions_setLocal]
    exact hPositions1
  have hWord2 : s2.get (base + 4) = some (.i64 rootWord) := by
    show (setLocal s1 (base + 5) _).get (base + 4) = _
    rw [Locals.get_setLocal_ne (s := s1) hLow5 (by omega)]
    show (setLocal s (base + 5) _).get (base + 4) = _
    rw [Locals.get_setLocal_ne (s := s) hLow5 (by omega)]
    exact hWord
  simp only [wpX_localGet_cons, hWord2]
  have hHigh2s2 : base + 2 < s2.params.length + s2.locals.length :=
    Locals.lt_total (by rw [hPositions2]; omega)
  refine wpX_localSet_local (s := s2) hLow2 hHigh2s2 ?_
  let s3 := setLocal s2 (base + 2) (.i64 rootWord)
  change wpX strict m _ Q store s3 host
  have hPositions3 : s3.positions = s.positions := by
    simp only [s3, Locals.positions_setLocal]
    exact hPositions2
  have hHigh5s1' : base + 5 < s1.params.length + s1.locals.length := hHigh5s1
  have hLength3 : s3.get (base + 5) = some (.i64 length) := by
    show (setLocal s2 (base + 2) _).get (base + 5) = _
    rw [Locals.get_setLocal_ne (s := s2) hLow2 (by omega)]
    exact Locals.get_setLocal_same (s := s1) hLow5 hHigh5s1'
  simp only [wpX_localGet_cons, hLength3]
  have hHigh3s3 : base + 3 < s3.params.length + s3.locals.length :=
    Locals.lt_total (by rw [hPositions3]; omega)
  refine wpX_localSet_local (s := s3) hLow3 hHigh3s3 ?_
  let s4 := setLocal s3 (base + 3) (.i64 length)
  change wpX strict m _ Q store s4 host
  have hRoot4 : s4.get (base + 2) = some (.i64 rootWord) := by
    show (setLocal s3 (base + 3) _).get (base + 2) = _
    rw [Locals.get_setLocal_ne (s := s3) hLow3 (by omega)]
    exact Locals.get_setLocal_same (s := s2) hLow2 hHigh2s2
  have hLength4 : s4.get (base + 3) = some (.i64 length) :=
    Locals.get_setLocal_same (s := s3) hLow3 hHigh3s3
  have hPositions4 : s4.positions = s.positions := by
    simp only [s4, Locals.positions_setLocal]
    exact hPositions3
  have hLocals4 : CopyLocals base s0 result current.pointer s4 :=
    (((hLocals.scratch hLow5 (by omega) (by omega)).scratch (s := s1) hLow5 (by omega)
      (by rw [hPositions1]; omega)).scratch (s := s2) hLow2 (by omega)
      (by rw [hPositions2]; omega)).scratch (s := s3) hLow3 (by omega)
      (by rw [hPositions3]; omega)
  -- The copy of the buffer.
  refine Bytes.wpX_copyOwned hm hRt h.1.step.at_ (fun hs => (h.2 hs).heap) (hSourceRep.toAt h.1.step.at_)
    hSourceRep.payload_region hSourceRep.length_eq hRoot4 hLength4 (by omega) (by omega)
    (by show s.params.length ≤ base + 4; omega) (by omega)
    (by rw [h.1.step.cap m]; exact hCap) (h.1.toCopyProgress.trapCost hCharge hTrap) ?_
  intro heap1 store1 s5 root' hNew hRep hFrame5 hTop hZero hAlloc
  obtain ⟨hFrames1, hSame1, hFresh1⟩ := h.1.frames.step hNew
  have hCurrent1 := hFrames1.current
  have hLow5' : s5.params.length ≤ base + 5 := by rw [hFrame5.params]; show s.params.length ≤ _; omega
  have hHigh5' : base + 5 < s5.params.length + s5.locals.length :=
    Locals.lt_total (by rw [hFrame5.positions, hPositions4]; omega)
  refine wpX_localSet_local hLow5' hHigh5' ?_
  let s6 := setLocal { s5 with values := .i64 root' :: s4.values } (base + 5) (.i64 length)
  have hLow4' : s6.params.length ≤ base + 4 := by
    show s5.params.length ≤ _
    rw [hFrame5.params]
    show s.params.length ≤ _
    omega
  have hHigh4' : base + 4 < s6.params.length + s6.locals.length := by
    simp only [s6, setLocal, List.length_set]
    exact Locals.lt_total (by rw [hFrame5.positions, hPositions4]; omega)
  change wpX strict m (.localSet (base + 4) :: _) Q store1 { s6 with values := .i64 root' :: s4.values }
    host
  refine wpX_localSet_local hLow4' hHigh4' ?_
  let s7 := setLocal { s6 with values := s4.values } (base + 4) (.i64 root')
  change wpX strict m _ Q store1 s7 host
  have hPositions7 : s7.positions = s.positions := by
    simp only [s7, s6, Locals.positions_setLocal, Locals.positions_values]
    rw [hFrame5.positions, hPositions4]
  have hBelow7 (j : Nat) (hj : j < base + 4) : s7.get j = s4.get j := by
    rw [Locals.get_setLocal_ne (s := { s6 with values := s4.values }) hLow4' (by omega)]
    change s6.get j = _
    rw [Locals.get_setLocal_ne (s := { s5 with values := .i64 root' :: s4.values }) hLow5'
      (by omega)]
    exact (hFrame5.below j hj).1
  have hLocals7 : CopyLocals base s0 result current.pointer s7 :=
    ⟨hLocals4.frame.trans ((hFrame5.mono (by omega)).trans
      ((Frame.setValues hLow5' (by omega)
        (by rw [hFrame5.positions, hPositions4]; omega)).trans
        (Frame.setValues hLow4' (by omega)
          (by
            simp only [Locals.positions_setLocal, Locals.positions_values]
            rw [hFrame5.positions, hPositions4]
            omega)))),
      (hBelow7 base (by omega)).trans hLocals4.result,
      (hBelow7 (base + 1) (by omega)).trans hLocals4.current, hLocals4.values⟩
  have hRoot7 : s7.get (base + 4) = some (.i64 root') :=
    Locals.get_setLocal_same (s := { s6 with values := s4.values }) hLow4' hHigh4'
  have hBase1 := hCurrent1.storage.base
  have hAddress1 := hCurrent1.storage.address
  have hBelow1 := hCurrent1.storage.below
  have hTop1 := hNew.at_.top
  -- The index, from the header.
  refine wpX_headerLoad hLocals7.current ?_ (fun hs => ⟨h.pointerAl hs, rfl⟩) ?_
  · rw [headerAddress_toNat (by change 8 ≤ current.pointer.toNat; omega) (by omega)]
    change current.pointer.toNat - 8 + 8 ≤ store1.mem.pages * 65536
    omega
  rw [hCurrent1.index]
  have hLow2' : s7.params.length ≤ base + 2 := by
    rw [hLocals7.frame.params, ← hLocals.frame.params]
    omega
  have hHigh2' : base + 2 < s7.params.length + s7.locals.length :=
    Locals.lt_total (by rw [hPositions7]; omega)
  refine wpX_localSet_local hLow2' hHigh2' ?_
  let s8 := setLocal s7 (base + 2) (.i64 (UInt64.ofNat current.next))
  change wpX strict m _ Q store1 s8 host
  have hLocals8 : CopyLocals base s0 result current.pointer s8 :=
    hLocals7.scratch hLow2' (by omega) (by rw [hPositions7]; omega)
  have hIndex8 : s8.get (base + 2) = some (.i64 (UInt64.ofNat current.next)) :=
    Locals.get_setLocal_same hLow2' hHigh2'
  have hRoot8 : s8.get (base + 4) = some (.i64 root') := by
    rw [Locals.get_setLocal_ne hLow2' (by omega)]
    exact hRoot7
  -- The root into the slot, and the next index.
  have hStep1 : Step heap0 initial (fun _ => True) heap1 store1
      (copyBlocks store current parents ++ Bytes.regions store1 root') :=
    h.1.step.transBoth hNew (fun _ _ => ⟨trivial, fun _ => trivial⟩)
  have hMem : block store1 current.pointer ∈ copyBlocks store current parents := by
    rw [← hSame1]
    simp [copyBlocks, CopyRecord.blocks]
  have hApart1 : (copyBlocks store1 current parents).Pairwise regionsDisjoint := by
    rw [hSame1]
    exact h.1.apart
  simp only [copyBlocks, CopyRecord.blocks, List.cons_append] at hApart1
  have hHead := (List.pairwise_cons.mp hApart1).1
  have hValue : (current.slots[current.next]).ValueOwned heap1 store1 root' := by
    rw [hSlot]
    exact hRep.slotOwned hZero
  have hValueBlocks : (current.slots[current.next]).valueBlocks store1 root' =
      Bytes.regions store1 root' := by
    rw [hSlot]
    exact hRep.slotBlocks hZero
  have hRun := wpX_copyRecordAdvance (rest := rest) (Q := Q) (s := s8) hCurrent1 hNew.at_ hBound
    hValue
    (fun r hr => h.1.sources.apart hStep1 List.mem_cons_self r hr _
      (List.mem_append_left _ hMem))
    (fun b hb => regionsDisjoint_symm (hHead b (List.mem_append_left _ hb)))
    (fun b hb => by
      rw [hValueBlocks] at hb
      exact regionsDisjoint_symm (hFresh1 _ hMem _ hb))
    hLocals8.current hIndex8 hRoot8 h.pointerAl
    (fun store' hHolds hWrite hBlocks => by
      rw [hValueBlocks] at hBlocks
      have hCharge' : (current.work parents).charge = Bytes.allocationCost data.data.size := by
        unfold CopyRecord.work
        rw [List.drop_eq_getElem_cons hBound, hSlot]
        rfl
      exact hNext heap1 store' s8
        (CopyInv.freshStepX h (CopyRecord.work_bytes hBound hSlot) hNew
          (by unfold Bytes.regions; split <;> simp) (by rw [hCharge']; exact hTop) hHolds hWrite
          hBlocks fun hs => ⟨(hAlloc hs).1, fun b hb => by
            unfold Bytes.regions at hb
            split at hb
            · exact nomatch hb
            · rename_i hNz
              rw [List.mem_singleton.mp hb]
              have hB : 4096 + 48 ≤ root'.toNat := by
                rcases hRep.buffer with ⟨h0, -⟩ | hBuf
                · exact absurd h0 hNz
                · exact hBuf.object.base
              obtain ⟨hr, hc⟩ := (hAlloc hs).2 hNz
              simp only [block]
              omega⟩) hLocals8)
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using hRun

end Verified
